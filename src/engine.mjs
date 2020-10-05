import { Value } from './value.mjs';
import {
  AbruptCompletion,
  EnsureCompletion,
  NormalCompletion,
  ThrowCompletion,
  Q, X,
} from './completion.mjs';
import {
  AsyncBlockStart,
  IsCallable,
  Call, Construct, Assert, GetModuleNamespace,
  PerformPromiseThen, CreateBuiltinFunction,
  GetActiveScriptOrModule,
  CleanupFinalizationRegistry,
  CreateArrayFromList,
  NewPromiseCapability,
} from './abstract-ops/all.mjs';
import {
  BlockDeclarationInstantiation,
  GlobalDeclarationInstantiation,
} from './runtime-semantics/all.mjs';
import { REPLEnvironmentRecord } from './environment.mjs';
import { Evaluate } from './evaluator.mjs';
import { CyclicModuleRecord } from './modules.mjs';
import { CallSite, unwind } from './helpers.mjs';
import * as messages from './messages.mjs';

export const FEATURES = Object.freeze([
  {
    name: 'Top-Level Await',
    flag: 'top-level-await',
    url: 'https://github.com/tc39/proposal-top-level-await',
  },
  {
    name: 'Hashbang Grammar',
    flag: 'hashbang',
    url: 'https://github.com/tc39/proposal-hashbang',
  },
  {
    name: 'RegExp Match Indices',
    flag: 'regexp-match-indices',
    url: 'https://github.com/tc39/proposal-regexp-match-indices',
  },
  {
    name: 'FinalizationRegistry.prototype.cleanupSome',
    flag: 'cleanup-some',
    url: 'https://github.com/tc39/proposal-cleanup-some',
  },
  {
    name: 'Arbitrary Module Namespace Names',
    flag: 'arbitrary-module-namespace-names',
    url: 'https://github.com/tc39/ecma262/pull/2154',
  },
  {
    name: 'item Method',
    flag: 'item-method',
    url: 'https://github.com/tc39/proposal-item-method',
  },
  {
    name: 'REPL parsing goal',
    flag: 'repl-parse-goal',
    url: 'https://github.com/bmeck/js-repl-goal',
  },
].map(Object.freeze));

let agentSignifier = 0;
// #sec-agents
export class Agent {
  constructor(options = {}) {
    // #table-agent-record
    const Signifier = agentSignifier;
    agentSignifier += 1;
    this.AgentRecord = {
      LittleEndian: Value.true,
      CanBlock: Value.true,
      Signifier,
      IsLockFree1: Value.true,
      IsLockFree2: Value.true,
      CandidateExecution: undefined,
      KeptAlive: new Set(),
    };

    // #execution-context-stack
    this.executionContextStack = [];
    const stackPop = this.executionContextStack.pop;
    this.executionContextStack.pop = function pop(ctx) {
      if (!ctx.poppedForTailCall) {
        const popped = stackPop.call(this);
        Assert(popped === ctx);
      }
    };

    // NON-SPEC
    this.jobQueue = [];
    this.hostDefinedOptions = {
      ...options,
      features: FEATURES.reduce((acc, { flag }) => {
        if (options.features) {
          acc[flag] = options.features.includes(flag);
        } else {
          acc[flag] = false;
        }
        return acc;
      }, {}),
    };
  }

  // #running-execution-context
  get runningExecutionContext() {
    return this.executionContextStack[this.executionContextStack.length - 1];
  }

  // #current-realm
  get currentRealmRecord() {
    return this.runningExecutionContext.Realm;
  }

  // #active-function-object
  get activeFunctionObject() {
    return this.runningExecutionContext.Function;
  }

  // Get an intrinsic by name for the current realm
  intrinsic(name) {
    return this.currentRealmRecord.Intrinsics[name];
  }

  // Generate a throw completion using message templates
  Throw(type, template, ...templateArgs) {
    if (type instanceof Value) {
      return ThrowCompletion(type);
    }
    const message = messages[template](...templateArgs);
    const cons = this.currentRealmRecord.Intrinsics[`%${type}%`];
    let error;
    if (type === 'AggregateError') {
      error = X(Construct(cons, [
        X(CreateArrayFromList([])),
        new Value(message),
      ]));
    } else {
      error = X(Construct(cons, [new Value(message)]));
    }
    return ThrowCompletion(error);
  }

  queueJob(queueName, job) {
    const callerContext = this.runningExecutionContext;
    const callerRealm = callerContext.Realm;
    const callerScriptOrModule = GetActiveScriptOrModule();
    const pending = {
      queueName,
      job,
      callerRealm,
      callerScriptOrModule,
    };
    this.jobQueue.push(pending);
  }

  // NON-SPEC: Check if a feature is enabled in this agent.
  feature(name) {
    return this.hostDefinedOptions.features[name];
  }

  // NON-SPEC
  mark(m) {
    this.AgentRecord.KeptAlive.forEach((v) => {
      m(v);
    });
    this.executionContextStack.forEach((e) => {
      m(e);
    });
    this.jobQueue.forEach((j) => {
      m(j.callerRealm);
      m(j.callerScriptOrModule);
    });
  }
}

export let surroundingAgent;
export function setSurroundingAgent(a) {
  surroundingAgent = a;
}

// #sec-execution-contexts
export class ExecutionContext {
  constructor() {
    this.codeEvaluationState = undefined;
    this.Function = undefined;
    this.Realm = undefined;
    this.ScriptOrModule = undefined;
    this.VariableEnvironment = undefined;
    this.LexicalEnvironment = undefined;

    // NON-SPEC
    this.callSite = new CallSite(this);
    this.promiseCapability = undefined;
    this.poppedForTailCall = false;
  }

  copy() {
    const e = new ExecutionContext();
    e.codeEvaluationState = this.codeEvaluationState;
    e.Function = this.Function;
    e.Realm = this.Realm;
    e.ScriptOrModule = this.ScriptOrModule;
    e.VariableEnvironment = this.VariableEnvironment;
    e.LexicalEnvironment = this.LexicalEnvironment;

    e.callSite = this.callSite.clone(e);
    e.promiseCapability = this.promiseCapability;
    return e;
  }

  // NON-SPEC
  mark(m) {
    m(this.Function);
    m(this.Realm);
    m(this.ScriptOrModule);
    m(this.VariableEnvironment);
    m(this.LexicalEnvironment);
    m(this.promiseCapability);
  }
}

// 15.1.10 #sec-runtime-semantics-scriptevaluation
export function ScriptEvaluation(scriptRecord) {
  if (surroundingAgent.hostDefinedOptions.boost?.evaluateScript) {
    return surroundingAgent.hostDefinedOptions.boost.evaluateScript(scriptRecord);
  }

  const globalEnv = scriptRecord.Realm.GlobalEnv;
  const scriptContext = new ExecutionContext();
  scriptContext.Function = Value.null;
  scriptContext.Realm = scriptRecord.Realm;
  scriptContext.ScriptOrModule = scriptRecord;
  scriptContext.VariableEnvironment = globalEnv;
  scriptContext.LexicalEnvironment = globalEnv;
  scriptContext.HostDefined = scriptRecord.HostDefined;
  // Suspend runningExecutionContext
  surroundingAgent.executionContextStack.push(scriptContext);
  const scriptBody = scriptRecord.ECMAScriptCode;
  let result = EnsureCompletion(GlobalDeclarationInstantiation(scriptBody, globalEnv));

  if (result.Type === 'normal') {
    result = EnsureCompletion(unwind(Evaluate(scriptBody)));
  }

  if (result.Type === 'normal' && !result.Value) {
    result = NormalCompletion(Value.undefined);
  }

  // Suspend scriptCtx
  surroundingAgent.executionContextStack.pop(scriptContext);
  // Resume(surroundingAgent.runningExecutionContext);

  return result;
}

// (*ReplParseGoal) #sec-repl-input-evaluation
export function REPLInputEvaluation(replInputRecord) {
  // 1. Let replEnv be replInputRecord.[[Environment]].
  const replEnv = replInputRecord.Environment;
  // 2. Assert: replEnv is a REPL Environment Record.
  Assert(replEnv instanceof REPLEnvironmentRecord);

  // 3. Let replInputContext be a new ECMAScript code execution context.
  const replInputContext = new ExecutionContext();
  // 4. Set the Function of replInputContext to null.
  replInputContext.Function = Value.null;
  // 5. Set the Realm of replInputContext to replInputRecord.[[Realm]].
  replInputContext.Realm = replInputRecord.Realm;
  // 6. Set the ScriptOrModule of replInputContext to replInputRecord.
  replInputContext.ScriptOrModule = replInputRecord;
  // 7. Set the VariableEnvironment of replInputContext to replEnv.
  replInputContext.VariableEnvironment = replEnv;
  // 8. Set the LexicalEnvironment of replInputContext to replEnv.
  replInputContext.LexicalEnvironment = replEnv;
  replInputContext.HostDefined = replInputRecord.HostDefined;
  // 9. Suspend the currently running execution context.
  // 10. Push replInputContext onto the execution context stack; replInputContext is now the running execution context.
  surroundingAgent.executionContextStack.push(replInputContext);
  // 11. Let replInputBody be replInputRecord.[[ECMAScriptCode]].
  const replInputBody = replInputRecord.ECMAScriptCode;

  // 12. Perform ! BlockDeclarationInstantiation(replInputBody, replEnv).
  X(BlockDeclarationInstantiation(replInputBody, replEnv));
  // 13. If replInputRecord.[[HasTopLevelAwait]] is true, then
  if (replInputRecord.HasTopLevelAwait === Value.true) {
    // a. Let promiseCapability be ! NewPromiseCapability(%Promise%).
    const promiseCapability = X(NewPromiseCapability(replInputContext.Realm.Intrinsics['%Promise%']));

    // b. Let asyncContext be a copy of replInputContext.
    const asyncContext = replInputContext.copy();

    // c. Perform ! AsyncBlockStart(promiseCapability, replInputBody, asyncContext).
    X(AsyncBlockStart(promiseCapability, replInputBody, asyncContext));

    // d. Suspend replInputContext and remove it from the execution context stack.
    surroundingAgent.executionContextStack.pop(replInputContext);

    // e. Assert: The execution context stack is not empty.
    // f. Resume the context that is now on the top of the execution context stack as the running execution context.
    // Resume(surroundingAgent.runningExecutionContext);

    // g. Return promiseCapability.
    return promiseCapability;
  } else { // 14. Else,
    // a. Let result be the result of evaluating replInputBody.
    let result = EnsureCompletion(unwind(Evaluate(replInputBody)));

    // b. If result.[[Type]] is normal and result.[[Value]] is empty, then
    if (result.Type === 'normal' && !result.Value) {
      // i. Set result to NormalCompletion(undefined).
      result = NormalCompletion(Value.undefined);
    }

    // c. Suspend replInputContext and remove it from the execution context stack.
    surroundingAgent.executionContextStack.pop(replInputContext);

    // d. Assert: The execution context stack is not empty.
    // e. Resume the context that is now on the top of the execution context stack as the running execution context.
    // Resume(surroundingAgent.runningExecutionContext);

    // f. Return Completion(result).
    return result;
  }
}

// #sec-hostenqueuepromisejob
export function HostEnqueuePromiseJob(job, _realm) {
  surroundingAgent.queueJob('PromiseJobs', job);
}

// #sec-agentsignifier
export function AgentSignifier() {
  // 1. Let AR be the Agent Record of the surrounding agent.
  const AR = surroundingAgent.AgentRecord;
  // 2. Return AR.[[Signifier]].
  return AR.Signifier;
}

export function HostEnsureCanCompileStrings(callerRealm, calleeRealm) {
  if (surroundingAgent.hostDefinedOptions.ensureCanCompileStrings !== undefined) {
    Q(surroundingAgent.hostDefinedOptions.ensureCanCompileStrings(callerRealm, calleeRealm));
  }
  return NormalCompletion(undefined);
}

export function HostPromiseRejectionTracker(promise, operation) {
  const realm = surroundingAgent.currentRealmRecord;
  if (realm && realm.HostDefined.promiseRejectionTracker) {
    X(realm.HostDefined.promiseRejectionTracker(promise, operation));
  }
}

export function HostHasSourceTextAvailable(func) {
  if (surroundingAgent.hostDefinedOptions.hasSourceTextAvailable) {
    return X(surroundingAgent.hostDefinedOptions.hasSourceTextAvailable(func));
  }
  return Value.true;
}

export function HostResolveImportedModule(referencingScriptOrModule, specifier) {
  const realm = referencingScriptOrModule.Realm || surroundingAgent.currentRealmRecord;
  if (realm.HostDefined.resolveImportedModule) {
    specifier = specifier.stringValue();
    if (referencingScriptOrModule !== Value.null) {
      if (!referencingScriptOrModule.HostDefined.moduleMap) {
        referencingScriptOrModule.HostDefined.moduleMap = new Map();
      }
      if (referencingScriptOrModule.HostDefined.moduleMap.has(specifier)) {
        return referencingScriptOrModule.HostDefined.moduleMap.get(specifier);
      }
    }
    const resolved = Q(realm.HostDefined.resolveImportedModule(referencingScriptOrModule, specifier));
    if (referencingScriptOrModule !== Value.null) {
      referencingScriptOrModule.HostDefined.moduleMap.set(specifier, resolved);
    }
    return resolved;
  }
  return surroundingAgent.Throw('Error', 'CouldNotResolveModule', specifier);
}

function FinishDynamicImport(referencingScriptOrModule, specifier, promiseCapability, completion) {
  // 1. If completion is an abrupt completion, then perform ! Call(promiseCapability.[[Reject]], undefined, « completion.[[Value]] »).
  if (completion instanceof AbruptCompletion) {
    X(Call(promiseCapability.Reject, Value.undefined, [completion.Value]));
  } else { // 2. Else,
    // a. Assert: completion is a normal completion and completion.[[Value]] is undefined.
    Assert(completion instanceof NormalCompletion);
    // b. Let moduleRecord be ! HostResolveImportedModule(referencingScriptOrModule, specifier).
    const moduleRecord = X(HostResolveImportedModule(referencingScriptOrModule, specifier));
    // c. Assert: Evaluate has already been invoked on moduleRecord and successfully completed.
    // d. Let namespace be GetModuleNamespace(moduleRecord).
    const namespace = EnsureCompletion(GetModuleNamespace(moduleRecord));
    // e. If namespace is an abrupt completion, perform ! Call(promiseCapability.[[Reject]], undefined, « namespace.[[Value]] »).
    if (namespace instanceof AbruptCompletion) {
      X(Call(promiseCapability.Reject, Value.undefined, [namespace.Value]));
    } else {
      // f. Else, perform ! Call(promiseCapability.[[Resolve]], undefined, « namespace.[[Value]] »).
      X(Call(promiseCapability.Resolve, Value.undefined, [namespace.Value]));
    }
  }
}

export function HostImportModuleDynamically(referencingScriptOrModule, specifier, promiseCapability) {
  surroundingAgent.queueJob('ImportModuleDynamicallyJobs', () => {
    const finish = (c) => FinishDynamicImport(referencingScriptOrModule, specifier, promiseCapability, c);
    const c = (() => {
      const module = Q(HostResolveImportedModule(referencingScriptOrModule, specifier));
      Q(module.Link());
      const maybePromise = Q(module.Evaluate());
      if (module instanceof CyclicModuleRecord) {
        const onFulfilled = CreateBuiltinFunction(([v = Value.undefined]) => {
          finish(NormalCompletion(v));
          return Value.undefined;
        }, []);
        const onRejected = CreateBuiltinFunction(([r = Value.undefined]) => {
          finish(ThrowCompletion(r));
          return Value.undefined;
        }, []);
        PerformPromiseThen(maybePromise, onFulfilled, onRejected);
      } else {
        finish(NormalCompletion(undefined));
      }
    })();
    if (c instanceof AbruptCompletion) {
      finish(c);
    }
  });
  return NormalCompletion(Value.undefined);
}

// #sec-hostgetimportmetaproperties
export function HostGetImportMetaProperties(moduleRecord) {
  const realm = surroundingAgent.currentRealmRecord;
  if (realm.HostDefined.getImportMetaProperties) {
    return X(realm.HostDefined.getImportMetaProperties(moduleRecord.HostDefined.public));
  }
  return [];
}

// #sec-hostfinalizeimportmeta
export function HostFinalizeImportMeta(importMeta, moduleRecord) {
  const realm = surroundingAgent.currentRealmRecord;
  if (realm.HostDefined.finalizeImportMeta) {
    return X(realm.HostDefined.finalizeImportMeta(importMeta, moduleRecord.HostDefined.public));
  }
  return Value.undefined;
}

// #sec-host-cleanup-finalization-registry
const scheduledForCleanup = new Set();
export function HostEnqueueFinalizationRegistryCleanupJob(fg) {
  if (surroundingAgent.hostDefinedOptions.cleanupFinalizationRegistry !== undefined) {
    Q(surroundingAgent.hostDefinedOptions.cleanupFinalizationRegistry(fg));
  } else {
    if (!scheduledForCleanup.has(fg)) {
      scheduledForCleanup.add(fg);
      surroundingAgent.queueJob('FinalizationCleanup', () => {
        scheduledForCleanup.delete(fg);
        CleanupFinalizationRegistry(fg);
      });
    }
  }
  return NormalCompletion(undefined);
}

// #sec-hostmakejobcallback
export function HostMakeJobCallback(callback) {
  // 1. Assert: IsCallable(callback) is true.
  Assert(IsCallable(callback) === Value.true);
  // 2. Return the JobCallback Record { [[Callback]]: callback, [[HostDefined]]: empty }.
  return { Callback: callback, HostDefined: undefined };
}

// #sec-hostcalljobcallback
export function HostCallJobCallback(jobCallback, V, argumentsList) {
  // 1. Assert: IsCallable(jobCallback.[[Callback]]) is true.
  Assert(IsCallable(jobCallback.Callback) === Value.true);
  // 1. Return ? Call(jobCallback.[[Callback]], V, argumentsList).
  return Q(Call(jobCallback.Callback, V, argumentsList));
}
