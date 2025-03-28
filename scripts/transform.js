'use strict';

const { relative, resolve } = require('path');

const IMPORT_PATH = resolve('./src/index.mts');

function fileToImport(file, refPath) {
  return relative(file.opts.filename, refPath)
    .replace(/\\/g, '/') // Support building on Windows
    .replace('../', './');
}

function findParentStatementPath(path) {
  while (path && !path.isStatement()) {
    path = path.parentPath;
  }
  return path;
}

function getEnclosingConditionalExpression(path) {
  while (path && !path.isStatement()) {
    if (path.isConditionalExpression()) {
      return path;
    }
    path = path.parentPath;
  }
  return null;
}

module.exports = ({ types: t, template }) => {
  function createImportCompletion(file) {
    const r = fileToImport(file, IMPORT_PATH);
    return template.ast(`
      import { Completion } from "${r}";
    `);
  }

  function createSkipDebuggerCompletion(file) {
    const r = fileToImport(file, IMPORT_PATH);
    return template.ast(`
      import { skipDebugger } from "${r}";
    `);
  }

  function createImportAbruptCompletion(file) {
    const r = fileToImport(file, IMPORT_PATH);
    return template.ast(`
      import { AbruptCompletion } from "${r}";
    `);
  }

  function createImportAssert(file) {
    const r = fileToImport(file, IMPORT_PATH);
    return template.ast(`
      import { Assert } from "${r}";
    `);
  }

  function createImportCall(file) {
    const r = fileToImport(file, IMPORT_PATH);
    return template.ast(`
      import { Call } from "${r}";
    `);
  }

  function createImportIteratorClose(file) {
    const r = fileToImport(file, IMPORT_PATH);
    return template.statement.ast`
      import { IteratorClose } from "${r}";
    `;
  }

  function createImportValue(file) {
    const r = fileToImport(file, IMPORT_PATH);
    return template.ast(`
      import { Value } from "${r}";
    `);
  }

  function addSectionFromComments(path) {
    if (path.node.leadingComments) {
      for (const c of path.node.leadingComments) {
        let name;
        if (path.node.id) {
          name = path.node.id.name;
        } else if (path.node.declaration) {
          name = path.node.declaration.id.name;
        } else {
          name = path.node.declarations[0].id.name;
        }
        const lines = c.value.split('\n');
        for (const line of lines) {
          if (/#sec/.test(line)) {
            const section = line.split(' ').find((l) => l.includes('#sec'));
            const url = section.includes('https') ? section : `https://tc39.es/ecma262/${section}`;
            path.insertAfter(template.ast(`${name}.section = '${url}';`));
            return;
          }
        }
      }
    }
  }

  const MACROS = {
    Q: {
      template: template(`
      /* ReturnIfAbrupt */
      let ID = ARGUMENT;
      /* c8 ignore if */ if (ID && typeof ID === 'object' && 'next' in ID) throw new Assert.Error('Forgot to yield*');
      /* c8 ignore if */ if (ID instanceof AbruptCompletion) return ID;
      /* c8 ignore if */ if (ID instanceof Completion) ID = ID.Value;
      `, { preserveComments: true }),
      imports: ['AbruptCompletion', 'Completion', 'Assert'],
    },
    X: {
      template: template(`
      /* X */
      let ID = ARGUMENT;
      /* c8 ignore if */ if (ID && typeof ID === 'object' && 'next' in ID) ID = skipDebugger(ID);
      /* c8 ignore if */ if (ID instanceof AbruptCompletion) throw new Assert.Error(SOURCE, { cause: ID });
      /* c8 ignore if */ if (ID instanceof Completion) ID = ID.Value;
      `, { preserveComments: true }),
      imports: ['Assert', 'Completion', 'AbruptCompletion', 'skipDebugger'],
    },
    IfAbruptCloseIterator: {
      template: template(`
      /* IfAbruptCloseIterator */
      /* c8 ignore if */
      if (%%value%% instanceof AbruptCompletion) return skipDebugger(IteratorClose(%%iteratorRecord%%, %%value%%));
      /* c8 ignore if */
      if (%%value%% instanceof Completion) %%value%% = %%value%%.Value;
      `, { preserveComments: true }),
      imports: ['IteratorClose', 'AbruptCompletion', 'Completion', 'skipDebugger'],
    },
    IfAbruptRejectPromise: {
      template: template(`
      /* IfAbruptRejectPromise */
      /* c8 ignore if */
      if (ID instanceof AbruptCompletion) {
        const hygenicTemp2 = skipDebugger(Call(CAPABILITY.Reject, Value.undefined, [ID.Value]));
        if (hygenicTemp2 instanceof AbruptCompletion) return hygenicTemp2;
        return CAPABILITY.Promise;
      }
      /* c8 ignore if */
      if (ID instanceof Completion) ID = ID.Value;
      `, { preserveComments: true }),
      imports: ['Call', 'Value', 'AbruptCompletion', 'Completion', 'skipDebugger'],
    },
  };
  MACROS.ReturnIfAbrupt = MACROS.Q;
  const MACRO_NAMES = Object.keys(MACROS);

  return {
    visitor: {
      Program: {
        enter(path, state) {
          state.needed = {};
        },
        exit(path, state) {
          if (state.needed.skipDebugger) {
            path.node.body.unshift(createSkipDebuggerCompletion(state.file));
          }
          if (state.needed.Completion) {
            path.node.body.unshift(createImportCompletion(state.file));
          }
          if (state.needed.AbruptCompletion) {
            path.node.body.unshift(createImportAbruptCompletion(state.file));
          }
          if (state.needed.Assert) {
            path.node.body.unshift(createImportAssert(state.file));
          }
          if (state.needed.Call) {
            path.node.body.unshift(createImportCall(state.file));
          }
          if (state.needed.IteratorClose) {
            path.unshiftContainer('body', createImportIteratorClose(state.file));
          }
          if (state.needed.Value) {
            path.node.body.unshift(createImportValue(state.file));
          }
        },
      },
      CallExpression(path, state) {
        if (!t.isIdentifier(path.node.callee)) {
          return;
        }

        const macroName = path.node.callee.name;
        if (MACRO_NAMES.includes(macroName)) {
          const enclosingConditional = getEnclosingConditionalExpression(path);
          if (enclosingConditional !== null) {
            if (enclosingConditional.parentPath.isVariableDeclarator()) {
              const declaration = enclosingConditional.parentPath.parentPath;
              const id = enclosingConditional.parentPath.get('id');
              declaration.replaceWithMultiple(template.ast(`
              let ${id};
              if (${enclosingConditional.get('test')}) {
                ${id} = ${enclosingConditional.get('consequent')}
              } else {
                ${id} = ${enclosingConditional.get('alternate')}
              }
              `));
              return;
            } else {
              throw path.buildCodeFrameError('Macros may not be used within conditional expressions');
            }
          }

          const macro = MACROS[macroName];
          const [argument] = path.node.arguments;

          if (macro === MACROS.Q && (t.isReturnStatement(path.parentPath) || path.parentPath.isArrowFunctionExpression())) {
            path.replaceWith(path.node.arguments[0]);
            return;
          }

          if (path.parentPath.isArrowFunctionExpression()) {
            throw path.buildCodeFrameError('Macros may not be the sole expression of an arrow function');
          }

          const statementPath = findParentStatementPath(path);

          macro.imports.forEach((i) => {
            state.needed[i] = path.scope.getBinding(i) === undefined;
          });

          if (macro === MACROS.Q && t.isIdentifier(argument)) {
            const binding = path.scope.getBinding(argument.name);
            binding.path.parent.kind = 'let';
            statementPath.insertBefore(template(`
              /* c8 ignore if */
              if (ID instanceof AbruptCompletion) {
                return ID;
              }
              /* c8 ignore if */
              if (ID instanceof Completion) {
                ID = ID.Value;
              }
            `, { preserveComments: true })({ ID: argument }));
            path.replaceWith(argument);
          } else {
            if (macro === MACROS.IfAbruptRejectPromise) {
              const [, capability] = path.node.arguments;
              if (!t.isIdentifier(argument)) {
                throw path.get('arguments.0').buildCodeFrameError('First argument to IfAbruptRejectPromise should be an identifier');
              }
              if (!t.isIdentifier(capability)) {
                throw path.get('arguments.1').buildCodeFrameError('Second argument to IfAbruptRejectPromise should be an identifier');
              }
              const binding = path.scope.getBinding(argument.name);
              binding.path.parent.kind = 'let';
              statementPath.insertBefore(macro.template({ ID: argument, CAPABILITY: capability }));
              try {
                path.remove();
              } catch (e) {
                throw path.get('arguments.0').buildCodeFrameError(`Macros error: ${e.message}`);
              }
            } else if (macro === MACROS.IfAbruptCloseIterator) {
              if (!t.isIdentifier(argument)) {
                throw path.get('arguments.0').buildCodeFrameError('First argument to IfAbruptCloseIterator should be an identifier');
              }
              const iteratorRecord = path.get('arguments.1');
              if (!iteratorRecord.isIdentifier()) {
                throw iteratorRecord.buildCodeFrameError('Second argument to IfAbruptCloseIterator should be an identifier');
              }
              const binding = path.scope.getBinding(argument.name);
              binding.path.parent.kind = 'let';
              statementPath.insertBefore(
                macro.template({
                  value: argument,
                  iteratorRecord: iteratorRecord.node,
                }),
              );
              path.remove();
            } else {
              const id = statementPath.scope.generateUidIdentifier();
              const replacement = {
                ARGUMENT: argument,
                ID: id,
              };
              if (macro === MACROS.X) {
                replacement.SOURCE = t.stringLiteral(`! ${path.get('arguments.0').getSource()} returned an abrupt completion`);
              }
              statementPath.insertBefore(macro.template(replacement));
              path.replaceWith(id);
            }
          }
        } else if (macroName === 'Assert') {
          path.node.arguments.push(t.stringLiteral(path.get('arguments.0').getSource()));
        }
      },
      SwitchCase(path) {
        const n = path.node.consequent[0];
        if (t.isThrowStatement(n) && t.isNewExpression(n.argument) && n.argument.callee.name === 'OutOfRange') {
          path.node.leadingComments = path.node.leadingComments || [];
          path.node.leadingComments.push({ type: 'CommentBlock', value: 'c8 ignore next' });
        }
      },
      FunctionDeclaration(path) {
        addSectionFromComments(path);
      },
      VariableDeclaration(path) {
        if (path.get('declarations.0.init').isArrowFunctionExpression() || path.get('declarations.0.init').isFunctionExpression()) {
          addSectionFromComments(path);
        }
      },
      ExportNamedDeclaration(path) {
        if (path.get('declaration').isFunctionDeclaration()) {
          addSectionFromComments(path);
        }
      },
    },
  };
};
