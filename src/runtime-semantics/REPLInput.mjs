import { Evaluate } from '../evaluator.mjs';

// (*ReplParseGoal)
// REPLInput :
//   Script[+Await]
export function* Evaluate_REPLInput({ Script }) {
  return yield* Evaluate(Script);
}
