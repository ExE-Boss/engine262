import { Evaluate, type ExpressionEvaluator } from '../evaluator.mts';
import { GetValue } from '../abstract-ops/all.mts';
import { Q } from '../completion.mts';
import type { ParseNode } from '../parser/ParseNode.mts';
import { ApplyStringOrNumericBinaryOperator, type BinaryOperator } from './all.mts';

/** https://tc39.es/ecma262/#sec-evaluatestringornumericbinaryexpression */
export function* EvaluateStringOrNumericBinaryExpression(leftOperand: ParseNode.Expression, opText: BinaryOperator, rightOperand: ParseNode.Expression): ExpressionEvaluator {
  // 1. Let lref be the result of evaluating leftOperand.
  const lref = yield* Evaluate(leftOperand);
  // 2. Let lval be ? GetValue(lref).
  const lval = Q(GetValue(lref));
  // 3. Let rref be the result of evaluating rightOperand.
  const rref = yield* Evaluate(rightOperand);
  // 4. Let rval be ? GetValue(rref).
  const rval = Q(GetValue(rref));
  // 5. Return ? ApplyStringOrNumericBinaryOperator(lval, opText, rval).
  return Q(ApplyStringOrNumericBinaryOperator(lval, opText, rval));
}
