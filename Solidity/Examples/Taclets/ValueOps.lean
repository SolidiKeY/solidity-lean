import Solidity.Semantics

/-!
# Ports of `keyext.solidity.examples/taclets`: value operators

Each example mirrors one `.key` test verbatim (same statements, same
postcondition) and is verified against the executable semantics.
Premises like `x = 5 ->` become leading declarations, and comparisons
are written parenthesized (`(a < b)`), see `AST.lean`.
-/

namespace Solidity
namespace TacletExamples

/-- `addition-simple.key` -/
example : (sol!{ < result = 1 + 2 > (result == 3) }).Holds := by
  native_decide

/-- `subtraction-simple.key` -/
example : (sol!{ < result = 7 - 2 > (result == 5) }).Holds := by
  native_decide

/-- `multiplication-simple.key` -/
example : (sol!{ < result = 3 * 4 > (result == 12) }).Holds := by
  native_decide

/-- `power-simple.key` -/
example : (sol!{ < result = 2 ** 3 > (result == 8) }).Holds := by
  native_decide

/-- `division-simple.key` -/
example : (sol!{ < result = 8 / 2 > (result == 4) }).Holds := by
  native_decide

/-- `modulo-simple.key` -/
example : (sol!{ < result = 7 % 3 > (result == 1) }).Holds := by
  native_decide

/-- Division by zero reverts: the box judgment holds vacuously and the
diamond judgment fails (KeY `divisionAssignment` revert branch). -/
example : (sol!{ [ result = 8 / 0 ] (result == 0) }).Holds := by
  native_decide
example : ¬ (sol!{ < result = 8 / 0 > (result == 0) }).Holds := by
  native_decide

/-- `less-than-simple.key` -/
example : (sol!{ < result = (3 < 5) > (result == true) }).Holds := by
  native_decide

/-- `less-equal-simple.key` -/
example : (sol!{ < result = (5 <= 5) > (result == true) }).Holds := by
  native_decide

/-- `greater-than-simple.key` -/
example : (sol!{ < result = (5 > 3) > (result == true) }).Holds := by
  native_decide

/-- `greater-equal-simple.key` -/
example : (sol!{ < result = (5 >= 6) > (result == false) }).Holds := by
  native_decide

/-- `logical-and-simple.key` -/
example : (sol!{ < result = true && false > (result == false) }).Holds := by
  native_decide

/-- `logical-or-simple.key` -/
example : (sol!{ < result = true || false > (result == true) }).Holds := by
  native_decide

/-- `logical-not-simple.key` -/
example : (sol!{ < result = !false > (result == true) }).Holds := by
  native_decide

/-- `not-equal-simple.key` -/
example : (sol!{ < result = (3 != 4) > (result == true) }).Holds := by
  native_decide

/-- `unary-minus-simple.key` (`x = 5 ->` becomes a declaration) -/
example : (sol!{ < uint x = 5; result = -x > (result == -5) }).Holds := by
  native_decide

/-- `addition-storage-read.key` -/
example :
    (sol!{ < alice.age = 10; result = alice.age + 1 >
           (result == 11) }).Holds := by
  native_decide

/-- `subtraction-storage-read.key` -/
example :
    (sol!{ < alice.age = 10; result = alice.age - 3 >
           (result == 7) }).Holds := by
  native_decide

/-- `addition-storage-write.key` -/
example :
    (sol!{ < uint x = 5; uint y = 7; alice.age = x + y;
             result = alice.age > (result == 12) }).Holds := by
  native_decide

/-- `addition-both-storage.key` -/
example :
    (sol!{ < alice.age = 10; bob.age = 5;
             result = alice.age + bob.age > (result == 15) }).Holds := by
  native_decide

/-- `localValueDeclInitDrop`/`valueDeclSkip`/`localValueAssign`: value
variable declaration and simple assignment. -/
example :
    (sol!{ < uint x; x = 4; uint y = x + 1; result = y >
           (result == 5) }).Holds := by
  native_decide

/-- Short-circuiting: the right operand of `&&` is not evaluated when the
left is false (an out-of-bounds read would revert otherwise). -/
example :
    (sol!{ < result = false && (values[7] == 0) >
           (result == false) }).Holds := by
  native_decide

/-- `localAddAssign`/`localSubAssign` (Lean `localOpAssign`):
compound assignment on a stack local. -/
example :
    (sol!{ < uint x = 10; x += 5; x -= 3; result = x >
           (result == 12) }).Holds := by
  native_decide

/-- `localDivAssign` zero-divisor branch: `x /= 0` reverts, so the box
judgment holds vacuously … -/
example :
    (sol!{ [ uint x = 10; uint y = 0; x /= y; result = x ]
           (result == 0) }).Holds := by
  native_decide

/-- … and the diamond judgment fails — without this twin the box entry
would also pass if `x /= 0` silently produced `0`. -/
example :
    ¬ (sol!{ < uint x = 10; uint y = 0; x /= y; result = x >
             (result == 0) }).Holds := by
  native_decide

/-- `localPreincrement`/`localPostincrement` (Lean `localIncrement`): bare
`++x;`/`x++;` statements on a stack local (`--` cannot be a token in the
`sol!` grammar — it opens a Lean comment — so the decrement twins are
exercised through `incDecExpr` in `RuleValidation`-style tests). -/
example :
    (sol!{ < uint x = 5; ++x; x++; result = x >
           (result == 7) }).Holds := by
  native_decide

/-- `localPredecrement` (Lean `localIncrement .preDec`), via `incDecExpr`. -/
example :
    (SolidityJudgment.mk
      ⟨.diamond,
        [ Stmt.stackDecl Ty.uint "x"
            (some (SoliditySyntax.intLitExpr 5)),
          Stmt.expr (SoliditySyntax.incDecExpr .preDec
            (SoliditySyntax.rootExpr "x")),
          sstmt!{ result = x } ]⟩
      sexpr!{ (result == 4) }).Holds := by
  native_decide

/-- `addAssignValueRhsCapture` (Lean `compoundAssignValueRhsCapture`):
nonsimple compound-assignment RHS. -/
example :
    (sol!{ < uint x = 1; bob.age = 3; x += bob.age + 2; result = x >
           (result == 6) }).Holds := by
  native_decide

/-- `ternaryCaptureCond`/`ternaryToIf`: `v = c ? e1 : e2` with a complex
condition captured first, then lowered to the statement `if`. -/
example :
    (sol!{ < uint x = 0; bob.age = 3; x = (bob.age > 2) ? 10 : 20;
             result = x > (result == 10) }).Holds := by
  native_decide

/-- Ternary short-circuit: the untaken branch is not evaluated (an
out-of-bounds read would revert otherwise), mirroring `&&`/`||`. -/
example :
    (sol!{ < result = false ? values[7] : 5 >
           (result == 5) }).Holds := by
  native_decide

/-- `ternaryToIfStorage`: storage-path assignment target. -/
example :
    (sol!{ < bool flag = false; age = flag ? 10 : 20; result = age >
           (result == 20) }).Holds := by
  native_decide

end TacletExamples
end Solidity
