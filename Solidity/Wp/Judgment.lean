import Solidity.Wp.Monad

/-!
# `Holds ↔ wp`: the dynamic-logic judgment as a weakest precondition

`SolidityJudgment.Holds` (defined by running the interpreter and checking the
postcondition) coincides with the weakest precondition of the monadic
interpreter under the matching modality — box with `Box.wpB`, diamond with
`Dia.wpD`. These two iffs are the bridge every later stage rests on: a
`sol!{…}` goal becomes a wp goal, wp goals decompose along
`execBlockM_cons`/`SolM.bind_run`, and the per-rule wp lemmas do the rest.
-/

namespace Solidity
namespace Wp

open Semantics

/-- The judgment postcondition as a wp postcondition: the post-expression
evaluates to `true` in the final state (evaluation effects included, exactly
as in `SolidityJudgment.check`). -/
def postCond (post : WrappedExpr) : Unit -> State -> Prop := fun _ s =>
  match evalValue s post with
  | .ok (_, Value.bool b) => b = true
  | _ => False

theorem Holds_box_iff (b : Block) (post : WrappedExpr) (s0 : State) :
    (SolidityJudgment.mk ⟨SolidityModality.box, b⟩ post).Holds s0
      ↔ Box.wpB (execBlockM b) (postCond post) s0 := by
  rw [SolidityJudgment.Holds, SolidityJudgment.check, Box.wpB_run]
  simp only [execBlockM_run]
  cases hb : execBlock s0 b with
  | ok s =>
      simp only [Except.map, postCond]
      cases hv : evalValue s post with
      | ok p =>
          obtain ⟨-, v⟩ := p
          cases v <;> simp
      | error h => simp
  | error h => cases h <;> simp [Except.map]

theorem Holds_dia_iff (b : Block) (post : WrappedExpr) (s0 : State) :
    (SolidityJudgment.mk ⟨SolidityModality.diamond, b⟩ post).Holds s0
      ↔ Dia.wpD (execBlockM b) (postCond post) s0 := by
  rw [SolidityJudgment.Holds, SolidityJudgment.check, Dia.wpD_run]
  simp only [execBlockM_run]
  cases hb : execBlock s0 b with
  | ok s =>
      simp only [Except.map, postCond]
      cases hv : evalValue s post with
      | ok p =>
          obtain ⟨-, v⟩ := p
          cases v <;> simp
      | error h => simp
  | error h => cases h <;> simp [Except.map]

/-! ### Smoke tests

The two `SemanticsExamples` from `Semantics.lean`, re-established through the
wp bridge: the wp of the monadic interpreter holds in the initial state iff
the judgment does. (`native_decide`, as in `SemanticsExamples`: the
WF-recursive interpreter does not kernel-reduce, so plain `decide` cannot
evaluate it — symbolic evaluation via equation lemmas is what the Stage 4
verifier will use instead.) -/

namespace SmokeWp

open SoliditySyntax

example :
    Dia.wpD (execBlockM (sol!{ < result = 1 + 2 > (result == 3) }).block.stmts)
      (postCond (sol!{ < result = 1 + 2 > (result == 3) }).post)
      State.exampleStore :=
  (Holds_dia_iff _ _ _).mp (by native_decide)

example :
    Dia.wpD
      (execBlockM (sol!{ < alice.account.balance = 10;
        result = alice.account.balance > (result == 10) }).block.stmts)
      (postCond (sol!{ < alice.account.balance = 10;
        result = alice.account.balance > (result == 10) }).post)
      State.exampleStore :=
  (Holds_dia_iff _ _ _).mp (by native_decide)

end SmokeWp

end Wp
end Solidity
