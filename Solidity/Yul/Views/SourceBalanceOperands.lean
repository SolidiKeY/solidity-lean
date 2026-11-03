import Solidity.Yul.Views.SourceBalanceReads

namespace Solidity.Yul.Views

/-- Exact compositional equation for ANY actual typed address operand run.
The balance branch observes the operand's resulting state, not the entry
snapshot. The premise is the actual evaluator equation, not view adequacy or
an assumed inverse/safety/coverage law. No operand implementation is replaced. -/
theorem sourceBalanceOperand_run {E Γ payable} (G : Source.Glob E) (F : Source.Fr)
    (n : Nat) (operand : Source.RExpr E Γ (.address payable))
    (s after : Source.EMState E Γ) (address : Roadmap.Address)
    (actual : (Source.evalE G F n operand).run s=(.ok (.val (.address address)),after)) :
    (Source.evalE G F (n+1) (.balance operand)).run s=
      (.ok (.val (uintValueOfWord E.layout (sourceObservedBalance G after address))),after) := by
  have stateRun : (Source.EM.st : Source.EM E Γ (Source.St E)).run after=(.ok after.2,after) := by
    cases after; rfl
  rw [Source.evalE,Source.Hoare.run_bind,actual]
  simp only []
  change (do
    let state ← Source.EM.st
    let word := match (state.ex.world.accounts address).code with
      | some _ => (state.ex.world.accounts address).balance
      | none => G.fixed.ledger G.balance0 state.events address
    pure (Source.RVal.val (Source.intWrap Source.IntTy.u256 word.val))).run after= _
  rw [Source.Hoare.run_bind,stateRun]
  change ((Except.ok (Source.RVal.val (Source.intWrap Source.IntTy.u256 (sourceObservedBalance G after address).val))),after)= _
  rw [sourceUintWrapWord]

/-- ALL actual operand halts propagate with the EXACT successful prefix state.
No balance observation happens after operand failure, even on static frames. -/
theorem sourceBalanceOperand_halt {E Γ payable} (G : Source.Glob E) (F : Source.Fr)
    (n : Nat) (operand : Source.RExpr E Γ (.address payable))
    (s after : Source.EMState E Γ) (error : Source.Halt)
    (actual : (Source.evalE G F n operand).run s=(.error error,after)) :
    (Source.evalE G F (n+1) (.balance operand)).run s=(.error error,after) := by
  rw [Source.evalE,Source.Hoare.run_bind,actual]

/-- Canonical target input observation belongs to the POST-operand snapshot.
Agreement with independently provided target funds remains separate. -/
theorem sourceBalanceOperand_target {E Γ payable} (G : Source.Glob E) (F : Source.Fr)
    (n : Nat) (operand : Source.RExpr E Γ (.address payable))
    (s after : Source.EMState E Γ) (address : Roadmap.Address)
    (actual : (Source.evalE G F n operand).run s=(.ok (.val (.address address)),after)) :
    (Source.evalE G F (n+1) (.balance operand)).run s=
      (.ok (.val (uintValueOfWord E.layout (sourceObservedBalance G after address))),after) ∧
    (uintValueOfWord E.layout (sourceObservedBalance G after address)).word.map environmentWord=
      some (sourceObservedFunds G after (environmentAddress address)) := by
  refine ⟨sourceBalanceOperand_run G F n operand s after address actual,?_⟩
  rw [uintValueOfWord_word,sourceObservedFunds_address]
  rfl

/-- The balance read adds no state effects to the ACTUAL operand result. This
transports every H that holds AFTER that operand; it does not postulate
preservation for arbitrary operand implementations or incoming states. -/
theorem sourceBalanceOperand_post_MemOK {E Γ payable} (G : Source.Glob E) (F : Source.Fr)
    (n : Nat) (operand : Source.RExpr E Γ (.address payable))
    (s after : Source.EMState E Γ) (address : Roadmap.Address)
    (actual : (Source.evalE G F n operand).run s=(.ok (.val (.address address)),after))
    (H : Source.HeapTy) (ok : Source.MemOK E H after) :
    Source.MemOK E H ((Source.evalE G F (n+1) (.balance operand)).run s).2 := by
  rw [sourceBalanceOperand_run G F n operand s after address actual]
  exact ok

end Solidity.Yul.Views
