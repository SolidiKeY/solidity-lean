import Solidity.Semantics.CallbackUnwk
import Solidity.Examples.Tactics.DeferredCallback

/-! Reverse callback weakening recovers explicit native executions with a fresh
alias, resumed storage, allocations, paying loops and violated invariants. -/

namespace Solidity.Examples.Tactics.CallbackUnwk

open Solidity.DeferredSource Solidity.Examples.Tactics.DeferredCallback

/-- Recover the original push from a directly constructed weakened callback run. -/
theorem allocation_recovered :
    ∃ o, ExecS keep before (pushBlock (allocatingPaymentAt _) .here) o ∧
      observed o = some 9 ∧ heapLength o = some 1 := by
  have hn : ∃ u, ExecS keep (before.push (t := .alias (.array .uint)) none)
      ((pushBlock (allocatingPaymentAt _) .here).wk (.drop .refl)).2.2 u ∧
        observed u = some 9 ∧ heapLength u = some 1 := by
    refine ⟨_, ExecS.block rfl
      (ExecP.cons (ExecS.transferResume (st := changed) (nt := []) rfl trivial trivial)
        (ExecP.cons (ExecS.det rfl) (ExecP.cons (ExecS.det rfl) ExecP.nil))), ?_⟩
    decide +kernel
  obtain ⟨u, hu, hobs, hheap⟩ := hn
  obtain ⟨o, ho, hr⟩ := Stmt.exec_unwk keep _ (.drop (t := .alias (.array .uint)) .refl)
    before (none, before.env) hu
  rw [hr.eq_lifted] at hobs hheap
  cases o <;> exact ⟨_, ho, hobs, hheap⟩

/-- Removing a fresh alias cannot hide an invariant violation at the payment. -/
theorem violation_recovered : ExecS broken before (pushBlock payment .here) .violated := by
  have hn : ExecS broken (before.push (t := .alias (.array .uint)) none)
      ((pushBlock payment .here).wk (.drop .refl)).2.2 .violated :=
    ExecS.block rfl (ExecP.violated (ExecS.transferViolated (J := broken) rfl (fun h => h)))
  obtain ⟨o, ho, hr⟩ := Stmt.exec_unwk broken _ (.drop (t := .alias (.array .uint)) .refl)
    before (none, before.env) hn
  cases o <;> first | exact ho | exact False.elim hr

def payingLoop : Stmt CallbackContract [] [] :=
  .loop (.unwind 1)
    (.binop .eqB rfl rfl (.read (.root "calls" rfl)) (.simple (.lit 0 rfl)))
    (allocatingPaymentAt []).code

/-- The callback changes the loop guard and its allocation survives the iteration. -/
theorem paying_loop_recovered :
    ∃ o, ExecS keep (State.init CallbackContract) payingLoop o ∧ heapLength o = some 1 := by
  have hn : ∃ u, ExecS keep ((State.init CallbackContract).push (t := .alias (.array .uint)) none)
      (payingLoop.wk (.drop .refl)).2.2 u ∧ heapLength u = some 1 := by
    refine ⟨_, ExecS.loopIter rfl rfl
      (ExecP.cons (ExecS.transferResume (J := keep) (st := changed) (nt := []) rfl trivial trivial)
        (ExecP.cons (ExecS.det rfl) ExecP.nil)) (ExecS.loopExit rfl ?_), ?_⟩
    · rfl
    · decide +kernel
  obtain ⟨u, hu, hh⟩ := hn
  obtain ⟨o, ho, hr⟩ := (Stmt.exec_wk_iff keep payingLoop
    (.drop (t := .alias (.array .uint)) .refl) (State.init CallbackContract)
    (none, (State.init CallbackContract).env)).mp hu
  rw [hr.eq_lifted] at hh
  cases o <;> exact ⟨_, ho, hh⟩

/-- Recover a prefix and remove its memory temporary without losing the allocation. -/
theorem prefix_scope_recovered :
    ∃ o, ExecP keep (State.init CallbackContract) (allocatingPaymentAt []).code o ∧
      heapLength (o.map (Out.drop (allocatingPaymentAt []).code.ext)) = some 1 := by
  have hn : ∃ u, ExecP keep ((State.init CallbackContract).push (t := .alias (.array .uint)) none)
      ((allocatingPaymentAt []).code.wk (.drop .refl)).2.2 u ∧
        heapLength (u.map (Out.drop ((allocatingPaymentAt []).code.wk (.drop .refl)).2.2.ext)) =
          some 1 := by
    refine ⟨_, ExecP.cons
      (ExecS.transferResume (J := keep) (st := changed) (nt := []) rfl trivial trivial)
      (ExecP.cons (ExecS.det rfl) ExecP.nil), ?_⟩
    decide +kernel
  obtain ⟨u, hu, hh⟩ := hn
  obtain ⟨o, ho, hr⟩ := Prog.exec_withoutAlias keep (allocatingPaymentAt []).code
    (State.init CallbackContract) (none : Option (SRef CallbackContract (.ref (.array .uint)))) hu
  rw [hr] at hh
  cases o <;> exact ⟨_, ho, hh⟩

end Solidity.Examples.Tactics.CallbackUnwk
