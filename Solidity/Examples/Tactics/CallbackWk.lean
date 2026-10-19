import Solidity.Semantics.CallbackWk
import Solidity.Examples.Tactics.DeferredCallback

/-! Fresh typed locals preserve callback runs, resumed storage and grown heaps. -/

namespace Solidity.Examples.Tactics.CallbackWk

open Solidity.DeferredSource Solidity.Examples.Tactics.DeferredCallback

def freshIsNone {H : HTy} {Γ : Ctx} :
    COut CallbackContract H (.alias (.array .uint) :: Γ) → Bool
  | .ok a => a.st.env.1.isNone
  | _ => false

/-- `to.transfer(0); new uint[](1); values.push(calls);` keeps a fresh unset alias
while retaining resumed `calls = 9` and the allocated object. -/
theorem allocation_under_fresh_alias :
    ∃ o, ExecS keep (before.push (t := .alias (.array .uint)) none)
      ((pushBlock (allocatingPaymentAt _) .here).wk (.drop .refl)).2.2 o ∧
        observed o = some 9 ∧ heapLength o = some 1 ∧ freshIsNone o = true := by
  obtain ⟨o, he, hobs, hheap⟩ := callback_allocation_survives_scope
  obtain ⟨u, hu, hr⟩ := Stmt.exec_wk keep _ (.drop (t := .alias (.array .uint)) .refl)
    before (none, before.env) he
  refine ⟨u, hu, ?_⟩
  rw [hr.eq_lifted]
  cases o with
  | ok a => exact ⟨hobs, hheap, rfl⟩
  | halt err => cases hobs
  | violated => cases hobs

/-- `to.transfer(0); values.push(calls);` still propagates a broken invariant
when a fresh storage alias is added. -/
example : ExecS broken (before.push (t := .alias (.array .uint)) none)
    ((pushBlock payment .here).wk (.drop .refl)).2.2 .violated := by
  obtain ⟨u, hu, hr⟩ := Stmt.exec_wk broken _ (.drop (t := .alias (.array .uint)) .refl)
    before (none, before.env) callback_violation_propagates
  cases u with
  | ok _ => cases hr
  | halt _ => cases hr
  | violated => exact hu

/-- `to.transfer(0); uint[] memory tmp = new uint[](1);` drops its temporary,
keeps a fresh unset storage alias and retains the allocated object. -/
theorem prefix_scope_keeps_fresh_alias :
    ∃ u, ExecP keep ((State.init CallbackContract).push (t := .alias (.array .uint)) none)
      ((allocatingPaymentAt []).code.wk (.drop .refl)).2.2 u ∧
        heapLength (u.map (Out.drop ((allocatingPaymentAt []).code.wk (.drop .refl)).2.2.ext)) = some 1 ∧
        freshIsNone (u.map (Out.drop ((allocatingPaymentAt []).code.wk (.drop .refl)).2.2.ext)) = true := by
  have hp : ∃ o, ExecP keep (State.init CallbackContract) (allocatingPaymentAt []).code o ∧
      heapLength o = some 1 := by
    refine ⟨_, ExecP.cons (ExecS.transferResume (J := keep) (σ := State.init CallbackContract)
      (st := changed) (nt := []) (r := .simple (.lit 9 rfl)) (a := .simple (.lit 0 rfl))
      rfl rfl trivial trivial) (ExecP.cons (ExecS.det rfl) ExecP.nil), ?_⟩
    decide +kernel
  obtain ⟨o, he, hheap⟩ := hp
  obtain ⟨u, hu, hr⟩ := Prog.exec_afterAlias keep (allocatingPaymentAt []).code
    (State.init CallbackContract) (none : Option (SRef CallbackContract (.ref (.array .uint)))) he
  refine ⟨u, hu, ?_⟩
  rw [hr]
  cases o with
  | ok a => exact ⟨hheap, rfl⟩
  | halt err => cases hheap
  | violated => cases hheap

end Solidity.Examples.Tactics.CallbackWk
