import Solidity.Source.Eval
import Solidity.Source.MonetaryWorld

/-! Actual Source monetary-operation range transport. These laws require an
explicit current-and-saved-account invariant. They do not prove whole-program
reachability, G01 authority agreement, or alter refusal behavior. -/
namespace Solidity.Source.MonetaryExecution
open Solidity.Roadmap (Address Word)
variable {E : Env} {Γ : RCtx}

/-- Exact actual credit result, including unchanged full state on overflow. -/
theorem credit_run (locals : Locals E.layout Γ) (state : St E) (address : Address) (value : Word) :
    (credit address value : EM E Γ Unit).run (locals,state) =
      if (state.ex.world.accounts address).balance + value.val < 2^256 then
        (.ok (), (locals,{state with ex := (state.ex.apply
          (.account address (fun account => account.withBalance
            ((state.ex.world.accounts address).balance + value.val))))}))
      else (.error (.revert []),(locals,state)) := by
  by_cases guard : (state.ex.world.accounts address).balance + value.val < 2^256
  · simp only [ExceptT.run, credit, bind, ExceptT.bind, ExceptT.mk, StateT.bind, EM.st, get, getThe, MonadStateOf.get, liftM, monadLift, MonadLift.monadLift, ExceptT.lift, Functor.map, StateT.map, StateT.get, pure, ExceptT.bindCont, ExceptT.pure, StateT.pure, guard, EM.modSt, modify, modifyGet, MonadStateOf.modifyGet, EM.halt, throw, throwThe, MonadExceptOf.throw, dif_pos, StateT.modifyGet, if_true]
  · simp only [ExceptT.run, credit, bind, ExceptT.bind, ExceptT.mk, StateT.bind, EM.st, get, getThe, MonadStateOf.get, liftM, monadLift, MonadLift.monadLift, ExceptT.lift, Functor.map, StateT.map, StateT.get, pure, ExceptT.bindCont, ExceptT.pure, StateT.pure, guard, EM.modSt, modify, modifyGet, MonadStateOf.modifyGet, EM.halt, throw, throwThe, MonadExceptOf.throw, dite_false, if_false]

/-- Exact actual debit result; insufficient funds is normal false, not revert. -/
theorem debit_run (locals : Locals E.layout Γ) (state : St E) (address : Address) (value : Word) :
    (debit address value : EM E Γ Bool).run (locals,state) =
      if value.val ≤ (state.ex.world.accounts address).balance then
        (.ok true, (locals,{state with ex := (state.ex.apply
          (.account address (fun account => account.withBalance
            ((state.ex.world.accounts address).balance - value.val))))}))
      else (.ok false,(locals,state)) := by
  by_cases guard : value.val ≤ (state.ex.world.accounts address).balance
  · simp only [ExceptT.run, debit, bind, ExceptT.bind, ExceptT.mk, StateT.bind, EM.st, get, getThe, MonadStateOf.get, liftM, monadLift, MonadLift.monadLift, ExceptT.lift, Functor.map, StateT.map, StateT.get, pure, ExceptT.bindCont, ExceptT.pure, StateT.pure, guard, EM.modSt, modify, modifyGet, MonadStateOf.modifyGet, dif_pos, StateT.modifyGet, if_true]
  · simp only [ExceptT.run, debit, bind, ExceptT.bind, ExceptT.mk, StateT.bind, EM.st, get, getThe, MonadStateOf.get, liftM, monadLift, MonadLift.monadLift, ExceptT.lift, Functor.map, StateT.map, StateT.get, pure, ExceptT.bindCont, ExceptT.pure, StateT.pure, guard, EM.modSt, modify, modifyGet, MonadStateOf.modifyGet, dite_false, if_false]

theorem credit_preserves (locals : Locals E.layout Γ) (state : St E)
    (address : Address) (value : Word) (fit : state.ex.BalancesFit) :
    ((credit address value : EM E Γ Unit).run (locals,state)).2.2.ex.BalancesFit := by
  rw [credit_run]
  split
  · next guard => exact state.ex.apply_balanceFits address _ fit guard
  · exact fit

theorem debit_preserves (locals : Locals E.layout Γ) (state : St E)
    (address : Address) (value : Word) (fit : state.ex.BalancesFit) :
    ((debit address value : EM E Γ Bool).run (locals,state)).2.2.ex.BalancesFit := by
  rw [debit_run]
  split
  · exact state.ex.apply_balanceFits address _ fit
      (Nat.lt_of_le_of_lt (Nat.sub_le _ _) (fit.1 address))
  · exact fit

/-- Any amount, including zero, is refused at the wide recipient. Exact money
is retained; no Word projection or financial-state cleanup is performed. -/
theorem wide_credit_refused (locals : Locals E.layout Γ) (state : St E)
    (address : Address) (value : Word)
    (wide : (state.ex.world.accounts address).balance = 2^256) :
    (credit address value : EM E Γ Unit).run (locals,state) =
      (.error (.revert []),(locals,state)) := by
  rw [credit_run,wide]
  have refused : ¬ 2^256 + value.val < 2^256 := by omega
  simp only [refused, if_false]

/-- A successful debit does not establish range for arbitrary exact money.
The generic preservation theorem therefore retains its real initial premise. -/
theorem wide_zero_debit (locals : Locals E.layout Γ) (state : St E) (address : Address)
    (wide : (state.ex.world.accounts address).balance = 2^256) :
    let result := (debit address ⟨0,by decide⟩ : EM E Γ Bool).run (locals,state)
    result.1 = .ok true ∧ (result.2.2.ex.world.accounts address).balance = 2^256 := by
  rw [debit_run]
  simp only [Nat.zero_le, if_true, true_and]
  simp only [ExecState.apply, World.set_get, Account.withBalance, Nat.sub_zero, wide]

end Solidity.Source.MonetaryExecution

/-- info: 'Solidity.Source.MonetaryExecution.credit_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Source.MonetaryExecution.credit_run
/-- info: 'Solidity.Source.MonetaryExecution.debit_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Source.MonetaryExecution.debit_run
/-- info: 'Solidity.Source.MonetaryExecution.credit_preserves' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Source.MonetaryExecution.credit_preserves
/-- info: 'Solidity.Source.MonetaryExecution.debit_preserves' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Source.MonetaryExecution.debit_preserves
/-- info: 'Solidity.Source.MonetaryExecution.wide_credit_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Source.MonetaryExecution.wide_credit_refused
/-- info: 'Solidity.Source.MonetaryExecution.wide_zero_debit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Source.MonetaryExecution.wide_zero_debit
