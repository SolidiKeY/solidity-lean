import Solidity.Backend.InternalFlow.Controls

/-! One actual intrinsic loop combines persistent/transient mutation, storage
push/pop, iteration allocation and local scope exit. This is a control for
independent backfill, not the missing general mixed-loop backend theorem. -/
namespace Solidity.Backend.InternalFlow.MixedLoopChecks

open Controls

private def exceptEq {α : Type} [DecidableEq α] : DecidableEq (Except THalt α)
  | .ok a, .ok b => if h : a = b then isTrue (h ▸ rfl)
      else isFalse (fun e => h (Except.ok.inj e))
  | .error a, .error b => if h : a = b then isTrue (h ▸ rfl)
      else isFalse (fun e => h (Except.error.inj e))
  | .ok _, .error _ => isFalse (by intro h; cases h)
  | .error _, .ok _ => isFalse (by intro h; cases h)

private def sumEq {α β : Type} [DecidableEq α] [DecidableEq β] : DecidableEq (Sum α β)
  | .inl a, .inl b => if h : a = b then isTrue (h ▸ rfl)
      else isFalse (fun e => h (Sum.inl.inj e))
  | .inr a, .inr b => if h : a = b then isTrue (h ▸ rfl)
      else isFalse (fun e => h (Sum.inr.inj e))
  | .inl _, .inr _ => isFalse (by intro h; cases h)
  | .inr _, .inl _ => isFalse (by intro h; cases h)


private def observationEq : DecidableEq
    ((Nat × Int × Int × Bool × Nat × Nat) ⊕ TRes (Nat × Int × Int × Bool × Nat × Nat)) :=
  @sumEq _ _ inferInstance (@exceptEq _ inferInstance)

def iteration : Prog contract [.val .bool] [.mem arrayType, .val .bool] :=
  .cons (.assign (.root "p" rfl) (.val (.simple (.lit 7 rfl))))
  (.cons (.assign (.root "t" rfl) (.val (.simple (.lit 9 rfl))))
  (.cons (.push (.loc (.root "a" rfl)) (some (.val (.simple (.lit 11 rfl)))) rfl)
  (.cons (.pop (.loc (.root "a" rfl)))
  (.cons (.assignLocal .here (.simple (.bool false)))
  (.cons (.declMem arrayType (.user "temporary") none rfl rfl) .nil)))))

def initial : State contract [.val .bool] := (State.init contract).push true

def observe (out : Out contract initial.H [.val .bool]) : Nat × Int × Int × Bool × Nat × Nat :=
  (out.st.H.length, (out.st.storage.get persistent.declared).view.1,
    (out.st.storage.get transient.declared).view.1, out.st.env.1,
    (out.st.storage.get (f := "a") (T := .ref arrayType) (by rfl)).view.n,
    (out.st.storage.get (f := "a") (T := .ref arrayType) (by rfl)).view.shadow.toList.length)

/-- A real while-loop exit, with the allocated heap surviving local unwind.
The popped storage array has no live elements but retains its shadow slot. -/
theorem mixed_loop :
    (TRun.loop (.simple (.local .here)) (.push .refl) iteration.runR initial).map observe =
      .ok (1, 7, 9, false, 0, 1) := by
  unfold TRun.loop
  apply loop_observed_of_prefix (n := 2)
  apply @of_decide_eq_true _ (observationEq _ _)
  decide +kernel

/-- Transient data must survive internal loop unwind rather than resetting. -/
theorem wrong_transient_reset :
    (TRun.loop (.simple (.local .here)) (.push .refl) iteration.runR initial).map observe ≠
      .ok (1, 7, 0, false, 0, 1) := by
  rw [mixed_loop]
  intro h
  have impossible : (9 : Int) = 0 := congrArg (fun x => x.2.2.1) (Except.ok.inj h)
  cases impossible

/-- info: 'Solidity.Backend.InternalFlow.MixedLoopChecks.mixed_loop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms mixed_loop
/-- info: 'Solidity.Backend.InternalFlow.MixedLoopChecks.wrong_transient_reset' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms wrong_transient_reset

end Solidity.Backend.InternalFlow.MixedLoopChecks
