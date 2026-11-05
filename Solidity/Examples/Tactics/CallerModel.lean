import Solidity.Calculus.Close
import Solidity.Calculus.Surface
import Solidity.Calculus.Closers
import Solidity.Theory.CallerModel.Static

/-!
# The caller-model lattice is strict

One example per adjacent pair of `none < staticOnly < nonReentrant setX <
any` (`Calculus/CallerModel.lean`): a formula valid under the weaker model
and refuted under the stronger, by a typed run under it, in the style of
`Examples/Tactics/Callback.lean`.  The lock's examples read one `Reentry`,
`setX()` (`require(!locked); x = 2;`) guarded by the lock `locked`, and the
transfer semantics `withCallback` with the trivial invariant, so what
separates those levels is what the callee may do, not what it must keep.

* **`none < staticOnly`**: `x = 1; to.transfer(0); x = 0;` breaks the
  invariant `x == 0` while control is away.  Under `none` nothing calls
  back and nothing is owed on exit (`ValidM .none` is `Fml.Valid`, which
  reads no invariant: `exit_none`); under every model that calls back, the
  invariant is owed when control leaves (KeY's "invariant on exit",
  `exit_staticOnly`), whatever the callee then does.  So this pair separates
  by the obligation calling back brings, not by the callee's power; the
  sharper witness (two equal calls answered alike only under `none`) is
  true but not proved here.
* **`staticOnly < nonReentrant setX`**: `x = 1; to.transfer(0);`, the lock
  not taken, keeps `x == 1` when the callee cannot write (`open_staticOnly`),
  not when it may call `setX()`, which the free lock lets through
  (`open_setX`).
* **`nonReentrant setX < any`**: `locked = true; x = 1; to.transfer(0);
  locked = false;` keeps `x == 1` when the lock turns `setX()` away
  (`lock_setX`); a callee that may leave any state breaks it (`lock_any`).
  `setX_guards` proves the lock judgment of `setX`, and `setX_reachAny` that
  a callee calling any entry reaches no more while the lock is held.
-/

namespace Solidity.Examples.Tactics.CallerModel

open Semantics

/-- A `uint`. -/
def u (n : Int) (h : PrimTy.uint.inRange n = true := by decide) : PrimTy.uint.Denote := ⟨n, h⟩

/-- A statement that calls nobody back runs, under every model, as its typed run. -/
theorem execOfRun {C : Contract} {M : CallerModel C} {J : StateInv C} {Γ Γ' : Ctx}
    {σ : State C Γ} {s : Stmt C Γ Γ'} {o : Out C σ.H Γ'} (hf : s.forks = false)
    (h : s.run σ = .ok o) : ExecSM M J σ s (.ok o) := by
  have := ExecSM.det (M := M) (J := J) (σ := σ) (Stmt.forksIn_of_forks hf)
  rwa [h] at this

/-- The same, for a callback run. -/
theorem execOfRunC {C : Contract} {J : StateInv C} {Γ Γ' : Ctx}
    {σ : State C Γ} {s : Stmt C Γ Γ'} {o : Out C σ.H Γ'} (hf : s.forks = false)
    (h : s.run σ = .ok o) : ExecS J σ s (.ok o) := by
  have := ExecS.det (J := J) (σ := σ) (Stmt.forksIn_of_forks hf)
  rwa [h] at this

/-! ## `staticOnly < nonReentrant`, `nonReentrant < any`: the lock -/

/-- A contract with a reentrancy lock. -/
def Locked : Contract := contract!{ uint x; bool locked; }

section Lock

local instance : InContract := ⟨Locked⟩

open scoped Scoped

/-- `locked = true; x = 1; to.transfer(0); locked = false;`, then `x == 1`. -/
def lockF : Fml Locked [] := dl!{
  [ locked = true; x = 1; to.transfer(0); locked = false; ] x == 1 }

/-- Without callbacks, `x` is `1`. -/
theorem lock_valid : ⊨ᶠ dl!{
    [ locked = true; x = 1; to.transfer(0); locked = false; ] x == 1 } := by
  sol_symex
  sol_close

/-- The lock is held: `locked == true`. -/
def lockedF : Fml Locked [] := dl!{ locked == true }

/-- The lock held in a storage. -/
def lockHeld (st : Storage Locked) : Prop :=
  holds ({ storage := st, H := [], heap := Heap.empty, env := () } : State Locked []) lockedF

/-- `setX()`: `require(!locked); x = 2;`, guarded by the lock. -/
def setX : Reentry Locked where
  Entry := Unit
  body := fun _ => sol{ require(!locked); x = 2; }
  guarded := fun _ => true
  held := lockHeld

/-- `Locked`'s storage: `x`, `locked`. -/
def lockSt (x : Int) (b : Bool) (hx : PrimTy.uint.inRange x = true := by decide) : Storage Locked :=
  .cons (.prim (u x hx)) (.cons (.prim b) .nil)

/-- `x = 0`, unlocked, `10` in funds. -/
def before : State Locked [] :=
  { storage := lockSt 0 false, H := [], heap := Heap.empty, env := (), selfBalance := u 10 }

/-- `x = 1; to.transfer(0);`, the lock not taken, then `x == 1`. -/
def openF : Fml Locked [] := dl!{ [ x = 1; to.transfer(0); ] x == 1 }

/-- Without callbacks, `x` is `1`. -/
theorem open_valid : ⊨ᶠ dl!{ [ x = 1; to.transfer(0); ] x == 1 } := by
  sol_symex
  sol_close

/-- **A callee that cannot write keeps `x`.** -/
theorem open_staticOnly : ValidM .staticOnly (.withCallback .top) openF :=
  fun σ v => holdsR_box_inert (I := .top) (CallerModel.inert_staticOnly _ fun _ => True)
    (fun _ => by simp only [Invariant.top, holds]) rfl (Prog.lockedAt_true _ _)
    (fun _ => Iff.rfl) (open_valid σ v)

/-- **With the lock not taken, a callee may call `setX()`**: from `before`,
with `to` the address `7`, it calls back into `setX()`, which the lock lets
through, and `x` is `2`. -/
theorem open_setX : ¬ ValidM (.nonReentrant setX) (.withCallback .top) openF := by
  intro h
  have H := h before (u 7) _
    (.cons (execOfRun rfl rfl)
      (.cons (ExecSM.transferResume (st := lockSt 2 false) rfl rfl trivial trivial
          (.tail (.refl _) ⟨(), .inr ?free, {}, _, rfl, rfl, ExecP.of_run rfl, rfl⟩)) .nil))
  case free => exact fun hh => absurd hh (by with_unfolding_all exact fun h => nomatch h)
  have H2 := H _ ExecFM.nil
  simp only [COut.after, holdsR, holds] at H2
  exact absurd H2 (by with_unfolding_all decide)

/-- **The lock taken, a callee calling back as the lock lets it keeps `x`**:
the only entry, `setX()`, is guarded. -/
theorem lock_setX : ValidM (.nonReentrant setX) (.withCallback .top) lockF := by
  intro σ v
  refine holdsR_box_inert (I := .top) (Reentry.inertAt fun _ => rfl)
    (fun _ => by simp only [Invariant.top, holds]) rfl ?_ (fun _ => Iff.rfl) (lock_valid σ v)
  -- the lock is held before the transfer: `locked = true` ran
  obtain ⟨st, H, heap, env, net, sb, tx⟩ := σ
  cases st with
  | cons a rest =>
    cases rest with
    | cons b rest =>
      cases rest
      refine ⟨fun h => (nomatch h), fun o₁ h₁ => ⟨fun h => (nomatch h), fun o₂ h₂ =>
        ⟨fun _ => ?_, fun _ _ => ⟨fun h => (nomatch h), fun _ _ => trivial⟩⟩⟩⟩
      injection h₁ with h₁
      subst h₁
      injection h₂ with h₂
      subst h₂
      with_unfolding_all exact rfl

/-- `lock_setX` read under `staticOnly` (`ValidM.weaken`). -/
theorem lock_staticOnly : ValidM .staticOnly (.withCallback .top) lockF :=
  ValidM.weaken (.staticNr setX) rfl lock_setX

/-- **A callee that may leave any state breaks `x == 1`.** -/
theorem lock_any : ¬ ValidM .any (.withCallback .top) lockF := by
  intro h
  have H := h before (u 7) _
    (.cons (execOfRun rfl rfl)
      (.cons (execOfRun rfl rfl)
        (.cons (ExecSM.transferResume (st := lockSt 2 true) (nt := []) (sb := u 10) rfl rfl
            trivial trivial trivial)
          (.cons (execOfRun rfl rfl) .nil))))
  have H2 := H _ ExecFM.nil
  simp only [COut.after, holdsR, holds] at H2
  exact absurd H2 (by with_unfolding_all decide)

/-- The weakening theorem asks for positive modalities: `¬ lockF` has one in
a negative position. -/
example : Fml.posModal true (.not lockF) = false := rfl

/-! ### `none < staticOnly` -/

/-- `x == 0`, owed whenever control leaves. -/
def zeroInv : Invariant Locked := ⟨dl!{ x == 0 }, rfl⟩

/-- `x = 1; to.transfer(0); x = 0;`. -/
def exitF : Fml Locked [] := dl!{ x == 0 → [ x = 1; to.transfer(0); x = 0; ] x == 0 }

/-- **With no callee calling back, nothing is owed on exit.** -/
theorem exit_valid : ⊨ᶠ dl!{ x == 0 → [ x = 1; to.transfer(0); x = 0; ] x == 0 } := by
  sol_symex
  sol_close

/-- `exit_valid` read under `none`: `x = 1; to.transfer(0); x = 0;`, no
callee calling back. -/
theorem exit_none : ValidM .none (.withCallback zeroInv) exitF := exit_valid

/-- **Under a model that calls back the invariant is owed on exit**: the
transfer leaves with `x == 1` (`transferViolated`, whatever the callee
does). -/
theorem exit_staticOnly : ¬ ValidM .staticOnly (.withCallback zeroInv) exitF := by
  intro h
  have H := h before (u 7) (by with_unfolding_all exact rfl) _
    (.cons (execOfRun rfl rfl)
      (.violated (ExecSM.transferViolated rfl rfl ?viol)))
  case viol =>
    intro hI
    exact absurd hI (by with_unfolding_all exact fun h => nomatch h)
  exact H

/-- **`setX` is guarded** (the lock judgment, `Reentry.Guards`): while
`locked` holds, its `require(!locked)` reverts, so it never completes. -/
theorem setX_guards (J : StateInv Locked) : setX.Guards J := by
  intro f _ g g' hh hc
  obtain ⟨tx, o, -, -, hr, -⟩ := hc
  have e := ExecP.eq_run hr rfl
  obtain ⟨st, H, heap, env, net, sb, tx0⟩ := g
  cases st with
  | cons a rest =>
    cases rest with
    | cons b rest =>
      cases rest
      cases b with
      | prim v =>
        cases v
        · exact absurd hh (by with_unfolding_all exact fun h => nomatch h)
        · revert e
          with_unfolding_all exact fun h => nomatch h

/-- **What the lock gives `setX`**: from a locked state, a callee calling
back into any entry reaches what one calling only unguarded entries does
(`Reentry.reachAny_iff`; `setX` has no unguarded entry to release the
lock). -/
theorem setX_reachAny (J : StateInv Locked) {g g' : State Locked []}
    (hh : setX.held g.storage) : setX.ReachAny J g g' ↔ setX.Reach J g g' :=
  Reentry.reachAny_iff (setX_guards J) (fun _ hf => Bool.noConfusion hf) hh

end Lock

end Solidity.Examples.Tactics.CallerModel

/-- info: 'Solidity.Examples.Tactics.CallerModel.open_setX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Examples.Tactics.CallerModel.open_setX
/-- info: 'Solidity.Examples.Tactics.CallerModel.lock_any' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Examples.Tactics.CallerModel.lock_any
/-- info: 'Solidity.Examples.Tactics.CallerModel.lock_setX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Examples.Tactics.CallerModel.lock_setX
/-- info: 'Solidity.Examples.Tactics.CallerModel.exit_staticOnly' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Examples.Tactics.CallerModel.exit_staticOnly
/-- info: 'Solidity.Examples.Tactics.CallerModel.exit_none' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Examples.Tactics.CallerModel.exit_none
/-- info: 'Solidity.Examples.Tactics.CallerModel.setX_guards' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Examples.Tactics.CallerModel.setX_guards
/-- info: 'Solidity.Examples.Tactics.CallerModel.setX_reachAny' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Examples.Tactics.CallerModel.setX_reachAny
