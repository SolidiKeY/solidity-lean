import Solidity.Calculus.Close
import Solidity.Calculus.Surface
import Solidity.Calculus.Closers
import Solidity.Theory.CallerModel.Static

/-!
# The caller-model lattice is strict

One example per adjacent pair of `none < staticOnly < nonReentrant R < any`
(`Calculus/CallerModel.lean`): a formula valid under the weaker model and
refuted under the stronger, by a typed run under it, in the style of
`Examples/Tactics/Callback.lean`.  The lock's examples read the transfer
semantics `withCallback` with the trivial invariant, so what separates those
levels is what the callee may do, not what it must keep.

* **`none < staticOnly`**: `x = 1; to.transfer(0); x = 0;` breaks the
  invariant `x == 0` while control is away.  No callee calls back, so
  nothing is owed (`exit_none`); a callee that may call back, if only to
  read, may observe it (`exit_staticOnly`, KeY's "invariant on exit").
* **`staticOnly < nonReentrant bump`**: `x = 1; to.transfer(0);` keeps
  `x == 1` when the callee cannot write (`lock_staticOnly`), not when it may
  call the unguarded `bump()` (`x = x + 1`, `lock_bump`).
* **`nonReentrant setX < any`**: with `setX()` guarded by the lock
  (`require(!locked); x = 2;`), a callee calling back only into unguarded
  entries keeps `x == 1` (`lock_setX`); one that may leave any state does
  not (`lock_any`).  `setX_guards` proves the lock judgment of `setX`.
-/

namespace Solidity.Theory.CallerModel.Separation

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

/-- `bump()`: `x = x + 1`, unguarded. -/
def bump : Reentry Locked where
  Entry := Unit
  body := fun _ => sol{ x = x + 1; }
  guarded := fun _ => false
  held := lockHeld

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

/-- **A callee that cannot write keeps `x`.** -/
theorem lock_staticOnly : ValidM .staticOnly (.withCallback .top) lockF :=
  fun σ v => holdsR_box_inert (I := .top) (CallerModel.inert_staticOnly _) (fun _ => by simp only [Invariant.top, holds]) rfl
    (fun _ => Iff.rfl) (lock_valid σ v)

/-- **A callee calling back only into unguarded entries keeps `x`**: `setX`
is guarded. -/
theorem lock_setX : ValidM (.nonReentrant setX) (.withCallback .top) lockF :=
  fun σ v => holdsR_box_inert (I := .top) (Reentry.inert fun _ => rfl) (fun _ => by simp only [Invariant.top, holds]) rfl
    (fun _ => Iff.rfl) (lock_valid σ v)

/-- `lock_staticOnly` again, weakened from `lock_setX` (`ValidM.weaken`). -/
theorem lock_staticOnly' : ValidM .staticOnly (.withCallback .top) lockF :=
  ValidM.weaken (.staticNr setX) rfl lock_setX

/-- **A callee that may call `bump()` breaks `x == 1`**: from `before`, with
`to` the address `7`, the callee calls back into `bump()` once. -/
theorem lock_bump : ¬ ValidM (.nonReentrant bump) (.withCallback .top) lockF := by
  intro h
  have H := h before (u 7) _
    (.cons (execOfRun rfl rfl)
      (.cons (execOfRun rfl rfl)
        (.cons (ExecSM.transferResume (st := lockSt 2 true) rfl rfl trivial trivial
            (.tail (.refl _) ⟨(), rfl, {}, _, rfl, rfl, .cons (execOfRunC rfl rfl) .nil, rfl⟩))
          (.cons (execOfRun rfl rfl) .nil))))
  have H2 := H _ ExecFM.nil
  simp only [COut.after, holdsR, holds] at H2
  exact absurd H2 (by with_unfolding_all decide)

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

theorem exit_none : ValidM .none (.withCallback zeroInv) exitF := exit_valid

/-- **A callee that may only read still observes the broken invariant**: the
transfer leaves with `x == 1`. -/
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

end Solidity.Theory.CallerModel.Separation

/-- info: 'Solidity.Theory.CallerModel.Separation.lock_bump' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Theory.CallerModel.Separation.lock_bump
/-- info: 'Solidity.Theory.CallerModel.Separation.lock_any' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Theory.CallerModel.Separation.lock_any
/-- info: 'Solidity.Theory.CallerModel.Separation.lock_setX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Theory.CallerModel.Separation.lock_setX
/-- info: 'Solidity.Theory.CallerModel.Separation.exit_staticOnly' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Theory.CallerModel.Separation.exit_staticOnly
/-- info: 'Solidity.Theory.CallerModel.Separation.exit_none' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Theory.CallerModel.Separation.exit_none
/-- info: 'Solidity.Theory.CallerModel.Separation.setX_guards' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Theory.CallerModel.Separation.setX_guards
/-- info: 'Solidity.Theory.CallerModel.Separation.setX_reachAny' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Theory.CallerModel.Separation.setX_reachAny
