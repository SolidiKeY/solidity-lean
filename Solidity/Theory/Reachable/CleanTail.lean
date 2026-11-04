import Solidity.Theory.Reachable.Mode
import Solidity.Calculus.TailMode

/-!
# Clean tails follow from reachability (O12 over O6)

`TailMode.clean` assumes the starting storage's array tails clean
(`Calculus/TailMode.lean`). Under the `reachable` mode that assumption is
discharged once for a contract whose constructor and entry points expose
nothing (`Prog.exposesNone`, `Typing/CleanTailRun.lean`): every world it
reaches has clean tails (`cleanTail_invariant`), so every entry state does,
and what `.clean` proves holds under `.reachable`
(`ValidTail.validStart_reachable`).

The transaction boundary resets the transient cells to their defaults
(`Storage.resetTransient`), which keeps clean tails
(`Storage.resetTransient_cleanTail`); a rollback and waiting keep the
storage. An interface that admits an entry exposing a dangling alias
reaches a dirty tail, and the implication fails there
(`Theory/Reachable/Witness.lean`, `dirty_refutes`).
-/

namespace Solidity

theorem SFields.all_anon {P : Hered} {fs : List (Name × Ty)} :
    (L : List Name) → {x y : SFields fs} → x.All P → y.All P → (SFields.anon L x y).All P
  | [], _, _, hx, _ => hx
  | r :: L, x, y, hx, hy => by
    rw [SFields.anon_cons]
    have ih := SFields.all_anon L hx hy
    unfold SFields.copyFrom
    split
    · exact SFields.all_set _ _ ih (SFields.all_get _ _ hy)
    · exact ih

/-- **Resetting the transient cells keeps clean tails**: a reset root reads
its default, whose tails are clean. -/
theorem Storage.resetTransient_cleanTail {C : Contract} {st : Storage C}
    (h : st.CleanTail) : (Storage.resetTransient st).CleanTail :=
  SFields.all_anon _ h (Storage.init_cleanTail C)

end Solidity

namespace Solidity.Reachable

open Lifetime

variable {C : Contract} {D A : Type}

/-- **Every program of the interface exposes nothing**: the constructors
and every entry call. -/
def ExposesNone (M : System C D A) : Prop :=
  (∀ d, (M.deploy d).exposesNone = true) ∧ ∀ a, (M.call a).exposesNone = true

/-- A world's storage has clean tails. -/
def CleanWorld (s : World C) : Prop := s.storage.CleanTail

private theorem ofState_clean {Γ : Ctx} {σ : State C Γ} (h : σ.storage.CleanTail) :
    CleanWorld (World.ofState σ) :=
  Storage.resetTransient_cleanTail h

/-- **Clean tails are the invariant of a contract that exposes nothing**,
by induction over its entry points: the constructor runs from the default
storage, each committed entry from a reset storage with no alias local, a
rollback and waiting keep the storage. -/
theorem cleanTail_invariant {M : System C D A} (hM : ExposesNone M) :
    Invariant M CleanWorld := by
  refine .ofRuns ?_ ?_ ?_
  · intro d tx σ _ run
    unfold Contract.deployT at run
    split at run
    · cases run
    · cases hr : Prog.run (State.deploy C tx) (M.deploy d) with
      | error e => simp only [hr, bind, Except.bind] at run; cases run
      | ok o =>
        simp only [hr, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at run
        subst run
        exact ofState_clean (Prog.run_cleanTail _ (hM.1 d) (Storage.init_cleanTail C) rfl hr)
  · intro s a tx t _ _ hi run
    obtain ⟨σ, o, en, ran, eq⟩ := System.run_ok run
    subst eq
    have hσ : σ.storage.CleanTail := by
      rw [World.enter_storage en]
      exact Storage.resetTransient_cleanTail hi
    exact ofState_clean (Prog.run_cleanTail _ (hM.2 a) hσ rfl ran)
  · intro s t _ hi
    exact hi

/-- Every entry state of such a contract has clean tails. -/
theorem EntryState.cleanTail {M : System C D A} (hM : ExposesNone M) {σ : State C []}
    (h : EntryState M σ) : σ.storage.CleanTail :=
  let ⟨s, hs, eq⟩ := h.storage
  eq ▸ Storage.resetTransient_cleanTail ((cleanTail_invariant hM).always s hs)

/-- **`TailMode.clean` follows from reachability**: what `.clean` proves
holds at every entry state of a contract that exposes nothing. -/
theorem _root_.Solidity.ValidTail.validStart_reachable {M : System C D A}
    (hM : ExposesNone M) {φ : Fml C []} (h : ValidTail .clean φ) :
    ValidStart (.reachable M) φ :=
  fun σ hσ => h.holds_of_clean σ (hσ.cleanTail hM)

/-- The same, as `ValidStart.of_invariant` reads it: the invariant
`CleanWorld`, the premise `cleanTail(storage) = true`. -/
example {M : System C D A} (hM : ExposesNone M) {φ : Fml C []} (h : ValidTail .clean φ) :
    ValidStart (.reachable M) φ :=
  .of_invariant (cleanTail_invariant hM)
    (fun _ _ _ hs _ en => holds_cleanTail_of
      ((World.enter_storage en) ▸ Storage.resetTransient_cleanTail hs)) h

end Solidity.Reachable
