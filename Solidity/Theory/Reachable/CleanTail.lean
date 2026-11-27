import Solidity.Theory.Reachable.Mode
import Solidity.Calculus.TailMode


namespace Solidity

theorem SFields.all_anon {P : Hered} {fs : List (Name × Ty)} :
    (L : List Name) → {x y : SFields fs} → x.All P → y.All P → (SFields.anon L x y).All P
  | [], _, _, hx, _ => hx
  | r :: L, x, y, hx, hy => by
    rw [SFields.anon_cons]
    have ih := SFields.all_anon L hx hy
    unfold SFields.copyFrom
    split
    · rename_i h
      exact SFields.all_set (P := P) h ih (SFields.all_get (P := P) h hy)
    · exact ih

theorem Storage.resetTransient_cleanTail {C : Contract} {st : Storage C}
    (h : st.CleanTail) : (Storage.resetTransient st).CleanTail :=
  SFields.all_anon _ h (Storage.init_cleanTail C)

end Solidity

namespace Solidity.Reachable

open Lifetime

variable {C : Contract} {D A : Type}

def ExposesNone (M : System C D A) : Prop :=
  (∀ d, (M.deploy d).exposesNone = true) ∧ ∀ a, (M.call a).exposesNone = true

def CleanWorld (s : World C) : Prop := s.storage.CleanTail

private theorem ofState_clean {Γ : Ctx} {σ : State C Γ} (h : σ.storage.CleanTail) :
    CleanWorld (World.ofState σ) :=
  Storage.resetTransient_cleanTail h

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

theorem EntryState.cleanTail {M : System C D A} (hM : ExposesNone M) {σ : State C []}
    (h : EntryState M σ) : σ.storage.CleanTail :=
  let ⟨s, hs, eq⟩ := h.storage
  eq ▸ Storage.resetTransient_cleanTail ((cleanTail_invariant hM).always s hs)

theorem _root_.Solidity.ValidTail.validStart_reachable {M : System C D A}
    (hM : ExposesNone M) {φ : Fml C []} (h : ValidTail .clean φ) :
    ValidStart (.reachable M) φ :=
  fun σ hσ => h.holds_of_clean σ (hσ.cleanTail hM)

example {M : System C D A} (hM : ExposesNone M) {φ : Fml C []} (h : ValidTail .clean φ) :
    ValidStart (.reachable M) φ :=
  .of_invariant (cleanTail_invariant hM)
    (fun _ _ _ _ hs _ _ _ en => holds_cleanTail_of
      ((World.enter_storage en) ▸ Storage.resetTransient_cleanTail hs)) h

end Solidity.Reachable
