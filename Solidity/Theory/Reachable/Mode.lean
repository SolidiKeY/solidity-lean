import Solidity.Calculus.Lifetime


namespace Solidity.Reachable

open Lifetime

variable {C : Contract} {D A : Type}

def _root_.Solidity.Lifetime.System.refuses (M : System C D A) (a : A) (tx : TTx) : Bool :=
  !M.payable a && tx.msgValue.1 != 0

def EntryState (M : System C D A) (σ : State C []) : Prop :=
  ∃ s tx a, Reachable M s ∧ s.accepts tx ∧ M.refuses a tx = false ∧ M.allowCall s a tx ∧
    s.enter tx = .ok σ

inductive StartMode (C : Contract) (D A : Type) where
  | any
  | reachable (M : System C D A)

def ValidStart : StartMode C D A → Fml C [] → Prop
  | .any, φ => Fml.Valid φ
  | .reachable M, φ => ∀ σ, EntryState M σ → holds σ φ

theorem validStart_any {φ : Fml C []} :
    ValidStart (.any : StartMode C D A) φ ↔ Fml.Valid φ := Iff.rfl

theorem validStart_reachable {M : System C D A} {φ : Fml C []} :
    ValidStart (.reachable M) φ ↔ ∀ σ, EntryState M σ → holds σ φ := Iff.rfl

theorem ValidStart.reachable_of_any {M : System C D A} {φ : Fml C []}
    (h : ValidStart (.any : StartMode C D A) φ) : ValidStart (.reachable M) φ :=
  fun σ _ => h σ

theorem ValidStart.of_invariant {M : System C D A} {I : World C → Prop} {J φ : Fml C []}
    (hI : Invariant M I)
    (entry : ∀ s tx a σ, I s → s.accepts tx → M.refuses a tx = false → M.allowCall s a tx →
      s.enter tx = .ok σ → holds σ J)
    (h : Fml.Valid (.imp J φ)) : ValidStart (.reachable M) φ :=
  fun σ ⟨s, tx, a, hs, acc, g, al, en⟩ => h σ (entry s tx a σ (hI.always s hs) acc g al en)

theorem EntryState.invariant {M : System C D A} {I : World C → Prop} (hI : Invariant M I)
    {σ : State C []} (h : EntryState M σ) : ∃ s tx, I s ∧ s.accepts tx ∧ s.enter tx = .ok σ :=
  let ⟨s, tx, _, hs, acc, _, _, en⟩ := h
  ⟨s, tx, hI.always s hs, acc, en⟩

theorem EntryState.storage {M : System C D A} {σ : State C []} (h : EntryState M σ) :
    ∃ s, Reachable M s ∧ σ.storage = Storage.resetTransient s.storage :=
  let ⟨s, _, _, hs, _, _, _, en⟩ := h
  ⟨s, hs, World.enter_storage en⟩


structure PersistentFml (C : Contract) where
  fml : Fml C []
  reads : ∀ σ σ' : State C [],
    Storage.resetTransient σ.storage = Storage.resetTransient σ'.storage →
      holds σ fml → holds σ' fml

def PersistentFml.ofStorage {C : Contract} (φ : Fml C []) (hT : C.transientRoots = [])
    (h : ∀ σ : State C [], holds σ φ ↔ holds { State.init C with storage := σ.storage } φ) :
    PersistentFml C where
  fml := φ
  reads σ σ' e hσ := by
    rw [Storage.resetTransient_none _ hT, Storage.resetTransient_none _ hT] at e
    exact (h σ').2 (e ▸ (h σ).1 hσ)

def PersistentFml.At (J : PersistentFml C) (s : World C) : Prop := holds s.observe J.fml

private theorem reset_ofState {Γ : Ctx} (σ : State C Γ) :
    Storage.resetTransient (World.ofState σ).observe.storage =
      Storage.resetTransient σ.storage := by
  show Storage.resetTransient (Storage.resetTransient (Storage.resetTransient σ.storage)) = _
  rw [Storage.resetTransient_idem, Storage.resetTransient_idem]

theorem PersistentFml.at_ofState (J : PersistentFml C) {σ : State C []}
    (h : holds σ J.fml) : J.At (World.ofState σ) :=
  J.reads σ _ (reset_ofState σ).symm h

theorem PersistentFml.at_enter (J : PersistentFml C) {s : World C} {tx : TTx}
    {σ : State C []} (hs : J.At s) (en : s.enter tx = .ok σ) : holds σ J.fml := by
  refine J.reads s.observe σ ?_ hs
  show Storage.resetTransient (Storage.resetTransient s.storage) = _
  rw [World.enter_storage en, Storage.resetTransient_idem]

theorem PersistentFml.invariant {M : System C D A} (J : PersistentFml C)
    (deploy : ∀ d tx, M.allowDeploy d tx →
      holds (State.deploy C tx) (.modal .box (M.deploy d) .nil J.fml))
    (calls : ∀ a, Fml.Valid (.imp J.fml (.modal .box (M.call a) .nil J.fml))) :
    Invariant M J.At :=
  .ofRuns
    (fun d tx _ allowed run => J.at_ofState (post_of_deploy_box (deploy d tx allowed) run))
    (fun _ a _ _ accepted allowed hi run =>
      System.preserves_of_fml J.fml J.fml (calls a)
        (fun _ _ _ _ _ hs en => J.at_enter hs en) (fun _ h => J.at_ofState h)
        accepted allowed hi run)
    (fun s _ _ hi => J.reads s.observe _ rfl hi)

theorem ValidStart.of_persistent {M : System C D A} (J : PersistentFml C) {φ : Fml C []}
    (deploy : ∀ d tx, M.allowDeploy d tx →
      holds (State.deploy C tx) (.modal .box (M.deploy d) .nil J.fml))
    (calls : ∀ a, Fml.Valid (.imp J.fml (.modal .box (M.call a) .nil J.fml)))
    (h : Fml.Valid (.imp J.fml φ)) : ValidStart (.reachable M) φ :=
  .of_invariant (J.invariant deploy calls) (fun _ _ _ _ hs _ _ _ en => J.at_enter hs en) h

end Solidity.Reachable
