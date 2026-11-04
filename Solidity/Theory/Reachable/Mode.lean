import Solidity.Calculus.Lifetime

/-!
# Reachable starting states as a mode (`docs/options.md`, O12)

`Fml.Valid φ` reads `φ` at every typed state: any storage, any ledger, any
transaction. The `reachable` mode reads it only at the states a deployed
contract's transactions start in: a successful deployment, then a finite
sequence of admitted entry calls (`Lifetime.Reachable`: a revert or a panic
rolls back, waiting advances time), then a fresh entry frame
(`Lifetime.World.enter`). As every option here, the mode is an argument of
the validity proved (`ValidStart m φ`), never a setting; `.any` is
`Fml.Valid`, the reading solkey proves, and stays the default.

The mode takes the contract and its interface (`Lifetime.System`): the
starting states are those of that interface, so a claim proved under one
interface is not one about another (`Witness.lean`'s two interfaces).

A proof under `.reachable M` needs no induction of its own: the contract's
invariant is proved once, by induction over the entry points
(`Lifetime.Invariant.ofRuns`, a rollback needing nothing), and then is a
premise of an ordinary `Fml.Valid` (`ValidStart.of_invariant`). For an
invariant that reads only persistent storage the induction is a constructor
box and one box per entry (`PersistentFml.invariant`).

The entry calls run deterministically here, solkey's `noCallback` reading
of the transaction itself; the callbacks inside it follow a caller model in
`Theory/Reachable/CallerModel.lean`.
-/

namespace Solidity.Reachable

open Lifetime

variable {C : Contract} {D A : Type}

/-- **The states a deployed contract's transactions start in**: a fresh
entry frame, of a transaction the world accepts, over a world reached from a
successful deployment through `M`'s interface. -/
def EntryState (M : System C D A) (σ : State C []) : Prop :=
  ∃ s tx, Reachable M s ∧ s.accepts tx ∧ s.enter tx = .ok σ

/-- **Which starting states validity ranges over**: `any` typed state (the
reading of `Fml.Valid`, solkey's), or the entry states of a contract's
reachable worlds through the interface `M`. -/
inductive StartMode (C : Contract) (D A : Type) where
  | any
  | reachable (M : System C D A)

/-- **`Fml.Valid` under a start mode**. -/
def ValidStart : StartMode C D A → Fml C [] → Prop
  | .any, φ => Fml.Valid φ
  | .reachable M, φ => ∀ σ, EntryState M σ → holds σ φ

theorem validStart_any {φ : Fml C []} :
    ValidStart (.any : StartMode C D A) φ ↔ Fml.Valid φ := Iff.rfl

theorem validStart_reachable {M : System C D A} {φ : Fml C []} :
    ValidStart (.reachable M) φ ↔ ∀ σ, EntryState M σ → holds σ φ := Iff.rfl

/-- `.any` assumes less: what it proves holds under every interface. -/
theorem ValidStart.reachable_of_any {M : System C D A} {φ : Fml C []}
    (h : ValidStart .any φ) : ValidStart (.reachable M) φ :=
  fun σ _ => h σ

/-- **Validity under `.reachable` from a contract invariant.** `I` is the
contract's invariant on its persistent worlds, proved once (`Invariant`, by
induction over the entry points); `J` is what it gives at an entry frame;
the claim is then an ordinary `Fml.Valid` with `J` as its premise. -/
theorem ValidStart.of_invariant {M : System C D A} {I : World C → Prop} {J φ : Fml C []}
    (hI : Invariant M I)
    (entry : ∀ s tx σ, I s → s.accepts tx → s.enter tx = .ok σ → holds σ J)
    (h : Fml.Valid (.imp J φ)) : ValidStart (.reachable M) φ :=
  fun σ ⟨s, tx, hs, acc, en⟩ => h σ (entry s tx σ (hI.always s hs) acc en)

/-- A contract invariant gives every entry state's persistent part. -/
theorem EntryState.invariant {M : System C D A} {I : World C → Prop} (hI : Invariant M I)
    {σ : State C []} (h : EntryState M σ) : ∃ s tx, I s ∧ s.accepts tx ∧ s.enter tx = .ok σ :=
  let ⟨s, tx, hs, acc, en⟩ := h
  ⟨s, tx, hI.always s hs, acc, en⟩

/-- An entry state's storage is its world's, its transient cells reset. -/
theorem EntryState.storage {M : System C D A} {σ : State C []} (h : EntryState M σ) :
    ∃ s, Reachable M s ∧ σ.storage = Storage.resetTransient s.storage :=
  let ⟨s, _, hs, _, en⟩ := h
  ⟨s, hs, World.enter_storage en⟩

/-! ## Invariants that read persistent storage -/

/-- **A formula that reads only the persistent storage**: two states whose
storages agree once their transient cells are reset agree on it. -/
structure PersistentFml (C : Contract) where
  fml : Fml C []
  reads : ∀ σ σ' : State C [],
    Storage.resetTransient σ.storage = Storage.resetTransient σ'.storage →
      holds σ fml → holds σ' fml

/-- The formula read at a world's observation frame. -/
def PersistentFml.At (J : PersistentFml C) (s : World C) : Prop := holds s.observe J.fml

private theorem reset_ofState {Γ : Ctx} (σ : State C Γ) :
    Storage.resetTransient (World.ofState σ).observe.storage =
      Storage.resetTransient σ.storage := by
  show Storage.resetTransient (Storage.resetTransient (Storage.resetTransient σ.storage)) = _
  rw [Storage.resetTransient_idem, Storage.resetTransient_idem]

/-- What holds at a state holds at its world's observation frame. -/
theorem PersistentFml.at_ofState (J : PersistentFml C) {σ : State C []}
    (h : holds σ J.fml) : J.At (World.ofState σ) :=
  J.reads σ _ (reset_ofState σ).symm h

/-- What holds at a world holds at every frame entered from it. -/
theorem PersistentFml.at_enter (J : PersistentFml C) {s : World C} {tx : TTx}
    {σ : State C []} (hs : J.At s) (en : s.enter tx = .ok σ) : holds σ J.fml := by
  refine J.reads s.observe σ ?_ hs
  show Storage.resetTransient (Storage.resetTransient s.storage) = _
  rw [World.enter_storage en, Storage.resetTransient_idem]

/-- **A persistent invariant by induction over the entry points**: the
constructor establishes it, each entry keeps it (one box per entry,
`Fml.Valid (J → [call] J)`), a rollback and waiting keep the storage. -/
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

/-- **Validity under `.reachable` from a persistent invariant**: the
invariant's two obligations, then `Fml.Valid (J → φ)`. -/
theorem ValidStart.of_persistent {M : System C D A} (J : PersistentFml C) {φ : Fml C []}
    (deploy : ∀ d tx, M.allowDeploy d tx →
      holds (State.deploy C tx) (.modal .box (M.deploy d) .nil J.fml))
    (calls : ∀ a, Fml.Valid (.imp J.fml (.modal .box (M.call a) .nil J.fml)))
    (h : Fml.Valid (.imp J.fml φ)) : ValidStart (.reachable M) φ :=
  .of_invariant (J.invariant deploy calls) (fun _ _ _ hs _ en => J.at_enter hs en) h

end Solidity.Reachable
