import Solidity.Theory.Reachable.Mode
import tests.h62.item2.«audit-theories».CleanTailWitnesses

/-! Original reachable-mode inputs, with a real admitted flag-writing interface.
Persistent truth is used only as a universally valid formula input; successful
call and nonempty-domain evidence are supplied independently. No physical EVM,
target compiler, gas or fork agreement is claimed. -/
namespace H62.AuditTheories
open Solidity Solidity.Lifetime Solidity.Reachable

/-- The selected typed setter succeeds for EVERY compatible state and sets flag. -/
theorem mode_setter_success (σ : State bridgeContract []) :
    ∃ o, assignableWrite.run σ = .ok o ∧
      o.st.storage.find bridgeFlag = some (.prim true) := by
  cases σ with
  | mk storage H heap env net balance tx =>
    cases storage with
    | cons items rest =>
      cases rest with
      | cons flag rest =>
        cases rest
        cases flag with
        | prim b => exact ⟨_, rfl, rfl⟩

/-- A globally persistent formula; the reads law covers the same state pair. -/
def modePersistentTruth : PersistentFml bridgeContract where
  fml := .tt
  reads := fun _ _ _ _ => True.intro

/-- The whole constructor obligation, for all constructor arguments and transactions. -/
theorem mode_persistent_deploy :
    ∀ d tx, tailAuditSystem.allowDeploy d tx →
      holds (State.deploy bridgeContract tx)
        (.modal .box (tailAuditSystem.deploy d) .nil modePersistentTruth.fml) := by
  intro d tx allowed
  exact ⟨True.intro, (by intro impossible; cases impossible)⟩

/-- All actions and all states satisfy the selected source call's box obligation. -/
theorem mode_persistent_calls :
    ∀ a, Fml.Valid (.imp modePersistentTruth.fml
      (.modal .box (tailAuditSystem.call a) .nil modePersistentTruth.fml)) := by
  intro a σ premise
  obtain ⟨o, success, _⟩ := mode_setter_success σ
  change Modality.afterRunTR .box (holds · modePersistentTruth.fml)
    (Prog.runFrames σ assignableWrite .nil)
  have run : Prog.runFrames σ assignableWrite .nil = .ok o.st := by
    unfold Prog.runFrames
    rw [success]
    rfl
  rw [run]
  exact ⟨True.intro, (by intro impossible; cases impossible)⟩

/-- The any-mode identity has actual configuration/formula data. -/
theorem mode_any_inputs_joint :
    ∃ (C : Contract) (_D _A : Type) (φ : Fml C []),
      ∃ σ : State C [], holds σ φ :=
  ⟨bridgeContract, Unit, Unit, .tt, tailAuditEntry, True.intro⟩

/-- The reachable-mode identity has a real admitted entry, not empty domains. -/
theorem mode_reachable_inputs_joint :
    ∃ (C : Contract) (D A : Type) (M : System C D A) (φ : Fml C [])
      (σ : State C []), EntryState M σ ∧ holds σ φ :=
  ⟨bridgeContract, Unit, Unit, tailAuditSystem, .tt, tailAuditEntry,
    tail_audit_entry, True.intro⟩

/-- Global validity coexists with the same interface and an actual entry. -/
theorem mode_any_transfer_inputs_joint :
    ∃ (C : Contract) (D A : Type) (M : System C D A) (φ : Fml C [])
      (σ : State C []), ValidStart (.any : StartMode C D A) φ ∧ EntryState M σ :=
  ⟨bridgeContract, Unit, Unit, tailAuditSystem, .tt, tailAuditEntry,
    (fun _ => True.intro), tail_audit_entry⟩

/-- The invariant and WHOLE conditional entry law hold for the same interface. -/
theorem mode_invariant_inputs_joint :
    ∃ (C : Contract) (D A : Type) (M : System C D A)
      (I : World C → Prop) (J φ : Fml C []),
      Invariant M I ∧
      (∀ s tx a σ, I s → s.accepts tx → M.refuses a tx = false →
        M.allowCall s a tx → s.enter tx = .ok σ → holds σ J) ∧
      Fml.Valid (.imp J φ) ∧ ∃ σ : State C [], EntryState M σ := by
  refine ⟨bridgeContract, Unit, Unit, tailAuditSystem, CleanWorld,
    Fml.cleanTail bridgeContract, Fml.cleanTail bridgeContract,
    cleanTail_invariant tail_audit_exposes, ?_, (fun _ h => h),
    tailAuditEntry, tail_audit_entry⟩
  intro world tx a σ clean accepted refused allowed entered
  have stateClean : σ.storage.CleanTail := by
    rw [World.enter_storage entered]
    exact Storage.resetTransient_cleanTail clean
  exact holds_cleanTail_of stateClean

/-- A nontrivial clean-world invariant and selected EntryState coexist. -/
theorem mode_entry_invariant_inputs_joint :
    ∃ (C : Contract) (D A : Type) (M : System C D A)
      (I : World C → Prop) (σ : State C []), Invariant M I ∧ EntryState M σ :=
  ⟨bridgeContract, Unit, Unit, tailAuditSystem, CleanWorld, tailAuditEntry,
    cleanTail_invariant tail_audit_exposes, tail_audit_entry⟩

/-- Storage projection's full input has an actual entry and observable flag. -/
theorem mode_entry_storage_inputs_joint :
    ∃ (C : Contract) (D A : Type) (M : System C D A) (σ : State C [])
      (r : SRef C (.prim .bool)), EntryState M σ ∧ σ.storage.find r = some (.prim false) :=
  ⟨bridgeContract, Unit, Unit, tailAuditSystem, tailAuditEntry,
    bridgeFlag, tail_audit_entry, rfl⟩

/-- Private reset_ofState data coexist on a nonempty transient/persistent store. -/
theorem mode_private_reset_inputs_joint :
    ∃ (C : Contract) (Γ : Ctx) (σ : State C Γ),
      Storage.resetTransient (World.ofState σ).observe.storage =
        Storage.resetTransient σ.storage := by
  refine ⟨tailTransientContract, [],
    { State.init tailTransientContract with storage := tailTransientStorage }, ?_⟩
  show Storage.resetTransient (Storage.resetTransient (Storage.resetTransient tailTransientStorage)) = _
  rw [Storage.resetTransient_idem, Storage.resetTransient_idem]

/-- Persistent formula data and the selected successful state's premise coexist. -/
theorem mode_persistent_state_inputs_joint :
    ∃ (C : Contract) (J : PersistentFml C) (σ : State C []), holds σ J.fml :=
  ⟨bridgeContract, modePersistentTruth, tailAuditEntry, True.intro⟩

/-- The global reads structure, world fact and successful entry are correlated. -/
theorem mode_persistent_enter_inputs_joint :
    ∃ (C : Contract) (J : PersistentFml C) (world : World C) (tx : TTx)
      (σ : State C []), J.At world ∧ world.enter tx = .ok σ ∧
      world.accepts tx :=
  ⟨bridgeContract, modePersistentTruth, tailAuditWorld, tailAuditTx,
    tailAuditEntry, True.intro, World.enter_zero _ _ rfl, tail_audit_accepts⟩

/-- Both UNIVERSAL boxed obligations coexist with an inhabited live interface. -/
theorem mode_persistent_invariant_inputs_joint :
    ∃ (C : Contract) (D A : Type) (M : System C D A) (J : PersistentFml C),
      (∀ d tx, M.allowDeploy d tx →
        holds (State.deploy C tx) (.modal .box (M.deploy d) .nil J.fml)) ∧
      (∀ a, Fml.Valid (.imp J.fml (.modal .box (M.call a) .nil J.fml))) ∧
      ∃ σ : State C [], EntryState M σ :=
  ⟨bridgeContract, Unit, Unit, tailAuditSystem, modePersistentTruth,
    mode_persistent_deploy, mode_persistent_calls, tailAuditEntry, tail_audit_entry⟩

/-- The two global box laws, transfer validity and real entry hold simultaneously. -/
theorem mode_persistent_transfer_inputs_joint :
    ∃ (C : Contract) (D A : Type) (M : System C D A) (J : PersistentFml C)
      (φ : Fml C []),
      (∀ d tx, M.allowDeploy d tx →
        holds (State.deploy C tx) (.modal .box (M.deploy d) .nil J.fml)) ∧
      (∀ a, Fml.Valid (.imp J.fml (.modal .box (M.call a) .nil J.fml))) ∧
      Fml.Valid (.imp J.fml φ) ∧ ∃ σ : State C [], EntryState M σ :=
  ⟨bridgeContract, Unit, Unit, tailAuditSystem, modePersistentTruth, .tt,
    mode_persistent_deploy, mode_persistent_calls, (fun _ _ => True.intro),
    tailAuditEntry, tail_audit_entry⟩

#print axioms mode_any_inputs_joint
#print axioms mode_reachable_inputs_joint
#print axioms mode_any_transfer_inputs_joint
#print axioms mode_invariant_inputs_joint
#print axioms mode_entry_invariant_inputs_joint
#print axioms mode_entry_storage_inputs_joint
#print axioms mode_private_reset_inputs_joint
#print axioms mode_persistent_state_inputs_joint
#print axioms mode_persistent_enter_inputs_joint
#print axioms mode_persistent_invariant_inputs_joint
#print axioms mode_persistent_transfer_inputs_joint
#print axioms mode_setter_success
#print axioms mode_persistent_deploy
#print axioms mode_persistent_calls
end H62.AuditTheories
