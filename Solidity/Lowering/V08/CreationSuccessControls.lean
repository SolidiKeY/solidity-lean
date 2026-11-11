import Solidity.Lowering.V08.SharedFailureFixture
import Solidity.Lowering.V08.LibraryHandlerControls

/-! Successful nonempty creation, then actual caller-typed library work in the
success continuation. Intrinsic supplied bodies only; no Source/runtime proof. -/
namespace Solidity.Lowering.V08.CreationSuccessControls
open Solidity.ContractWorld Controls LibraryHandlerControls

def goodCtor : Prog Cell [] [] := sol[Cell]{ saved = 8; scratch = 12; }
def created : World Catalog :=
  (outer.create false candidate goodCtor ctorCtx).toOption.map Prod.fst |>.getD initial
def linked : World Catalog := (delegated created).toOption.map Prod.fst |>.getD initial
private instance : DecidableEq (Handle false) := fun a b =>
  decidable_of_iff (a.address = b.address) ⟨(by
    cases a; cases b; intro h; cases h; rfl), congrArg Handle.address⟩
private theorem extract_success {α : Type} (run : TRes (World Catalog × α)) (value : α)
    (checked : run.toOption.map Prod.snd = some value) :
    run = .ok ((run.toOption.map Prod.fst).getD initial, value) := by
  cases run with
  | error halt => cases checked
  | ok pair =>
    cases pair with
    | mk world result =>
      have same : result = value := Option.some.inj checked
      cases same
      rfl

theorem creation_reached : outer.create false candidate goodCtor ctorCtx = .ok (created, ⟨candidate⟩) :=
  extract_success _ _ (by decide +kernel)
theorem library_reached : delegated created = .ok (linked, expected) :=
  extract_success _ _ (by decide +kernel)
theorem later_reached : later linked expected = .error laterHalt :=
  Solidity.Lowering.V08.SharedFailureFixture.extract_failure _ _ (by decide +kernel)

def successWork (w : World Catalog) (_ : Handle false) : TRes (World Catalog × Unit) := do
  let (next, output) ← delegated w
  later next output
def caught (_ : World Catalog) (_ : THalt) : TRes (World Catalog × Unit) := .error .panic
def attempt (w : World Catalog) : TRes (World Catalog × Unit) :=
  w.tryCreate (.ok [0xab, 0xcd]) false (fun _ => candidate) (fun _ => goodCtor)
    (fun _ => ctorCtx) successWork caught

theorem success_work_failed : successWork created ⟨candidate⟩ = .error laterHalt := by
  simp only [successWork, library_reached, bind, Except.bind, later_reached]
theorem combined_application : attempt outer = .error laterHalt :=
  tryCreate_library_success_failure outer created linked [0xab, 0xcd] false (fun _ => candidate)
    (fun _ => goodCtor) (fun _ => ctorCtx) ⟨candidate⟩ (⟨self⟩ : Handle false)
    library paidCtx later caught expected laterHalt rfl creation_reached library_reached later_reached

theorem atomic_application : atomic outer (attempt outer) = (outer, .error laterHalt) := by
  rw [combined_application]; rfl

def frame (w : World Catalog) : TRes (World Catalog × Unit) := do
  let (next, _) ← enter w
  attempt next

theorem frame_failed : frame base.resetTransient = .error laterHalt := by
  simp only [frame, ancestor_reached, bind, Except.bind, combined_application]
theorem transaction_application : base.transact frame = (base.resetTransient, .error laterHalt) :=
  transact_descendant_failure base outer enter (fun next _ => attempt next)
    [0xab, 0xcd] laterHalt ancestor_reached combined_application

/-- The original vector is retained whole; append candidate typed cells and identity. -/
def extended (w : World Catalog) :=
  (vector w, cells w candidate, (w.storage? (⟨candidate⟩ : Handle false)).isSome)
def installedFlags : List Bool := [true, true, true, true, true, true, false, true, false, true]

theorem creation_and_library_vectors :
    extended created =
      (([88, 7, 0, 5, 0], [some [3, 9], some [19, 0], some []], installedFlags), some [8, 12], true) ∧
    extended linked =
      (([88, 7, 0, 5, 0], [some [11, 23], some [19, 0], some []], installedFlags), some [8, 12], true) := by decide +kernel

theorem library_result_context : expected = ([0xb1, 0xb2], [1, 7, 2, 7, 12345]) := rfl
/-- These are actual complete account equalities, not a generic balance claim. -/
theorem untouched_accounts : linked.accounts link = created.accounts link ∧
    linked.accounts third = created.accounts third ∧ linked.accounts candidate = created.accounts candidate := by
  exact ⟨libraryCall_other_accounts _ library paidCtx expected library_reached link (by decide +kernel),
    libraryCall_other_accounts _ library paidCtx expected library_reached third (by decide +kernel),
    libraryCall_other_accounts _ library paidCtx expected library_reached candidate (by decide +kernel)⟩

theorem rollback_vectors_status :
    (extended (atomic outer (attempt outer)).1, (atomic outer (attempt outer)).2) =
      ((([88, 7, 0, 5, 0], [some [3, 9], some [19, 0], some []], flags), none, false), .error laterHalt) ∧
    (extended (base.transact frame).1, (base.transact frame).2) =
      ((([95, 0, 0, 5, 0], [some [0, 0], some [19, 0], some []], flags), none, false), .error laterHalt) := by
  rw [atomic_application, transaction_application]
  constructor <;> apply Prod.ext
  · decide +kernel
  · rfl
  · decide +kernel
  · rfl

theorem not_recaught : caught linked laterHalt = .error .panic ∧
    (attempt outer).halt? = some laterHalt ∧ laterHalt ≠ .panic := by
  rw [combined_application]
  exact ⟨rfl, rfl, by decide +kernel⟩

theorem wrong_world : extended linked ≠ extended outer ∧ extended linked ≠ extended created := by decide +kernel
theorem wrong_rollback_snapshot : extended created ≠ extended (atomic outer (attempt outer)).1 := by
  rw [atomic_application]; decide +kernel

def doublePay := created.call (⟨self⟩ : Handle false) workEntry paidCtx
theorem double_payment_run : doublePay.toOption.map (fun pair => (extended pair.1, pair.2)) =
    some ((([81, 14, 0, 5, 0], [some [11, 23], some [19, 0], some []], installedFlags), some [8, 12], true),
      ([0xb1, 0xb2], [1, 7, 2, 14, 12345])) := by decide +kernel

theorem wrong_role : created.libraryCall (⟨self⟩ : Handle false) wrongRole paidCtx = .error .revert :=
  Solidity.Lowering.V08.SharedFailureFixture.extract_failure _ _ (by decide +kernel)

-- Successful counterpart: actual library result, not a constant world stand-in.
def keep (w : World Catalog) : TRes (World Catalog × Result) :=
  w.tryCreate (.ok [0xab, 0xcd]) false (fun _ => candidate) (fun _ => goodCtor)
    (fun _ => ctorCtx) (fun next _ => delegated next) (fun _ _ => .error .panic)
theorem keep_reached : keep outer = .ok (linked, expected) := by
  have mutable : ctorCtx.isStatic = false := rfl
  simp only [keep, World.tryCreate, bind, Except.bind, mutable,
    Bool.false_eq_true, ↓reduceIte, creation_reached, library_reached]

def commitFrame (w : World Catalog) : TRes (World Catalog × Result) := do
  let (next, _) ← enter w
  keep next

theorem commit_frame_reached : commitFrame base.resetTransient = .ok (linked, expected) := by
  simp only [commitFrame, ancestor_reached, bind, Except.bind, keep_reached]
theorem commit_application : base.transact commitFrame = (linked.resetTransient, .ok expected) :=
  World.transact_commit base linked commitFrame expected commit_frame_reached

theorem committed_vector : extended (base.transact commitFrame).1 =
    (([88, 7, 0, 5, 0], [some [11, 0], some [19, 0], some []], installedFlags), some [8, 0], true) := by
  rw [commit_application]; decide +kernel

def readCandidate (w : World Catalog) : TRes (World Catalog × List Int) := do
  let (next, values) ← readFrame w
  let (final, candidateValues) ← next.call (⟨candidate⟩ : Handle false) readEntry Controls.ctx
  pure (final, values ++ candidateValues)
def readWorld : World Catalog :=
  (readCandidate linked.resetTransient).toOption.map Prod.fst |>.getD initial

theorem read_candidate_reached : readCandidate linked.resetTransient =
    .ok (readWorld, [11, 0, 19, 0, 8, 0]) := extract_success _ _ (by decide +kernel)
theorem commit_repeat : ((base.transact commitFrame).2, (base.transact commitFrame).1.transact readCandidate) =
    (.ok expected, (readWorld.resetTransient, .ok [11, 0, 19, 0, 8, 0])) := by
  rw [commit_application]
  have ran : readCandidate linked.resetTransient.resetTransient = .ok (readWorld, [11, 0, 19, 0, 8, 0]) := by
    rw [resetTransient_idem]; exact read_candidate_reached
  rw [World.transact_commit linked.resetTransient readWorld readCandidate _ ran]

theorem failure_repeat : ((base.transact frame).2, (base.transact frame).1.transact readFrame) =
    (.error laterHalt, (readAfter.resetTransient, .ok [0, 0, 19, 0])) :=
  transact_failure_then_commit base readAfter frame readFrame laterHalt [0, 0, 19, 0]
    frame_failed read_reached

-- Lossless library observation retains all return bytes and incoming context.
def observedKeep (w : World Catalog) :=
  w.tryCreate (.ok [0xab, 0xcd]) false (fun _ => candidate) (fun _ => goodCtor)
    (fun _ => ctorCtx) (fun next _ => next.libraryCall (⟨self⟩ : Handle false) observedLibrary paidCtx)
    (fun _ _ => .error .panic)
private theorem observe_map_value (w : World Catalog) :
    ((.ok (w, expected) : TRes (World Catalog × Result)).map
      (fun pair => (pair.1, LibraryHandlerControls.observe pair.2))) = .ok (w, (expected, 2)) := rfl

private theorem observed_at (w : World Catalog) :
    w.libraryCall (⟨self⟩ : Handle false) observedLibrary paidCtx =
      (delegated w).map (fun pair => (pair.1, LibraryHandlerControls.observe pair.2)) :=
  libraryCall_observe w (⟨self⟩ : Handle false) library paidCtx LibraryHandlerControls.observe

theorem observed_keep_reached : observedKeep outer = .ok (linked, (expected, 2)) := by
  have mapped : created.libraryCall (⟨self⟩ : Handle false) observedLibrary paidCtx =
      .ok (linked, (expected, 2)) := by
    rw [observed_at, library_reached]
    exact observe_map_value linked
  have mutable : ctorCtx.isStatic = false := rfl
  simp only [observedKeep, World.tryCreate, bind, Except.bind, mutable,
    Bool.false_eq_true, ↓reduceIte, creation_reached, mapped]

theorem exact_payload : (attempt outer).halt?.map THalt.data = some (Source.errorData laterReason) := by
  rw [combined_application, errorData_transport_total]; rfl

/-- A failed enclosing transaction really frees the candidate address: the
next actual transaction can create and commit the same candidate. -/
theorem failure_then_recreate :
    ((base.transact frame).2, (base.transact frame).1.transact commitFrame) =
      (.error laterHalt, (linked.resetTransient, .ok expected)) :=
  transact_failure_then_commit base linked frame commitFrame laterHalt expected
    frame_failed commit_frame_reached

theorem recreate_vector_statuses :
    (extended ((base.transact frame).1.transact commitFrame).1,
      (base.transact frame).2, ((base.transact frame).1.transact commitFrame).2) =
    ((([88, 7, 0, 5, 0], [some [11, 0], some [19, 0], some []], installedFlags), some [8, 0], true),
      .error laterHalt, .ok expected) := by
  rw [transaction_application]
  have ran : commitFrame base.resetTransient.resetTransient = .ok (linked, expected) := by
    rw [resetTransient_idem]; exact commit_frame_reached
  rw [World.transact_commit base.resetTransient linked commitFrame expected ran]
  apply Prod.ext
  · decide +kernel
  · rfl

def observedFailure (w : World Catalog) : TRes (World Catalog × Unit) :=
  w.tryCreate (.ok [0xab, 0xcd]) false (fun _ => candidate) (fun _ => goodCtor)
    (fun _ => ctorCtx) (fun next _ => do
      let (after, output) ← next.libraryCall (⟨self⟩ : Handle false) observedLibrary paidCtx
      observedLater after output) caught

theorem observed_failure_application : observedFailure outer = .error laterHalt := by
  have linkedObserved : created.libraryCall (⟨self⟩ : Handle false) observedLibrary paidCtx =
      .ok (linked, (expected, 2)) := by
    rw [observed_at, library_reached]
    exact observe_map_value linked
  have failed : observedLater linked (expected, 2) = .error laterHalt := by
    simpa only [observedLater, ↓reduceIte] using later_reached
  exact tryCreate_library_success_failure outer created linked [0xab, 0xcd] false
    (fun _ => candidate) (fun _ => goodCtor) (fun _ => ctorCtx) ⟨candidate⟩
    (⟨self⟩ : Handle false) observedLibrary paidCtx observedLater caught (expected, 2)
    laterHalt rfl creation_reached linkedObserved failed

theorem wrong_runtime_identity : created.libraryCall (⟨self⟩ : Handle false) wrongIdentity paidCtx = .error .revert :=
  Solidity.Lowering.V08.SharedFailureFixture.extract_failure _ _ (by decide +kernel)

theorem wrong_payload : (attempt outer).halt? ≠ some (.revertWith (Semantics.encodeError [0x6c, 0, 0xfe, 0x48])) := by
  rw [combined_application]; decide +kernel

/-- The wrong incoming value actually changes the delegated result/context;
the real later continuation rejects it instead of producing the desired halt. -/
def wrongContinuation (w : World Catalog) : TRes (World Catalog × Unit) :=
  w.tryCreate (.ok [0xab, 0xcd]) false (fun _ => candidate) (fun _ => goodCtor)
    (fun _ => ctorCtx) (fun next _ => do
      let (after, output) ← next.libraryCall (⟨self⟩ : Handle false) library Controls.ctx
      later after output) caught

theorem wrong_continuation_run : wrongContinuation outer = .error .panic :=
  Solidity.Lowering.V08.SharedFailureFixture.extract_failure _ _ (by decide +kernel)

/-- Full listed observations after actual repeated reads, with both statuses. -/
theorem repeat_vector_statuses :
    (extended ((base.transact commitFrame).1.transact readCandidate).1,
      (base.transact commitFrame).2, ((base.transact commitFrame).1.transact readCandidate).2) =
    ((([88, 7, 0, 5, 0], [some [11, 0], some [19, 0], some []], installedFlags), some [8, 0], true),
      .ok expected, .ok [11, 0, 19, 0, 8, 0]) := by
  rw [commit_application]
  have ran : readCandidate linked.resetTransient.resetTransient = .ok (readWorld, [11, 0, 19, 0, 8, 0]) := by
    rw [resetTransient_idem]; exact read_candidate_reached
  rw [World.transact_commit linked.resetTransient readWorld readCandidate _ ran]
  apply Prod.ext
  · decide +kernel
  · rfl

/-- The same actual read procedure fails at the rolled-back missing candidate. -/
theorem rollback_candidate_read_fails : readCandidate (base.transact frame).1 = .error .revert := by
  rw [transaction_application]
  exact Solidity.Lowering.V08.SharedFailureFixture.extract_failure _ _ (by decide +kernel)

#print axioms creation_reached
#print axioms library_reached
#print axioms later_reached
#print axioms success_work_failed
#print axioms combined_application
#print axioms atomic_application
#print axioms frame_failed
#print axioms transaction_application
#print axioms creation_and_library_vectors
#print axioms library_result_context
#print axioms untouched_accounts
#print axioms rollback_vectors_status
#print axioms not_recaught
#print axioms wrong_world
#print axioms wrong_rollback_snapshot
#print axioms double_payment_run
#print axioms wrong_role
#print axioms keep_reached
#print axioms commit_frame_reached
#print axioms commit_application
#print axioms committed_vector
#print axioms read_candidate_reached
#print axioms commit_repeat
#print axioms failure_repeat
#print axioms observed_keep_reached
#print axioms exact_payload

#print axioms failure_then_recreate
#print axioms recreate_vector_statuses
#print axioms observed_failure_application
#print axioms wrong_runtime_identity
#print axioms wrong_payload
#print axioms wrong_continuation_run
#print axioms repeat_vector_statuses
#print axioms rollback_candidate_read_fails
end Solidity.Lowering.V08.CreationSuccessControls
