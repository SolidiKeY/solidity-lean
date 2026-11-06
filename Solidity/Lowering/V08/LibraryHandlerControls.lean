import Solidity.Lowering.V08.HandlerControls
import Solidity.Lowering.V08.LibraryControls

/-! Real linked library work inside a failed creation handler. Supplied typed
bodies/context only; no Source, callback, source-linkage or runtime-bytecode
preservation is asserted. Empty library storage is required by deployLibrary. -/
namespace Solidity.Lowering.V08.LibraryHandlerControls
open Solidity.ContractWorld
open Controls

abbrev Catalog := LibraryControls.linkedCatalog
def link : Address := LibraryControls.link
def candidate : Address := ⟨⟨5, by decide +kernel⟩, by decide +kernel⟩
def initial : World Catalog := LibraryControls.linkedInitial.atTime ⟨12345, by decide +kernel⟩
def setup : TRes (World Catalog) := do
  let (w, _) ← initial.create false self .nil Controls.ctx
  let (w, _) ← w.create false third .nil Controls.ctx
  let (w, _) ← w.deployLibrary true link Controls.ctx
  let (w, _) ← w.call (⟨third⟩ : Handle false) HandlerControls.fourthEntry HandlerControls.fourthCtx
  pure w

def base : World Catalog := setup.toOption.getD initial
def enter (w : World Catalog) := w.call (⟨self⟩ : Handle false) entry paidCtx
def outer : World Catalog := (enter base.resetTransient).toOption.map Prod.fst |>.getD initial

def ctorReason : List UInt8 := [0x63, 0x74, 0x6f, 0x72]
def laterReason : List UInt8 := [0x6c, 0x00, 0xff, 0x48]
def ctorHalt : THalt := .revertWith (Semantics.encodeError ctorReason)
def laterHalt : THalt := .revertWith (Semantics.encodeError laterReason)
def constructor : Prog Cell [] [] :=
  (sol[Cell]{ saved = 8; scratch = 12; }).join
    (.cons (.revertData [.bytes (Semantics.encodeError ctorReason)]) .nil)
def ctorCtx : Context := { sender := self }

abbrev Result := List UInt8 × List Int
/-- Ordered context: sender,value,self,balance,timestamp. -/
def contextView (state : State Cell []) : List Int :=
  [state.tx.msgSender.1, state.tx.msgValue.1, state.tx.selfAddress.1,
    state.selfBalance.1, state.tx.timestamp.1]
def expected : Result := ([0xb1, 0xb2], [1, 7, 2, 7, 12345])
def workEntry : Entry Cell Result :=
  { locals := [], body := sol[Cell]{ saved = msg.value + 4; scratch = 23; },
    result := fun state => .ok ([0xb1, 0xb2], contextView state), payable := true }
def library : Library Catalog false Result := ⟨true, link, workEntry⟩
def delegated (w : World Catalog) := w.libraryCall (⟨self⟩ : Handle false) library paidCtx

def failureEntry : Entry Cell Unit :=
  { locals := [], body := (sol[Cell]{ saved = 31; scratch = 37; }).join
      (.cons (.revertData [.bytes (Semantics.encodeError laterReason)]) .nil),
    result := fun _ => .ok (), payable := true }
def later (w : World Catalog) (output : Result) : TRes (World Catalog × Unit) :=
  if output = expected then w.call (⟨self⟩ : Handle false) failureEntry HandlerControls.failureCtx
  else .error .panic

def success (w : World Catalog) (_ : Handle false) : TRes (World Catalog × Unit) := .ok (w, ())
def handler (w : World Catalog) (_ : THalt) : TRes (World Catalog × Unit) := do
  let (next, output) ← delegated w
  later next output

def attempt (w : World Catalog) : TRes (World Catalog × Unit) :=
  w.tryCreate (.ok [0xab, 0xcd]) false (fun _ => candidate) (fun _ => constructor)
    (fun _ => ctorCtx) success handler

def handled : World Catalog := (delegated outer).toOption.map Prod.fst |>.getD initial

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
private theorem extract_failure {α : Type} (run : TRes α) (halt : THalt)
    (checked : run.halt? = some halt) : run = .error halt := by
  cases run with
  | ok value => cases checked
  | error actual =>
    have same : actual = halt := Option.some.inj checked
    cases same
    rfl
private theorem extract_value {α : Type} (run : TRes α) (fallback : α)
    (checked : run.toOption.isSome = true) : run = .ok (run.toOption.getD fallback) := by
  cases run with
  | error halt => cases checked
  | ok value => rfl

theorem setup_reached : setup = .ok base := extract_value _ _ (by decide +kernel)
theorem ancestor_reached : enter base.resetTransient = .ok (outer, [0xab, 0xcd]) :=
  extract_success _ _ (by decide +kernel)
theorem constructor_failed : outer.create false candidate constructor ctorCtx = .error ctorHalt :=
  extract_failure _ _ (by decide +kernel)
theorem delegated_reached : delegated outer = .ok (handled, expected) :=
  extract_success _ _ (by decide +kernel)
theorem later_failed : later handled expected = .error laterHalt :=
  extract_failure _ _ (by decide +kernel)
theorem handler_failed : handler outer ctorHalt = .error laterHalt := by
  simp only [handler, delegated_reached, bind, Except.bind, later_failed]

theorem combined_application : attempt outer = .error laterHalt :=
  tryCreate_library_handler_failure outer handled [0xab, 0xcd] false (fun _ => candidate)
    (fun _ => constructor) (fun _ => ctorCtx) success (⟨self⟩ : Handle false) library paidCtx
    later expected ctorHalt laterHalt rfl constructor_failed rfl delegated_reached later_failed

theorem atomic_application : atomic outer (attempt outer) = (outer, .error laterHalt) :=
  atomic_tryCreate_library_handler_failure outer handled [0xab, 0xcd] false (fun _ => candidate)
    (fun _ => constructor) (fun _ => ctorCtx) success (⟨self⟩ : Handle false) library paidCtx
    later expected ctorHalt laterHalt rfl constructor_failed rfl delegated_reached later_failed

def frame (w : World Catalog) : TRes (World Catalog × Unit) := do
  let (next, _) ← enter w
  attempt next

theorem transaction_application : base.transact frame = (base.resetTransient, .error laterHalt) :=
  transact_tryCreate_library_handler_failure base outer handled enter [0xab, 0xcd] false
    (fun _ => candidate) (fun _ => constructor) (fun _ => ctorCtx) success
    (⟨self⟩ : Handle false) library paidCtx later expected ctorHalt laterHalt
    ancestor_reached rfl constructor_failed rfl delegated_reached later_failed

/-- The account proof covers the complete library record, not an invented slot. -/
theorem library_account_preserved : handled.accounts link = outer.accounts link :=
  libraryCall_other_accounts (⟨self⟩ : Handle false) library paidCtx expected delegated_reached link (by decide +kernel)
theorem other_account_preserved : handled.accounts third = outer.accounts third :=
  libraryCall_other_accounts (⟨self⟩ : Handle false) library paidCtx expected delegated_reached third (by decide +kernel)
theorem library_fields_empty : LibraryControls.Empty.vars = [] := rfl

def cells (w : World Catalog) (owner : Address) : Option (List Int) := do
  let store ← w.storage? (⟨owner⟩ : Handle false)
  let .prim saved ← store.find (SRef.ofRoot "saved" rfl)
  let .prim scratch ← store.find (SRef.ofRoot "scratch" rfl)
  pure [saved.1, scratch.1]
def libraryCells (w : World Catalog) : Option (List Int) :=
  match w.storage? (⟨link⟩ : Handle true) with | none => none | some _ => some []
abbrev Vector := List Int × List (Option (List Int)) × List Bool
/-- Balances sender/caller/library/other/candidate; stores caller/other/library;
installed caller/library/other/candidate; typed lookups; contract/library roles. -/
def vector (w : World Catalog) : Vector :=
  ([sender, self, link, third, candidate].map (fun address => (w.balance address).1),
    [cells w self, cells w third, libraryCells w],
    [(w.accounts self).isSome, (w.accounts link).isSome, (w.accounts third).isSome,
      (w.accounts candidate).isSome, (w.storage? (⟨self⟩ : Handle false)).isSome,
      (w.storage? (⟨link⟩ : Handle true)).isSome, (w.storage? (⟨link⟩ : Handle false)).isSome,
      (w.storage? (⟨third⟩ : Handle false)).isSome, w.isLibrary false, w.isLibrary true])
def flags : List Bool := [true, true, true, false, true, true, false, true, false, true]
private instance resultDecidable : DecidableEq Result := inferInstance
private instance vectorDecidable : DecidableEq Vector := inferInstance

theorem populated_vectors :
    vector base = ([95, 0, 0, 5, 0], [some [0, 0], some [19, 29], some []], flags) ∧
    vector outer = ([88, 7, 0, 5, 0], [some [3, 9], some [19, 0], some []], flags) ∧
    vector handled = ([88, 7, 0, 5, 0], [some [11, 23], some [19, 0], some []], flags) := by decide +kernel

theorem atomic_vector_status : (vector (atomic outer (attempt outer)).1, (atomic outer (attempt outer)).2) =
    (([88, 7, 0, 5, 0], [some [3, 9], some [19, 0], some []], flags), .error laterHalt) := by
  rw [atomic_application]
  apply Prod.ext
  · decide +kernel
  · rfl

theorem transaction_vector_status : (vector (base.transact frame).1, (base.transact frame).2) =
    (([95, 0, 0, 5, 0], [some [0, 0], some [19, 0], some []], flags), .error laterHalt) := by
  rw [transaction_application]
  apply Prod.ext
  · decide +kernel
  · rfl

def view (run : TRes (World Catalog × Result)) := run.toOption.map (fun pair => (vector pair.1, pair.2))

theorem delegated_vector_context : view (delegated outer) =
    some (([88, 7, 0, 5, 0], [some [11, 23], some [19, 0], some []], flags), expected) := by
  rw [delegated_reached]
  decide +kernel

def doublePayment := outer.call (⟨self⟩ : Handle false) workEntry paidCtx
theorem double_payment_run : view doublePayment =
    some (([81, 14, 0, 5, 0], [some [11, 23], some [19, 0], some []], flags),
      ([0xb1, 0xb2], [1, 7, 2, 14, 12345])) := by decide +kernel

theorem no_second_payment : view (delegated outer) ≠ view doublePayment := by
  rw [delegated_vector_context, double_payment_run]
  decide +kernel

def wrongCaller := outer.libraryCall (⟨third⟩ : Handle false) library paidCtx
theorem wrong_caller_run : view wrongCaller =
    some (([88, 7, 0, 5, 0], [some [3, 9], some [11, 23], some []], flags),
      ([0xb1, 0xb2], [1, 7, 3, 5, 12345])) := by decide +kernel

theorem wrong_caller : view (delegated outer) ≠ view wrongCaller := by
  rw [delegated_vector_context, wrong_caller_run]
  decide +kernel

def wrongContext := outer.libraryCall (⟨self⟩ : Handle false) library Controls.ctx
theorem wrong_context_run : view wrongContext =
    some (([88, 7, 0, 5, 0], [some [4, 23], some [19, 0], some []], flags),
      ([0xb1, 0xb2], [1, 0, 2, 7, 12345])) := by decide +kernel

theorem wrong_context : view (delegated outer) ≠ view wrongContext := by
  rw [delegated_vector_context, wrong_context_run]
  decide +kernel

def wrongIdentity : Library Catalog false Result := { library with address := third }
theorem wrong_runtime_identity : outer.libraryCall (⟨self⟩ : Handle false) wrongIdentity paidCtx = .error .revert :=
  extract_failure _ _ (by decide +kernel)

theorem wrong_rollback_snapshot : vector (base.transact frame).1 ≠ vector (atomic outer (attempt outer)).1 := by
  rw [transaction_application, atomic_application]
  decide +kernel

theorem dirty_transient_reuse : vector (base.transact frame).1 ≠ vector base := by
  rw [transaction_application]
  decide +kernel

theorem exact_payload : (attempt outer).halt?.map THalt.data = some (Source.errorData laterReason) := by
  rw [combined_application, errorData_transport_total]
  rfl

theorem distinct_payloads : ctorHalt ≠ laterHalt := by decide +kernel

def ctorInput : TRes (State Cell []) :=
  outer.enter (k := false) candidate ctorCtx (Storage.init Cell) false
def ctorState : State Cell [] := ctorInput.toOption.getD (State.init Cell)
theorem ctor_input_reached : ctorInput = .ok ctorState := extract_value _ _ (by decide +kernel)
theorem ctor_input_context : contextView ctorState = [2, 0, 5, 0, 12345] := by decide +kernel

/-- Extend the actual result: retain every byte/context field and add length. -/
def observe (output : Result) : Result × Nat := (output, output.1.length)
theorem observation_retains_result (output : Result) : (observe output).1 = output := rfl
def observedLibrary := observeLibrary library observe
private theorem observed_at (w : World Catalog) :
    w.libraryCall (⟨self⟩ : Handle false) observedLibrary paidCtx =
      (delegated w).map (fun pair => (pair.1, observe pair.2)) :=
  libraryCall_observe w (⟨self⟩ : Handle false) library paidCtx observe

private theorem map_observed_value (w : World Catalog) :
    ((.ok (w, expected) : TRes (World Catalog × Result)).map
      (fun pair => (pair.1, observe pair.2))) = .ok (w, (expected, 2)) := rfl

theorem observed_prefix_reached : outer.libraryCall (⟨self⟩ : Handle false) observedLibrary paidCtx =
    .ok (handled, (expected, 2)) := by
  rw [observed_at, delegated_reached]
  exact map_observed_value handled

def observedLater (w : World Catalog) (output : Result × Nat) : TRes (World Catalog × Unit) :=
  if output = (expected, 2) then later w output.1 else .error .panic

theorem observed_later_failed : observedLater handled (expected, 2) = .error laterHalt := by
  simpa only [observedLater, ↓reduceIte] using later_failed

def observedAttempt (w : World Catalog) : TRes (World Catalog × Unit) :=
  w.tryCreate (.ok [0xab, 0xcd]) false (fun _ => candidate) (fun _ => constructor)
    (fun _ => ctorCtx) success (fun snapshot _ => do
      let (next, output) ← snapshot.libraryCall (⟨self⟩ : Handle false) observedLibrary paidCtx
      observedLater next output)

theorem observed_combined_application : observedAttempt outer = .error laterHalt :=
  tryCreate_library_handler_failure outer handled [0xab, 0xcd] false (fun _ => candidate)
    (fun _ => constructor) (fun _ => ctorCtx) success (⟨self⟩ : Handle false) observedLibrary paidCtx
    observedLater (expected, 2) ctorHalt laterHalt rfl constructor_failed rfl
    observed_prefix_reached observed_later_failed

theorem observed_atomic_status : atomic outer (observedAttempt outer) = (outer, .error laterHalt) := by
  rw [observed_combined_application]
  rfl

def mappedAttempt (w : World Catalog) : TRes (World Catalog × Nat) :=
  w.tryCreate (.ok [0xab, 0xcd]) false (fun _ => candidate) (fun _ => constructor)
    (fun _ => ctorCtx)
    (fun next reference => (success next reference).map (fun pair => (pair.1, HandlerControls.seven pair.2)))
    (fun snapshot halt => (handler snapshot halt).map (fun pair => (pair.1, HandlerControls.seven pair.2)))
private theorem mapped_at (w : World Catalog) :
    mappedAttempt w = (attempt w).map (fun pair => (pair.1, HandlerControls.seven pair.2)) :=
  tryCreate_observe w (.ok ([0xab, 0xcd] : List UInt8)) false (fun _ => candidate)
    (fun _ => constructor) (fun _ => ctorCtx) success handler HandlerControls.seven

theorem mapped_handler_failure : mappedAttempt outer = .error laterHalt := by
  rw [mapped_at, combined_application]
  rfl

def readEntry : Entry Cell (List Int) :=
  { locals := [], body := .nil, result := fun state => do
      let .prim saved ← TRes.ofOpt (state.storage.find (SRef.ofRoot "saved" rfl))
      let .prim scratch ← TRes.ofOpt (state.storage.find (SRef.ofRoot "scratch" rfl))
      pure [saved.1, scratch.1] }
def readFrame (w : World Catalog) : TRes (World Catalog × List Int) := do
  let (w, caller) ← w.call (⟨self⟩ : Handle false) readEntry Controls.ctx
  let (w, other) ← w.call (⟨third⟩ : Handle false) readEntry Controls.ctx
  pure (w, caller ++ other)
def readAfter : World Catalog := (readFrame base.resetTransient).toOption.map Prod.fst |>.getD initial

theorem frame_failed : frame base.resetTransient = .error laterHalt := by
  simp only [frame, ancestor_reached, bind, Except.bind, combined_application]
theorem read_reached : readFrame base.resetTransient = .ok (readAfter, [0, 0, 19, 0]) :=
  extract_success _ _ (by decide +kernel)

theorem repeat_application : ((base.transact frame).2, (base.transact frame).1.transact readFrame) =
    (.error laterHalt, (readAfter.resetTransient, .ok [0, 0, 19, 0])) :=
  transact_failure_then_commit base readAfter frame readFrame laterHalt [0, 0, 19, 0] frame_failed read_reached

theorem repeat_vector_statuses :
    (vector ((base.transact frame).1.transact readFrame).1, (base.transact frame).2,
      ((base.transact frame).1.transact readFrame).2) =
    (([95, 0, 0, 5, 0], [some [0, 0], some [19, 0], some []], flags),
      .error laterHalt, .ok [0, 0, 19, 0]) := by
  rw [transaction_application]
  have ran : readFrame base.resetTransient.resetTransient = .ok (readAfter, [0, 0, 19, 0]) := by
    rw [resetTransient_idem]
    exact read_reached
  rw [World.transact_commit base.resetTransient readAfter readFrame [0, 0, 19, 0] ran]
  apply Prod.ext
  · decide +kernel
  · rfl

def wrongRole : Library Catalog false Result := { library with kind := false }
theorem wrong_role_guard : outer.libraryCall (⟨self⟩ : Handle false) wrongRole paidCtx = .error .revert :=
  extract_failure _ _ (by decide +kernel)
theorem static_library_guard : outer.libraryCall (⟨self⟩ : Handle false) library
    { sender, mode := .readOnly } = .error .revert := extract_failure _ _ (by decide +kernel)

theorem wrong_failure_payload : (attempt outer).halt? ≠
    some (.revertWith (Semantics.encodeError [0x6c, 0x00, 0xff, 0x49])) := by
  rw [combined_application]
  decide +kernel

#print axioms setup_reached
#print axioms ancestor_reached
#print axioms constructor_failed
#print axioms delegated_reached
#print axioms later_failed
#print axioms handler_failed
#print axioms combined_application
#print axioms atomic_application
#print axioms transaction_application
#print axioms library_account_preserved
#print axioms other_account_preserved
#print axioms library_fields_empty
#print axioms populated_vectors
#print axioms atomic_vector_status
#print axioms transaction_vector_status
#print axioms delegated_vector_context
#print axioms double_payment_run
#print axioms no_second_payment
#print axioms wrong_caller_run
#print axioms wrong_caller
#print axioms wrong_context_run
#print axioms wrong_context
#print axioms wrong_runtime_identity
#print axioms wrong_rollback_snapshot
#print axioms dirty_transient_reuse
#print axioms exact_payload
#print axioms distinct_payloads
#print axioms observation_retains_result
#print axioms ctor_input_reached
#print axioms ctor_input_context
#print axioms observed_prefix_reached
#print axioms observed_later_failed
#print axioms observed_combined_application
#print axioms observed_atomic_status
#print axioms mapped_handler_failure
#print axioms frame_failed
#print axioms read_reached
#print axioms repeat_application
#print axioms repeat_vector_statuses
#print axioms wrong_role_guard
#print axioms static_library_guard
#print axioms wrong_failure_payload
end Solidity.Lowering.V08.LibraryHandlerControls
