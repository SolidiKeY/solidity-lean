import Solidity.Lowering.V08.SharedFailureFixture
import Solidity.Lowering.V08.NestedControls
import Solidity.Lowering.V08.AbiObservations

/-! Completed constructor failure and failed catch continuation are different
boundaries. These are actual supplied intrinsic runs, not Source execution,
source catchability, canonical ABI/layout lowering or runtime bytecode proofs. -/
namespace Solidity.Lowering.V08.HandlerControls
open Solidity.ContractWorld
open Controls

def fourth : Address := ⟨⟨4, by decide +kernel⟩, by decide +kernel⟩
def fourthEntry : Entry Cell Unit :=
  { locals := [], body := sol[Cell]{ saved = 19; scratch = 29; },
    result := fun _ => .ok (), payable := true }
def fourthCtx : Context := { sender, mode := .ordinary ⟨5, by decide +kernel⟩ }
def setup : TRes (World NestedControls.catalog) := do
  let w ← NestedControls.setup
  let (w, _) ← w.create false fourth .nil Controls.ctx
  let (w, _) ← w.call (⟨fourth⟩ : Handle false) fourthEntry fourthCtx
  pure w

def base : World NestedControls.catalog := setup.toOption.getD NestedControls.initial
def outer : World NestedControls.catalog := (NestedControls.enterOuter base.resetTransient).toOption.map Prod.fst |>.getD NestedControls.initial

def constructorReason : List UInt8 := [99, 116, 111, 114]
def handlerReason : List UInt8 := [104, 97, 110, 100, 108, 101, 114]
def constructorHalt : THalt := .revertWith (Semantics.encodeError constructorReason)
def handlerHalt : THalt := .revertWith (Semantics.encodeError handlerReason)
def failingConstructor : Prog NestedControls.CreatedCell [] [] :=
  NestedControls.constructor.join (.cons (.revertData [.bytes (Semantics.encodeError constructorReason)]) .nil)
def workEntry : Entry Cell (List UInt8) :=
  { locals := [], body := sol[Cell]{ saved = 11; scratch = 23; },
    result := fun _ => .ok [0xb1, 0xb2], payable := true }
def workCtx : Context := { sender, mode := .ordinary ⟨2, by decide +kernel⟩ }
def failureEntry : Entry Cell Unit :=
  { locals := [], body := (sol[Cell]{ saved = 31; scratch = 37; }).join
      (.cons (.revertData [.bytes (Semantics.encodeError handlerReason)]) .nil),
    result := fun _ => .ok (), payable := true }
def failureCtx : Context := { sender, mode := .ordinary ⟨1, by decide +kernel⟩ }
def work (w : World NestedControls.catalog) (halt : THalt) : TRes (World NestedControls.catalog × List UInt8) :=
  if halt = constructorHalt then w.call (⟨self⟩ : Handle false) workEntry workCtx else .error .panic
def later (w : World NestedControls.catalog) (bytes : List UInt8) : TRes (World NestedControls.catalog × Unit) :=
  if bytes = [0xb1, 0xb2] then w.call (⟨self⟩ : Handle false) failureEntry failureCtx else .error .panic
def handler (w : World NestedControls.catalog) (halt : THalt) : TRes (World NestedControls.catalog × Unit) := do
  let (next, result) ← work w halt
  later next result
def success (w : World NestedControls.catalog) (_ : Handle true) : TRes (World NestedControls.catalog × Unit) := .ok (w, ())
def attempt (w : World NestedControls.catalog) : TRes (World NestedControls.catalog × Unit) :=
  w.tryCreate (.ok [0xab, 0xcd]) true (fun _ => third) (fun _ => failingConstructor)
    (fun _ => NestedControls.createCtx) success handler

def handled : World NestedControls.catalog := (work outer constructorHalt).toOption.map Prod.fst |>.getD NestedControls.initial

private theorem extract_success {α : Type} (run : TRes (World NestedControls.catalog × α)) (value : α)
    (checked : run.toOption.map Prod.snd = some value) :
    run = .ok ((run.toOption.map Prod.fst).getD NestedControls.initial, value) := by
  cases run with
  | error halt => cases checked
  | ok pair =>
    cases pair with
    | mk world result =>
      have same : result = value := Option.some.inj checked
      cases same
      rfl


private theorem extract_value {α : Type} (run : TRes α) (fallback : α)
    (checked : run.toOption.isSome = true) : run = .ok (run.toOption.getD fallback) := by
  cases run with
  | error halt => cases checked
  | ok value => rfl

theorem setup_reached : setup = .ok base :=
  extract_value _ _ (by decide +kernel)
theorem outer_reached : NestedControls.enterOuter base.resetTransient = .ok (outer, [0xab, 0xcd]) :=
  extract_success _ _ (by decide +kernel)
theorem constructor_failed : outer.create true third failingConstructor NestedControls.createCtx = .error constructorHalt :=
  Solidity.Lowering.V08.SharedFailureFixture.extract_failure _ _ (by decide +kernel)
theorem constructor_catchable : catchable constructorHalt = true := rfl
theorem work_reached : work outer constructorHalt = .ok (handled, [0xb1, 0xb2]) :=
  extract_success _ _ (by decide +kernel)
theorem later_failed : later handled [0xb1, 0xb2] = .error handlerHalt :=
  Solidity.Lowering.V08.SharedFailureFixture.extract_failure _ _ (by decide +kernel)

/-- Handler failure is derived from the paid prefix and the real failing call. -/
theorem handler_failed : handler outer constructorHalt = .error handlerHalt := by
  simp only [handler, work_reached, bind, Except.bind, later_failed]

theorem handler_failure_application : attempt outer = .error handlerHalt :=
  tryCreate_handler_steps_failure outer handled [0xab, 0xcd] true (fun _ => third)
    (fun _ => failingConstructor) (fun _ => NestedControls.createCtx) success work later [0xb1, 0xb2]
    constructorHalt handlerHalt rfl constructor_failed constructor_catchable work_reached later_failed

theorem atomic_application : atomic outer (attempt outer) = (outer, .error handlerHalt) :=
  atomic_tryCreate_handler_steps_failure outer handled [0xab, 0xcd] true (fun _ => third)
    (fun _ => failingConstructor) (fun _ => NestedControls.createCtx) success work later [0xb1, 0xb2]
    constructorHalt handlerHalt rfl constructor_failed constructor_catchable work_reached later_failed

def frame (w : World NestedControls.catalog) : TRes (World NestedControls.catalog × Unit) := do
  let (next, _) ← NestedControls.enterOuter w
  attempt next

theorem transaction_application : base.transact frame = (base.resetTransient, .error handlerHalt) := by
  exact transact_tryCreate_handler_steps_failure base outer handled NestedControls.enterOuter [0xab, 0xcd]
    true (fun _ => third) (fun _ => failingConstructor) (fun _ => NestedControls.createCtx) success work later
    [0xb1, 0xb2] constructorHalt handlerHalt outer_reached rfl constructor_failed constructor_catchable
    work_reached later_failed

abbrev Vector := NestedControls.Vector × (Option (Int × Int × Int) × List Bool)
def vector (w : World NestedControls.catalog) : Vector :=
  (NestedControls.vector w, (do
    let store ← w.storage? (⟨fourth⟩ : Handle false)
    let .prim saved ← store.find (SRef.ofRoot "saved" rfl)
    let .prim scratch ← store.find (SRef.ofRoot "scratch" rfl)
    pure ((w.balance fourth).1, saved.1, scratch.1)),
    [(w.accounts fourth).isSome, (w.storage? (⟨fourth⟩ : Handle true)).isSome, w.isLibrary false])

private instance : DecidableEq (Int × Int × Int × Int) := inferInstance
private instance : DecidableEq (Int × Option (Int × Int) × Bool × Bool) := inferInstance
private instance nestedVectorDecidable : DecidableEq NestedControls.Vector := inferInstance
private instance handlerVectorDecidable : DecidableEq Vector := inferInstance
private instance workViewDecidable : DecidableEq (Vector × List UInt8) := inferInstance

theorem populated_vectors :
    vector base = ((some (95, 0, 0, 0), 0, none, false, false), some (5, 19, 29), [true, false, false]) ∧
    vector outer = ((some (88, 7, 3, 9), 0, none, false, false), some (5, 19, 0), [true, false, false]) ∧
    vector handled = ((some (86, 9, 11, 23), 0, none, false, false), some (5, 19, 0), [true, false, false]) := by
  decide +kernel

/-- This projection retains the raw exact TRes, not only success/failure. -/
theorem atomic_vector_status :
    (vector (atomic outer (attempt outer)).1, (atomic outer (attempt outer)).2) =
      (((some (88, 7, 3, 9), 0, none, false, false), some (5, 19, 0), [true, false, false]), .error handlerHalt) := by
  rw [atomic_application]
  apply Prod.ext
  · decide +kernel
  · rfl

theorem transaction_vector_status :
    (vector (base.transact frame).1, (base.transact frame).2) =
      (((some (95, 0, 0, 0), 0, none, false, false), some (5, 19, 0), [true, false, false]), .error handlerHalt) := by
  rw [transaction_application]
  apply Prod.ext
  · decide +kernel
  · rfl

theorem untouched_atomic : (atomic outer (attempt outer)).1.accounts fourth = outer.accounts fourth := by
  rw [atomic_application]
theorem untouched_transaction : (base.transact frame).1.accounts fourth = base.resetTransient.accounts fourth := by
  rw [transaction_application]

def workView (run : TRes (World NestedControls.catalog × List UInt8)) := run.toOption.map (fun pair => (vector pair.1, pair.2))

theorem correct_work_vector : workView (work outer constructorHalt) =
    some (((some (86, 9, 11, 23), 0, none, false, false), some (5, 19, 0), [true, false, false]), [0xb1, 0xb2]) := by
  rw [work_reached]
  decide +kernel

theorem wrong_snapshot_run : workView (work base.resetTransient constructorHalt) =
    some (((some (93, 2, 11, 23), 0, none, false, false), some (5, 19, 0), [true, false, false]), [0xb1, 0xb2]) := by
  decide +kernel

theorem wrong_snapshot : workView (work outer constructorHalt) ≠ workView (work base.resetTransient constructorHalt) := by
  rw [correct_work_vector, wrong_snapshot_run]
  decide +kernel

def skippedPayment : TRes (World NestedControls.catalog × List UInt8) :=
  outer.call (⟨self⟩ : Handle false) workEntry Controls.ctx

theorem skipped_payment_run : workView skippedPayment =
    some (((some (88, 7, 11, 23), 0, none, false, false), some (5, 19, 0), [true, false, false]), [0xb1, 0xb2]) := by
  decide +kernel

theorem skipped_payment : workView (work outer constructorHalt) ≠ workView skippedPayment := by
  rw [correct_work_vector, skipped_payment_run]
  decide +kernel

theorem distinct_halts : constructorHalt ≠ handlerHalt := by decide +kernel

theorem recatch_run : handler outer handlerHalt = .error .panic := by
  have different : handlerHalt ≠ constructorHalt := Ne.symm distinct_halts
  simp only [handler, work, different, ↓reduceIte, bind, Except.bind]

theorem recatch_negative : (attempt outer).halt? ≠ (handler outer handlerHalt).halt? := by
  rw [handler_failure_application, recatch_run]
  decide +kernel

/-- Reuse only published encoder agreement; no Source execution is inferred. -/
theorem handler_payload_observation : (attempt outer).halt?.map THalt.data =
    some (Source.errorData handlerReason) := by
  rw [handler_failure_application, errorData_transport_total]
  rfl

theorem constructor_payload_observation :
    (outer.create true third failingConstructor NestedControls.createCtx).halt?.map THalt.data =
      some (Source.errorData constructorReason) := by
  rw [constructor_failed, errorData_transport_total]
  rfl

theorem wrong_handler_payload : (attempt outer).halt? ≠
    some (.revertWith (Semantics.encodeError [104, 97, 110, 100, 108, 101, 115])) := by
  rw [handler_failure_application]
  decide +kernel

/-- Actual typed frame entry for the constructor, before the failure. -/
def ctorInput : TRes (State NestedControls.CreatedCell []) :=
  outer.enter (k := true) third NestedControls.createCtx (Storage.init NestedControls.CreatedCell) true
def ctorState : State NestedControls.CreatedCell [] := ctorInput.toOption.getD (State.init NestedControls.CreatedCell)
theorem ctor_input_reached : ctorInput = .ok ctorState :=
  extract_value _ _ (by decide +kernel)

def ctorPrefixView : TRes ((Int × Int × Int × Int) × List (Int × Int)) := do
  let output ← NestedControls.constructor.run ctorState
  let .prim saved ← TRes.ofOpt (output.st.storage.find (SRef.ofRoot "saved" rfl))
  let .prim scratch ← TRes.ofOpt (output.st.storage.find (SRef.ofRoot "scratch" rfl))
  pure ((output.st.selfBalance.1, saved.1, scratch.1, output.st.tx.msgValue.1),
    output.st.net.map (fun pair => (pair.1.1, pair.2)))

/-- Before the joined revertData, the real typed frame has incoming balance3,
writes8/12 and pending sender debit3. No installed world is invented here. -/
theorem constructor_prefix_view : ctorPrefixView.toOption = some ((3, 8, 12, 3), [(1, 3)]) := by
  decide +kernel

def panicConstructor : Prog NestedControls.CreatedCell [] [] :=
  NestedControls.constructor.join (sol[NestedControls.CreatedCell]{ assert(false); })
def panicWork (w : World NestedControls.catalog) (halt : THalt) : TRes (World NestedControls.catalog × List UInt8) :=
  if halt = .panic then w.call (⟨self⟩ : Handle false) workEntry workCtx else .error .revert

theorem panic_constructor_failed : outer.create true third panicConstructor NestedControls.createCtx = .error .panic :=
  Solidity.Lowering.V08.SharedFailureFixture.extract_failure _ _ (by decide +kernel)
theorem panic_work_reached : panicWork outer .panic = .ok (handled, [0xb1, 0xb2]) := by
  simpa only [panicWork, work, ↓reduceIte] using work_reached

def panicConstructorAttempt : TRes (World NestedControls.catalog × Unit) :=
  outer.tryCreate (.ok [0xab, 0xcd]) true (fun _ => third) (fun _ => panicConstructor)
    (fun _ => NestedControls.createCtx) success (fun snapshot halt => do
      let (next, result) ← panicWork snapshot halt
      later next result)

theorem panic_constructor_application : panicConstructorAttempt = .error handlerHalt :=
  tryCreate_handler_steps_failure outer handled [0xab, 0xcd] true (fun _ => third)
    (fun _ => panicConstructor) (fun _ => NestedControls.createCtx) success panicWork later
    [0xb1, 0xb2] .panic handlerHalt rfl panic_constructor_failed rfl panic_work_reached later_failed

def panicEntry : Entry Cell Unit :=
  { locals := [], body := sol[Cell]{ saved = 31; scratch = 37; assert(false); },
    result := fun _ => .ok (), payable := true }
def laterPanic (w : World NestedControls.catalog) (_ : List UInt8) :=
  w.call (⟨self⟩ : Handle false) panicEntry failureCtx

theorem later_panic_failed : laterPanic handled [0xb1, 0xb2] = .error .panic :=
  Solidity.Lowering.V08.SharedFailureFixture.extract_failure _ _ (by decide +kernel)

def panicHandlerAttempt (w : World NestedControls.catalog) : TRes (World NestedControls.catalog × Unit) :=
  w.tryCreate (.ok [0xab, 0xcd]) true (fun _ => third) (fun _ => failingConstructor)
    (fun _ => NestedControls.createCtx) success (fun snapshot halt => do
      let (next, result) ← work snapshot halt
      laterPanic next result)

theorem panic_handler_application : panicHandlerAttempt outer = .error .panic :=
  tryCreate_handler_steps_failure outer handled [0xab, 0xcd] true (fun _ => third)
    (fun _ => failingConstructor) (fun _ => NestedControls.createCtx) success work laterPanic
    [0xb1, 0xb2] constructorHalt .panic rfl constructor_failed constructor_catchable work_reached later_panic_failed

theorem panic_not_exhausted_or_diverged :
    (panicHandlerAttempt outer).halt? ≠ some .exhausted ∧
    (panicHandlerAttempt outer).halt? ≠ some .diverge := by
  rw [panic_handler_application]
  decide +kernel

def guardWork (w : World NestedControls.catalog) (halt : THalt) : TRes (World NestedControls.catalog × List UInt8) :=
  if halt = .revert then w.call (⟨self⟩ : Handle false) workEntry workCtx else .error .panic

theorem guard_work_reached : guardWork outer .revert = .ok (handled, [0xb1, 0xb2]) := by
  simpa only [guardWork, work, ↓reduceIte] using work_reached

theorem collision_failed : outer.create true self failingConstructor NestedControls.createCtx = .error .revert :=
  Solidity.Lowering.V08.SharedFailureFixture.extract_failure _ _ (by decide +kernel)

def collisionAttempt : TRes (World NestedControls.catalog × Unit) :=
  outer.tryCreate (.ok [0xab, 0xcd]) true (fun _ => self) (fun _ => failingConstructor)
    (fun _ => NestedControls.createCtx) success (fun snapshot halt => do
      let (next, result) ← guardWork snapshot halt
      later next result)

theorem collision_handler_application : collisionAttempt = .error handlerHalt :=
  tryCreate_handler_steps_failure outer handled [0xab, 0xcd] true (fun _ => self)
    (fun _ => failingConstructor) (fun _ => NestedControls.createCtx) success guardWork later
    [0xb1, 0xb2] .revert handlerHalt rfl collision_failed rfl guard_work_reached later_failed

theorem argument_bypasses_handler :
    outer.tryCreate (.error (.revertWith [0xa0, 0x01]) : TRes (List UInt8)) true
      (fun _ => third) (fun _ => failingConstructor) (fun _ => NestedControls.createCtx) success handler =
      .error (.revertWith [0xa0, 0x01]) :=
  World.tryCreate_argument_failure _ _ _ _ _ _ _ _

theorem static_bypasses_handler :
    outer.tryCreate (.ok [0xab, 0xcd]) true (fun _ => third) (fun _ => failingConstructor)
      (fun _ => ({ sender, mode := .readOnly } : Context)) success handler = .error .revert :=
  tryCreate_static _ _ _ _ _ _ _ _ rfl

theorem constructor_reason_not_returned : (attempt outer).halt? ≠ some constructorHalt := by
  rw [handler_failure_application]
  have different : handlerHalt ≠ constructorHalt := Ne.symm distinct_halts
  exact fun same => different (Option.some.inj same)

theorem wrong_ancestor_boundary : vector (base.transact frame).1 ≠ vector (atomic outer (attempt outer)).1 := by
  rw [transaction_application, atomic_application]
  decide +kernel

theorem dirty_transaction_snapshot : vector (base.transact frame).1 ≠ vector base := by
  rw [transaction_application]
  decide +kernel

theorem panic_handler_atomic_vector_status :
    (vector (atomic outer (panicHandlerAttempt outer)).1, (atomic outer (panicHandlerAttempt outer)).2) =
      (((some (88, 7, 3, 9), 0, none, false, false), some (5, 19, 0), [true, false, false]), .error .panic) := by
  rw [panic_handler_application]
  apply Prod.ext
  · decide +kernel
  · rfl

theorem collision_atomic_vector_status :
    (vector (atomic outer collisionAttempt).1, (atomic outer collisionAttempt).2) =
      (((some (88, 7, 3, 9), 0, none, false, false), some (5, 19, 0), [true, false, false]), .error handlerHalt) := by
  rw [collision_handler_application]
  apply Prod.ext
  · decide +kernel
  · rfl

def seven (_ : Unit) : Nat := 7
/-- Apply the published observation extension to BOTH creation continuations. -/
def observedAttempt (w : World NestedControls.catalog) : TRes (World NestedControls.catalog × Nat) :=
  w.tryCreate (.ok [0xab, 0xcd]) true (fun _ => third) (fun _ => failingConstructor)
    (fun _ => NestedControls.createCtx)
    (fun next reference => (success next reference).map (fun pair => (pair.1, seven pair.2)))
    (fun snapshot halt => (handler snapshot halt).map (fun pair => (pair.1, seven pair.2)))

private theorem observation_at (w : World NestedControls.catalog) :
    observedAttempt w = (attempt w).map (fun pair => (pair.1, seven pair.2)) :=
  tryCreate_observe w (.ok ([0xab, 0xcd] : List UInt8)) true (fun _ => third)
    (fun _ => failingConstructor) (fun _ => NestedControls.createCtx) success handler seven

theorem observed_handler_failure : observedAttempt outer = .error handlerHalt := by
  rw [observation_at, handler_failure_application]
  rfl

theorem observed_atomic_status : atomic outer (observedAttempt outer) = (outer, .error handlerHalt) := by
  rw [observed_handler_failure]
  rfl

theorem frame_failed : frame base.resetTransient = .error handlerHalt := by
  simp only [frame, outer_reached, bind, Except.bind, handler_failure_application]

def readFourth (w : World NestedControls.catalog) :=
  w.call (⟨fourth⟩ : Handle false) NestedControls.readEntry Controls.ctx
def readAfter : World NestedControls.catalog := (readFourth base.resetTransient).toOption.map Prod.fst |>.getD NestedControls.initial

theorem fourth_read_reached : readFourth base.resetTransient = .ok (readAfter, 0) :=
  extract_success _ _ (by decide +kernel)

theorem repeated_after_failure_application :
    ((base.transact frame).2, (base.transact frame).1.transact readFourth) =
      (.error handlerHalt, (readAfter.resetTransient, .ok 0)) :=
  transact_failure_then_commit base readAfter frame readFourth handlerHalt 0 frame_failed fourth_read_reached

theorem repeated_after_failure_vector :
    (vector ((base.transact frame).1.transact readFourth).1,
      (base.transact frame).2, ((base.transact frame).1.transact readFourth).2) =
      (((some (95, 0, 0, 0), 0, none, false, false), some (5, 19, 0), [true, false, false]),
        .error handlerHalt, .ok 0) := by
  rw [transaction_application]
  have ran : readFourth base.resetTransient.resetTransient = .ok (readAfter, 0) := by
    rw [resetTransient_idem]
    exact fourth_read_reached
  rw [World.transact_commit base.resetTransient readAfter readFourth 0 ran]
  apply Prod.ext
  · decide +kernel
  · rfl

#print axioms setup_reached
#print axioms outer_reached
#print axioms constructor_failed
#print axioms constructor_catchable
#print axioms work_reached
#print axioms later_failed
#print axioms handler_failed
#print axioms handler_failure_application
#print axioms atomic_application
#print axioms transaction_application
#print axioms populated_vectors
#print axioms atomic_vector_status
#print axioms transaction_vector_status
#print axioms untouched_atomic
#print axioms untouched_transaction
#print axioms correct_work_vector
#print axioms wrong_snapshot_run
#print axioms wrong_snapshot
#print axioms skipped_payment_run
#print axioms skipped_payment
#print axioms distinct_halts
#print axioms recatch_run
#print axioms recatch_negative
#print axioms handler_payload_observation
#print axioms constructor_payload_observation
#print axioms wrong_handler_payload
#print axioms ctor_input_reached
#print axioms constructor_prefix_view
#print axioms panic_constructor_failed
#print axioms panic_work_reached
#print axioms panic_constructor_application
#print axioms later_panic_failed
#print axioms panic_handler_application
#print axioms panic_not_exhausted_or_diverged
#print axioms guard_work_reached
#print axioms collision_failed
#print axioms collision_handler_application
#print axioms argument_bypasses_handler
#print axioms static_bypasses_handler
#print axioms constructor_reason_not_returned
#print axioms wrong_ancestor_boundary
#print axioms dirty_transaction_snapshot
#print axioms panic_handler_atomic_vector_status
#print axioms collision_atomic_vector_status
#print axioms observed_handler_failure
#print axioms observed_atomic_status
#print axioms frame_failed
#print axioms fourth_read_reached
#print axioms repeated_after_failure_application
#print axioms repeated_after_failure_vector
end Solidity.Lowering.V08.HandlerControls
