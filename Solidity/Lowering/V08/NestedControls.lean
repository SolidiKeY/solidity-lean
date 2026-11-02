import Solidity.Lowering.V08.LibraryControls
import Solidity.Lowering.V08.ProjectionControls

/-! Two populated atomic snapshots and a real funded constructor. Atomic status
consumers handle arbitrary THalts; only tryCreate uses published catchability.
No source callback/interpreter, canonical layout or ABI certificate is supplied. -/
namespace Solidity.Lowering.V08.NestedControls
open Solidity.ContractWorld
open Controls

def CreatedCell : Contract := contract!{
  uint saved; uint transient scratch;
  constructor() payable { saved = 8; scratch = 12; }
}
def catalog : Bool → Contract | false => Cell | true => CreatedCell
def initial : World catalog := World.empty catalog
  (fun address => if address = sender then ⟨100, by decide +kernel⟩ else ⟨0, by decide +kernel⟩)
def setup : TRes (World catalog) := do
  let (world, _) ← initial.create false self .nil Controls.ctx
  pure world

def observe (world : World catalog) : Option (Int × Int × Int × Int) := do
  let store ← world.storage? (⟨self⟩ : Handle false)
  let .prim saved ← store.find (SRef.ofRoot "saved" rfl)
  let .prim scratch ← store.find (SRef.ofRoot "scratch" rfl)
  pure ((world.balance sender).1, (world.balance self).1, saved.1, scratch.1)

def constructedCells (world : World catalog) : Option (Int × Int) := do
  let store ← world.storage? (⟨third⟩ : Handle true)
  let .prim saved ← store.find (SRef.ofRoot "saved" rfl)
  let .prim scratch ← store.find (SRef.ofRoot "scratch" rfl)
  pure (saved.1, scratch.1)

def innerHalt : THalt := .revertWith [0xde, 0xad]
def middleHalt : THalt := .revertWith [0xfa, 0x02]
def constructor : Prog CreatedCell [] [] := sol[CreatedCell]{ saved = 8; scratch = 12; }
def createCtx : Context := { sender, mode := .ordinary ⟨3, by decide +kernel⟩ }
def enterOuter (w : World catalog) := w.call (⟨self⟩ : Handle false) entry paidCtx
def enterMiddle (w : World catalog) (_ : List UInt8) :=
  w.call (⟨self⟩ : Handle false) ProjectionControls.innerEntry ProjectionControls.innerContext

def failSuccess (_ : World catalog) (_ : Handle true) : TRes (World catalog × Unit) := .error innerHalt
def handler (w : World catalog) (_ : THalt) : TRes (World catalog × Unit) := .ok (w, ())
def inner (w : World catalog) (_ : Unit) : TRes (World catalog × Unit) :=
  w.tryCreate (.ok ()) true (fun _ => third) (fun _ => constructor) (fun _ => createCtx)
    failSuccess handler

def middleTail (w : World catalog) (status : TRes Unit) : TRes (World catalog × Unit) := do
  match status with
  | .error (.revertWith bytes) =>
    if bytes = [0xde, 0xad] then
      let _ ← w.call (⟨self⟩ : Handle false) entry paidCtx
      .error middleHalt
    else .error .panic
  | _ => .error .panic

def tailEntry : Entry Cell (List UInt8) :=
  { locals := [], body := sol[Cell]{ saved = 11; scratch = 23; },
    result := fun _ => .ok [0xab, 0xcd], payable := true }
def tailCtx : Context := { sender, mode := .ordinary ⟨1, by decide +kernel⟩ }
def outerTail (w : World catalog) (status : TRes Unit) : TRes (World catalog × List UInt8) :=
  match status with
  | .error (.revertWith bytes) =>
    if bytes = [0xfa, 0x02] then w.call (⟨self⟩ : Handle false) tailEntry tailCtx else .error .panic
  | _ => .error .panic

def frame (input : World catalog) : TRes (World catalog × List UInt8) := do
  let (outerSnapshot, a) ← enterOuter input
  let (afterMiddle, middleStatus) := atomic outerSnapshot (do
    let (middleSnapshot, b) ← enterMiddle outerSnapshot a
    let (afterInner, innerStatus) := atomic middleSnapshot (inner middleSnapshot b)
    middleTail afterInner innerStatus)
  outerTail afterMiddle middleStatus

-- Extraction defaults are accompanied by complete successful execution equalities.
def base : World catalog := setup.toOption.getD initial
def outer : World catalog := (enterOuter base.resetTransient).toOption.map Prod.fst |>.getD initial
def middle : World catalog := (enterMiddle outer [0xab, 0xcd]).toOption.map Prod.fst |>.getD initial
def created : World catalog := (middle.create true third constructor createCtx).toOption.map Prod.fst |>.getD initial
def final : World catalog := (outerTail outer (.error middleHalt)).toOption.map Prod.fst |>.getD initial

theorem setup_reached : setup = .ok base := by rfl
/-- A checked result observation proves successful extraction without comparing
function-valued world fields or increasing reduction budgets. -/
private theorem extract_success {α : Type} (run : TRes (World catalog × α))
    (fallback : World catalog) (value : α)
    (checked : run.toOption.map Prod.snd = some value) :
    run = .ok ((run.toOption.map Prod.fst).getD fallback, value) := by
  cases run with
  | error halt => cases checked
  | ok pair =>
    cases pair with
    | mk world result =>
      have same : result = value := Option.some.inj checked
      cases same
      rfl

theorem outer_reached : enterOuter base.resetTransient = .ok (outer, [0xab, 0xcd]) := by
  exact extract_success _ initial _ (by decide +kernel)
theorem middle_reached : enterMiddle outer [0xab, 0xcd] = .ok (middle, ()) := by
  exact extract_success _ initial _ (by decide +kernel)
private instance : DecidableEq (Handle true) := fun a b =>
  decidable_of_iff (a.address = b.address) ⟨(by
    cases a
    cases b
    intro h
    cases h
    rfl), congrArg Handle.address⟩

theorem creation_reached : middle.create true third constructor createCtx = .ok (created, ⟨third⟩) := by
  exact extract_success _ initial _ (by decide +kernel)

theorem inner_not_reCaught : inner middle () = .error innerHalt := by
  exact tryCreate_success_continuation_failure middle created () true (fun _ => third)
    (fun _ => constructor) (fun _ => createCtx) ⟨third⟩ failSuccess handler innerHalt
    rfl creation_reached rfl

theorem creation_atomic : atomic middle (inner middle ()) = (middle, .error innerHalt) := by
  exact atomic_tryCreate_success_continuation_failure middle created () true (fun _ => third)
    (fun _ => constructor) (fun _ => createCtx) ⟨third⟩ failSuccess handler innerHalt
    rfl creation_reached rfl

theorem middle_failed : middleTail middle (.error innerHalt) = .error middleHalt := by
  change (do
    let _ ← middle.call (⟨self⟩ : Handle false) entry paidCtx
    (.error middleHalt : TRes (World catalog × Unit))) = .error middleHalt
  have paid : (middle.call (⟨self⟩ : Handle false) entry paidCtx).toOption.map Prod.snd = some [0xab, 0xcd] := by decide +kernel
  rw [extract_success _ initial _ paid]
  rfl
theorem tail_reached : outerTail outer (.error middleHalt) = .ok (final, [0xab, 0xcd]) := by
  exact extract_success _ initial _ (by decide +kernel)

/-- Actual supplied operations inhabit every premise of the general two-boundary law. -/
theorem nested_application : base.transact frame = (final.resetTransient, .ok [0xab, 0xcd]) := by
  exact transact_two_boundaries base outer middle final enterOuter enterMiddle inner
    middleTail outerTail [0xab, 0xcd] () [0xab, 0xcd] innerHalt middleHalt
    outer_reached middle_reached inner_not_reCaught middle_failed tail_reached

abbrev Vector := Option (Int × Int × Int × Int) × Int × Option (Int × Int) × Bool × Bool
/-- Ordered vector: sender/self balances, self persistent/transient slots;
third balance, third persistent/transient slots, third installed, catalogue library-role. -/
def vector (w : World catalog) : Vector :=
  (observe w, (w.balance third).1, constructedCells w,
    (w.accounts third).isSome, w.isLibrary true)

-- Stage product instances rather than increasing typeclass search budgets.
private instance : DecidableEq (Int × Int × Int × Int) := inferInstance
private instance : DecidableEq (Int × Option (Int × Int) × Bool × Bool) := inferInstance
private instance : DecidableEq Vector := inferInstance

theorem populated_snapshots :
    vector outer = (some (93, 7, 3, 9), 0, none, false, false) ∧
    vector middle = (some (91, 9, 5, 17), 0, none, false, false) ∧
    vector created = (some (88, 9, 5, 17), 3, some (8, 12), true, false) := by decide +kernel

def complete {α : Type} (run : World catalog × TRes α) := (vector run.1, run.2.toOption)
theorem complete_observation : complete (base.transact frame) =
    ((some (92, 8, 11, 0), 0, none, false, false), some [0xab, 0xcd]) := by
  rw [nested_application]
  decide +kernel

def readEntry : Entry Cell Int :=
  { locals := [], body := .nil, result := fun state => do
      let .prim value ← TRes.ofOpt (state.storage.find (SRef.ofRoot "scratch" rfl))
      pure value.1 }
def readFrame (w : World catalog) := w.call (⟨self⟩ : Handle false) readEntry Controls.ctx

theorem frame_reached : frame base.resetTransient = .ok (final, [0xab, 0xcd]) := by
  simp only [frame, outer_reached, bind, Except.bind, middle_reached,
    inner_not_reCaught, atomic_failure, middle_failed, tail_reached]

def readFinal : World catalog := (readFrame final.resetTransient).toOption.map Prod.fst |>.getD initial

theorem read_reached : readFrame final.resetTransient = .ok (readFinal, 0) := by
  exact extract_success _ initial _ (by decide +kernel)

/-- Apply the existing repeated transaction law, with a real scratch-slot read. -/
theorem repeated_application : (base.transact frame).1.transact readFrame =
    (readFinal.resetTransient, .ok 0) :=
  transact_repeat base final readFinal frame readFrame [0xab, 0xcd] 0 frame_reached read_reached

theorem repeated_reset : complete ((base.transact frame).1.transact readFrame) =
    ((some (92, 8, 11, 0), 0, none, false, false), some 0) := by
  rw [repeated_application]
  decide +kernel

/-- A real read outside a new transaction observes the still-dirty outer tail. -/
theorem dirty_read : (readFrame final).toOption.map Prod.snd = some 23 := by decide +kernel

theorem repeated_dirty_negative :
    ((base.transact frame).1.transact readFrame).2.toOption ≠
      (readFrame final).toOption.map Prod.snd := by
  rw [repeated_application, dirty_read]
  decide +kernel

def wrongAncestor : TRes (World catalog × List UInt8) := outerTail base (.error middleHalt)

theorem wrong_ancestor_run : wrongAncestor.toOption.map (fun pair => complete (pair.1.resetTransient, .ok pair.2)) =
    some ((some (99, 1, 11, 0), 0, none, false, false), some [0xab, 0xcd]) := by decide +kernel

theorem wrong_ancestor : some (complete (base.transact frame)) ≠
    wrongAncestor.toOption.map (fun pair => complete (pair.1.resetTransient, .ok pair.2)) := by
  rw [complete_observation, wrong_ancestor_run]
  decide +kernel

theorem dirty_transient_reuse : complete (base.transact frame) ≠
    ((some (92, 8, 11, 23), 0, none, false, false), some [0xab, 0xcd]) := by
  rw [complete_observation]
  decide +kernel

theorem wrong_payload : complete (base.transact frame) ≠
    ((some (92, 8, 11, 0), 0, none, false, false), some [0xab, 0xce]) := by
  rw [complete_observation]
  decide +kernel

theorem recatch_negative : (inner middle ()).toOption ≠ some (middle, ()) := by
  rw [inner_not_reCaught]
  exact Option.noConfusion

theorem distinct_halts : innerHalt ≠ middleHalt := by decide +kernel

/-- The raw TRes is retained too, independently of the decidable success view. -/
theorem complete_status : (vector (base.transact frame).1, (base.transact frame).2) =
    ((some (92, 8, 11, 0), 0, none, false, false), .ok [0xab, 0xcd]) := by
  rw [nested_application]
  apply Prod.ext
  · decide +kernel
  · rfl

theorem argument_failure :
    middle.tryCreate (.error (.revertWith [0x44, 0x55]) : TRes Unit) true
      (fun _ => third) (fun _ => constructor) (fun _ => createCtx) failSuccess handler =
      .error (.revertWith [0x44, 0x55]) :=
  World.tryCreate_argument_failure _ _ _ _ _ _ _ _

theorem static_failure :
    middle.tryCreate (.ok ()) true (fun _ => third) (fun _ => constructor)
      (fun _ => ({ sender, mode := .readOnly } : Context)) failSuccess handler = .error .revert :=
  tryCreate_static _ _ _ _ _ _ _ _ rfl

def revertingConstructor : Prog CreatedCell [] [] := sol[CreatedCell]{ saved = 8; scratch = 12; revert(); }
def caughtCreation : TRes (World catalog × Unit) :=
  middle.tryCreate (.ok ()) true (fun _ => third) (fun _ => revertingConstructor)
    (fun _ => createCtx) failSuccess handler

theorem caught_creation_vector : caughtCreation.toOption.map (fun pair => (vector pair.1, pair.2)) =
    some ((some (91, 9, 5, 17), 0, none, false, false), ()) := by decide +kernel

/-- Exhaustion/divergence remain outside the creation handler. This is the
published classification, not an execution witness for those constructors. -/
theorem catch_classification :
    catchable .revert = true ∧ catchable innerHalt = true ∧ catchable .panic = true ∧
    catchable .exhausted = false ∧ catchable .diverge = false := by decide +kernel

theorem middle_tail_dirty : (middle.call (⟨self⟩ : Handle false) entry paidCtx).toOption.map
    (fun pair => (vector pair.1, pair.2)) =
      some ((some (84, 16, 3, 9), 0, none, false, false), [0xab, 0xcd]) := by decide +kernel

def secondHalt : THalt := .revertWith [0x66, 0x77]
def readFail (w : World catalog) : TRes (World catalog × Unit) := do
  let (_, scratch) ← readFrame w
  if scratch = 0 then .error secondHalt else .error .panic

theorem second_failed : readFail final.resetTransient = .error secondHalt := by
  unfold readFail
  rw [read_reached]
  rfl

theorem repeated_failure_application : (base.transact frame).1.transact readFail =
    (final.resetTransient, .error secondHalt) :=
  transact_repeat_failure base final frame readFail [0xab, 0xcd] secondHalt frame_reached second_failed

theorem repeated_failure_vector :
    (vector ((base.transact frame).1.transact readFail).1,
      ((base.transact frame).1.transact readFail).2) =
    ((some (92, 8, 11, 0), 0, none, false, false), .error secondHalt) := by
  rw [repeated_failure_application]
  apply Prod.ext
  · decide +kernel
  · rfl

theorem second_wrong_payload : ((base.transact frame).1.transact readFail).2 ≠
    .error (.revertWith [0x66, 0x78]) := by
  rw [repeated_failure_application]
  intro same
  have bad := Except.error.inj same
  cases bad

#print axioms setup_reached
#print axioms outer_reached
#print axioms middle_reached
#print axioms creation_reached
#print axioms inner_not_reCaught
#print axioms creation_atomic
#print axioms middle_failed
#print axioms tail_reached
#print axioms nested_application
#print axioms populated_snapshots
#print axioms complete_observation
#print axioms frame_reached
#print axioms read_reached
#print axioms repeated_application
#print axioms repeated_reset
#print axioms dirty_read
#print axioms repeated_dirty_negative
#print axioms wrong_ancestor_run
#print axioms wrong_ancestor
#print axioms dirty_transient_reuse
#print axioms wrong_payload
#print axioms recatch_negative
#print axioms distinct_halts
#print axioms complete_status
#print axioms argument_failure
#print axioms static_failure
#print axioms caught_creation_vector
#print axioms catch_classification
#print axioms middle_tail_dirty
#print axioms second_failed
#print axioms repeated_failure_application
#print axioms repeated_failure_vector
#print axioms second_wrong_payload
end Solidity.Lowering.V08.NestedControls
