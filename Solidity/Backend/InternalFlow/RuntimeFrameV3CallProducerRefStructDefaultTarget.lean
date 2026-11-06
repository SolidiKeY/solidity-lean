import Solidity.Backend.InternalFlow.RuntimeFrameFootprint
import Solidity.Evm.MemoryStructDefaultPlan

/-! Actual target execution and reserved-word framing for finite default plans.
These are proof predicates over the existing certified plans and Evm.run, not
another allocation representation. Typed heap simulation remains DefaultPlan.sound. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.V3CallProducerRef.StructDefault
open Evm Evm.Memory Semantics

/-- A real allocation run, exact cursor/root and unchanged words1..frame.
The input may be any machine with the stated cursor and capacity, not merely a
whitelist of represented source heaps. -/
def PlanRuns {R : RefTy} (plan : DefaultPlan R) : Prop :=
  ∀ (m : Machine) (frame : Nat) (cursor : Fin W),
    0 < frame → frame ≤ cursor.val → m.mem 0 = .val cursor →
    cursor.val + plan.cost < W →
    ∃ after : Machine,
      Evm.run plan.code m = .ok (after.push (.val (wmod (cursor.val + plan.root)))) 0 ∧
      after.mem 0 = .val (wmod (cursor.val + plan.cost)) ∧
      Footprint.Words 1 frame m after ∧ after.stack = m.stack

/-- A field fold consumes child allocations without retaining their temporary
stack results; all old reserved words and the caller stack remain exact. -/
def FieldsRun {fs : List (Name × Ty)} (fields : DefaultFieldsPlan fs) : Prop :=
  ∀ (m : Machine) (frame : Nat) (cursor : Fin W),
    0 < frame → frame ≤ cursor.val → m.mem 0 = .val cursor →
    cursor.val + fields.cost < W →
    ∃ after : Machine, Evm.run fields.code m = .ok after 0 ∧
      after.mem 0 = .val (wmod (cursor.val + fields.cost)) ∧
      Footprint.Words 1 frame m after ∧ after.stack = m.stack

theorem array_runs (p : PrimTy) : PlanRuns (DefaultPlan.array p) := by
  intro m frame cursor positive above cell space
  refine ⟨allocateMachine m cursor (wmod 0), ?_, ?_,
    Footprint.allocation_words (by decide) cursor (wmod 0) above, rfl⟩
  · change Evm.run ([.push w[0]] ++ allocateArrayCode) m = _
    rw [Evm.run_append_ok (show Evm.run [.push w[0]] m = .ok (m.push w[0]) 0 from rfl)]
    simpa only [DefaultPlan.array, Nat.add_zero, wmod_of_lt cursor.isLt] using
      allocateArray_run m cursor (wmod 0) cell
  · rfl

theorem nil_runs : FieldsRun DefaultFieldsPlan.nil := by
  intro m frame cursor positive above cell space
  refine ⟨m, rfl, ?_, Footprint.words_refl _ _ _, rfl⟩
  simpa only [DefaultFieldsPlan.nil, Nat.add_zero, wmod_of_lt cursor.isLt] using cell

theorem primitive_runs (f : Name) (p : PrimTy) {fs : List (Name × Ty)}
    (tail : DefaultFieldsPlan fs) (framed : FieldsRun tail) :
    FieldsRun (DefaultFieldsPlan.consPrimitive f p tail) := framed

theorem reference_runs (f : Name) {R : RefTy} {fs : List (Name × Ty)}
    (head : DefaultPlan R) (tail : DefaultFieldsPlan fs)
    (headFramed : PlanRuns head) (tailFramed : FieldsRun tail) :
    FieldsRun (DefaultFieldsPlan.consReference f head tail) := by
  intro m frame cursor positive above cell space
  change cursor.val + (head.cost + tail.cost) < W at space
  have headSpace : cursor.val + head.cost < W := by omega
  obtain ⟨first, firstRun, firstCursor, firstWords, firstStack⟩ :=
    headFramed m frame cursor positive above cell headSpace
  let cursor₁ : Fin W := ⟨cursor.val + head.cost, headSpace⟩
  have firstCell : first.mem 0 = .val cursor₁ := by
    simpa only [wmod_of_lt headSpace] using firstCursor
  obtain ⟨last, tailRun, tailCursor, tailWords, tailStack⟩ :=
    tailFramed first frame cursor₁ positive (by dsimp only [cursor₁]; omega)
      firstCell (by dsimp only [cursor₁]; omega)
  refine ⟨last, ?_, ?_, Footprint.words_trans firstWords tailWords,
    tailStack.trans firstStack⟩
  · change Evm.run (head.code ++ ([.pop] ++ tail.code)) m = _
    rw [Evm.run_append_ok firstRun,
      Evm.run_append_ok (show Evm.run [.pop]
        (first.push (.val (wmod (cursor.val + head.root)))) = .ok first 0 from rfl)]
    exact tailRun
  · change last.mem 0 = .val (wmod (cursor.val + (head.cost + tail.cost)))
    simpa only [cursor₁, Nat.add_assoc] using tailCursor

theorem struct_runs (s : Name) (fields : DefaultFieldsPlan (structDef s))
    (framed : FieldsRun fields) : PlanRuns (DefaultPlan.struct s fields) := by
  intro m frame cursor positive above cell space
  change cursor.val + (fields.cost + structAllocationSize s) < W at space
  have childSpace : cursor.val + fields.cost < W := by omega
  obtain ⟨first, firstRun, firstCursor, firstWords, firstStack⟩ :=
    framed m frame cursor positive above cell childSpace
  let parent : Fin W := ⟨cursor.val + fields.cost, childSpace⟩
  have parentCell : first.mem 0 = .val parent := by
    simpa only [wmod_of_lt childSpace] using firstCursor
  have parentPositive : 0 < parent.val := by dsimp only [parent]; omega
  have parentAbove : frame ≤ parent.val := by dsimp only [parent]; omega
  have rootBelow : fields.cost ≤ parent.val := by dsimp only [parent]; omega
  have fieldsFit : parent.val + 0 + (structDef s).length ≤ W := by
    have size : (structDef s).length ≤ structAllocationSize s := Nat.le_max_right _ _
    dsimp only [parent]
    omega
  let allocated := allocateStructMachine first parent (structAllocationSize s)
  let final := initializeReferenceMachine (structDef s) fields.offsets fields.cost 0 parent allocated
  have parentRun := allocateStruct_run first parent (structAllocationSize s) parentCell
  have initialized := initializeReference_run (structDef s) fields.offsets fields.cost 0
    parent allocated rootBelow fieldsFit
  refine ⟨final, ?_, ?_, ?_, ?_⟩
  · change Evm.run (fields.code ++ (allocateStructCode (structAllocationSize s) ++
      initializeReferenceCode (structDef s) fields.offsets fields.cost 0)) m = _
    rw [Evm.run_append_ok firstRun, Evm.run_append_ok parentRun]
    simpa only [DefaultPlan.struct, wmod_of_lt childSpace] using initialized
  · change final.mem 0 = .val (wmod (cursor.val + (fields.cost + structAllocationSize s)))
    have untouched := initializeReference_other (structDef s) fields.offsets fields.cost 0
      parent allocated 0 (.inl (by omega))
    change final.mem 0 = allocated.mem 0 at untouched
    rw [untouched]
    change Evm.Word.val (wmod ((cursor.val + fields.cost) + structAllocationSize s)) = _
    rw [Nat.add_assoc]
  · intro address lower upper
    have untouched := initializeReference_other (structDef s) fields.offsets fields.cost 0
      parent allocated address (.inl (by omega))
    exact untouched.trans ((allocateStructMachine_other first parent (structAllocationSize s)
      address (by omega)).trans (firstWords address lower upper))
  · have shape := congrArg Machine.stack
      (initializeReference_shape (structDef s) fields.offsets fields.cost 0 parent allocated)
    exact shape.trans firstStack

#print axioms array_runs
#print axioms reference_runs
#print axioms struct_runs

theorem fields_selected (child : (R : RefTy) → Option (DefaultPlan R))
    (childFramed : ∀ R plan, child R = some plan → PlanRuns plan)
    (fs : List (Name × Ty)) : ∀ fields,
    defaultFieldsPlanWith child fs = some fields → FieldsRun fields := by
  induction fs with
  | nil =>
    intro fields selected
    change some DefaultFieldsPlan.nil = some fields at selected
    cases selected
    exact nil_runs
  | cons fT fs ih =>
    obtain ⟨f, T⟩ := fT
    intro fields selected
    cases T with
    | prim p =>
      cases tailEq : defaultFieldsPlanWith child fs with
      | none =>
        simp only [defaultFieldsPlanWith, tailEq, Option.map_none] at selected
        cases selected
      | some tail =>
        simp only [defaultFieldsPlanWith, tailEq, Option.map_some] at selected
        cases selected
        exact primitive_runs f p tail (ih tail tailEq)
    | ref R =>
      cases headEq : child R with
      | none =>
        simp only [defaultFieldsPlanWith, headEq] at selected
        cases selected
      | some head =>
        cases tailEq : defaultFieldsPlanWith child fs with
        | none =>
          simp only [defaultFieldsPlanWith, headEq, tailEq] at selected
          cases selected
        | some tail =>
          simp only [defaultFieldsPlanWith, headEq, tailEq] at selected
          cases selected
          exact reference_runs f head tail (childFramed R head headEq) (ih tail tailEq)

/-- Every plan actually selected by the published bounded selector has the
proved target framing. Depth and refusal boundaries are unchanged. -/
theorem selector_runs (depth : Nat) : ∀ R (plan : DefaultPlan R),
    defaultPlanAt depth R = some plan → PlanRuns plan := by
  induction depth with
  | zero =>
    intro R plan selected
    cases R with
    | array E =>
      cases E with
      | prim p =>
        change some (DefaultPlan.array p) = some plan at selected
        cases selected
        exact array_runs p
      | ref R => cases selected
    | struct s => cases selected
    | fixed E n => cases selected
    | mapping p E => cases selected
  | succ depth ih =>
    intro R plan selected
    cases R with
    | array E =>
      cases E with
      | prim p =>
        change some (DefaultPlan.array p) = some plan at selected
        cases selected
        exact array_runs p
      | ref R => cases selected
    | fixed E n => cases selected
    | mapping p E => cases selected
    | struct s =>
      cases fieldsEq : defaultFieldsPlanWith (defaultPlanAt depth) (structDef s) with
      | none =>
        simp only [defaultPlanAt, fieldsEq, Option.map_none] at selected
        cases selected
      | some fields =>
        simp only [defaultPlanAt, fieldsEq, Option.map_some] at selected
        cases selected
        exact struct_runs s fields (fields_selected (defaultPlanAt depth) ih _ fields fieldsEq)

/-- Wrap the existing selector result with its proved footprint, without a
second selector or any new admitted type. -/
def select? (R : RefTy) : Option {plan : DefaultPlan R // PlanRuns plan} :=
  match selected : defaultPlan? R with
  | none => none
  | some plan => some ⟨plan, selector_runs (tyRank (.ref R)) R plan selected⟩

theorem selection_unchanged (R : RefTy) : (select? R).map Subtype.val = defaultPlan? R := by
  unfold select?
  split <;> rename_i selected <;> simp only [selected, Option.map_none, Option.map_some]

#print axioms selector_runs
#print axioms selection_unchanged

end Solidity.Backend.InternalFlow.RuntimeFrame.V3CallProducerRef.StructDefault
