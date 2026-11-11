import Solidity.Correctness.Lowering.Unchecked.WordProgram
import Solidity.Correctness.Lowering.Unchecked.IntegerOne
import Solidity.Correctness.Lowering.Unchecked.SourceOne
import Solidity.Source.Agreement.PrimitiveSlot
import Solidity.Lowering.V07.IntegerLocalFamily

/-!
# Exact destination/old-value association for word increments

Guards certifying `z = a +% b` as an increment of `z`. The total refinement
requires the arithmetic's left operand to be that same destination slot and
its right operand to be the literal one. Certificates contain only typed AST
facts. Raw/Source name binding, checkedness association, full state/failure
correspondence and the production endpoint remain separate obligations.
-/
namespace Solidity.Correctness.Lowering.Unchecked
open Solidity.Lowering.V07

/-- Static refinement of the supplied program to a same-slot update by one. -/
structure WordOneAssociation {C : Contract} {Γ : Ctx}
    (inc : Bool) (program : Prog C Γ Γ) where
  target : WordProgramAssociation (if inc then .add else .sub) program
  old : target.arithmetic.left = .simple (.local target.slot)
  one : target.arithmetic.right = .simple (.lit 1 (by decide))

/-- Total checking of destination, old-value slot and exact literal operand.
This uint256/local prototype is not a final exclusion of wider syntax. -/
def checkWordOne {C : Contract} {Γ : Ctx}
    (inc : Bool) (program : Prog C Γ Γ) : Option (WordOneAssociation inc program) := do
  let target ← checkWordProgram (if inc then .add else .sub) program
  match hOld : target.arithmetic.left, hOne : target.arithmetic.right with
  | .simple (.local slot), .simple (.lit n _) =>
    if same : slot = target.slot then
      if number : n = 1 then
        some ⟨target, by rw [hOld, same], by subst n; exact hOne⟩
      else none
    else none
  | _, _ => none

/-- The actual supplied program's arithmetic operands follow from static
association and one initial local observation. No operand-evaluation equation
or whole-program correctness certificate is an input. This remains a model
update/Source arithmetic leaf, not the complete Source statement bridge. -/
theorem wordOne_run {D : Source.Layout} {C : Contract} {Γ : Ctx}
    (target : State C Γ) (inc : Bool) (program : Prog C Γ Γ)
    (certificate : WordOneAssociation inc program) (x : Int)
    (range : Source.IntTy.u256.lo ≤ x ∧ x ≤ Source.IntTy.u256.hi)
    (read : TEnv.get certificate.target.slot target.env = integerValue Source.IntTy.u256 x range) :
    ∃ (sourceResult : Source.Val D (.int Source.IntTy.u256)) (modelResult : PrimTy.uint.Denote),
      Source.binVal false (if inc then .add else .sub)
        (.int x range) (.int 1 (integerOne_range Source.IntTy.u256)) = .ok sourceResult ∧
      IntValueRel Source.IntTy.u256 sourceResult modelResult ∧
      program.run target = .ok (⟨target.setLocal certificate.target.slot modelResult,
        List.prefix_refl _⟩ : Out C target.H Γ) := by
  apply wordProgramAssociation_run target (if inc then .add else .sub) program certificate.target
    x 1 range (integerOne_range Source.IntTy.u256)
  · rw [certificate.old]
    change Except.ok (TEnv.get certificate.target.slot target.env) = _
    rw [read]
  · rw [certificate.one]
    rfl

open Source.Agreement

/-- One intrinsic Source shape records both the selected expression and
its unchanged context. Other statement constructors cannot acquire this
witness by erasing an output-context index. -/
inductive IncrementSourceShapeV2 {E : Source.Env} {R : List Source.STy}
    {M : Bool} {k : Source.SCtx} {Γ : Source.RCtx}
    (inc prefixResult : Bool) (slot : Source.Idx Γ (.int Source.IntTy.u256)) :
    {Δ : Source.RCtx} → Source.RStmt E R M k Γ Δ → Type where
  | matched : IncrementSourceShapeV2 inc prefixResult slot
      (.expr (.incDec inc prefixResult (.local slot)))

/-- Static V2 association of the actual resolved Source update and supplied
model program at the same primitive local position. Only syntax and index
facts are fields; neither execution nor a poststate relation is assumed.
This first uint256 increment family leaves other syntax/types as coverage
obligations, not exclusions from the production domain. -/
structure PairedIncrementV2 {E : Source.Env} {C : Contract}
    {R : List Source.STy} {M loop : Bool} {Δ : Source.RCtx} (pre tail : List PrimTy)
    (source : Source.RStmt E R M ⟨loop, true⟩
      (sourceContext (pre ++ .uint :: tail)) Δ)
    (program : Prog C (modelContext (pre ++ .uint :: tail))
      (modelContext (pre ++ .uint :: tail))) where
  inc : Bool
  prefixResult : Bool
  sourceShape : IncrementSourceShapeV2 inc prefixResult
    (sourcePrimitiveSlot .uint tail pre) source
  model : WordOneAssociation inc program
  modelSlot : model.target.slot = modelPrimitiveSlot .uint tail pre

private def checkPairedExpressionV2 {E : Source.Env} {C : Contract}
    {R : List Source.STy} {M loop : Bool} (pre tail : List PrimTy) {τ : Source.STy}
    (expression : Source.RExpr E (sourceContext (pre ++ .uint :: tail)) τ)
    (program : Prog C (modelContext (pre ++ .uint :: tail))
      (modelContext (pre ++ .uint :: tail))) :
    Option (PairedIncrementV2 (R := R) (M := M) (loop := loop) pre tail (.expr expression) program) :=
  match expression with
  | .incDec inc prefixResult location =>
    match location with
    | .local slot =>
      match τ with
      | .int ⟨false, 256, _⟩ => do
        if position : slot.toNat = (sourcePrimitiveSlot .uint tail pre).toNat then
          let model ← checkWordOne inc program
          if same : model.target.slot = modelPrimitiveSlot .uint tail pre then
            some ⟨inc, prefixResult,
              by rw [source_idx_injective _ _ position]; exact .matched, model, same⟩
          else none
        else none
      | _ => none
    | _ => none
  | _ => none

/-- Total supplied-pair checking. The actual Source type is matched before
its typed index is compared; integer positions alone cannot erase a width.
Wrong directions, slots and model shapes are refused, without accepting
semantic proof arguments. Raw/name and unchecked-entry linkage remain. -/
def checkPairedIncrementV2 {E : Source.Env} {C : Contract}
    {R : List Source.STy} {M loop : Bool} {Δ : Source.RCtx} (pre tail : List PrimTy)
    (source : Source.RStmt E R M ⟨loop, true⟩ (sourceContext (pre ++ .uint :: tail)) Δ)
    (program : Prog C (modelContext (pre ++ .uint :: tail))
      (modelContext (pre ++ .uint :: tail))) : Option (PairedIncrementV2 pre tail source program) :=
  match source with
  | .expr expression => checkPairedExpressionV2 pre tail expression program
  | _ => none

private theorem primitiveUInt_of_integerRelationV2 {D : Source.Layout}
    (source : Source.Val D (.int Source.IntTy.u256)) (target : PrimTy.uint.Denote)
    (related : IntValueRel Source.IntTy.u256 source target) :
    PrimitiveRel D .uint source target := by
  cases source with
  | int x range =>
    have same : x = target.val := Option.some.inj related
    subst x
    exact .uint target range
  | memRef h _ => cases h
  | storRef h _ => cases h
  | cdRef h _ _ => cases h

/-- Derive both actual runs and every primitive post-local from initial
correspondence. The Source computation uses the explicit unchecked runtime
frame and keeps the complete interpreter state; the model keeps every
nonlocal field through glob. This does not prove unchecked entry, a concrete
global encoding, raw producer association, resources or PassCorrect. -/
theorem pairedIncrementV2_run {E : Source.Env} {C : Contract}
    {R : List Source.STy} {M loop : Bool} (pre tail : List PrimTy)
    (source : Source.RStmt E R M ⟨loop, true⟩
      (sourceContext (pre ++ .uint :: tail)) (sourceContext (pre ++ .uint :: tail)))
    (program : Prog C (modelContext (pre ++ .uint :: tail))
      (modelContext (pre ++ .uint :: tail)))
    (association : PairedIncrementV2 pre tail source program)
    (G : Source.Glob E) (F : Source.Fr) (fuel nps : Nat) (ph : Option (Source.Ph E))
    (plan : Source.FailureExecution.RuntimePlan) (known : Bool)
    (ls : Source.Locals E.layout (sourceContext (pre ++ .uint :: tail))) (st : Source.St E)
    (model : Solidity.State C (modelContext (pre ++ .uint :: tail)))
    (initial : LocalsRel E.layout C model.H (pre ++ .uint :: tail) ls model.env) :
    ∃ (sourceResult : Source.Val E.layout (.int Source.IntTy.u256))
      (modelResult : PrimTy.uint.Denote),
      (Source.execS G { F with checked := false } (fuel + 3) nps ph source ls
        (plan := plan) (calldataKnown := known)).run (.nil, st) =
          (.ok (.normal (ls.set (sourcePrimitiveSlot .uint tail pre) sourceResult)), (.nil, st)) ∧
      program.run model = .ok (⟨model.setLocal (modelPrimitiveSlot .uint tail pre) modelResult,
        List.prefix_refl _⟩ : Out C model.H (modelContext (pre ++ .uint :: tail))) ∧
      StateLocalsRel E C (pre ++ .uint :: tail)
        (ls.set (sourcePrimitiveSlot .uint tail pre) sourceResult)
        (model.setLocal (modelPrimitiveSlot .uint tail pre) modelResult) ∧
      (model.setLocal (modelPrimitiveSlot .uint tail pre) modelResult).glob = model.glob := by
  rcases association with ⟨inc, prefixResult, shape, certificate, same⟩
  cases shape
  let value : PrimTy.uint.Denote := TEnv.get (modelPrimitiveSlot .uint tail pre) model.env
  have range : Source.IntTy.u256.lo ≤ value.val ∧ value.val ≤ Source.IntTy.u256.hi :=
    (Source.Agreement.uint_range value.val).mp value.property
  have selected := primitive_slot_get_related E.layout C model.H .uint pre tail ls model.env initial
  have readSource : ls.get (sourcePrimitiveSlot .uint tail pre) =
      Source.Val.int value.val range :=
    primitive_related_ofModel E.layout .uint _ value selected
  have readModel : TEnv.get certificate.target.slot model.env =
      integerValue Source.IntTy.u256 value.val range := by
    rw [same]
    rfl
  obtain ⟨sourceResult, modelResult, arithmetic, valueRelated, modelRun⟩ :=
    wordOne_run (D := E.layout) model inc program certificate value.val range readModel
  rw [same] at modelRun
  have operation : Source.incDecVal false inc
      (ls.get (sourcePrimitiveSlot .uint tail pre)) = .ok sourceResult := by
    rw [readSource]
    exact (integerValueUpdate Source.IntTy.u256 false inc
      (.int value.val range)).symm.trans arithmetic
  refine ⟨sourceResult, modelResult, ?_, modelRun, ?_, rfl⟩
  · simp only [localUpdate_statementV2, operation]
  · exact primitive_slot_set_related E.layout C model.H .uint pre tail ls model.env
      sourceResult modelResult
      (primitiveUInt_of_integerRelationV2 sourceResult modelResult valueRelated) initial

#print axioms pairedIncrementV2_run

#print axioms wordOne_run

end Solidity.Correctness.Lowering.Unchecked
