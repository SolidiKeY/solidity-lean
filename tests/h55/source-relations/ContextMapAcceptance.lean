import Solidity.Lowering.V07.P12NextInterface

/-! Standalone full-contract transport. Pointwise equivalence is a premise of
these generic adapters, not a claim about an as-yet unimplemented new producer.
No Condition/MemoryCapture/StorageCapture field is dropped or reconstructed with
a weaker statement: transport uses equality of the entire world-indexed inputs. -/
namespace H55.SourceRelations
open Solidity Solidity.Lowering.V07 Solidity.Lowering.V07.P12NextInterface

theorem related_iff {D : Source.Layout} {srcΓ : Source.RCtx}
    {C : Contract} {H : HTy} {Γ : Ctx}
    {R S : (τ : Source.STy) → (u : LTy) → Source.Val D τ → u.TDenote C H → Prop}
    (equivalent : ∀ τ u sv tv, R τ u sv tv ↔ S τ u sv tv)
    (m : ContextMap srcΓ Γ) (source : Source.Locals D srcΓ) (target : TEnv C H Γ) :
    m.Related R source target ↔ m.Related S source target := by
  constructor
  · intro related τ i
    exact (equivalent _ _ _ _).mp (related i)
  · intro related τ i
    exact (equivalent _ _ _ _).mpr (related i)

section
variable {E : Source.Env} {C : Contract} {srcΓ : Source.RCtx} {Γ : Ctx}
variable {a b : ValueRelation E C} {wa wb : WorldRelation E C}

def ValuesEquivalent (a b : ValueRelation E C) : Prop :=
  ∀ source target τ u sv tv, a source target τ u sv tv ↔ b source target τ u sv tv

def WorldsEquivalent (wa wb : WorldRelation E C) : Prop :=
  ∀ source target, wa source target ↔ wb source target

/-- Retains both reached worlds, the target heap, all Source types, and all
intrinsic local kinds. Equivalence proved only on scalar inputs does not
establish this hypothesis for arbitrary world-indexed relations. -/
theorem values_eq (equivalent : ValuesEquivalent a b) : a = b := by
  funext source target τ u sv tv
  exact propext (equivalent source target τ u sv tv)

theorem worlds_eq (equivalent : WorldsEquivalent wa wb) : wa = wb := by
  funext source target
  exact propext (equivalent source target)

theorem aligned_iff (values : ValuesEquivalent a b) (worlds : WorldsEquivalent wa wb)
    (m : ContextMap srcΓ Γ) (source : Source.EMState E srcΓ) (target : State C Γ) :
    Aligned m a wa source target ↔ Aligned m b wb source target := by
  cases values_eq values
  cases worlds_eq worlds
  exact Iff.rfl

variable {G : Source.Glob E} {F : Source.Fr} {m : ContextMap srcΓ Γ}
variable {conditionExpr : Source.RExpr E srcΓ .bool}

def transportCondition (values : a = b) (worlds : wa = wb)
    (input : Condition G F m a wa conditionExpr) : Condition G F m b wb conditionExpr := by
  cases values
  cases worlds
  exact input

theorem condition_operand_preserved (values : a = b) (worlds : wa = wb)
    (input : Condition G F m a wa conditionExpr) :
    (transportCondition values worlds input).operand = input.operand := by
  cases values
  cases worlds
  rfl

theorem condition_roundtrip (values : a = b) (worlds : wa = wb)
    (input : Condition G F m a wa conditionExpr) :
    transportCondition values.symm worlds.symm (transportCondition values worlds input) = input := by
  cases values
  cases worlds
  rfl

variable {τ : Source.STy} {R : RefTy} {valueExpr : Source.RExpr E srcΓ τ}
variable {memory : τ.loc? = some .memory} {mapFree : (Ty.ref R).mapFree = true}

def transportMemory (values : a = b) (worlds : wa = wb)
    (input : MemoryCapture G F m a wa τ memory R mapFree valueExpr) :
    MemoryCapture G F m b wb τ memory R mapFree valueExpr := by
  cases values
  cases worlds
  exact input

theorem memory_code_preserved (values : a = b) (worlds : wa = wb)
    (input : MemoryCapture G F m a wa τ memory R mapFree valueExpr) :
    (transportMemory values worlds input).code = input.code := by
  cases values
  cases worlds
  rfl

theorem memory_roundtrip (values : a = b) (worlds : wa = wb)
    (input : MemoryCapture G F m a wa τ memory R mapFree valueExpr) :
    transportMemory values.symm worlds.symm (transportMemory values worlds input) = input := by
  cases values
  cases worlds
  rfl

variable {storage : τ.loc? = some .storage}

def transportStorage (values : a = b) (worlds : wa = wb)
    (input : StorageCapture G F m a wa τ storage R valueExpr) :
    StorageCapture G F m b wb τ storage R valueExpr := by
  cases values
  cases worlds
  exact input

theorem storage_code_preserved (values : a = b) (worlds : wa = wb)
    (input : StorageCapture G F m a wa τ storage R valueExpr) :
    (transportStorage values worlds input).code = input.code := by
  cases values
  cases worlds
  rfl

theorem storage_roundtrip (values : a = b) (worlds : wa = wb)
    (input : StorageCapture G F m a wa τ storage R valueExpr) :
    transportStorage values.symm worlds.symm (transportStorage values worlds input) = input := by
  cases values
  cases worlds
  rfl
end

#print axioms related_iff
#print axioms values_eq
#print axioms worlds_eq
#print axioms aligned_iff
#print axioms condition_operand_preserved
#print axioms condition_roundtrip
#print axioms memory_code_preserved
#print axioms memory_roundtrip
#print axioms storage_code_preserved
#print axioms storage_roundtrip
end H55.SourceRelations
