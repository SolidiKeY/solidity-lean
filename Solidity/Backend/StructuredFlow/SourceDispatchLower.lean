import Solidity.Backend.StructuredFlow.SourceDispatchDomain
import Solidity.Backend.StructuredFlow.SourceDispatchSlots

/-!
# Checked lowering of recognized Source templates

Guards emitting a target program from lexical shape alone: each selected
operand retains its context-map equation and intrinsic target type. Target
programs are the existing G19 builders, rather than a second implementation
of Source semantics or of any individual control-flow construct.
-/
namespace Solidity.Backend.StructuredFlow.SourceDispatch
open Solidity.Lowering.V07 Solidity.Lowering.G19

/-- Only the mapping facts required by the selected published theorem. -/
def Mapping {E : Source.Env} {M : Bool} {R : List Source.STy}
    {k : Source.SCtx} {srcΓ srcΔ : Source.RCtx} {s : Source.RStmt E R M k srcΓ srcΔ}
    {Γ : Ctx} (m : ContextMap srcΓ Γ) (plan : Plan E M s) : Type := by
  cases plan
  case blocks steps => exact BooleanSlots m.slot
  case conditional ci ca i a j b => exact BranchSlots m.slot ci ca i a j b
  case sequence ci ca i a j b dest donor =>
    exact BranchSlots m.slot ci ca i a j b × CopySlots m.slot dest donor
  case returning ci ca i a j b => exact BranchSlots m.slot ci ca i a j b
  case continuation ci ca i a j b tail => exact BranchSlots m.slot ci ca i a j b
  case returnTail ci ca dest donor => exact BoolPair m.slot ci ca × CopySlots m.slot dest donor
  case returnPair ci ca i a dest donor =>
    exact BoolPair m.slot ci ca × CopySlots m.slot i a × CopySlots m.slot dest donor
  case whileBreak i a => exact BoolPair m.slot i a
  case whileContinue i a tail => exact BoolPair m.slot i a
  case whileReturn i a => exact BoolPair m.slot i a
  case forBreak i a post => exact BoolPair m.slot i a
  case forContinue i a tail => exact BoolPair m.slot i a
  case forReturn i a post => exact BoolPair m.slot i a
  case doBreak i a condition => exact BoolPair m.slot i a
  case doContinue i a tail => exact BoolPair m.slot i a
  case doReturn i a condition => exact BoolPair m.slot i a

/-- Type mismatch is an explicit refusal, independently of syntax recognition. -/
def mapping? {E : Source.Env} {M : Bool} {R : List Source.STy}
    {k : Source.SCtx} {srcΓ srcΔ : Source.RCtx} {s : Source.RStmt E R M k srcΓ srcΔ}
    {Γ : Ctx} (m : ContextMap srcΓ Γ) (plan : Plan E M s) : Option (Mapping m plan) := by
  cases plan
  case blocks steps => exact booleanSlots? _ m.slot
  case conditional ci ca i a j b => exact branchSlots? m.slot ci ca i a j b
  case sequence ci ca i a j b dest donor =>
    exact do return (← branchSlots? m.slot ci ca i a j b, ← copySlots? m.slot dest donor)
  case returning ci ca i a j b => exact branchSlots? m.slot ci ca i a j b
  case continuation ci ca i a j b tail => exact branchSlots? m.slot ci ca i a j b
  case returnTail ci ca dest donor =>
    exact do return (← boolPair? m.slot ci ca, ← copySlots? m.slot dest donor)
  case returnPair ci ca i a dest donor =>
    exact do return (← boolPair? m.slot ci ca, ← copySlots? m.slot i a, ← copySlots? m.slot dest donor)
  case whileBreak i a => exact boolPair? m.slot i a
  case whileContinue i a tail => exact boolPair? m.slot i a
  case whileReturn i a => exact boolPair? m.slot i a
  case forBreak i a post => exact boolPair? m.slot i a
  case forContinue i a tail => exact boolPair? m.slot i a
  case forReturn i a post => exact boolPair? m.slot i a
  case doBreak i a condition => exact boolPair? m.slot i a
  case doContinue i a tail => exact boolPair? m.slot i a
  case doReturn i a condition => exact boolPair? m.slot i a

/-- Reuse the exact intrinsic target builders of the selected compiler theorem. -/
def program {E : Source.Env} {M : Bool} {R : List Source.STy}
    {k : Source.SCtx} {srcΓ srcΔ : Source.RCtx} {s : Source.RStmt E R M k srcΓ srcΔ}
    {C : Contract} {Γ : Ctx} (m : ContextMap srcΓ Γ) (plan : Plan E M s)
    (mapped : Mapping m plan) : (outΓ : Ctx) × Prog C Γ outΓ := by
  cases plan <;> dsimp [Mapping] at mapped
  case blocks steps => exact ⟨Γ,AssignmentBlocks.code mapped.index steps⟩
  case conditional ci ca i a j b =>
    exact ⟨Γ,ConditionalStatement.code mapped.condition.dest.index mapped.condition.donor.index
      mapped.left.dest.index mapped.left.donor.index mapped.rightDest.index mapped.rightDonor.index⟩
  case sequence ci ca i a j b dest donor =>
    exact ⟨Γ,ConditionalSequence.code mapped.1.condition.dest.index mapped.1.condition.donor.index
      mapped.1.left.dest.index mapped.1.left.donor.index mapped.1.rightDest.index mapped.1.rightDonor.index
      mapped.2.dest.index mapped.2.donor.index⟩
  case returning ci ca i a j b =>
    exact ⟨.val .bool :: Γ,ConditionalReturn.code mapped.condition.dest.index mapped.condition.donor.index
      mapped.left.dest.index mapped.left.donor.index mapped.rightDest.index mapped.rightDonor.index⟩
  case continuation ci ca i a j b tail =>
    exact ⟨.val .bool :: Γ,ConditionalReturnContinuation.code mapped.condition.dest.index mapped.condition.donor.index
      mapped.left.dest.index mapped.left.donor.index mapped.rightDest.index mapped.rightDonor.index .nil⟩
  case returnTail ci ca dest donor =>
    exact ⟨.val .bool :: Γ,ReturnTail.code mapped.1.dest.index mapped.1.donor.index
      mapped.2.dest.index mapped.2.donor.index⟩
  case returnPair ci ca i a dest donor =>
    exact ⟨.val .bool :: Γ,ReturnPair.code mapped.1.dest.index mapped.1.donor.index
      mapped.2.1.dest.index mapped.2.1.donor.index mapped.2.2.dest.index mapped.2.2.donor.index⟩
  case whileBreak i a =>
    exact ⟨Γ,AssignmentWhileBreak.code m i a mapped.dest.type_eq mapped.donor.type_eq⟩
  case whileContinue i a tail =>
    exact ⟨Γ,AssignmentWhileReset.code m i a mapped.dest.type_eq mapped.donor.type_eq⟩
  case whileReturn i a =>
    exact ⟨.val .bool :: Γ,AssignmentReturnFlag.code m i a mapped.dest.type_eq mapped.donor.type_eq⟩
  case forBreak i a post =>
    exact ⟨Γ,AssignmentWhileBreak.code m i a mapped.dest.type_eq mapped.donor.type_eq⟩
  case forContinue i a tail =>
    exact ⟨Γ,AssignmentWhileReset.code m i a mapped.dest.type_eq mapped.donor.type_eq⟩
  case forReturn i a post =>
    exact ⟨.val .bool :: Γ,AssignmentReturnFlag.code m i a mapped.dest.type_eq mapped.donor.type_eq⟩
  case doBreak i a condition =>
    exact ⟨Γ,AssignmentWhileBreak.code m i a mapped.dest.type_eq mapped.donor.type_eq⟩
  case doContinue i a tail =>
    exact ⟨Γ,AssignmentWhileBreak.code m i a mapped.dest.type_eq mapped.donor.type_eq⟩
  case doReturn i a condition =>
    exact ⟨.val .bool :: Γ,AssignmentDoWhileReturn.code m i a mapped.dest.type_eq mapped.donor.type_eq⟩

end Solidity.Backend.StructuredFlow.SourceDispatch
