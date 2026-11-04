import Solidity.Backend.FailurePaths.GuardLowering
import Solidity.Backend.FailurePaths.CheckedGuardsControls

/-! Computed intrinsic targets in the shared mixed context. All clients prove
actual lowering and public compilation, then consume the lowered-target
correctness theorem. No opaque witness choice or desired execution is supplied. -/
namespace Solidity.Backend.FailurePaths.GuardLowering.Controls
open Evm Evm.Memory CheckedGuards.Controls

def localTarget : Stmt C TgtCtx TgtCtx := RuntimeGuard.target .here
def logicalTarget (disjunction : Bool) : Stmt C TgtCtx TgtCtx :=
  LogicalGuard.target disjunction .here (.there .here)
def relationalTarget (o : PrimitivePackets.Comparisons.Order) : Stmt C TgtCtx TgtCtx :=
  RelationalGuard.target o false (.there (.there .here)) (.there (.there (.there .here)))

theorem local_lowered : lower (C:=C) maps localInput = some localTarget := rfl
theorem logical_lowered (disjunction : Bool) :
    lower (C:=C) maps (logicalInput disjunction) = some (logicalTarget disjunction) := by
  cases disjunction <;> rfl
theorem relational_lowered (o : PrimitivePackets.Comparisons.Order) :
    lower (C:=C) maps (relationalInput o) = some (relationalTarget o) := by cases o <;> rfl

theorem local_public : compileStmt 0 fragment localTarget = some (RuntimeGuard.selected 0 fragment .here) := rfl
theorem logical_public (disjunction : Bool) : compileStmt 0 fragment (logicalTarget disjunction) =
    some (LogicalGuard.selected 0 fragment disjunction .here (.there .here)) := by cases disjunction <;> rfl
theorem relational_public (o : PrimitivePackets.Comparisons.Order) : compileStmt 0 fragment (relationalTarget o) =
    some (RelationalGuard.selected 0 fragment o false (.there (.there .here)) (.there (.there (.there .here)))) := by
  cases o <;> rfl

theorem local_compiled : compile (C:=C) maps 0 fragment localInput = some localCode := by
  rw [compile_eq_checked]
  exact CheckedGuards.Controls.local_selected

theorem logical_compiled (disjunction : Bool) :
    compile (C:=C) maps 0 fragment (logicalInput disjunction) = some (logicalCode disjunction) := by
  rw [compile_eq_checked]
  exact CheckedGuards.Controls.logical_selected disjunction

theorem relational_compiled (o : PrimitivePackets.Comparisons.Order) :
    compile (C:=C) maps 0 fragment (relationalInput o) = some (relationalCode o) := by
  rw [compile_eq_checked]
  exact CheckedGuards.Controls.relational_selected o

theorem local_client (p : Roadmap.Pipeline) (left right : Bool) (x y : Int)
    (hx : (PrimitivePackets.Comparisons.ty false).lo ≤ x ∧ x ≤ (PrimitivePackets.Comparisons.ty false).hi)
    (hy : (PrimitivePackets.Comparisons.ty false).lo ≤ y ∧ y ≤ (PrimitivePackets.Comparisons.ty false).hi) :
    Agrees p left right x y hx hy localInput localCode :=
  lowered_correct maps 0 fragment localInput localTarget local_lowered _ local_public
    (globals p) frame 0 (locals left right x y hx hy) original (state left right x y hx hy)
    (related left right x y hx hy) (represented left right x y hx hy)

theorem logical_client (p : Roadmap.Pipeline) (left right disjunction : Bool) (x y : Int)
    (hx : (PrimitivePackets.Comparisons.ty false).lo ≤ x ∧ x ≤ (PrimitivePackets.Comparisons.ty false).hi)
    (hy : (PrimitivePackets.Comparisons.ty false).lo ≤ y ∧ y ≤ (PrimitivePackets.Comparisons.ty false).hi) :
    Agrees p left right x y hx hy (logicalInput disjunction) (logicalCode disjunction) :=
  lowered_correct maps 0 fragment _ _ (logical_lowered disjunction) _ (logical_public disjunction)
    (globals p) frame 0 (locals left right x y hx hy) original (state left right x y hx hy)
    (related left right x y hx hy) (represented left right x y hx hy)

theorem relational_client (p : Roadmap.Pipeline) (left right : Bool) (o : PrimitivePackets.Comparisons.Order) (x y : Int)
    (hx : (PrimitivePackets.Comparisons.ty false).lo ≤ x ∧ x ≤ (PrimitivePackets.Comparisons.ty false).hi)
    (hy : (PrimitivePackets.Comparisons.ty false).lo ≤ y ∧ y ≤ (PrimitivePackets.Comparisons.ty false).hi) :
    Agrees p left right x y hx hy (relationalInput o) (relationalCode o) :=
  lowered_correct maps 0 fragment _ _ (relational_lowered o) _ (relational_public o)
    (globals p) frame 0 (locals left right x y hx hy) original (state left right x y hx hy)
    (related left right x y hx hy) (represented left right x y hx hy)

theorem refusals_preserved (stmt : Source.RStmt E [] false .body SrcCtx SrcCtx) :
    compile (C:=C) maps 0 fragment stmt = none ↔ CheckedGuards.compile (C:=C) maps 0 fragment stmt = none := by
  rw [compile_eq_checked]

theorem assert_lowering_refused :
    lower (C:=C) maps (.expr (.builtin .assert (.cons (.local .here) .nil) rfl) :
      Source.RStmt E [] false .body SrcCtx SrcCtx) = none := rfl

theorem literal_lowering_refused :
    lower (C:=C) maps (.expr (.builtin .require (.cons (.bool false) .nil) rfl) :
      Source.RStmt E [] false .body SrcCtx SrcCtx) = none := rfl

theorem message_lowering_refused :
    lower (C:=C) maps (.expr (.builtin .require (.cons (.local .here) (.cons (.str [1]) .nil)) rfl) :
      Source.RStmt E [] false .body SrcCtx SrcCtx) = none := rfl

#print axioms local_lowered
#print axioms logical_lowered
#print axioms relational_lowered
#print axioms local_public
#print axioms logical_public
#print axioms relational_public
#print axioms local_compiled
#print axioms logical_compiled
#print axioms relational_compiled
#print axioms local_client
#print axioms logical_client
#print axioms relational_client
#print axioms refusals_preserved
#print axioms assert_lowering_refused
#print axioms literal_lowering_refused
#print axioms message_lowering_refused
end Solidity.Backend.FailurePaths.GuardLowering.Controls
