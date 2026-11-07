import Solidity.Lowering.P8.SourceAstUnit
import Solidity.Source.WellFormed
import Solidity.Lowering.V07.LocationGraphProducer

/-! Whole converted-unit metadata to the existing computed location graphs.
Regression purpose: preserve every declaration/body in the exact resolution;
never replace its environment by a struct-only projection or confuse graph
component failure with Source rejection. Generic soundness is kernel checked;
fixture evaluation does not prove actual Source typing, origin or lifecycle. -/
namespace Solidity.Lowering.P8.SourceAstResolvedGraphs
open Lean Solidity.Source

/-- Existing resolution plus optional existing graph/certificate, with no new AST. -/
abbrev Result (loc : DataLoc) :=
  (r : Resolution) × Option
    ((G : TypeGraph.Schema (V07.LocationGraphProducer.choices r.env loc).length) ×
      V07.LocationGraphInterface.LocationDeclarationGraph r.env loc G)

def produceUnit (origin : Name) (settings : Settings) (unit : Syn .unit)
    (loc : DataLoc) : Result loc :=
  let resolved := Source.resolveUnit settings unit
  ⟨resolved, V07.LocationGraphProducer.produce origin resolved.env loc⟩

/-- Conversion errors and graph-component None remain distinct outcomes. -/
def produce (origin : Name) (fuel : Nat) (settings : Settings) (node : Json)
    (loc : DataLoc) : Except String (Result loc) := do
  return produceUnit origin settings (← SourceAstUnit.unit fuel node) loc

/-- All syntax, declarations and settings survive before graph selection. -/
theorem resolution_exact (origin : Name) (settings : Settings) (unit : Syn .unit)
    (loc : DataLoc) :
    (produceUnit origin settings unit loc).1.unit = unit ∧
    (produceUnit origin settings unit loc).1.env = unit.env ∧
    (produceUnit origin settings unit loc).1.pipeline = settings.pipeline ∧
    (produceUnit origin settings unit loc).1.coder = settings.coder unit :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Existing Source resolution additionally requires its original empty-link premise. -/
theorem resolves (origin : Name) (settings : Settings) (unit : Syn .unit)
    (loc : DataLoc) (links : settings.links = []) :
    Source.Resolves' settings unit (produceUnit origin settings unit loc).1 := ⟨links, rfl⟩

theorem conversion_success (origin : Name) (fuel : Nat) (settings : Settings)
    (node : Json) (loc : DataLoc) (unit : Syn .unit)
    (converted : SourceAstUnit.unit fuel node = .ok unit) :
    produce origin fuel settings node loc = .ok (produceUnit origin settings unit loc) := by
  rw [produce, converted]
  rfl

theorem conversion_failure (origin : Name) (fuel : Nat) (settings : Settings)
    (node : Json) (loc : DataLoc) (message : String)
    (failed : SourceAstUnit.unit fuel node = .error message) :
    produce origin fuel settings node loc = .error message := by
  rw [produce, failed]
  rfl

/-- Every output resolution comes from that complete converted unit. -/
theorem output_resolution (origin : Name) (fuel : Nat) (settings : Settings)
    (node : Json) (loc : DataLoc) (result : Result loc)
    (returned : produce origin fuel settings node loc = .ok result) :
    ∃ unit, SourceAstUnit.unit fuel node = .ok unit ∧ result.1 = Source.resolveUnit settings unit := by
  cases converted : SourceAstUnit.unit fuel node with
  | error message =>
    rw [conversion_failure origin fuel settings node loc message converted] at returned
    cases returned
  | ok unit =>
    rw [conversion_success origin fuel settings node loc unit converted] at returned
    cases returned
    exact ⟨unit, rfl, rfl⟩

/-- A computed successful component carries a certificate for this exact environment. -/
theorem certificate_exists (loc : DataLoc) (result : Result loc)
    (success : result.2.isSome = true) :
    ∃ n, ∃ G : TypeGraph.Schema n,
      Nonempty (V07.LocationGraphInterface.LocationDeclarationGraph result.1.env loc G) := by
  cases present : result.2 with
  | none => rw [present] at success; cases success
  | some packed => exact ⟨_, packed.1, ⟨packed.2⟩⟩

/-- Joint output provenance/resolution/certificate, under the original link condition. -/
theorem certified_output (origin : Name) (fuel : Nat) (settings : Settings)
    (node : Json) (loc : DataLoc) (result : Result loc)
    (returned : produce origin fuel settings node loc = .ok result)
    (success : result.2.isSome = true) (links : settings.links = []) :
    ∃ unit, SourceAstUnit.unit fuel node = .ok unit ∧
      result.1 = Source.resolveUnit settings unit ∧ Source.Resolves' settings unit result.1 ∧
      ∃ n, ∃ G : TypeGraph.Schema n,
        Nonempty (V07.LocationGraphInterface.LocationDeclarationGraph unit.env loc G) := by
  obtain ⟨unit, converted, same⟩ := output_resolution origin fuel settings node loc result returned
  have graph := certificate_exists loc result success
  rw [same] at graph
  exact ⟨unit, converted, same, ⟨links, same⟩, graph⟩

/-- info: 'Solidity.Lowering.P8.SourceAstResolvedGraphs.certified_output' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms certified_output

/-- info: 'Solidity.Lowering.P8.SourceAstResolvedGraphs.resolution_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms resolution_exact
/-- info: 'Solidity.Lowering.P8.SourceAstResolvedGraphs.resolves' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms resolves
/-- info: 'Solidity.Lowering.P8.SourceAstResolvedGraphs.conversion_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms conversion_success
/-- info: 'Solidity.Lowering.P8.SourceAstResolvedGraphs.conversion_failure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms conversion_failure
/-- info: 'Solidity.Lowering.P8.SourceAstResolvedGraphs.output_resolution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms output_resolution
/-- info: 'Solidity.Lowering.P8.SourceAstResolvedGraphs.certificate_exists' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms certificate_exists
end Solidity.Lowering.P8.SourceAstResolvedGraphs
