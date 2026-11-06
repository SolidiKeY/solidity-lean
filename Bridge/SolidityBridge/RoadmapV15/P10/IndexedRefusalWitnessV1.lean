import SolidityBridge.RoadmapV15.P10.IndexedRefusalInterfaceV1
import SolidityBridge.RoadmapV15.P10.InstructionSelectionRefusal

/-! Packages the checked instruction-local DUP/SWAP shortage results into the
frozen V1 contract. This supplies no successful execution, source frame origin,
world/CALL composition or complete opcode-row adequacy. -/
namespace SolidityBridge.RoadmapV15.P10.IndexedRefusalWitnessV1
open IndexedRefusalInterfaceV1

theorem dup : DupClaim := by
  intro valid n site words m fuel represented short gas
  exact ⟨InstructionSelectionRefusal.dup_refusal valid n site words m represented short gas fuel,
    InstructionSelectionRefusal.dup_native_refusal valid n site words short gas fuel⟩

theorem swap : SwapClaim := by
  intro valid n site words m fuel represented short gas
  exact ⟨InstructionSelectionRefusal.swap_refusal valid n site words m represented short gas fuel,
    InstructionSelectionRefusal.swap_native_refusal valid n site words short gas fuel⟩

theorem producer : Producer := ⟨dup, swap⟩

/-- info: 'SolidityBridge.RoadmapV15.P10.IndexedRefusalWitnessV1.dup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms dup
/-- info: 'SolidityBridge.RoadmapV15.P10.IndexedRefusalWitnessV1.swap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms swap
/-- info: 'SolidityBridge.RoadmapV15.P10.IndexedRefusalWitnessV1.producer' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms producer
end SolidityBridge.RoadmapV15.P10.IndexedRefusalWitnessV1
