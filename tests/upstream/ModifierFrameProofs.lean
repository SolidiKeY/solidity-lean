import Solidity.Tools.Upstream
import Solidity.Calculus.Close
import Solidity.Calculus.ProvesDerive
import Solidity.Calculus.Surface
import Solidity.Calculus.Closers

/-! Kernel proof controls for the two affected primitive-return programs.
These theorems concern the typed interpreter, not a universal solc theorem. -/
namespace Solidity.Tests.ModifierFrameProofs
open Solidity Semantics

private def ProofLegacy : Contract := contract!{
  modifier repeatCount(uint count) { for (uint i = 0; i < count; ++i) { _; } }
  modifier maybeTwice(bool twice) { if (twice) { _; } _; }
  function loop() repeatCount(10) returns (uint r) { r += 1; }
  function multi(bool b) maybeTwice(b) returns (uint r) { r += 1; }
}
private def ProofIR : Contract := { ProofLegacy with evalOrder := .viaIR }

open scoped Solidity.Scoped

/-- Every typed state: viaIR placeholders each receive the incoming return slot. -/
theorem multi_ir : ⊨ᶠ dl[ProofIR]{ ⟨ uint r = multi(true); ⟩ r == 1 } := by
  sol_symex
  sol_close

/-- Legacy control: the second placeholder reads the first result. -/
theorem multi_legacy : ⊨ᶠ dl[ProofLegacy]{ ⟨ uint r = multi(true); ⟩ r == 2 } := by
  sol_symex
  sol_close

/-- The ten-iteration viaIR modifier returns one. -/
theorem loop_ir : ⊨ᶠ dl[ProofIR]{ ⟨ uint r = loop(); ⟩ r == 1 } := by
  sol_prove (steps := 256)

/-- The ten-iteration legacy control returns ten. -/
theorem loop_legacy : ⊨ᶠ dl[ProofLegacy]{ ⟨ uint r = loop(); ⟩ r == 10 } := by
  sol_prove (steps := 256)

/-- info: 'Solidity.Tests.ModifierFrameProofs.multi_ir' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms multi_ir
/-- info: 'Solidity.Tests.ModifierFrameProofs.multi_legacy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms multi_legacy
/-- info: 'Solidity.Tests.ModifierFrameProofs.loop_ir' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms loop_ir
/-- info: 'Solidity.Tests.ModifierFrameProofs.loop_legacy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms loop_legacy
end Solidity.Tests.ModifierFrameProofs
