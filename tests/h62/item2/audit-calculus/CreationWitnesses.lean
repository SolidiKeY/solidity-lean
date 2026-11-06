import Solidity.Backend.Creation.Artifact
import tests.h62.item2.«audit-calculus».KernelCensus

/-! Closed simultaneous witnesses extracted from the unchanged theorem types.
These cover all nine source-authored theorem declarations in Artifact, including its implicit library type,
record bounds and the jointly positive and bounded byte-width input. -/
namespace H62.AuditCalculus.Creation
open Solidity.Backend Solidity.Backend.Creation

private def nonemptyRuntime : Artifact Unit :=
  ⟨[0x60, 0x2a, 0x00], [0xaa, 0xbb], by decide, 0, []⟩

#joint_premises Solidity.Backend.Creation.Immediate.read as immediateReadPremises
/-- The same immediate contains its value and its fitting proof. -/
theorem immediate_read_joint : immediateReadPremises := ⟨⟨3, by decide⟩, True.intro⟩

#joint_premises Solidity.Backend.Creation.runtimeOffset_fits as runtimeOffsetPremises
/-- A positive runtime length, with its intrinsic bound. -/
theorem runtime_offset_joint : runtimeOffsetPremises := ⟨⟨3, by decide⟩, True.intro⟩

#joint_premises Solidity.Backend.Creation.wrapper_size as wrapperSizePremises
/-- Concrete emitted-wrapper input. -/
theorem wrapper_size_joint : wrapperSizePremises := ⟨⟨3, by decide⟩, True.intro⟩

#joint_premises Solidity.Backend.Creation.wrapper_length as wrapperLengthPremises
/-- Concrete encoded-wrapper input. -/
theorem wrapper_length_joint : wrapperLengthPremises := ⟨⟨3, by decide⟩, True.intro⟩

#joint_premises Solidity.Backend.Creation.Artifact.runtime_slice as runtimeSlicePremises
/-- Library type, nonempty runtime, arguments and bound share one artifact. -/
theorem runtime_slice_joint : runtimeSlicePremises := ⟨Unit, nonemptyRuntime, True.intro⟩

#joint_premises Solidity.Backend.Creation.Artifact.args_slice as argsSlicePremises
/-- Constructor arguments are distinct from the chosen runtime. -/
theorem args_slice_joint : argsSlicePremises := ⟨Unit, nonemptyRuntime, True.intro⟩

#joint_premises Solidity.Backend.Creation.Artifact.initcode_length as initcodeLengthPremises
/-- Full intrinsic artifact, with nonempty runtime and arguments. -/
theorem initcode_length_joint : initcodeLengthPremises := ⟨Unit, nonemptyRuntime, True.intro⟩

#joint_premises Solidity.Backend.Creation.byteWidth_zero as byteWidthZeroPremises
/-- No telescope hypotheses: the empty joint witness is true. -/
theorem byte_width_zero_joint : byteWidthZeroPremises := True.intro

#joint_premises Solidity.Backend.Creation.byteWidth_small as byteWidthSmallPremises
/-- Both inequalities hold for the SAME input; separate inhabitants do not suffice. -/
theorem byte_width_small_joint : byteWidthSmallPremises :=
  ⟨1, by decide, by decide, True.intro⟩

#verify_joint Solidity.Backend.Creation.Immediate.read with immediate_read_joint
#verify_joint Solidity.Backend.Creation.runtimeOffset_fits with runtime_offset_joint
#verify_joint Solidity.Backend.Creation.wrapper_size with wrapper_size_joint
#verify_joint Solidity.Backend.Creation.wrapper_length with wrapper_length_joint
#verify_joint Solidity.Backend.Creation.Artifact.runtime_slice with runtime_slice_joint
#verify_joint Solidity.Backend.Creation.Artifact.args_slice with args_slice_joint
#verify_joint Solidity.Backend.Creation.Artifact.initcode_length with initcode_length_joint
#verify_joint Solidity.Backend.Creation.byteWidth_zero with byte_width_zero_joint
#verify_joint Solidity.Backend.Creation.byteWidth_small with byte_width_small_joint

#audit_module "Solidity.Backend.Creation.Artifact"
#print axioms immediate_read_joint
#print axioms runtime_slice_joint
#print axioms byte_width_small_joint
end H62.AuditCalculus.Creation
