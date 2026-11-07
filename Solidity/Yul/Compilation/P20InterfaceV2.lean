import Solidity.Yul.Compilation.P20InterfaceV1

/-! H57 P20 V2 draft. Regression: an actual checked memory-backed local store
cannot meet V1's unrestricted stack-only lowering certificate. V2 relates the
same original AST and scalar block to actual checked G24 Input/Rep, preserving
source forward/backward laws, payment freedom and joint inhabited success.
V1 remains frozen. Admission/origin, failures, divergence, physical views,
dirty readback and native/resource/observation closure remain open. -/
namespace Solidity.Yul.Compilation.P20.InterfaceV2
open Backend Scalar Selection Closed ProducerExpressions

/-- Success correspondence on the actual admitted represented machine, not on
unrelated machines with equal stacks. Every original G24 observation remains. -/
structure CheckedLowering {C : Contract} {Γ Δ : Ctx} {b : Nat}
    {F : Evm.Frag Γ} {program : Solidity.Prog C Γ Δ}
    (result : Evm.Compiler.Compilation b F program)
    {c : Solidity.Yul.Control} {n : Nat} (stmt : Solidity.Yul.Stmt [] [] c n)
    (profile : StmtWordP stmt) (block : Backend.Block)
    (domain : State C Γ → Prop)
    (encodeInput : State C Γ → Vector Scalar.Word n)
    (encodeOutput : (σ : State C Γ) → Solidity.Out C σ.H Δ → Vector Scalar.Word n) where
  success : ∀ (L frame : Nat) (base : Nat → Fin Evm.W)
      (σ : State C Γ) (m : Evm.Machine),
    domain σ → result.Input L frame base σ m → Evm.Prog.pays program = false →
    ∀ final : Vector Scalar.Word n,
    StructuredExec block (encodeInput σ).toList final.toList ↔
      ∃ (out : Solidity.Out C σ.H Δ) (target : Evm.Machine),
        program.run σ = .ok out ∧ encodeOutput σ out = final ∧
        Evm.run result.code m = .ok target 0 ∧ target.stack = m.stack ∧
        result.Rep (L + Evm.Prog.pushes program) frame base σ m out.st target

/-- Versioned source/Yul link. The original source laws and successful witness
are retained; required_input additionally witnesses them jointly with G24 input. -/
structure PendingG24 {C : Contract} {Γ Δ : Ctx} {b : Nat}
    {F : Evm.Frag Γ} {program : Solidity.Prog C Γ Δ}
    (result : Evm.Compiler.Compilation b F program)
    {c : Solidity.Yul.Control} {n : Nat} (stmt : Solidity.Yul.Stmt [] [] c n)
    (profile : StmtWordP stmt) (block : Backend.Block)
    (domain : State C Γ → Prop)
    (encodeInput : State C Γ → Vector Scalar.Word n)
    (encodeOutput : (σ : State C Γ) → Solidity.Out C σ.H Δ → Vector Scalar.Word n) where
  lowering : CheckedLowering result stmt profile block domain encodeInput encodeOutput
  required_success : ∃ (σ : State C Γ) (out : Solidity.Out C σ.H Δ) (fuel : Nat),
    domain σ ∧ program.run σ = .ok out ∧
    evalStmt fuel .nil True.intro stmt profile (sourceLocals (encodeInput σ)) =
      some ⟨sourceLocals (encodeOutput σ out),.normal⟩
  source_forward : ∀ (σ : State C Γ), domain σ →
    ∀ (out : Solidity.Out C σ.H Δ), program.run σ = .ok out →
    ∃ fuel, evalStmt fuel .nil True.intro stmt profile (sourceLocals (encodeInput σ)) =
      some ⟨sourceLocals (encodeOutput σ out),.normal⟩
  source_backward : ∀ (σ : State C Γ), domain σ →
    ∀ (fuel : Nat) (final : Vector Scalar.Word n),
    evalStmt fuel .nil True.intro stmt profile (sourceLocals (encodeInput σ)) =
      some ⟨sourceLocals final,.normal⟩ →
    ∃ out : Solidity.Out C σ.H Δ, program.run σ = .ok out ∧ encodeOutput σ out = final
  required_input : ∃ (L frame : Nat) (base : Nat → Fin Evm.W)
      (σ : State C Γ) (m : Evm.Machine) (out : Solidity.Out C σ.H Δ) (fuel : Nat),
    domain σ ∧ result.Input L frame base σ m ∧ Evm.Prog.pays program = false ∧
      program.run σ = .ok out ∧
      evalStmt fuel .nil True.intro stmt profile (sourceLocals (encodeInput σ)) =
        some ⟨sourceLocals (encodeOutput σ out),.normal⟩

structure PendingRepresentedSuccess {C : Contract} {Γ Δ : Ctx} {b : Nat}
    {F : Evm.Frag Γ} {program : Solidity.Prog C Γ Δ}
    (result : Evm.Compiler.Compilation b F program)
    {c : Solidity.Yul.Control} {n : Nat} (stmt : Solidity.Yul.Stmt [] [] c n)
    (profile : StmtWordP stmt) (block : Backend.Block)
    (domain : State C Γ → Prop)
    (encodeInput : State C Γ → Vector Scalar.Word n)
    (encodeOutput : (σ : State C Γ) → Solidity.Out C σ.H Δ → Vector Scalar.Word n)
    (link : PendingG24 result stmt profile block domain encodeInput encodeOutput) : Prop where
  required_input : ∃ (L frame : Nat) (base : Nat → Fin Evm.W)
      (σ : State C Γ) (m : Evm.Machine) (out : Solidity.Out C σ.H Δ) (fuel : Nat),
    domain σ ∧ result.Input L frame base σ m ∧ Evm.Prog.pays program = false ∧
      program.run σ = .ok out ∧
      evalStmt fuel .nil True.intro stmt profile (sourceLocals (encodeInput σ)) =
        some ⟨sourceLocals (encodeOutput σ out),.normal⟩
  success : ∀ (L frame : Nat) (base : Nat → Fin Evm.W) (σ : State C Γ) (m : Evm.Machine),
    domain σ → result.Input L frame base σ m → Evm.Prog.pays program = false →
    ∀ (fuel : Nat) (final : Vector Scalar.Word n),
    evalStmt fuel .nil True.intro stmt profile (sourceLocals (encodeInput σ)) =
      some ⟨sourceLocals final,.normal⟩ →
    ∃ (out : Solidity.Out C σ.H Δ) (target : Evm.Machine),
      program.run σ = .ok out ∧ encodeOutput σ out = final ∧
      Evm.run result.code m = .ok target 0 ∧ target.stack = m.stack ∧
      result.Rep (L + Evm.Prog.pushes program) frame base σ m out.st target

end Solidity.Yul.Compilation.P20.InterfaceV2

namespace Solidity.Yul.Compilation.P20.InterfaceV2
open Backend Scalar Selection Closed ProducerExpressions
variable {C : Contract} {Γ Δ : Ctx} {b : Nat} {F : Evm.Frag Γ}
 {program : Solidity.Prog C Γ Δ} (result : Evm.Compiler.Compilation b F program)
 {c : Solidity.Yul.Control} {n : Nat} (stmt : Solidity.Yul.Stmt [] [] c n)
 (profile : StmtWordP stmt) (block : Backend.Block) (domain : State C Γ → Prop)
 (encodeInput : State C Γ → Vector Scalar.Word n)
 (encodeOutput : (σ : State C Γ) → Solidity.Out C σ.H Δ → Vector Scalar.Word n)

/-- Actual G24 correctness supplies machine execution/Rep after a concrete
source-program/block correspondence. No desired target run is a premise. -/
def CheckedLowering.of_source (source_block : ∀ (σ : State C Γ), domain σ → ∀ final : Vector Scalar.Word n,
 StructuredExec block (encodeInput σ).toList final.toList ↔
 ∃ out : Solidity.Out C σ.H Δ, program.run σ = .ok out ∧ encodeOutput σ out = final) :
    CheckedLowering result stmt profile block domain encodeInput encodeOutput where
  success := by
    intro L frame base σ m admitted input noPay final
    constructor
    · intro trace
      obtain ⟨out, sourceRun, encoding⟩ := (source_block σ admitted final).mp trace
      obtain ⟨target, targetRun, stack, represented⟩ :=
        Backend.Passes.compilation_success result input noPay sourceRun
      exact ⟨out, target, sourceRun, encoding, targetRun, stack, represented⟩
    · intro execution
      obtain ⟨out, target, sourceRun, encoding, targetRun, stack, represented⟩ := execution
      exact (source_block σ admitted final).mpr ⟨out, sourceRun, encoding⟩

/-- V1 migration applies only when its original unrestricted stack-only field
is independently proved. It is never inferred from V2 represented lowering. -/
def PendingG24.toV1
    (link : PendingG24 result stmt profile block domain encodeInput encodeOutput)
    (legacy : LoweringCertificate result.code block) :
    InterfaceV1.PendingG24 result stmt profile block domain encodeInput encodeOutput where
  lowering := legacy
  required_success := link.required_success
  source_forward := link.source_forward
  source_backward := link.source_backward

/-- The joint witness and original branch-specific observations are retained. -/
def PendingG24.represented
    (link : PendingG24 result stmt profile block domain encodeInput encodeOutput) :
    PendingRepresentedSuccess result stmt profile block domain encodeInput encodeOutput link where
  required_input := link.required_input
  success := by
    intro L frame base σ m admitted input noPay fuel final yulRun
    obtain ⟨out, sourceRun, encoding⟩ := link.source_backward σ admitted fuel final yulRun
    obtain ⟨target, targetRun, stack, represented⟩ :=
      Backend.Passes.compilation_success result input noPay sourceRun
    exact ⟨out, target, sourceRun, encoding, targetRun, stack, represented⟩

/-- Preserve the frozen represented-success endpoint on the same V1 overlap. -/
def PendingG24.represented_toV1
    (link : PendingG24 result stmt profile block domain encodeInput encodeOutput)
    (legacy : LoweringCertificate result.code block) :
    InterfaceV1.PendingRepresentedSuccess result stmt profile block domain encodeInput encodeOutput
      (PendingG24.toV1 result stmt profile block domain encodeInput encodeOutput link legacy) where
  required_input := link.required_input
  success := (PendingG24.represented result stmt profile block domain encodeInput encodeOutput link).success

/-- info: 'Solidity.Yul.Compilation.P20.InterfaceV2.CheckedLowering.of_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Yul.Compilation.P20.InterfaceV2.CheckedLowering.of_source
/-- info: 'Solidity.Yul.Compilation.P20.InterfaceV2.PendingG24.toV1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Yul.Compilation.P20.InterfaceV2.PendingG24.toV1
/-- info: 'Solidity.Yul.Compilation.P20.InterfaceV2.PendingG24.represented' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Yul.Compilation.P20.InterfaceV2.PendingG24.represented
/-- info: 'Solidity.Yul.Compilation.P20.InterfaceV2.PendingG24.represented_toV1' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Yul.Compilation.P20.InterfaceV2.PendingG24.represented_toV1
end Solidity.Yul.Compilation.P20.InterfaceV2
