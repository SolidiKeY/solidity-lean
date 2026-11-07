import Solidity.Yul.Compilation.P20InterfaceV1

/-! Regression: represented P20 success must retain the actual G24 Input/Rep
and a jointly inhabited successful source input. The concrete closed producer
witnesses only the reused Yul part. The conditional construction below uses
the unchanged PendingG24 fields; it supplies no concrete PendingG24 instance.
The local-store regression also checks the exact boundary between memory-backed
G24 locals and a stack-only Yul block, without changing either representation. -/
namespace Solidity.Yul.Compilation.P20.InterfaceV1.Controls
open Backend Scalar ProducerExpressions

def dirty : Scalar.Word := BitVec.ofNat 256 (2^200+257)
def statement : Solidity.Yul.Stmt [] [] ⟨false,false⟩ 2 :=
  .assign (fun _ : Fin 1 => .local 1) (.literal dirty.toFin)
def producer : ClosedProducer 2 statement :=
  ProducerStatements.assignTargets (fun _ : Fin 1 => .local 1) (ProducerExpressions.literal 0 dirty.toFin)

#guard producer.update #v[9,0] == #v[9,dirty]
#check producer.source
#check producer.lowered.correct
#check PendingG24
#check PendingRepresentedSuccess
/-- info: 'Solidity.Yul.Compilation.P20.InterfaceV1.Controls.producer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms producer
end Solidity.Yul.Compilation.P20.InterfaceV1.Controls

namespace Solidity.Yul.Compilation.P20.InterfaceV1
open Backend Scalar Selection Closed ProducerExpressions
variable {C : Contract} {Γ Δ : Ctx} {b : Nat} {F : Evm.Frag Γ}
 {program : Solidity.Prog C Γ Δ} (result : Evm.Compiler.Compilation b F program)
 {c : Solidity.Yul.Control} {n : Nat} (stmt : Solidity.Yul.Stmt [] [] c n)
 (profile : StmtWordP stmt) (block : Backend.Block)
 (domain : State C Γ → Prop)
 (encodeInput : State C Γ → Vector Scalar.Word n)
 (encodeOutput : (σ : State C Γ) → Solidity.Out C σ.H Δ → Vector Scalar.Word n)
 (link : PendingG24 result stmt profile block domain encodeInput encodeOutput)

/-- Compose the actual G24 success theorem with the unchanged source/Yul link.
The seed jointly witnesses domain, Input, payment freedom and source success;
its Yul run and the target run/Rep are derived. This does not produce the link. -/
def represented_of_successful_input (seed : ∃ (L frame : Nat) (base : Nat → Fin Evm.W)
 (σ : State C Γ) (m : Evm.Machine) (out : Solidity.Out C σ.H Δ),
 domain σ ∧ result.Input L frame base σ m ∧ Evm.Prog.pays program = false ∧
 program.run σ = .ok out) :
    PendingRepresentedSuccess result stmt profile block domain encodeInput encodeOutput link where
  required_input := by
    obtain ⟨L, frame, base, σ, m, out, admitted, input, noPay, sourceRun⟩ := seed
    obtain ⟨fuel, yulRun⟩ := link.source_forward σ admitted out sourceRun
    exact ⟨L, frame, base, σ, m, out, fuel, admitted, input, noPay, sourceRun, yulRun⟩
  success := by
    intro L frame base σ m admitted input noPay fuel final yulRun
    obtain ⟨out, sourceRun, same⟩ := link.source_backward σ admitted fuel final yulRun
    obtain ⟨target, targetRun, stack, represented⟩ :=
      Backend.Passes.compilation_success result input noPay sourceRun
    exact ⟨out, target, sourceRun, same, targetRun, stack, represented⟩

/-- info: 'Solidity.Yul.Compilation.P20.InterfaceV1.represented_of_successful_input' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Yul.Compilation.P20.InterfaceV1.represented_of_successful_input
end Solidity.Yul.Compilation.P20.InterfaceV1

/-! A concrete local-write regression for the frozen stack-only lowering field.
Both selected programs really execute; their distinct local representations
prevent this particular pair from supplying PendingG24.lowering. -/
namespace Solidity.Yul.Compilation.P20.InterfaceV1.Controls.StoreBoundary
open Backend Scalar Selection
abbrev Γ : Ctx := [.val .uint]
def program (C : Contract) : Solidity.Prog C Γ Γ :=
  .cons (.assignLocal .here (.simple (.lit 5 rfl))) .nil
def compilation (C : Contract) : Evm.Compiler.Compilation 0 (Evm.Frag.init Γ) (program C) :=
  .core (Evm.Frag.init Γ) (by first | rfl | decide | omega | simp only [])
def value : Scalar.Word := 5
def statement : Solidity.Yul.Stmt [] [] ⟨false,false⟩ 1 :=
  .assign (fun _ : Fin 1 => .local 0) (.literal value.toFin)
def producer : ProducerStatements.Compiled 2 statement :=
  ProducerStatements.assignTargets (fun _ : Fin 1 => .local 0)
    (ProducerExpressions.literal 0 value.toFin)
def code := (producer.lowered.code 0).get (by first | rfl | decide | omega | simp only [])
def block : Backend.Block := .code code
def initial : Evm.Machine := {Evm.Machine.init with stack := irStack [0]}
theorem actual_store (C : Contract) : Evm.run (compilation C).code initial =
    .ok (Evm.Memory.writeMachine initial 0 (.val (Evm.wmod value.toNat))) 0 := by
  first | rfl | decide | omega | simp only []

theorem scalar_success : StructuredExec block [0] [value] := by
  apply StructuredExec.code
  first | rfl | decide | omega | simp only []

theorem no_certificate (C : Contract) :
    ¬ LoweringCertificate (compilation C).code block := by
  intro certificate
  have expected := (certificate.success [0] [value] initial rfl).mpr scalar_success
  have stack := congrArg (fun result : Evm.Out => match result with
    | .ok m _ => m.stack
    | _ => []) expected
  change irStack [0] = irStack [value] at stack
  exact (by decide : irStack [0] ≠ irStack [value]) stack

/-- This is the actual checked compiler result, not caller-supplied code. -/
theorem public_selection (C : Contract) :
    Evm.Compiler.compile 0 (Evm.Frag.init Γ) (program C) = some (compilation C) := by
  first | rfl | decide | omega | simp only []

/-- The existing intrinsic Yul producer executes the same literal write for
all original locals; this is separate from G24 representation alignment. -/
theorem source_success (locals : Vector Scalar.Word 1) :
    Closed.evalStmt 2 .nil True.intro statement producer.profile
      (ProducerExpressions.sourceLocals locals) =
        some ⟨ProducerExpressions.sourceLocals (producer.update locals),.normal⟩ :=
  producer.source locals

/-- info: 'Solidity.Yul.Compilation.P20.InterfaceV1.Controls.StoreBoundary.compilation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Yul.Compilation.P20.InterfaceV1.Controls.StoreBoundary.compilation
/-- info: 'Solidity.Yul.Compilation.P20.InterfaceV1.Controls.StoreBoundary.producer' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Yul.Compilation.P20.InterfaceV1.Controls.StoreBoundary.producer
/-- info: 'Solidity.Yul.Compilation.P20.InterfaceV1.Controls.StoreBoundary.actual_store' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Yul.Compilation.P20.InterfaceV1.Controls.StoreBoundary.actual_store
/-- info: 'Solidity.Yul.Compilation.P20.InterfaceV1.Controls.StoreBoundary.scalar_success' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Yul.Compilation.P20.InterfaceV1.Controls.StoreBoundary.scalar_success
/-- info: 'Solidity.Yul.Compilation.P20.InterfaceV1.Controls.StoreBoundary.no_certificate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Yul.Compilation.P20.InterfaceV1.Controls.StoreBoundary.no_certificate
/-- info: 'Solidity.Yul.Compilation.P20.InterfaceV1.Controls.StoreBoundary.public_selection' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Yul.Compilation.P20.InterfaceV1.Controls.StoreBoundary.public_selection
/-- info: 'Solidity.Yul.Compilation.P20.InterfaceV1.Controls.StoreBoundary.source_success' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Yul.Compilation.P20.InterfaceV1.Controls.StoreBoundary.source_success
end Solidity.Yul.Compilation.P20.InterfaceV1.Controls.StoreBoundary

/-! Memory-sensitivity regression: identical numeric stacks cannot encode an
observable memory difference under the frozen stack-only lowering contract.
The checked store below therefore has no such certificate for any block. -/
namespace Solidity.Yul.Compilation.P20.InterfaceV1
open Backend Scalar Selection
theorem no_lowering_of_memory_sensitivity (code : List Evm.Instr) (block : Backend.Block) (input output : Scalar.Stack)
 (good bad final : Evm.Machine) (address : Nat)
 (goodStack : good.stack = irStack input) (badStack : bad.stack = irStack input)
 (goodRun : Evm.run code good = .ok {good with stack := irStack output} 0)
 (badRun : Evm.run code bad = .ok final 0)
 (changed : final.mem address ≠ bad.mem address)
 : ¬ LoweringCertificate code block := by
  intro certificate
  have trace := (certificate.success input output good goodStack).mp goodRun
  have unchanged := (certificate.success input output bad badStack).mpr trace
  have same := (Evm.Out.ok.inj (badRun.symm.trans unchanged)).1
  have observed := congrArg (fun machine : Evm.Machine => machine.mem address) same
  exact changed observed
end Solidity.Yul.Compilation.P20.InterfaceV1

namespace Solidity.Yul.Compilation.P20.InterfaceV1.Controls.StoreBoundary
open Backend Scalar Selection

def aligned : Evm.Machine :=
  {initial with mem := fun _ => .val (Evm.wmod value.toNat)}

theorem aligned_run (C : Contract) :
    Evm.run (compilation C).code aligned = .ok aligned 0 := by
  change Evm.Out.ok {aligned with mem := Evm.upd aligned.mem 0 (.val (Evm.wmod value.toNat))} 0 = _
  have memory : Evm.upd aligned.mem 0 (.val (Evm.wmod value.toNat)) = aligned.mem := by
    funext address
    first | simp only [Evm.upd,aligned,ite_self] | rfl | decide | omega
  rw [memory]

theorem memory_changed :
    (Evm.Memory.writeMachine initial 0 (.val (Evm.wmod value.toNat))).mem 0 ≠ initial.mem 0 := by
  first | decide | rfl | omega | simp only []

theorem no_block_certificate (C : Contract) (other : Backend.Block) :
    ¬ LoweringCertificate (compilation C).code other :=
  no_lowering_of_memory_sensitivity (compilation C).code other [0] [0]
    aligned initial (Evm.Memory.writeMachine initial 0 (.val (Evm.wmod value.toNat)))
    0 rfl rfl (aligned_run C) (actual_store C) memory_changed

/-- info: 'Solidity.Yul.Compilation.P20.InterfaceV1.no_lowering_of_memory_sensitivity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Yul.Compilation.P20.InterfaceV1.no_lowering_of_memory_sensitivity
/-- info: 'Solidity.Yul.Compilation.P20.InterfaceV1.Controls.StoreBoundary.aligned' does not depend on any axioms -/
#guard_msgs in
#print axioms Solidity.Yul.Compilation.P20.InterfaceV1.Controls.StoreBoundary.aligned
/-- info: 'Solidity.Yul.Compilation.P20.InterfaceV1.Controls.StoreBoundary.aligned_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Yul.Compilation.P20.InterfaceV1.Controls.StoreBoundary.aligned_run
/-- info: 'Solidity.Yul.Compilation.P20.InterfaceV1.Controls.StoreBoundary.memory_changed' does not depend on any axioms -/
#guard_msgs in
#print axioms Solidity.Yul.Compilation.P20.InterfaceV1.Controls.StoreBoundary.memory_changed
/-- info: 'Solidity.Yul.Compilation.P20.InterfaceV1.Controls.StoreBoundary.no_block_certificate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Yul.Compilation.P20.InterfaceV1.Controls.StoreBoundary.no_block_certificate
end Solidity.Yul.Compilation.P20.InterfaceV1.Controls.StoreBoundary
