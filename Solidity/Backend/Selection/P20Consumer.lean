import Solidity.Backend.Selection.P20ConsumerInterface
import Solidity.Backend.Selection.Composition

/-! Conditional H26 assembly consumer of the exact published P20 pending link.
The concrete producer, Source laws and representation endpoint are not supplied. -/
namespace Solidity.Backend.Selection
open Solidity.Yul.Closed

variable {C : Contract} {Γ Δ : Ctx} {b : Nat}
  {F : Evm.Frag Γ} {program : Solidity.Prog C Γ Δ}
  (result : Evm.Compiler.Compilation b F program)
  {c : Solidity.Yul.Control} {n : Nat} (stmt : Solidity.Yul.Stmt [] [] c n)
  (profile : StmtWordP stmt) (block : Block) (domain : State C Γ → Prop)
  (encodeInput : State C Γ → Vector Scalar.Word n)
  (encodeOutput : (σ : State C Γ) → Solidity.Out C σ.H Δ → Vector Scalar.Word n)

/-- Supply the existing composition from the explicit pending lowering field.
The actual checked code and assembler result are fixed by the interface. -/
def p20AssemblyConsumer :
    P20AssemblyConsumer result stmt profile block domain encodeInput encodeOutput :=
  fun link {_input _output} shape room out assembly =>
    ⟨compose link.lowering shape room out assembly, rfl⟩

/-- The ordinary finite successful-IR endpoint, now linked to the exact P20
compilation. This is not Source adequacy or a represented-success producer. -/
theorem p20_execute
    (link : Solidity.Yul.Compilation.P20.InterfaceV1.PendingG24
      result stmt profile block domain encodeInput encodeOutput)
    {input output : Nat} (shape : LabelExec.BlockShape block input output)
    (room : ExpansionRoom block input output) (out : Assembled Empty)
    (assembly : assemble 0 LabelExec.emptyLink (block.expand 0).1 = some out)
    (before after : Scalar.Stack) (caller : Evm.Machine)
    (height : before.length = input) (stack : caller.stack = irStack before)
    (actual : Evm.run result.code caller = .ok { caller with stack := irStack after } 0) :
    ∃ count, ExecutionTrace.Safe (encode out.code) count
      ⟨0,before⟩ ⟨size out.code,after⟩ := by
  let certificate : CompositionCertificate result.code block input output :=
    (p20AssemblyConsumer result stmt profile block domain encodeInput encodeOutput
      link shape room out assembly).val
  have same : certificate.assembled = out :=
    (p20AssemblyConsumer result stmt profile block domain encodeInput encodeOutput
      link shape room out assembly).property
  have trace : ∃ count, ExecutionTrace.Safe (encode certificate.assembled.code) count
      ⟨0,before⟩ ⟨size certificate.assembled.code,after⟩ :=
    certificate.execute before after caller height stack actual
  simpa only [same] using trace

/-- The published required-success witness makes the owner domain nonempty.
It does not assert complete admission or construct the missing producer. -/
theorem p20_domain_nonempty
    (link : Solidity.Yul.Compilation.P20.InterfaceV1.PendingG24
      result stmt profile block domain encodeInput encodeOutput) :
    ∃ σ : State C Γ, domain σ := by
  obtain ⟨σ,_out,_fuel,admitted,_sourceRun,_yulRun⟩ := link.required_success
  exact ⟨σ,admitted⟩

/-- A false owner domain cannot hide the pending producer obligations. -/
theorem p20_false_domain
    (link : Solidity.Yul.Compilation.P20.InterfaceV1.PendingG24
      result stmt profile block (fun _ => False) encodeInput encodeOutput) : False := by
  obtain ⟨σ,impossible⟩ := p20_domain_nonempty result stmt profile block
    (fun _ => False) encodeInput encodeOutput link
  exact impossible

#print axioms p20AssemblyConsumer
#print axioms p20_execute
#print axioms p20_domain_nonempty
#print axioms p20_false_domain

end Solidity.Backend.Selection

namespace Solidity.Backend.Selection
open Solidity.Yul.Closed
open Solidity.Yul.Compilation.ProducerExpressions
variable {C : Contract} {Γ Δ : Ctx} {b : Nat}
  {F : Evm.Frag Γ} {program : Solidity.Prog C Γ Δ}
  (result : Evm.Compiler.Compilation b F program)
  {c : Solidity.Yul.Control} {n : Nat} (stmt : Solidity.Yul.Stmt [] [] c n)
  (profile : StmtWordP stmt) (block : Block) (domain : State C Γ → Prop)
  (encodeInput : State C Γ → Vector Scalar.Word n)
  (encodeOutput : (σ : State C Γ) → Solidity.Out C σ.H Δ → Vector Scalar.Word n)

/-- Consume the reviewed V2 represented endpoint directly. V1 assembly
consumption above and its unrestricted lowering requirement remain unchanged. -/
def p20RepresentedConsumerV2 :
    P20RepresentedConsumerV2 result stmt profile block domain encodeInput encodeOutput :=
  fun link => Solidity.Yul.Compilation.P20.InterfaceV2.PendingG24.represented
    result stmt profile block domain encodeInput encodeOutput link

/-- The consumed joint input produces an actual represented target success.
The original source/Yul run, payment freedom and full G24 Rep are retained;
no target execution or coverage theorem is added as a premise. -/
theorem p20_joint_success_v2
    (link : Solidity.Yul.Compilation.P20.InterfaceV2.PendingG24
      result stmt profile block domain encodeInput encodeOutput) :
    ∃ (L frame : Nat) (base : Nat → Fin Evm.W)
      (σ : State C Γ) (m : Evm.Machine) (out : Solidity.Out C σ.H Δ)
      (fuel : Nat) (target : Evm.Machine),
      domain σ ∧ result.Input L frame base σ m ∧ Evm.Prog.pays program = false ∧
      program.run σ = .ok out ∧
      evalStmt fuel .nil True.intro stmt profile (sourceLocals (encodeInput σ)) =
        some ⟨sourceLocals (encodeOutput σ out),.normal⟩ ∧
      Evm.run result.code m = .ok target 0 ∧ target.stack = m.stack ∧
      result.Rep (L + Evm.Prog.pushes program) frame base σ m out.st target := by
  let consumed := p20RepresentedConsumerV2 result stmt profile block domain
    encodeInput encodeOutput link
  obtain ⟨L,frame,base,σ,m,out,fuel,admitted,input,noPay,sourceRun,yulRun⟩ :=
    consumed.required_input
  obtain ⟨out',target,sourceRun',_encoding,targetRun,stack,represented⟩ :=
    consumed.success L frame base σ m admitted input noPay fuel (encodeOutput σ out) yulRun
  have same : out' = out := Except.ok.inj (sourceRun'.symm.trans sourceRun)
  subst out'
  exact ⟨L,frame,base,σ,m,out,fuel,target,admitted,input,noPay,sourceRun,
    yulRun,targetRun,stack,represented⟩

/-- V2's actual joint input prevents vacuous acceptance through a false domain. -/
theorem p20_false_domain_v2
    (link : Solidity.Yul.Compilation.P20.InterfaceV2.PendingG24
      result stmt profile block (fun _ => False) encodeInput encodeOutput) : False := by
  obtain ⟨L,frame,base,σ,m,out,fuel,target,impossible,_rest⟩ :=
    p20_joint_success_v2 result stmt profile block (fun _ => False)
      encodeInput encodeOutput link
  exact impossible

/-- info: 'Solidity.Backend.Selection.p20RepresentedConsumerV2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms p20RepresentedConsumerV2
/-- info: 'Solidity.Backend.Selection.p20_joint_success_v2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms p20_joint_success_v2
/-- info: 'Solidity.Backend.Selection.p20_false_domain_v2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms p20_false_domain_v2
end Solidity.Backend.Selection
