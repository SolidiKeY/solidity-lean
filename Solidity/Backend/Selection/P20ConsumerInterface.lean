import Solidity.Yul.Compilation.P20InterfaceV2
import Solidity.Yul.Compilation.P20InterfaceV1

/-! Statement-only consumer of the published P20 pending G24 interface.
The exact original compilation and pending producer record remain parameters.
This extends the existing composition contract, not the compiler or evaluator. -/
namespace Solidity.Backend.Selection
open Solidity.Yul.Closed

/-- A consumer may assemble the explicitly supplied lowering field for the
actual checked compilation. The subtype pins the same assembler output.
No PendingG24 inhabitant, Source adequacy or representation endpoint is supplied. -/
abbrev P20AssemblyConsumer {C : Contract} {Γ Δ : Ctx} {b : Nat}
    {F : Evm.Frag Γ} {program : Solidity.Prog C Γ Δ}
    (result : Evm.Compiler.Compilation b F program)
    {c : Solidity.Yul.Control} {n : Nat} (stmt : Solidity.Yul.Stmt [] [] c n)
    (profile : StmtWordP stmt) (block : Block) (domain : State C Γ → Prop)
    (encodeInput : State C Γ → Vector Scalar.Word n)
    (encodeOutput : (σ : State C Γ) → Solidity.Out C σ.H Δ → Vector Scalar.Word n) :=
  ∀ (_link : Solidity.Yul.Compilation.P20.InterfaceV1.PendingG24
      result stmt profile block domain encodeInput encodeOutput)
    {input output : Nat} (_shape : LabelExec.BlockShape block input output)
    (_room : ExpansionRoom block input output) (out : Assembled Empty)
    (_assembly : assemble 0 LabelExec.emptyLink (block.expand 0).1 = some out),
    { certificate : CompositionCertificate result.code block input output //
      certificate.assembled = out }

#print axioms P20AssemblyConsumer

end Solidity.Backend.Selection

namespace Solidity.Backend.Selection
open Solidity.Yul.Closed

/-- H198 versioned represented-success consumer. This preserves the actual
G24 Input/Rep endpoint and its joint witness. It does not supply V1's
unrestricted stack-only lowering or an assembly composition certificate. -/
abbrev P20RepresentedConsumerV2 {C : Contract} {Γ Δ : Ctx} {b : Nat}
    {F : Evm.Frag Γ} {program : Solidity.Prog C Γ Δ}
    (result : Evm.Compiler.Compilation b F program)
    {c : Solidity.Yul.Control} {n : Nat} (stmt : Solidity.Yul.Stmt [] [] c n)
    (profile : StmtWordP stmt) (block : Block) (domain : State C Γ → Prop)
    (encodeInput : State C Γ → Vector Scalar.Word n)
    (encodeOutput : (σ : State C Γ) → Solidity.Out C σ.H Δ → Vector Scalar.Word n) :=
  ∀ link : Solidity.Yul.Compilation.P20.InterfaceV2.PendingG24
      result stmt profile block domain encodeInput encodeOutput,
    Solidity.Yul.Compilation.P20.InterfaceV2.PendingRepresentedSuccess
      result stmt profile block domain encodeInput encodeOutput link

/-- info: 'Solidity.Backend.Selection.P20RepresentedConsumerV2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms P20RepresentedConsumerV2
end Solidity.Backend.Selection
