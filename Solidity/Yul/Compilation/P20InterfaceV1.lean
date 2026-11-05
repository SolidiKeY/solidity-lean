import Solidity.Yul.Compilation.ProducerStatements
import Solidity.Backend.Passes.Boundary
import Solidity.Backend.Selection.InterfaceV2

/-! H26 frozen P20 success endpoints, version 1. Existing concrete compiler
certificates and G24 Input/Rep stay unchanged. PendingG24 has no producer
instance: its fields are obligations, not established adequacy. This narrow
success contract does not cover admission/origin, failures, divergence,
physical views, dirty readback or native/resource/observation closure. -/
namespace Solidity.Yul.Compilation.P20.InterfaceV1
open Backend Scalar Selection Closed ProducerExpressions

/-- Reuse the real original-AST-indexed compiler certificate unchanged. -/
abbrev ClosedProducer := @ProducerStatements.Compiled

/-- Pending link between an original Yul statement and the ACTUAL checked
G24 compilation. The owner-supplied domain must have a genuine successful
source/Yul witness; that one witness is not full admission coverage.
`encodeInput`/`encodeOutput` and both source laws are explicit obligations,
not a replacement Source representation or an assumed embedding theorem. -/
structure PendingG24 {C : Contract} {Γ Δ : Ctx} {b : Nat}
    {F : Evm.Frag Γ} {program : Solidity.Prog C Γ Δ}
    (result : Evm.Compiler.Compilation b F program)
    {c : Solidity.Yul.Control} {n : Nat} (stmt : Solidity.Yul.Stmt [] [] c n)
    (profile : StmtWordP stmt) (block : Backend.Block)
    (domain : State C Γ → Prop)
    (encodeInput : State C Γ → Vector Scalar.Word n)
    (encodeOutput : (σ : State C Γ) → Solidity.Out C σ.H Δ → Vector Scalar.Word n) where
  lowering : LoweringCertificate result.code block
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

/-- Pending success endpoint over the original branch-specific G24 relation.
Payment freedom and actual Input are retained and jointly witnessed in
required_input, alongside real source/Yul success. Nothing instantiates this
structure; it must be supplied by a reviewed concrete producer. -/
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

/-- info: 'Solidity.Yul.Compilation.P20.InterfaceV1.PendingG24' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PendingG24
/-- info: 'Solidity.Yul.Compilation.P20.InterfaceV1.PendingRepresentedSuccess' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PendingRepresentedSuccess
end Solidity.Yul.Compilation.P20.InterfaceV1
