import Solidity.Backend.Selection.Interface

/-! Typed external obligations; no theorem or axiom is asserted here.
G24.03 is compiler-pass preservation, G45.05-BR the Bridge decoder
agreement and G49.02 the runtime consumer. Actual source observations and budgets remain parameters. -/
namespace Solidity.Backend.Selection

/-- G24.03 producer: each concrete source observation relates to the existing
IR execution, including its original machine and resource budget. -/
structure CompilerPremise (SourceObservation : Type)
    (source : Nat → SourceObservation) (ir : List Evm.Instr)
    (relation : SourceObservation → Evm.Machine → Evm.Machine → Prop) : Prop where
  preserves : ∀ (budget : Nat) (initial final : Evm.Machine),
    relation (source budget) initial final → Evm.run ir initial = .ok final 0

/-- G45.05-BR: the actual Bridge adapter supplies one-step agreement and its
iteration equations. Reachability includes the entry and all supported steps;
choosing an empty reachable set cannot discharge this premise. -/
structure DecoderPremise (bytes : List UInt8) (input : Nat)
    (bridgeStep : LabelExec.State → Option LabelExec.State)
    (bridgeRun : Nat → LabelExec.State → Option LabelExec.State)
    (reachable : LabelExec.State → Prop) : Prop where
  entry : ∀ s : Scalar.Stack, s.length = input → reachable ⟨0,s⟩
  closed : ∀ s t : LabelExec.State, reachable s →
    LabelExec.step bytes s = some t → reachable t
  agrees : ∀ s : LabelExec.State, reachable s → bridgeStep s = LabelExec.step bytes s
  zero : ∀ s : LabelExec.State, bridgeRun 0 s = some s
  succ : ∀ (n : Nat) (s : LabelExec.State),
    bridgeRun (n+1) s = (bridgeStep s).bind (bridgeRun n)

/-- G49.02 consumer STATEMENT, not a proof. The result is concrete execution
of the exact composed bytes through the Bridge adapter.
The source/IR relation and budget remain explicit; gas and divergence are
not reclassified by this finite successful-execution interface. -/
structure RuntimeConsumer (SourceObservation : Type)
    (source : Nat → SourceObservation) (ir : List Evm.Instr)
    (relation : SourceObservation → Evm.Machine → Evm.Machine → Prop)
    (b : Block) (input output : Nat)
    (composition : CompositionCertificate ir b input output)
    (bridgeStep : LabelExec.State → Option LabelExec.State)
    (bridgeRun : Nat → LabelExec.State → Option LabelExec.State)
    (reachable : LabelExec.State → Prop) : Prop where
  consume : CompilerPremise SourceObservation source ir relation →
    DecoderPremise (encode composition.assembled.code) input bridgeStep bridgeRun reachable →
    ∀ (budget : Nat) (m : Evm.Machine) (s t : Scalar.Stack),
      s.length = input → m.stack = irStack s →
      relation (source budget) m { m with stack := irStack t } →
      ∃ steps : Nat,
        bridgeRun steps ⟨0,s⟩ = some ⟨size composition.assembled.code,t⟩ ∧
        ∀ k : Nat, k ≤ steps → ∃ reached : LabelExec.State,
          bridgeRun k ⟨0,s⟩ = some reached ∧ reached.stack.length ≤ 1024

end Solidity.Backend.Selection
