import Solidity.Backend.Selection.InterfaceV2
import Solidity.Backend.Selection.Premises

/-!
# Nonempty compiler and runtime-consumer contracts, version 2

The observation relation remains an explicit G24.03 producer parameter, but
must have a witness. The runtime consumer additionally requires a witness at
its own declared numeric input height with the exact unchanged nonstack frame
and the actual successful IR execution equation.
Neither contract can be instantiated with the constantly-false relation.
Nonemptiness does not prove that a relation covers all source evaluations.
The existing G45.05-BR DecoderPremise is reused without change.
-/
namespace Solidity.Backend.Selection.V2

/-- G24.03 preservation with a nonempty observation relation. -/
structure CompilerPremise (SourceObservation : Type)
    (source : Nat → SourceObservation) (ir : List Evm.Instr)
    (relation : SourceObservation → Evm.Machine → Evm.Machine → Prop) : Prop where
  inhabited : ∃ (budget : Nat) (initial final : Evm.Machine),
    relation (source budget) initial final
  preserves : ∀ (budget : Nat) (initial final : Evm.Machine),
    relation (source budget) initial final → Evm.run ir initial = .ok final 0

/-- G49.02 statement only, with an admitted source/IR case. The witness is
independent of both implication premises, preventing an empty source relation
from making the consumer trivially inhabited. Source budgets and the exact
composed bytes remain explicit. This is not a runtime theorem. -/
structure RuntimeConsumer (SourceObservation : Type)
    (source : Nat → SourceObservation) (ir : List Evm.Instr)
    (relation : SourceObservation → Evm.Machine → Evm.Machine → Prop)
    (b : Block) (input output : Nat)
    (composition : CompositionCertificate ir b input output)
    (bridgeStep : LabelExec.State → Option LabelExec.State)
    (bridgeRun : Nat → LabelExec.State → Option LabelExec.State)
    (reachable : LabelExec.State → Prop) : Prop where
  inhabited : ∃ (budget : Nat) (m : Evm.Machine) (s t : Scalar.Stack),
    s.length = input ∧ m.stack = irStack s ∧
      relation (source budget) m { m with stack := irStack t } ∧
      Evm.run ir m = .ok { m with stack := irStack t } 0
  consume : CompilerPremise SourceObservation source ir relation →
    DecoderPremise (encode composition.assembled.code) input bridgeStep bridgeRun reachable →
    ∀ (budget : Nat) (m : Evm.Machine) (s t : Scalar.Stack),
      s.length = input → m.stack = irStack s →
      relation (source budget) m { m with stack := irStack t } →
      ∃ steps : Nat,
        bridgeRun steps ⟨0,s⟩ = some ⟨size composition.assembled.code,t⟩ ∧
        ∀ k : Nat, k ≤ steps → ∃ reached : LabelExec.State,
          bridgeRun k ⟨0,s⟩ = some reached ∧ reached.stack.length ≤ 1024

end Solidity.Backend.Selection.V2
