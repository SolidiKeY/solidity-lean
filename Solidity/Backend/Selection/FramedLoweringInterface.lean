import Solidity.Backend.Selection.Interface

/-! A strengthening of the existing lowering contract for recursive control.
Statements only: this local obligation is not an external producer premise. -/
namespace Solidity.Backend.Selection

/-- The existing success equivalence plus reflection of every actual successful
IR result. The numeric output and complete nonstack caller frame are recovered,
and a pending skip is proved zero rather than reclassified as normal return.
Faults, reverts, divergence, source observations and budgets are not identified
or removed by this successful-execution contract. -/
structure FramedLoweringCertificate (ir : List Evm.Instr) (block : Block)
    extends LoweringCertificate ir block where
  reflect : ∀ (input : Scalar.Stack) (initial final : Evm.Machine) (skip : Nat),
    initial.stack = irStack input → Evm.run ir initial = .ok final skip →
    ∃ output : Scalar.Stack,
      skip = 0 ∧ final = { initial with stack := irStack output } ∧
        StructuredExec block input output

#print axioms FramedLoweringCertificate
#print axioms FramedLoweringCertificate.reflect

end Solidity.Backend.Selection
