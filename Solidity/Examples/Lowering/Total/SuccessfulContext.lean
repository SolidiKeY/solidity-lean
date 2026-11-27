import Solidity.Correctness.Lowering.Total.Decode.SuccessfulContext

/-! Coverage regression: even an empty successful caller does not certify the
contract's declaration table. No full context decoder or mixed-unit coverage is
claimed by this obstruction check. -/
namespace Solidity.Examples.Lowering.Total.SuccessfulContext

open Solidity.Correctness.Lowering.Total
open Solidity.Correctness.Lowering.Total.Decode.SuccessfulContext

/-- The existing enum component refuses the exact empty enum used in the
successful-production witness. -/
example : EnumDecode.decode { vars := [], enums := [("E", [])] } =
    .error (.emptyEnum 0 "E") := rfl

/-- Any input supplies a successful request outside enum representability;
caller locals, scope and return slots have not been restricted. -/
example (input : ProductionInput) :
    ¬ (∀ (r : Request) (o : ProductionOutput),
      r.success o → EnumDecode.Representable r.contract) := by
  obtain ⟨r, o, hs, hn⟩ := success_without_enum_representation input
  exact fun h => hn (h r o hs)

end Solidity.Examples.Lowering.Total.SuccessfulContext
