import Solidity.Correctness.Lowering.Total.Decode.Tables

namespace Solidity.Examples.LoopsDecode

open Solidity.Correctness.Lowering.Total

/-- The landed decoder table, retained from the producer examples. -/
example : Decode.tables1 = ⟨Decode.typeName, Decode.localTy, Decode.unit, Decode.env⟩ := rfl

/-- The bridge: the generic decoder at the landed tables preserves every request. -/
example (r : Request) : Decode.tables1.decode r = Decode.decode r := Decode.decode_tables1 r

end Solidity.Examples.LoopsDecode
