import Solidity.Tools.Goal
import Solidity.Backend.AbiWorld.PublicCompilerTotal
import Solidity.Backend.Passes.WholeProgram.Refusal

/-! Accepted-fragment compiler totality (`Solidity.Backend.compiler_total`, plan
`t0-endpoint-total`): every program of the intrinsic `ProgOk []` domain is compiled by
the public entry from its fresh frame, and the result passes the production static
refusal check for every array bound `L ≤ Lmax` and every frame, so success cannot come
from refusing every input (H503(1), H506). -/

namespace Solidity.Goals

open Solidity.Goal

@[goal Solidity.Backend.compiler_total "t0-endpoint-total"]
def compilerTotal : Prop :=
  ∀ (C : Solidity.Contract) (Gamma Delta : Solidity.Ctx)
    (P : Solidity.Prog C Gamma Delta),
    Solidity.Backend.AbiWorld.PublicCompilerTotal.ProgOk [] P →
    ∀ (b L frame : Nat), L ≤ Solidity.Evm.Lmax →
      ∃ r : Solidity.Evm.Compiler.Compilation b (Solidity.Evm.Frag.init Gamma) P,
        Solidity.Evm.Compiler.compile b (Solidity.Evm.Frag.init Gamma) P = some r ∧
        Solidity.Backend.Passes.WholeProgram.staticRefused r L frame = false

end Solidity.Goals
