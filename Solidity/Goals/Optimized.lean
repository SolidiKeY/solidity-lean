import Solidity.Tools.Goal
import Solidity.Backend.CompilerOptimized

/-! The optimizing endpoint and accepted-fragment totality, including the static
non-refusal clause. The selected code is related to the original source run. -/
namespace Solidity.Goals

open Solidity.Goal

@[goal Solidity.Backend.compiler_optimized_endpoint "o1-optimize-endpoint"]
def compilerOptimizedEndpoint : Prop :=
  Solidity.Backend.CompilerOptimizedEndpoint ∧ Solidity.Backend.CompilerOptimizedTotal

end Solidity.Goals
