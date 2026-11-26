import Solidity.Tools.Goal
import Solidity.Backend.CompilerOptimized

namespace Solidity.Goals

open Solidity.Goal

@[goal Solidity.Backend.compiler_optimized_endpoint "o1-optimize-endpoint"]
def compilerOptimizedEndpoint : Prop :=
  Solidity.Backend.CompilerOptimizedEndpoint ∧ Solidity.Backend.CompilerOptimizedTotal

end Solidity.Goals
