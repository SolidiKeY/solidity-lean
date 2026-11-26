import Solidity.Calculus.ProvesDerive
import Solidity.Calculus.DecideComplete
import Solidity.Calculus.SurfaceSpec
import Solidity.Calculus.Surface
import Solidity.Calculus.Closers

/-!
# DeFi: constant-product swap accounting

Source: Uniswap v2 whitepaper (March 2020), section 3.2.1; pinned companion
implementation, invariant check in `swap`:
<https://github.com/Uniswap/v2-core/blob/v1.0.1/contracts/UniswapV2Pair.sol>.
This is its zero-fee reserve accounting algorithm, not the pair's complete EVM
implementation. External token transfers, callbacks, mint/burn and the protocol
fee are outside this standalone reserve benchmark. The caller supplies the
already-received input and requested output. The product check is retained,
so integer rounding cannot decrease k. Solidity checked multiplication may
revert on large reserves; the specification does not hide that with bounds.
-/
namespace Solidity.Examples.Benchmark.Defi.ConstantProduct

def ConstantProduct : Contract := contract!{
  uint public reserve0;
  uint public reserve1;
  ensures reserve0 == \old(reserve0) + amountIn;
  ensures reserve1 == \old(reserve1) - amountOut;
  ensures reserve0 * reserve1 >= \old(reserve0) * \old(reserve1);
  function swap(uint amountIn, uint amountOut) public {
    require(amountIn > 0);
    require(amountOut < reserve1);
    uint x = reserve0 + amountIn;
    uint y = reserve1 - amountOut;
    require(x * y >= reserve0 * reserve1);
    reserve0 = x;
    reserve1 = y;
  }
}
local instance : InContract := ⟨ConstantProduct⟩
open scoped Scoped

/-- The accepted swap changes reserves exactly and cannot decrease k. -/
theorem swap_spec : ⊢ spec!{ swap } := by sol_prove

end Solidity.Examples.Benchmark.Defi.ConstantProduct
