import Solidity.Calculus.ProvesDerive
import Solidity.Calculus.DecideComplete
import Solidity.Calculus.SurfaceSpec
import Solidity.Calculus.Surface
import Solidity.Calculus.Closers
/-!
# Benchmark: an abstract contract calling a hook its heir implements

Source: solc's semantic test `functionCall/inheritance/call_unimplemented_base.sol`,
<https://raw.githubusercontent.com/ethereum/solidity/v0.8.26/test/libsolidity/semanticTests/functionCall/inheritance/call_unimplemented_base.sol>
(expected `b() -> 42`).

The abstract `I` declares the hook `a()` with no body, `J` re-declares it,
the abstract `V` calls it from `b()`, and `C` implements it.  `C` is written
linearized (`C, V, J, I`): the declarations without a body leave no code,
so `V`'s internal call `a()` names `C`'s `a`, the one version there is (no
interface type is involved).  Nothing else is changed.
```solidity
abstract contract I { function a() internal view virtual returns(uint256); }
abstract contract J is I { function a() internal view virtual override returns(uint256); }
abstract contract V is J { function b() public view returns(uint256) { return a(); } }
contract C is V { function a() internal view override returns (uint256) { return 42; } }
```

Verdicts: `a`, `b`: proved.
-/

namespace Solidity.Examples.Benchmark.Inheritance.AbstractHook
/-- `C`, linearized `C, V, J, I`, with the clauses. -/
def C : Contract := contract!{
  ensures \result == 42;
  function a() internal view override returns (uint256) { return 42; }
  ensures \result == 42;
  function b() public view returns (uint256) { return a(); }
}

local instance : InContract := ⟨C⟩

open scoped Scoped
/-- `C.a()`, the hook's implementation, returns `42`. -/
theorem spec_a : ⊢ spec!{ a } := by
  sol_prove
/-- `V.b()` calls the hook, which is `C.a()`. -/
theorem spec_b : ⊢ spec!{ b } := by
  sol_prove

end Solidity.Examples.Benchmark.Inheritance.AbstractHook
