import Solidity.Calculus.ProvesDerive
import Solidity.Calculus.SurfaceSpec
import Solidity.Calculus.Surface
import Solidity.Calculus.Closers

/-!
# SMTChecker: a struct in a mapping

Source: <https://github.com/ethereum/solidity/blob/7893614a31fbeacd1966994e310ed4f760772658/test/libsolidity/smtCheckerTests/types/struct_1.sol> (contract `C`).
Changes: none. The test's property is its `assert`, so the specification is
that no `assert` fails (`[ f(y, v); ] true`); the SMTChecker proves it safe.
-/

namespace Solidity.Examples.Benchmark.SolcVerify.StructMapping

/-- The source contract, with its clauses. -/
def C : Contract := contract!{
  struct S {
    uint x;
  }
  mapping (uint => S) smap;
  function f(uint y, uint v) public {
    smap[y] = S(v);
    S memory smem = S(v);
    assert(smap[y].x == smem.x);
  }
}
local instance : InContract := ⟨C⟩
open scoped Scoped

/-- `f`: the stored copy and the memory copy agree. Proved. -/
theorem f_spec : ⊢ spec!{ f } := by sol_prove

end Solidity.Examples.Benchmark.SolcVerify.StructMapping
