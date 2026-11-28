import Solidity.Calculus.ProvesDerive
import Solidity.Calculus.SurfaceSpec
import Solidity.Calculus.Surface
import Solidity.Calculus.Closers

/-!
# Benchmark: string equality by `keccak256`

Source: <https://raw.githubusercontent.com/OpenZeppelin/openzeppelin-contracts/v5.3.0/contracts/utils/Strings.sol>, lines 131–136 (OpenZeppelin 5.3.0 `Strings.equal`).
Adaptation: the library function written as an internal function of a contract; its body unchanged.

Natural specification: equal contents give `true`, and `true` implies
equal lengths.  (That `true` implies equal contents rests on collision
resistance, which the model does not assume; it is not stated.)

Status of `equal`: **unknown**.  The obligation does not elaborate: the
clauses cannot name a `string memory` (or `bytes memory`/`calldata`)
parameter (`spec!` fails with "unknown name a", pinned below).  Missing:
memory byte-array parameters in `SpecCtx.refs` (`Calculus/SurfaceSpec.lean`).
Two concrete runs are proved instead (`equalSame`, `equalSwapped`).
-/

namespace Solidity.Examples.Benchmark.Bytes.StringEquality

/-- `Strings.equal`, as published, with the natural clauses. -/
def StringEquality : Contract := contract!{
  ensures (a.length == b.length && \forall uint i; i < a.length -> a[i] == b[i]) -> \result;
  ensures \result -> a.length == b.length;
  function equal(string memory a, string memory b) internal pure returns (bool) {
    return bytes(a).length == bytes(b).length && keccak256(bytes(a)) == keccak256(bytes(b));
  }
}

local instance : InContract := ⟨StringEquality⟩
open scoped Scoped

/-- error: Solidity elaboration failed: unknown name a -/
#guard_msgs in #check spec!{ equal }

/-- `equal("ab", "ab")` is `true`. -/
theorem equalSame : ⊨ᶠ dl!{ [ bool r = equal("ab", "ab"); ] r == true } := by
  sol_symex
  sol_decide

/-- `equal("ab", "ba")` is `false`: same length, different hashes. -/
theorem equalSwapped : ⊨ᶠ dl!{ [ bool r = equal("ab", "ba"); ] r == false } := by
  sol_symex
  sol_decide

end Solidity.Examples.Benchmark.Bytes.StringEquality
