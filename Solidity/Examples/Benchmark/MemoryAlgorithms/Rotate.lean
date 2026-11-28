import Solidity.Calculus.ProvesDerive
import Solidity.Calculus.SurfaceSpec
import Solidity.Calculus.Surface
import Solidity.Calculus.Closers

/-!
# Rotation by k into a fresh memory array

Source: the Dafny guide, sections "Loop Invariants", "Arrays" and
"Quantifiers" (pinned): <https://raw.githubusercontent.com/dafny-lang/dafny/0b85e632f110f2a078e22cf1f0e94b976ed571ba/docs/OnlineTutorial/guide.md>.
Program: `r[(i + k % n) % n] = xs[i]` for every `i`.
Adaptation: uint256 memory arrays; the result goes to a caller's array `r`
of the same length (Dafny's `modifies`: a function here returns value types
only, and the surface does not snapshot a memory heap, so an in-place
rotation has no entry state to specify against); a nonempty input (`% n`).
Natural specification: element `i` at position `(i + k) mod n`. Invariant: that placement below `i`; variant
`n - i`.
-/
namespace Solidity.Examples.Benchmark.MemoryAlgorithms.Rotate

def Rotate : Contract := contract!{
  requires xs.length > 0 && r.length == xs.length;
  ensures \forall uint j; j < xs.length -> r[(j + k % xs.length) % xs.length] == xs[j];
  function rotate(uint[] memory xs, uint k, uint[] memory r) public pure {
    uint n = xs.length;
    uint i = 0;
    /// @custom:key invariant i <= n && n == xs.length && r.length == n
    /// @custom:key invariant \forall uint j; j < i -> r[(j + k % n) % n] == xs[j]
    /// @custom:key decreases n - i
    while (i < n) { r[(i + k % n) % n] = xs[i]; i++; }
  }
}
local instance : InContract := ⟨Rotate⟩
open scoped Scoped

/-- False as stated, by aliasing; no formal counterexample yet. Two memory
inputs may be one array (`NRead.refInputs` asks only that each exists), and
the clause `r.length == xs.length` allows `r = xs`: with `n = 3`, `k = 2` and
`xs = r = [1, 2, 3]` the writes give `[1, 2, 1]`, `[2, 2, 1]`, `[2, 1, 1]`, and
`r[2] = 1 ≠ 2 = xs[0]`. Dafny's version needs `requires r != xs`, which
SolSpec cannot state (no reference disequality). Not written as an
`example`: no tactic refutes a box postcondition at a typed state with two
aliased memory inputs. Separately, `sol_prove` leaves `leaf1` as
`… ⟹ false` (no frame for a loop body that writes memory). -/
def correctnessTarget := spec!{ rotate }

end Solidity.Examples.Benchmark.MemoryAlgorithms.Rotate
