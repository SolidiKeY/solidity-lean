import Solidity.Calculus.ProvesDerive
import Solidity.Calculus.SurfaceSpec
import Solidity.Calculus.Surface
import Solidity.Calculus.Closers

/-!
# Insertion sort of a small memory array

Source: Cormen et al., *Introduction to Algorithms*, 3rd edition (2009),
section 2.1, INSERTION-SORT. Adaptation: zero-based uint256 memory array,
limited to at most eight elements; shift larger elements before insertion.
Natural specification: sorted result and a permutation of the entry array.
Outer invariant: sorted prefix and unchanged multiset. Inner invariant:
the hole contains the saved key logically; the shifted region exceeds it.
-/
namespace Solidity.Examples.Benchmark.Algorithms.InsertionSort

def NaturalSpec (before after : List Nat) : Prop :=
  before.Perm after ∧ after.Pairwise (fun a b => a <= b)

def InsertionSort : Contract := contract!{
  requires xs.length <= 8;
  ensures \forall uint i; \forall uint j; i < j && j < xs.length -> xs[i] <= xs[j];
  function sort(uint[] memory xs) public pure {
    uint i = 1;
    /// @custom:key invariant 1 <= i && i <= xs.length + 1
    /// @custom:key invariant \forall uint p; \forall uint q; p < q && q < i -> xs[p] <= xs[q]
    /// @custom:key decreases xs.length + 1 - i
    while (i < xs.length) {
      uint key = xs[i]; uint j = i;
      /// @custom:key invariant j <= i
      /// @custom:key invariant \forall uint p; \forall uint q; p < q && q <= i && p != j && q != j -> xs[p] <= xs[q]
      /// @custom:key invariant \forall uint q; j < q && q <= i -> key < xs[q]
      /// @custom:key decreases j
      while (j > 0 && xs[j - 1] > key) { xs[j] = xs[j - 1]; j -= 1; };
      xs[j] = key; i++;
    }
  }
}
local instance : InContract := ⟨InsertionSort⟩
open scoped Scoped

/-- Unknown even for sortedness: the walk leaves a false loop-cut leaf.
Blocks.loopStep refuses bodies whose Prog.frame is none; memory writes
need a sound heap-modifies/havoc frame. This is not a counterexample. -/
def sortednessTarget := spec!{ sort }
-- Unknown: sortedness is only one conjunct of NaturalSpec. The full target
-- additionally needs an entry-memory snapshot and multiset/permutation syntax.
-- NaturalSpec is a mathematical target, not a proof about the contract.
end Solidity.Examples.Benchmark.Algorithms.InsertionSort
