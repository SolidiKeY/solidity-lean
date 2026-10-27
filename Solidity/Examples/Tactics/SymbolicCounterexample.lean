import Solidity.Calculus.Surface
import Solidity.Tools.Counterexample

/-!
# Counterexamples past every storage the search builds

`s + 2` over a loop bounded by an array's length overflows only when the
array has `2^255` elements: no candidate the search draws is that long, and
no run with fuel iterates that often.  The search proposes such arrays
itself after the ordinary candidates (`longCands`, `Tools/Counterexample.lean`):
the array is `2^255` copies of its default, never unfolded
(`SVec.rep`, `Tools/LazyStorage.lean`), `wt(storage)` is proved of it rather
than evaluated (`holds_wt_of`), and a loop that only counts runs in closed
form (`Prog.runA`, `Semantics/RunAccel.lean`): its first overflow, or the
iteration its condition fails, in O(1) kernel steps.
-/

namespace Solidity.Examples.Tactics.SymbolicCounterexample

open scoped Scoped

-- Preserve the candidate order and boundary behavior without allocating an
-- exponential product to discover that it exceeds the search budget.
#guard Tools.productsWithin 6 [[1, 2], [3, 4, 5]] = Tools.products [[1, 2], [3, 4, 5]]
#guard Tools.productsWithin 5 [[1, 2], [3, 4, 5]] = []
#guard Tools.productsWithin 0 ([] : List (List Nat)) = []
#guard Tools.productsWithin 1 ([] : List (List Nat)) = [[]]
#guard Tools.productsWithin 1000 (List.replicate 40 (List.range 10)) = []
#guard Tools.productsWithin 1000 (List.replicate 40 (List.range 10) ++ [[]]) = []

def Counted : Contract := contract!{
  uint[] values;
  uint total;
}

local instance : InContract := ⟨Counted⟩

/-- `Counted`'s storage with `values` `2^255` zeros long, which the kernel
never unfolds. -/
def longValues : Storage Counted :=
  .cons (SVal.arrayOf (SVec.rep (.prim (PrimTy.dflt .uint)) (2 ^ 255)) .nil)
    (.cons (.prim (PrimTy.dflt .uint)) .nil)

def sumLoop := sol[Counted]{ uint s = 0; uint i = 0;
  while (i < values.length) { s = s + 2; i = i + 1; } }

/-- With fuel alone the run gives up after its `1000` iterations; in closed
form it reverts at the overflow. -/
example : (Prog.runF 1000 sumLoop (State.ofStorage longValues)).halt? = some .diverge := by
  decide +kernel

example : (Prog.runA 1000 sumLoop (State.ofStorage longValues)).halt? = some .revert := by
  decide +kernel

/-! The loop of solkey's `invariantClosedFormSum`: from `2^255` elements the
`2^255`-th `s + 2` reverts, which the diamond refuses. -/

/--
info: counterexample (certified):
  msg.sender = 1, msg.value = 0
  before: values.length = 2^255, each element its default; every other root its default
-/
#guard_msgs in
#counterexample dl!{ wt(storage) → ⟨ uint s = 0; uint i = 0;
  while (i < values.length) { s = s + 2; i = i + 1; }; ⟩ true }

theorem sumOverflows : ¬ (⊨ᶠ dl!{ wt(storage) → ⟨ uint s = 0; uint i = 0;
    while (i < values.length) { s = s + 2; i = i + 1; }; ⟩ true }) := by
  sol_refute

/-- The other closed form: the loop ends, at `i = 2^255`, when its condition
fails, which no run with fuel reaches. -/
theorem countEndsLate : ¬ (⊨ᶠ dl!{ wt(storage) → ⟨ uint i = 0;
    while (i < values.length) { i++; }; ⟩ i < 1000 }) := by
  sol_refute

/-- `x += d` counts too, and so does a bound written the other way round. -/
theorem countEndsLateOp : ¬ (⊨ᶠ dl!{ wt(storage) → ⟨ uint i = 0;
    while (values.length > i) { i += 3; }; ⟩ i < 1000 }) := by
  sol_refute

/-! A true property is not refuted: `s` and `i` count to the length, which no
array takes past `2^256 - 1`, so no addition overflows, and the long arrays
end the loop where the postcondition holds. -/

/-- info: no counterexample found in 2000 candidates -/
#guard_msgs in
#counterexample dl!{ wt(storage) → ⟨ uint s = 0; uint i = 0;
  while (i < values.length) { s = s + 1; i = i + 1; }; ⟩ s == values.length }

/-- error: sol_refute: no counterexample found in 2000 candidates -/
#guard_msgs in
example : ¬ (⊨ᶠ dl!{ wt(storage) → ⟨ uint s = 0; uint i = 0;
    while (i < values.length) { s = s + 1; i = i + 1; }; ⟩ s == values.length }) := by
  sol_refute

end Solidity.Examples.Tactics.SymbolicCounterexample
