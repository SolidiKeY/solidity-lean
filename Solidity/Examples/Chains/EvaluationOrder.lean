import Solidity.FreshNames
import Solidity.Calculus.Chains

/-!
# Evaluation order of indexed writes

The calculus's worked example `m[i++] = i;`: Solidity evaluates the value
before it resolves the target, so with `i` initially `0` the write stores `0`.
The listing is `balances[i++] = i;` here (`balances` is a mapping of
`StandardExample`, `m` of the printed lines).  The elaborator captures the
value first (the printed Repair 1), so the unsound derivation has no chain;
Repair 2 is not taken.
-/

namespace Solidity.Examples.Chains.EvaluationOrder

local instance : InContract := ⟨StandardExample⟩

/-! ## The Unsound Derivation

`m[i++] = i;` captured index first, as `uint idx = i++; m[idx] = i;`, would
store `i + 1`.  Lean has no such derivation: the elaborator captures the
value before the index, so the program it reads is the first repair's, and
there is no rule or chain to write for the other. -/

/-! ## Repair 1: Capture the Value and the Index Together -/

namespace Repair1

/-- `m[i++] = i;`: the value `a`, then the index `b`. -/
def names : FreshTable := [("a", "se1"), ("b", "se2")]

local instance : FreshNames := .ofTable names

#guard (FreshNames.clashes StandardExample names).isEmpty

/-- `balances[i++] = i;` as `uint a = i; uint b = i++; balances[b] = a;`: the
write stores the old `i`.  Lean declares `b` and then assigns it, where the
printed lines initialise it, so its update is `{ i := i + 1 ‖ b := i }`.  The
write by the captured index (`balances[b]`) is crossed unwritten; the merge
resolves it to `balances[i]` and the value to `i`, and the dead `b := 0` goes. -/
def snapshot (m : Modality) (φ : Post StandardExample) :
    dl![m]{ ⟨[ balances[i++] = i; ]⟩ φ }
    ~~> dl![m]{ { a := i ‖ i := i + 1 ‖ b := i ‖ storage := save(storage, balances[i], i) } φ } :=
  calc dl![m]{ ⟨[ balances[i++] = i; ]⟩ φ }
    _ = dl![m]{ ⟨[ uint a = i; uint b; b = i++; balances[b] = a; ]⟩ φ } := rfl
    _ ~*> dl![m]{ { a := i } { b := 0 } { i := i + 1 ‖ b := i } ⟨[ balances[b] = a; ]⟩ φ } := by sol_chain
    _ ~[storageIndexWriteMappingSave]~> _ := by sol_chain
    _ ~> _ := by sol_chain
    _ ~[sequentialToParallel]~>
        dl![m]{ { a := i ‖ b := 0 ‖ i := i + 1 ‖ b := i ‖ storage := save(storage, balances[i], i) } φ } := by
      sol_chain
    _ ~[simplifyUpdate]~>
        dl![m]{ { a := i ‖ i := i + 1 ‖ b := i ‖ storage := save(storage, balances[i], i) } φ } := by sol_chain

end Repair1

/-! ## Repair 2: Settle the Value, Then Reuse the Existing Rule

Not taken: `uint const a = i; m[i++] = a;` needs a rule of its own to introduce
the `const` binding, so it buys nothing; no chain. -/

end Solidity.Examples.Chains.EvaluationOrder
