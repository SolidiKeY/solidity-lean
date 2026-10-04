import Solidity.FreshNames
import Solidity.Calculus.Chains
import Solidity.Calculus.LastLine

/-!
# Evaluation order of indexed writes

The calculus's worked example `m[i++] = i;`: Solidity evaluates the value
before it resolves the target, so the write stores the old `i`.  The listing
is `balances[i++] = i;` here (`balances` is a mapping of `StandardExample`, `m`
of the printed lines), from `i` 7.  The elaborator captures the value first
(the printed Repair 1), so the unsound derivation has no chain; Repair 2 is
not taken.  The chain is one term, grouped as the paper prints it, every
capture kept, and ends with the write folded to literals.
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

variable (m : Modality) (φ : Post StandardExample)

-- The paper's first `⇝`, the program split into its captures, is the elaborator's: the printed line
-- `uint a = i; uint b = i++; m[b] = a;` is the same formula as the source (Lean declares `b`, then
-- assigns it).
example : dl![m]{ { i := 7 } ⟨[ balances[i++] = i; ]⟩ φ }
    = dl![m]{ { i := 7 } ⟨[ uint a = i; uint b; b = i++; balances[b] = a; ]⟩ φ } := rfl

/-- `balances[i++] = i;` with `i` 7, as `uint a = i; uint b = i++; balances[b] = a;`: the
write stores the old `i`, `7` at `balances[7]`, where a capture of the index first would store `8`.
Lean declares `b` and then assigns it, where the printed lines initialise it, so the paper's `⇝*` binds
`b := 0` and then `{ i := i + 1 ‖ b := i }`.  The write by the captured index (`balances[b]`) with the
empty program after it is the paper's `⇝`; the merge resolves it to `balances[7]` and the value to `7`,
and `i + 1` folds to `8`. -/
theorem chain :
    dl![m]{ { i := 7 } ⟨[ balances[i++] = i; ]⟩ φ }
    ~*> dl![m]{ { i := 7 } { a := i } { b := 0 } { i := i + 1 ‖ b := i } ⟨[ balances[b] = a; ]⟩ φ }
    ~*> dl![m]{ { i := 7 } { a := i } { b := 0 } { i := i + 1 ‖ b := i }
          { storage := save(storage, balances[b], a) } φ }
    ~[sequentialToParallel]~>
      dl![m]{ { i := 7 ‖ a := 7 ‖ b := 0 ‖ i := 7 + 1 ‖ b := 7 ‖ storage := save(storage, balances[7], 7) } φ }
    ~[add_literals]~>
      dl![m]{ { i := 7 ‖ a := 7 ‖ b := 0 ‖ i := 8 ‖ b := 7 ‖ storage := save(storage, balances[7], 7) } φ } := by
  sol_chain

#last_line chain
end Repair1

/-! ## Repair 2: Settle the Value, Then Reuse the Existing Rule

Not taken: `uint const a = i; m[i++] = a;` needs a rule of its own to introduce
the `const` binding, so it buys nothing; no chain. -/

end Solidity.Examples.Chains.EvaluationOrder
