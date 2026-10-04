import Solidity.Calculus.Chains
import Solidity.Calculus.LastLine
import Solidity.Calculus.Close

/-!
# Arithmetic: the compound storage update

The calculus's worked example `alice.age += 1;` as one chain term over any modality `m` and postcondition `φ`
(`Calculus/Chains.lean`, `.claude/rules/derivations.md`), through `storageFieldOpAssign`.

Every line is written.  The paper's one `⇝` is the rule with the empty program after it, one `~*>`; past the
program the stack merges (`~[sequentialToParallel]~>`) and the read is resolved one law a link, to the last
line, which `#last_line` checks.  The storage the program reads gets a concrete value in an update on the first
line, so the read ends at a literal and the sum folds.
-/

namespace Solidity.Examples.Chains.Arithmetic

local instance : InContract := ⟨StandardExample⟩

/-! ## Example: Compound Storage Update -/

section
variable (m : Modality) (φ : Post StandardExample)

namespace CompoundStorageUpdate

/-- `alice.age += 1;` from a storage where `alice.age` is 10: the field is read, added to and written back in
one update, with no branch split; the merge puts the starting storage under the read, which finds 10, and
the sum folds to 11. -/
theorem chain :
    dl![m]{ { storage := save(storage, alice.age, 10) } ⟨[ alice.age += 1; ]⟩ φ }
    ~*> dl![m]{ { storage := save(storage, alice.age, 10) }
        { storage := save(storage, alice.age, find(storage, alice.age) + 1) } φ }
    ~[sequentialToParallel]~> dl![m]{
        { storage := save(save(storage, alice.age, 10), alice.age, find(save(storage, alice.age, 10), alice.age) + 1) } φ }
    ~[findOnSave]~> dl![m]{ { storage := save(save(storage, alice.age, 10), alice.age, 10 + 1) } φ }
    ~[add_literals]~> dl![m]{ { storage := save(save(storage, alice.age, 10), alice.age, 11) } φ } := by
  sol_chain
#last_line chain
end CompoundStorageUpdate

end

end Solidity.Examples.Chains.Arithmetic
