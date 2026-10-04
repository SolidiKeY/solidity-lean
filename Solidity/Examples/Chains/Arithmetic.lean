import Solidity.Calculus.Chains
import Solidity.Calculus.LastLine
import Solidity.Calculus.Close

/-!
# Arithmetic: the compound storage update

The calculus's worked example `alice.age += 1;`, one chain for every modality
and postcondition.  Lean's rule is `storageFieldOpAssign` (the printed
`arithStorageFieldCompoundAssign`); the elaborator's `uint` is the printed
`int`.  The printed lines are all present, in the printed order.
-/

namespace Solidity.Examples.Chains.Arithmetic

local instance : InContract := ⟨StandardExample⟩

/-! ## Example: Compound Storage Update -/

section CompoundStorageUpdate
variable (m : Modality) (φ : Post StandardExample)

/-- `alice.age += 1;`: the field is read, added to and written back in one
update, with no branch split. -/
def compoundStorageUpdate :
    dl![m]{ ⟨[ alice.age += 1; ]⟩ φ }
    ~*> dl![m]{ { storage := save(storage, alice.age, find(storage, alice.age) + 1) } φ } :=
  calc dl![m]{ ⟨[ alice.age += 1; ]⟩ φ }
    _ ~*>
        dl![m]{ { storage := save(storage, alice.age, find(storage, alice.age) + 1) } φ } := by sol_chain

end CompoundStorageUpdate

#last_line compoundStorageUpdate
end Solidity.Examples.Chains.Arithmetic
