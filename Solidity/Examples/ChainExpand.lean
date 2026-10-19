import Solidity.Calculus.ExpandLaws
import Solidity.Calculus.Chains
import Solidity.Calculus.Close
import Solidity.Calculus.DecideComplete
import Solidity.Calculus.Surface

/-!
# A whole value's write, as the writes of its words

The four Lean-only links of `Calculus/ExpandLaws.lean`, each on a line past
the program, under any modality `m` and postcondition `φ`: `delAtExpand`
(`delete alice.account;`: a member of a struct and a member of its member),
`pushExpand` and `popExpand` (`values.push(5);`, `values.pop();`, KeY's
nested writes over `values.length`, the word saved at the slot past the end,
`values[values.length]@storage`, or reset at the last one), `copyExpand`
(`alice.account = bob.account;`, each word read in the storage before the
copy).  The lines are the ones the strategy leaves (`#chain`); each link is
named, never tried by `~=>` or `#last_line`.  Then the closer on the
expanded line (`deleteValue`, `pushValue`, `copyValue`): `sol_decide` reads
a word back from the save of that word.  Which types expand is pinned last.
-/

namespace Solidity.Examples.ChainExpand

open scoped Scoped

local instance : InContract := ⟨StandardExample⟩

section
variable (m : Modality) (φ : Post StandardExample [])

/-- `delete alice.account;`: `balance` and `token.value` reset, one `save` each. -/
example : dl![m]{ { storage := delAt(storage, alice.account) } φ }
    ~[delAtExpand]~> dl![m]{ { storage := save(save(storage, alice.account.balance, 0), alice.account.token.value, 0) } φ } := by
  sol_chain

/-- `values.push(5);`: one more slot, then `5` saved at it. -/
example : dl![m]{ { storage := save(save(storage, values[values.length], 5), values.length, values.length + 1) } φ }
    ~[pushExpand]~> dl![m]{ { storage := save(save(storage, values.length, values.length + 1), values[values.length]@storage, 5) } φ } := by
  sol_chain

/-- `values.pop();`: the last word reset, then the length shrunk. -/
example : dl![m]{ { storage := save(delAt(storage, values[values.length - 1]), values.length, values.length - 1) } φ }
    ~[popExpand]~> dl![m]{ { storage := save(save(storage, values[values.length - 1]@storage, 0), values.length, values.length - 1) } φ } := by
  sol_chain

/-- `alice.account = bob.account;`: each word of `bob.account`, read before
the copy, saved at `alice.account`'s. -/
example : dl![m]{ { sp1 := bob.account ‖ storage := save(storage, alice.account, find(storage, bob.account)) } φ }
    ~[copyExpand]~> dl![m]{ { sp1 := bob.account ‖
        storage := save(save(storage, alice.account.balance, select(storage, bob.account.balance)),
          alice.account.token.value, select(storage, bob.account.token.value)) } φ } := by
  sol_chain

/-- `delete alice.account;` resets `alice.account.token.value`, closed on the
expanded line. -/
theorem deleteValue : ⊨ dl!{ [ delete alice.account; ] alice.account.token.value == 0 } := by
  refine Fml.Via.valid (show dl!{ [ delete alice.account; ] alice.account.token.value == 0 }
      ~[storageFieldDelete]~> dl![.box]{ { storage := delAt(storage, alice.account) }
        alice.account.token.value == 0 }
      ~[delAtExpand]~> dl![.box]{
        { storage := save(save(storage, alice.account.balance, 0), alice.account.token.value, 0) }
          alice.account.token.value == 0 } by sol_chain) ?_
  dsimp only [Fml.Via.last]
  sol_decide

/-- `values.push(5);` leaves `5` last, closed on the expanded line. -/
theorem pushValue : ⊨ dl!{ [ values.push(5); ] values[values.length - 1] == 5 } := by
  refine Fml.Via.valid (show dl!{ [ values.push(5); ] values[values.length - 1] == 5 }
      ~[storagePushValueSave]~> dl![.box]{
        { storage := save(save(storage, values[values.length], 5), values.length, values.length + 1) }
          values[values.length - 1] == 5 }
      ~[pushExpand]~> dl![.box]{
        { storage := save(save(storage, values.length, values.length + 1), values[values.length]@storage, 5) }
          values[values.length - 1] == 5 } by sol_chain) ?_
  dsimp only [Fml.Via.last]
  sol_decide

/-- `alice.account = bob.account;` copies `balance`, closed on the expanded
line. -/
theorem copyValue :
    ⊨ dl!{ [ alice.account = bob.account; ] alice.account.balance == bob.account.balance } := by
  refine Fml.Via.valid (show dl!{ [ alice.account = bob.account; ] alice.account.balance == bob.account.balance }
      ~*> dl![.box]{ { sp1 := bob.account } { storage := save(storage, alice.account, find(storage, sp1)) }
        alice.account.balance == bob.account.balance }
      ~[sequentialToParallel]~> dl![.box]{
        { sp1 := bob.account ‖ storage := save(storage, alice.account, find(storage, bob.account)) }
          alice.account.balance == bob.account.balance }
      ~[copyExpand]~> dl![.box]{ { sp1 := bob.account ‖
        storage := save(save(storage, alice.account.balance, select(storage, bob.account.balance)),
          alice.account.token.value, select(storage, bob.account.token.value)) }
          alice.account.balance == bob.account.balance } by sol_chain) ?_
  dsimp only [Fml.Via.last]
  sol_decide

end

/-! ## Which types expand

A struct of words, a fixed array of words; not a dynamic array (its delete
truncates it), not a `uint[2^200]` (counted, `Ty.leafCountAt`, without
listing its leaves), not a struct of mappings only (no word). -/

#guard (Ty.ref (.struct "Account")).expandable
#guard (Ty.ref (.fixed Ty.uint 3)).expandable
#guard !(Ty.ref (.array Ty.uint)).expandable
#guard !(Ty.ref (.fixed Ty.uint (2 ^ 200))).expandable
#guard !(Ty.ref (.fixed Ty.uint 65)).expandable
#guard (Ty.ref (.struct "Account")).leafCount == 2

end Solidity.Examples.ChainExpand
