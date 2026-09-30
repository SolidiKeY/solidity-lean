import Solidity.Calculus.Chains
import Solidity.Calculus.Close
import Solidity.Examples.ExampleNames

/-!
# Chains: `φ ~> ψ`, `φ ~[r]~> ψ`, `φ ~*> ψ`, and `calc`

A derivation, stated (`Calculus/Chains.lean`): both ends written in
`dl!{ … }`, and in between as many lines as you like (mini-solkey's chain
examples).

* `φ ~[r]~> ψ` — the rule `r` turns `φ` into `ψ`, as `#derivation` prints a
  line; proved by `rfl`, and a wrong `r` does not elaborate;
* `φ ~> ψ` — the strategy's step does; proved by `rfl` or `sol_chain`;
* `φ ~*> ψ` — several steps; proved by `sol_chain`;
* `φ ~*> φ₁ ~[r]~> φ₂ ~*> …` — a chain, every link holding; `sol_chain`;
* `calc` — the same chain, one line per step, each with its reason.

Every line is a formula `dl!{ … }`: copy it from `#derivation` (`se1`, `sp1`
are the rules' fresh variables; from § 2 on, the printed `pv` and `acc`, by
the headline's table in `Examples/ExampleNames.lean`).  The chains are under
the diamond, whose lines read back; a line with no modality left reads as a
diamond (`fmlModality?`), so a box derivation's last line does not.  What is
*proved valid* is under the box (`Close.lean`: a write under the diamond is
stuck in a state without `alice`), with the lines left to `sol_chain`.
-/

namespace Solidity.Examples.Chains

local instance : InContract := ⟨StandardExample⟩

/-! ## 1 · One step: `~[r]~>` and `~>` -/

example : dl!{ ⟨ alice.age = v; ⟩ alice.age == v }
    ~[storageFieldWriteSave]~> dl!{ { storage := save(storage, alice.age, v) } ⟨⟩ alice.age == v } :=
  rfl

example : dl!{ ⟨ alice.age = v; ⟩ alice.age == v }
    ~> dl!{ { storage := save(storage, alice.age, v) } ⟨⟩ alice.age == v } := by
  sol_chain

-- The rule is checked: `storageRootWriteStore` writes a state variable, not a field.
/--
error: ~[storageRootWriteStore]~>: the rule for
  dl{ ⟨ alice.age = v; ⟩ find(storage, alice.age) = v }
is storageFieldWriteSave, not storageRootWriteStore
-/
#guard_msgs in
example : dl!{ ⟨ alice.age = v; ⟩ alice.age == v }
    ~[storageRootWriteStore]~> dl!{ { storage := save(storage, alice.age, v) } ⟨⟩ alice.age == v } :=
  rfl

-- So is the line: `sol_chain` shows the derivation it computed instead.
/--
error: sol_chain: the derivation of
  dl{ ⟨ alice.age = v; ⟩ find(storage, alice.age) = v }
does not reach
  dl{ { storage := save(storage, alice.age, w) } ⟨ ⟩ find(storage, alice.age) = v }
Its lines:
    dl{ ⟨ alice.age = v; ⟩ find(storage, alice.age) = v }
  ~[storageFieldWriteSave]~>
    dl{ { storage := save(storage, alice.age, v) } ⟨ ⟩ find(storage, alice.age) = v }
-/
#guard_msgs in
example : dl!{ ⟨ alice.age = v; ⟩ alice.age == v }
    ~> dl!{ { storage := save(storage, alice.age, w) } ⟨⟩ alice.age == v } := by
  sol_chain

/-- A rule of Step 1 lands its read in a hole (`Hole.fill`), which unification
cannot see through (`StorageSteps.lean`); the label is computed, so it names
it all the same. -/
example : dl!{ ⟨ x = people[i].age; ⟩ x == 1 }
    ~[storageFieldRead_unfold_rightFst]~> dl!{ ⟨ Person storage sp1 = people[i]; x = sp1.age; ⟩ x == 1 } :=
  rfl

/-- The headline in the printed names: the value `pv`, the alias `acc`. -/
local instance : FreshNames := .ofTable ExampleNames.Headline.names

/-! ## 2 · Several steps: `~*>`

The headline, from the statement to the formula with its three updates. -/

/--
info:     dl{ ⟨ alice.account.balance = 10; ⟩ find(storage, alice.account.balance) = 10 }
  ~[storageFieldWrite_unfold_leftFst]~>
    dl{
  ⟨ uint pv = 10; Account storage acc = alice.account; acc.balance = pv; ⟩ find(storage, alice.account.balance) = 10 }
  ~[localValueDeclInitDrop]~>
    dl{ ⟨ pv = 10; Account storage acc = alice.account; acc.balance = pv; ⟩ find(storage, alice.account.balance) = 10 }
  ~[localValueAssign]~>
    dl{
  { pv := 10 } ⟨ Account storage acc = alice.account; acc.balance = pv; ⟩ find(storage, alice.account.balance) = 10 }
  ~[storageLocalDeclInitDrop]~>
    dl{ { pv := 10 } ⟨ acc = alice.account; acc.balance = pv; ⟩ find(storage, alice.account.balance) = 10 }
  ~[storageFieldReadBindLocalRoot]~>
    dl{ { pv := 10 } { acc := alice.account } ⟨ acc.balance = pv; ⟩ find(storage, alice.account.balance) = 10 }
  ~[storageFieldWriteSave]~>
    dl{
  { pv := 10 }
    { acc := alice.account }
      { storage := save(storage, acc.balance, pv) } ⟨ ⟩ find(storage, alice.account.balance) = 10 }
  ~[emptyModality]~>
    dl{
  { pv := 10 }
    { acc := alice.account } { storage := save(storage, acc.balance, pv) } find(storage, alice.account.balance) = 10 }
-/
#guard_msgs in
#derivation dl!{ ⟨ alice.account.balance = 10; ⟩ alice.account.balance == 10 }

example : dl!{ ⟨ alice.account.balance = 10; ⟩ alice.account.balance == 10 }
    ~*> dl!{ { pv := 10 } { acc := alice.account } { storage := save(storage, acc.balance, pv) }
            alice.account.balance == 10 } := by
  sol_chain

/-! ## 3 · A chain: the arrows mixed

The lines you want to see, and `~*>` over the ones you do not.  Here: Step 2
opens the write, the declaration of the alias `acc` is dropped, and the rest
runs to the end. -/

example : dl!{ ⟨ alice.account.balance = 10; ⟩ alice.account.balance == 10 }
    ~*> dl!{ { pv := 10 } ⟨ Account storage acc = alice.account; acc.balance = pv; ⟩
            alice.account.balance == 10 }
    ~[storageLocalDeclInitDrop]~>
        dl!{ { pv := 10 } ⟨ acc = alice.account; acc.balance = pv; ⟩ alice.account.balance == 10 }
    ~> dl!{ { pv := 10 } { acc := alice.account } ⟨ acc.balance = pv; ⟩ alice.account.balance == 10 }
    ~*> dl!{ { pv := 10 } { acc := alice.account } { storage := save(storage, acc.balance, pv) }
            alice.account.balance == 10 } := by
  sol_chain

/-! ## 4 · `calc`

The derivation of the headline, one line per rule,
each checked by `rfl`.  It is a `def`: the chain is data. -/

def headline : dl!{ ⟨ alice.account.balance = 10; ⟩ alice.account.balance == 10 }
    ~*> dl!{ { pv := 10 } { acc := alice.account } { storage := save(storage, acc.balance, pv) }
            alice.account.balance == 10 } :=
  calc dl!{ ⟨ alice.account.balance = 10; ⟩ alice.account.balance == 10 }
    _ ~[storageFieldWrite_unfold_leftFst]~>
        dl!{ ⟨ uint pv = 10; Account storage acc = alice.account; acc.balance = pv; ⟩
            alice.account.balance == 10 } := rfl
    _ ~[localValueDeclInitDrop]~>
        dl!{ ⟨ pv = 10; Account storage acc = alice.account; acc.balance = pv; ⟩
            alice.account.balance == 10 } := rfl
    _ ~[localValueAssign]~>
        dl!{ { pv := 10 } ⟨ Account storage acc = alice.account; acc.balance = pv; ⟩
            alice.account.balance == 10 } := rfl
    _ ~[storageLocalDeclInitDrop]~>
        dl!{ { pv := 10 } ⟨ acc = alice.account; acc.balance = pv; ⟩
            alice.account.balance == 10 } := rfl
    _ ~[storageFieldReadBindLocalRoot]~>
        dl!{ { pv := 10 } { acc := alice.account } ⟨ acc.balance = pv; ⟩
            alice.account.balance == 10 } := rfl
    _ ~[storageFieldWriteSave]~>
        dl!{ { pv := 10 } { acc := alice.account } { storage := save(storage, acc.balance, pv) } ⟨⟩
            alice.account.balance == 10 } := rfl
    _ ~[emptyModality]~>
        dl!{ { pv := 10 } { acc := alice.account } { storage := save(storage, acc.balance, pv) }
            alice.account.balance == 10 } := rfl

-- A wrong rule in a `calc` step is refused once the line before it is known.
/--
error: ~[storageRootWriteStore]~>: the rule for
  dl{ ⟨ alice.age = v; ⟩ find(storage, alice.age) = v }
is storageFieldWriteSave, not storageRootWriteStore
-/
#guard_msgs in
example : dl!{ ⟨ alice.age = v; ⟩ alice.age == v }
    ~*> dl!{ { storage := save(storage, alice.age, v) } alice.age == v } :=
  calc dl!{ ⟨ alice.age = v; ⟩ alice.age == v }
    _ ~[storageRootWriteStore]~> dl!{ { storage := save(storage, alice.age, v) } ⟨⟩ alice.age == v } := rfl
    _ ~> dl!{ { storage := save(storage, alice.age, v) } alice.age == v } := rfl

/-- A chain is a proof: prove its last line, and the first one follows.  Under
the box, so that the write is valid; `_ ~*> _` runs to the end. -/
theorem headline_valid : ⊨ dl!{ [ alice.account.balance = 10; ] alice.account.balance == 10 } := by
  apply Fml.Steps.valid
  · calc dl!{ [ alice.account.balance = 10; ] alice.account.balance == 10 }
      _ ~*> dl!{ { pv := 10 } [ Account storage acc = alice.account; acc.balance = pv; ]
                alice.account.balance == 10 } := by sol_chain
      _ ~[storageLocalDeclInitDrop]~>
          dl!{ { pv := 10 } [ acc = alice.account; acc.balance = pv; ]
              alice.account.balance == 10 } := rfl
      _ ~*> _ := by sol_chain
  · sol_close

/-! ## 5 · A branch

`ifElseSplit` makes the two goals one formula, `(c → …) ∧ ((c' → …) ∧ cover)`
(`Logic.lean`'s `Premise.fml`; under the diamond the cover is
`¬(¬c ∧ ¬c')`).  The chain runs the `then` branch, then the `else` branch.

The condition is a literal: a boolean local that an update binds
(`{ se1 := find(storage, flags[a]) } ⟨ if (se1) … ⟩`) reads back as a
`uint` parameter, and the `if` is then refused, so such a line cannot be
written in `dl!{ … }`. -/

example : dl!{ ⟨ balances[a] = 1; if (true) { x = 2; } else { x = 1; }; ⟩ balances[a] == x }
    ~> dl!{ { storage := save(storage, balances[a], 1) }
            ⟨ if (true) { x = 2; } else { x = 1; }; ⟩ balances[a] == x }
    ~[ifElseSplit]~>
        dl!{ { storage := save(storage, balances[a], 1) }
            ((true ≐ true → ⟨ x = 2; ⟩ balances[a] == x) ∧
              (true ≐ false → ⟨ x = 1; ⟩ balances[a] == x) ∧ ¬(¬true ≐ true ∧ ¬true ≐ false)) }
    ~*> dl!{ { storage := save(storage, balances[a], 1) }
            ((true ≐ true → { x := 2 } balances[a] == x) ∧
              (true ≐ false → { x := 1 } balances[a] == x) ∧ ¬(¬true ≐ true ∧ ¬true ≐ false)) } := by
  sol_chain

/-! ## 6 · The evidence is unique

A formula has one next line and one rule (`Fml.StepBy.unique`), so two
derivations of the same length between the same ends are one: every
seven-step derivation of the headline is the `calc` above. -/

example (d : dl!{ ⟨ alice.account.balance = 10; ⟩ alice.account.balance == 10 }
    ~*> dl!{ { pv := 10 } { acc := alice.account } { storage := save(storage, acc.balance, pv) }
            alice.account.balance == 10 }) (h : d.length = 7) : d = headline :=
  Fml.Steps.eq_of_length d headline (h.trans rfl)

/-- The strategy of `Symex.lean` is a chain, of the same seven steps. -/
example : (Fml.Steps.ofSymex 200
    dl!{ ⟨ alice.account.balance = 10; ⟩ alice.account.balance == 10 }).length = 7 := by
  decide

/-! ## 7 · What is printed reads back -/

/--
info: dl{ ⟨ alice.age = v; ⟩ find(storage, alice.age) = v }
    ~[storageFieldWriteSave]~> dl{ { storage := save(storage, alice.age, v) } ⟨ ⟩ find(storage, alice.age) = v } : Prop
-/
#guard_msgs in
#check dl!{ ⟨ alice.age = v; ⟩ alice.age == v }
    ~[storageFieldWriteSave]~> dl!{ { storage := save(storage, alice.age, v) } ⟨⟩ alice.age == v }

-- `pv` and `acc` are the fresh variables the rule declares, `se1` and `sp1`,
-- whose default spelling still reads
example : dl!{ ⟨ alice.account.balance = 10; ⟩ true }
    ~[storageFieldWrite_unfold_leftFst]~>
      dl!{ ⟨ uint se1 = 10; Account storage sp1 = alice.account; sp1.balance = se1; ⟩ true } :=
  rfl

end Solidity.Examples.Chains
