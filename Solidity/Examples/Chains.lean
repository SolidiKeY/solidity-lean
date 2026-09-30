import Solidity.Calculus.Chains
import Solidity.Calculus.Close

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
are the rules' fresh variables).  A line keeps two unknowns:
`dl![m]{ … }` reads it at a modality `m` (`⟨[ P ]⟩ ψ` is `P` under `m`, and
an update with no modality under it is judged at `m`, so a box derivation's
last line is `dl![.box]{ … }`), and a name where a formula stands is a
postcondition `φ : Post C`.  The headline (§4) is the printed trace, for
every `m` and `φ`; what is *proved valid* is its instance under the box
(`Close.lean`: a write under the diamond is stuck in a state without
`alice`).
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

/-! ## 2 · Several steps: `~*>`

The headline, from the statement to the formula with its three updates, for
any modality `m` and postcondition `φ`. -/

section Headline
variable (m : Modality) (φ : Post StandardExample)

/--
info:     dl{ ⟨[ alice.account.balance = 10; ]⟩ φ }
  ~[storageFieldWrite_unfold_leftFst]~>
    dl{ ⟨[ uint se1 = 10; Account storage sp1 = alice.account; sp1.balance = se1; ]⟩ φ }
  ~[localValueDeclInitDrop]~>
    dl{ ⟨[ se1 = 10; Account storage sp1 = alice.account; sp1.balance = se1; ]⟩ φ }
  ~[localValueAssign]~>
    dl{ { se1 := 10 } ⟨[ Account storage sp1 = alice.account; sp1.balance = se1; ]⟩ φ }
  ~[storageLocalDeclInitDrop]~>
    dl{ { se1 := 10 } ⟨[ sp1 = alice.account; sp1.balance = se1; ]⟩ φ }
  ~[storageFieldReadBindLocalRoot]~>
    dl{ { se1 := 10 } { sp1 := alice.account } ⟨[ sp1.balance = se1; ]⟩ φ }
  ~[storageFieldWriteSave]~>
    dl{ { se1 := 10 } { sp1 := alice.account } { storage := save(storage, sp1.balance, se1) } ⟨[ ]⟩ φ }
  ~[emptyModality]~>
    dl{ { se1 := 10 } { sp1 := alice.account } { storage := save(storage, sp1.balance, se1) } φ }
-/
#guard_msgs in
#derivation dl![m]{ ⟨[ alice.account.balance = 10; ]⟩ φ }

example : dl![m]{ ⟨[ alice.account.balance = 10; ]⟩ φ }
    ~*> dl![m]{ { se1 := 10 } { sp1 := alice.account } { storage := save(storage, sp1.balance, se1) } φ } := by
  sol_chain

/-- A step whose rule declares nothing fresh is `rfl` over `φ`; one that does
needs its fresh index, which `rfl` cannot compute over `φ`, and `sol_chain`
proves it from `Post.noFresh`. -/
example : dl![m]{ ⟨[ se1 = 10; Account storage sp1 = alice.account; sp1.balance = se1; ]⟩ φ }
    ~[localValueAssign]~>
      dl![m]{ { se1 := 10 } ⟨[ Account storage sp1 = alice.account; sp1.balance = se1; ]⟩ φ } :=
  rfl

-- A formula that is no `Post` may name a fresh variable, or have a modality.
/--
error: sol_chain: ψ may name a fresh variable or have a modality: take it as a postcondition, `ψ : Post StandardExample`
-/
#guard_msgs in
example (ψ : Fml StandardExample) : dl![m]{ ⟨[ alice.account.balance = 10; ]⟩ ψ }
    ~> dl![m]{ ⟨[ uint se1 = 10; Account storage sp1 = alice.account; sp1.balance = se1; ]⟩ ψ } := by
  sol_chain

end Headline

/-! ## 3 · A chain: the arrows mixed

The lines you want to see, and `~*>` over the ones you do not.  Here: Step 2
opens the write, the declaration of the alias `sp1` is dropped, and the rest
runs to the end. -/

example : dl!{ ⟨ alice.account.balance = 10; ⟩ alice.account.balance == 10 }
    ~*> dl!{ { se1 := 10 } ⟨ Account storage sp1 = alice.account; sp1.balance = se1; ⟩
            alice.account.balance == 10 }
    ~[storageLocalDeclInitDrop]~>
        dl!{ { se1 := 10 } ⟨ sp1 = alice.account; sp1.balance = se1; ⟩ alice.account.balance == 10 }
    ~> dl!{ { se1 := 10 } { sp1 := alice.account } ⟨ sp1.balance = se1; ⟩ alice.account.balance == 10 }
    ~*> dl!{ { se1 := 10 } { sp1 := alice.account } { storage := save(storage, sp1.balance, se1) }
            alice.account.balance == 10 } := by
  sol_chain

/-! ## 4 · `calc`

The derivation of the headline
in the storage examples, for every modality `m` and postcondition
`φ`: a step, the steps to the write, the write, the end of the program.  Its
fresh names are the rules' (`se1`, `sp1` for the printed `pv`, `acc`), and its
updates stay as the rules leave them (the printed trace merges them).  It is a
`def`: the chain is data. -/

def headline (m : Modality) (φ : Post StandardExample) :
    dl![m]{ ⟨[ alice.account.balance = 10; ]⟩ φ }
    ~*> dl![m]{ { se1 := 10 } { sp1 := alice.account } { storage := save(storage, sp1.balance, se1) } φ } :=
  calc dl![m]{ ⟨[ alice.account.balance = 10; ]⟩ φ }
    _ ~[storageFieldWrite_unfold_leftFst]~>
        dl![m]{ ⟨[ uint se1 = 10; Account storage sp1 = alice.account; sp1.balance = se1; ]⟩ φ } := by
      sol_chain
    _ ~*> dl![m]{ { se1 := 10 } { sp1 := alice.account } ⟨[ sp1.balance = se1; ]⟩ φ } := by sol_chain
    _ ~[storageFieldWriteSave]~>
        dl![m]{ { se1 := 10 } { sp1 := alice.account } { storage := save(storage, sp1.balance, se1) }
          ⟨[ ]⟩ φ } := rfl
    _ ~[emptyModality]~>
        dl![m]{ { se1 := 10 } { sp1 := alice.account } { storage := save(storage, sp1.balance, se1) } φ } :=
      rfl

/-- A chain is a proof: prove its last line, and the first one follows.  The
headline under the box, where the write is valid, at the postcondition the
statement is written for. -/
theorem headline_valid : ⊨ dl!{ [ alice.account.balance = 10; ] alice.account.balance == 10 } :=
  (headline .box { fml := dl!{ alice.account.balance == 10 } }).valid (by sol_close)

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

/-- A box derivation's last line, written: an update with no modality under
it is judged at the box in `dl![.box]{ … }` (in `dl!{ … }`, at the diamond). -/
example : dl!{ [ alice.account.balance = 10; ] alice.account.balance == 10 }
    ~*> dl![.box]{ { se1 := 10 } { sp1 := alice.account } { storage := save(storage, sp1.balance, se1) }
          alice.account.balance == 10 } :=
  calc dl!{ [ alice.account.balance = 10; ] alice.account.balance == 10 }
    _ ~*> dl!{ { se1 := 10 } [ Account storage sp1 = alice.account; sp1.balance = se1; ]
              alice.account.balance == 10 } := by sol_chain
    _ ~[storageLocalDeclInitDrop]~>
        dl!{ { se1 := 10 } [ sp1 = alice.account; sp1.balance = se1; ] alice.account.balance == 10 } :=
      rfl
    _ ~*> dl![.box]{ { se1 := 10 } { sp1 := alice.account } { storage := save(storage, sp1.balance, se1) }
            alice.account.balance == 10 } := by sol_chain

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
seven-step derivation of the headline is the `calc` above, at the diamond and
the headline's postcondition. -/

example (d : dl!{ ⟨ alice.account.balance = 10; ⟩ alice.account.balance == 10 }
    ~*> dl!{ { se1 := 10 } { sp1 := alice.account } { storage := save(storage, sp1.balance, se1) }
            alice.account.balance == 10 }) (h : d.length = 7) :
    d = headline .diamond { fml := dl!{ alice.account.balance == 10 } } :=
  Fml.Steps.eq_of_length d _ (h.trans rfl)

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

-- `se1` and `sp1` are the fresh variables the rule declares
example : dl!{ ⟨ alice.account.balance = 10; ⟩ true }
    ~[storageFieldWrite_unfold_leftFst]~>
      dl!{ ⟨ uint se1 = 10; Account storage sp1 = alice.account; sp1.balance = se1; ⟩ true } :=
  rfl

/--
info: dl{ ⟨[ alice.age = v; ]⟩ φ }
    ~[storageFieldWriteSave]~> dl{ { storage := save(storage, alice.age, v) } ⟨[ ]⟩ φ } : Prop
-/
#guard_msgs in
variable (m : Modality) (φ : Post StandardExample) in
#check dl![m]{ ⟨[ alice.age = v; ]⟩ φ }
    ~[storageFieldWriteSave]~> dl![m]{ { storage := save(storage, alice.age, v) } ⟨[ ]⟩ φ }

/-! ## 8 · Where the modality matters

A revert, and the cover of a branch (`Premise.cover`, left by an `if`, a
`require`, an `assert`), are the only steps that look at the modality: under
`m` the lines stop in front of them, and the chain goes on after `cases m`.
Nothing after a split is written under `m`: its cover, and every fresh index
after it, are stuck on it. -/

section Modality
variable (m : Modality)

example : dl![m]{ ⟨[ x = 1; revert(); ]⟩ true } ~> dl![m]{ { x := 1 } ⟨[ revert(); ]⟩ true } := by
  sol_chain

/--
error: sol_chain: the line after
  dl{ { x := 1 } ⟨[ revert(); ]⟩ true }
depends on the modality m, through a `revert();` or a branch's cover: go on after `cases m`
-/
#guard_msgs in
example : dl![m]{ { x := 1 } ⟨[ revert(); ]⟩ true } ~> dl![m]{ { x := 1 } true } := by
  sol_chain

/--
error: the rule on
  dl{ ⟨[ revert(); ]⟩ true }
depends on its modality m (`revertBox`, `revertDiamond`): go on after `cases m`
-/
#guard_msgs in
example : dl![m]{ ⟨[ revert(); ]⟩ true } ~[revertBox]~> dl![.box]{ true } := rfl

/-- After `cases m`, each modality steps on. -/
example : ∃ ψ, dl![m]{ { x := 1 } ⟨[ revert(); ]⟩ true } ~> ψ := by
  cases m <;> exact ⟨_, by sol_chain⟩

/-- A `transfer` is a guard: the same under either modality, up to the revert
of its failing branch. -/
example : dl![m]{ ⟨[ to.transfer(x + 2); ]⟩ true }
    ~*> dl![m]{ { se1 := x + 2 }
          (((0 <= se1 ∧ se1 <= selfBalance) →
              { selfBalance := selfBalance - se1 ‖ net := store(net, at(to), net(to) - se1) } true) ∧
            (¬(0 <= se1 ∧ se1 <= selfBalance) → ⟨[ revert(); ]⟩ true)) } := by
  sol_chain

-- A `require` and an `if` are branches, whose cover depends on the modality.
/--
info:     dl{ ⟨[ require(true); x = 1; ]⟩ x = 1 }
  (the line after depends on the modality m, through a `revert();` or a branch's cover: go on after `cases m`)
-/
#guard_msgs in
#derivation dl![m]{ ⟨[ require(true); x = 1; ]⟩ x == 1 }

/--
info:     dl{ ⟨[ if (true) {x = 2;} else {x = 1;}; ]⟩ x = 1 }
  (the line after depends on the modality m, through a `revert();` or a branch's cover: go on after `cases m`)
-/
#guard_msgs in
#derivation dl![m]{ ⟨[ if (true) { x = 2; } else { x = 1; }; ]⟩ x == 1 }

end Modality

end Solidity.Examples.Chains
