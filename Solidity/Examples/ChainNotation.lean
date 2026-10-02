import Solidity.Calculus.Chains
import Solidity.Calculus.Close
import Solidity.Examples.Chains.Storage
import Solidity.Examples.Chains.Payment

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
postcondition `φ : Post C`.  The headline (§2, §4) is the printed trace, for
every `m` and `φ` (`Examples/Chains/Storage.lean`'s `BalanceWrite.chain`);
what is *proved valid* is its instance under the box (`Close.lean`: a write
under the diamond is stuck in a state without `alice`).

This file tests the notation, not the calculus: the worked examples are the
chains of `Examples/Chains/`, and are cited here, not drawn again.
-/

namespace Solidity.Examples.ChainNotation

local instance : InContract := ⟨StandardExample⟩

/-! ## 1 · One step: `~[r]~>` and `~>`

The first link of `Chains.Storage.AgeWrite.chain`, and the strategy's `~>` where its
rule is left unnamed (§3). -/

example : dl!{ ⟨ alice.age = v; ⟩ alice.age == v }
    ~[storageFieldWriteSave]~> dl!{ { storage := save(storage, alice.age, v) } ⟨⟩ alice.age == v } :=
  rfl

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

The headline (`Chains.Storage.BalanceWrite.chain`, from the statement to the
formula with its updates merged, for any modality `m` and postcondition `φ`),
as `#derivation` prints it: the rules' names, and their fresh variables. -/

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

/-- At a modality the formula names, `φ` alone is open. -/
example : dl!{ ⟨ alice.account.balance = 10; ⟩ φ }
    ~*> dl!{ { se1 := 10 } { sp1 := alice.account } { storage := save(storage, sp1.balance, se1) } φ } := by
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

/-! ## 4 · A chain is a proof

The headline, `Chains.Storage.BalanceWrite.chain` (a `calc`, for every modality `m`
and postcondition `φ`), proves its first line from its last
(`Fml.Leads.valid`).  Here under the box, where the write is valid, at the
postcondition the statement is written for. -/

theorem headline_valid : ⊨ dl!{ [ alice.account.balance = 10; ] alice.account.balance == 10 } :=
  (Chains.Storage.BalanceWrite.chain .box { fml := dl!{ alice.account.balance == 10 } }).valid
    (by sol_close)

/-- A box derivation's last line, written: an update with no modality under
it is judged at the box in `dl![.box]{ … }` (in `dl!{ … }`, at the diamond). -/
example : dl!{ [ alice.age = v; ] alice.age == v }
    ~*> dl![.box]{ { storage := save(storage, alice.age, v) } alice.age == v } :=
  calc dl!{ [ alice.age = v; ] alice.age == v }
    _ ~[storageFieldWriteSave]~> dl!{ { storage := save(storage, alice.age, v) } [ ] alice.age == v } := rfl
    _ ~> dl![.box]{ { storage := save(storage, alice.age, v) } alice.age == v } := rfl

/-! ## 5 · A branch

`ifElseSplit` makes the two goals one formula, `(c → …) ∧ ((c' → …) ∧ cover)`
(`Logic.lean`'s `Premise.fml`), the cover `⟨ revert(); ⟩ false ∨ c ∨ c'`
(`Premise.coverFml`: a stuck condition is owed under the diamond only).  The
chain runs the `then` branch, then the `else` branch.

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
              (true ≐ false → ⟨ x = 1; ⟩ balances[a] == x) ∧
              (⟨ revert(); ⟩ false ∨ true ≐ true ∨ true ≐ false)) }
    ~*> dl!{ { storage := save(storage, balances[a], 1) }
            ((true ≐ true → { x := 2 } balances[a] == x) ∧
              (true ≐ false → { x := 1 } balances[a] == x) ∧
              (⟨ revert(); ⟩ false ∨ true ≐ true ∨ true ≐ false)) } := by
  sol_chain

/-! ## 6 · The evidence is unique

A formula has one next line and one rule (`Fml.StepBy.unique`), so two
derivations of the same length between the same ends are one: every
two-step derivation of `alice.age = ageVal;` is `Chains.Storage.AgeWrite.chain`,
at the diamond and any postcondition. -/

example (φ : Post StandardExample)
    (d : dl!{ ⟨ alice.age = ageVal; ⟩ φ } ~*> dl!{ { storage := save(storage, alice.age, ageVal) } φ })
    (h : d.length = 2) : d = Chains.Storage.AgeWrite.chain .diamond φ :=
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

A revert is the only step that looks at the modality (`revertBox` leaves
`true`, `revertDiamond` `false`): under `m` the lines go through branches and
guards and stop in front of the first `revert();` the strategy steps, which
is where the calculus's traces part too, and the chain goes on after `cases m`.
A branch's cover is one formula under either modality,
`⟨[ revert(); ]⟩ false ∨ c ∨ c'` (`Premise.coverFml`). -/

section Modality
variable (m : Modality)

example : dl![m]{ ⟨[ x = 1; revert(); ]⟩ true } ~> dl![m]{ { x := 1 } ⟨[ revert(); ]⟩ true } := by
  sol_chain

/--
error: sol_chain: the line after
  dl{ { x := 1 } ⟨[ revert(); ]⟩ true }
depends on the modality m, through a `revert();` (`revertBox`, `revertDiamond`): go on after `cases m`
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

-- A revert in the `then` goal stops the lines before the `else` goal.
/--
info:     dl{ ⟨[ if (true) {revert();} else {x = 1;}; ]⟩ x = 1 }
  ~[ifElseSplit]~>
    dl{
  (true ≐ true → ⟨[ revert(); ]⟩ x = 1) ∧
    (true ≐ false → ⟨[ x = 1; ]⟩ x = 1) ∧ (⟨[ revert(); ]⟩ false ∨ true ≐ true ∨ true ≐ false) }
  (the line after depends on the modality m, through a `revert();` (`revertBox`, `revertDiamond`): go on after `cases m`)
-/
#guard_msgs in
#derivation dl![m]{ ⟨[ if (true) { revert(); } else { x = 1; }; ]⟩ x == 1 }

end Modality

-- A line holds no other Lean term than a modality and postconditions…
/--
error: sol_chain: n is free in the line: only a modality `m` and postconditions `φ : Post C` may be
  dl{ { y := ‹Term.lit (Semantics.PrimVal.int n)› } ⟨ x = 1; ⟩ true }
-/
#guard_msgs in
example (n : Int) : ∃ ψ, Fml.upd .diamond [.val (.user "y") (.lit (.int n))]
    dl!{ ⟨ x = 1; ⟩ true } ~> ψ := ⟨_, by sol_chain⟩

-- … and one modality.
/--
error: sol_chain: the line is under two modalities: take `cases` on one
  dl{ ⟨[ x = 1; ]⟩ true ∧ ⟨[ x = 2; ]⟩ true }
-/
#guard_msgs in
example (m m' : Modality) : ∃ ψ, Fml.and dl![m]{ ⟨[ x = 1; ]⟩ true } dl![m']{ ⟨[ x = 2; ]⟩ true }
    ~> ψ := ⟨_, by sol_chain⟩

/-! ## 9 · Past a finished goal

Once the first goal of a branch is done, `(c → {U} φ) ∧ …`, the step on the
next one asks `φ` whether a modality is left, which only `Post.inactive`
knows (`Chains.stepAtProof`): a `require`, an `assert` and an `if`, each to its
end, at a modality and over any postcondition.  (A `transfer` does too:
`Chains.Payment.TransferSum.box`.)  These are the calculus's traces: every
rule of a `require`, an `assert` and an `if` is the same under either modality,
the cover of the split included (`⟨[ revert(); ]⟩ false ∨ c ∨ c'`,
`Premise.coverFml`), so the lines are written once, up to the `revert();` of a
failing branch.  There the modalities part: after it the chain is one per
modality, `revertBox` to `true` and `revertDiamond` to `false`
(`Examples/Tactics/Revert.lean` proves the same programs by tactics).

The condition is a `bool` of the storage, `flags[a]`, which `se` stands for
once captured: `{ se1 := find(storage, flags[a]) }`. -/

section Past
variable (m : Modality) (φ : Post StandardExample)

/-- `revert();` ends the calculus's traces: under the box it closes to `true`,
whatever follows… -/
example : dl![.box]{ ⟨[ revert(); y = 1; ]⟩ φ } ~[revertBox]~> dl![.box]{ true } := rfl

/-- …and under the diamond to `false`. -/
example : dl!{ ⟨ revert(); y = 1; ⟩ φ } ~[revertDiamond]~> dl!{ false } := rfl

/-- The `requireSimple` trace: the condition captured and read, the
split, the goal where it holds run to its end; the goal where it fails is
left at its revert. -/
def requireTrace : dl![m]{ ⟨[ require(flags[a]); y = 1; ]⟩ φ }
    ~*> dl![m]{ { se1 := find(storage, flags[a]) }
          ((se1 ≐ true → { y := 1 } φ) ∧ (se1 ≐ false → ⟨[ revert(); y = 1; ]⟩ φ) ∧
            (⟨[ revert(); ]⟩ false ∨ se1 ≐ true ∨ se1 ≐ false)) } :=
  calc dl![m]{ ⟨[ require(flags[a]); y = 1; ]⟩ φ }
    _ ~[requireConditionCapture]~> dl![m]{ ⟨[ bool se1 = flags[a]; require(se1); y = 1; ]⟩ φ } := by
      sol_chain
    -- `localValueDeclInitDrop`, `storageIndexReadMappingFind`, `requireSimple`: the two
    -- lines between leave `se1` bound by an update in a statement, which `dl![m]{ … }`
    -- reads as a `uint` parameter (`Branch.lean`), so they are not written
    _ ~*> dl![m]{ { se1 := find(storage, flags[a]) }
          ((se1 ≐ true → ⟨[ y = 1; ]⟩ φ) ∧ (se1 ≐ false → ⟨[ revert(); y = 1; ]⟩ φ) ∧
            (⟨[ revert(); ]⟩ false ∨ se1 ≐ true ∨ se1 ≐ false)) } := by
      sol_chain
    _ ~*> dl![m]{ { se1 := find(storage, flags[a]) }
          ((se1 ≐ true → { y := 1 } φ) ∧ (se1 ≐ false → ⟨[ revert(); y = 1; ]⟩ φ) ∧
            (⟨[ revert(); ]⟩ false ∨ se1 ≐ true ∨ se1 ≐ false)) } := by
      sol_chain

/-- Under the box the failing goal closes: the trace, then `revertBox`. -/
example : dl![.box]{ ⟨[ require(flags[a]); y = 1; ]⟩ φ }
    ~*> dl![.box]{ { se1 := find(storage, flags[a]) }
          ((se1 ≐ true → { y := 1 } φ) ∧ (se1 ≐ false → true) ∧
            ([ revert(); ] false ∨ se1 ≐ true ∨ se1 ≐ false)) } :=
  calc dl![.box]{ ⟨[ require(flags[a]); y = 1; ]⟩ φ }
    _ ~*> dl![.box]{ { se1 := find(storage, flags[a]) }
          ((se1 ≐ true → { y := 1 } φ) ∧ (se1 ≐ false → [ revert(); y = 1; ] φ) ∧
            ([ revert(); ] false ∨ se1 ≐ true ∨ se1 ≐ false)) } := requireTrace .box φ
    _ ~[revertBox]~> dl![.box]{ { se1 := find(storage, flags[a]) }
          ((se1 ≐ true → { y := 1 } φ) ∧ (se1 ≐ false → true) ∧
            ([ revert(); ] false ∨ se1 ≐ true ∨ se1 ≐ false)) } := by
      sol_chain

/-- Under the diamond it leaves `false`: the condition must hold. -/
example : dl!{ ⟨ require(flags[a]); y = 1; ⟩ φ }
    ~*> dl!{ { se1 := find(storage, flags[a]) }
          ((se1 ≐ true → { y := 1 } φ) ∧ (se1 ≐ false → false) ∧
            (⟨ revert(); ⟩ false ∨ se1 ≐ true ∨ se1 ≐ false)) } :=
  (requireTrace .diamond φ).trans (by sol_chain)

/-- `assert` has `require`'s trace (the table's `assertSimple`). -/
def assertTrace : dl![m]{ ⟨[ assert(flags[a]); y = 1; ]⟩ φ }
    ~[assertConditionCapture]~> dl![m]{ ⟨[ bool se1 = flags[a]; assert(se1); y = 1; ]⟩ φ }
    ~*> dl![m]{ { se1 := find(storage, flags[a]) }
          ((se1 ≐ true → { y := 1 } φ) ∧ (se1 ≐ false → ⟨[ revert(); y = 1; ]⟩ φ) ∧
            (⟨[ revert(); ]⟩ false ∨ se1 ≐ true ∨ se1 ≐ false)) } := by
  sol_chain

/-- The `ifElseSplit` trace: both goals to their end, under `m`. -/
def ifTrace : dl![m]{ ⟨[ if (flags[a]) { y = 1; } else { y = 2; }; ]⟩ φ }
    ~[ifElseUnfold]~> dl![m]{ ⟨[ bool se1 = flags[a]; if (se1) { y = 1; } else { y = 2; }; ]⟩ φ }
    ~*> dl![m]{ { se1 := find(storage, flags[a]) }
          ((se1 ≐ true → ⟨[ y = 1; ]⟩ φ) ∧ (se1 ≐ false → ⟨[ y = 2; ]⟩ φ) ∧
            (⟨[ revert(); ]⟩ false ∨ se1 ≐ true ∨ se1 ≐ false)) }
    ~*> dl![m]{ { se1 := find(storage, flags[a]) }
          ((se1 ≐ true → { y := 1 } φ) ∧ (se1 ≐ false → { y := 2 } φ) ∧
            (⟨[ revert(); ]⟩ false ∨ se1 ≐ true ∨ se1 ≐ false)) } := by
  sol_chain

/-- A revert in the `else` branch: the lines stop at it, the `then` goal done. -/
def ifRevertTrace : dl![m]{ ⟨[ if (flags[a]) { y = 1; } else { revert(); }; ]⟩ φ }
    ~*> dl![m]{ { se1 := find(storage, flags[a]) }
          ((se1 ≐ true → { y := 1 } φ) ∧ (se1 ≐ false → ⟨[ revert(); ]⟩ φ) ∧
            (⟨[ revert(); ]⟩ false ∨ se1 ≐ true ∨ se1 ≐ false)) } := by
  sol_chain

-- In the `then` branch it stops them before the `else` goal: go on after `cases m`.
/--
error: sol_chain: the derivation of
  dl{ ⟨[ if (flags[a]) {revert();} else {y = 1;}; ]⟩ φ }
does not reach
  dl{
    { se1 := find(storage, flags[a]) }
      ((se1 ≐ true → true) ∧ (se1 ≐ false → { y := 1 } φ) ∧ (⟨[ revert(); ]⟩ false ∨ se1 ≐ true ∨ se1 ≐ false)) }
Its lines:
    dl{ ⟨[ if (flags[a]) {revert();} else {y = 1;}; ]⟩ φ }
  ~[ifElseUnfold]~>
    dl{ ⟨[ bool se1 = flags[a]; if (se1) {revert();} else {y = 1;}; ]⟩ φ }
  ~[localValueDeclInitDrop]~>
    dl{ ⟨[ se1 = flags[a]; if (se1) {revert();} else {y = 1;}; ]⟩ φ }
  ~[storageIndexReadMappingFind]~>
    dl{ { se1 := find(storage, flags[a]) } ⟨[ if (se1) {revert();} else {y = 1;}; ]⟩ φ }
  ~[ifElseSplit]~>
    dl{
  { se1 := find(storage, flags[a]) }
    ((se1 ≐ true → ⟨[ revert(); ]⟩ φ) ∧
        (se1 ≐ false → ⟨[ y = 1; ]⟩ φ) ∧ (⟨[ revert(); ]⟩ false ∨ se1 ≐ true ∨ se1 ≐ false)) }
  (the line after depends on the modality m, through a `revert();` (`revertBox`, `revertDiamond`): go on after `cases m`)
-/
#guard_msgs in
example : dl![m]{ ⟨[ if (flags[a]) { revert(); } else { y = 1; }; ]⟩ φ }
    ~*> dl![m]{ { se1 := find(storage, flags[a]) }
          ((se1 ≐ true → true) ∧ (se1 ≐ false → { y := 1 } φ) ∧
            (⟨[ revert(); ]⟩ false ∨ se1 ≐ true ∨ se1 ≐ false)) } := by
  sol_chain

/-- After `cases m`, each modality runs to the end. -/
example : ∃ ψ, Nonempty (dl![m]{ ⟨[ if (flags[a]) { revert(); } else { y = 1; }; ]⟩ φ } ~*> ψ) := by
  cases m <;> exact ⟨_, ⟨by sol_chain⟩⟩


-- Nested: past the done goal of the inner branch, its cover included, the
-- next step asks the goal `⟨[ x = 1; ]⟩ φ`, active whatever `φ` is.
/--
info:     dl{ ⟨[ if (true) {if (true) {x = 2;} else {x = 1;};} else {x = 1;}; ]⟩ φ }
  ~[ifElseSplit]~>
    dl{
  (true ≐ true → ⟨[ if (true) {x = 2;} else {x = 1;}; ]⟩ φ) ∧
    (true ≐ false → ⟨[ x = 1; ]⟩ φ) ∧ (⟨[ revert(); ]⟩ false ∨ true ≐ true ∨ true ≐ false) }
  ~[ifElseSplit]~>
    dl{
  (true ≐ true →
        (true ≐ true → ⟨[ x = 2; ]⟩ φ) ∧
          (true ≐ false → ⟨[ x = 1; ]⟩ φ) ∧ (⟨[ revert(); ]⟩ false ∨ true ≐ true ∨ true ≐ false)) ∧
    (true ≐ false → ⟨[ x = 1; ]⟩ φ) ∧ (⟨[ revert(); ]⟩ false ∨ true ≐ true ∨ true ≐ false) }
  ~[localValueAssign]~>
    dl{
  (true ≐ true →
        (true ≐ true → { x := 2 } ⟨[ ]⟩ φ) ∧
          (true ≐ false → ⟨[ x = 1; ]⟩ φ) ∧ (⟨[ revert(); ]⟩ false ∨ true ≐ true ∨ true ≐ false)) ∧
    (true ≐ false → ⟨[ x = 1; ]⟩ φ) ∧ (⟨[ revert(); ]⟩ false ∨ true ≐ true ∨ true ≐ false) }
  ~[emptyModality]~>
    dl{
  (true ≐ true →
        (true ≐ true → { x := 2 } φ) ∧
          (true ≐ false → ⟨[ x = 1; ]⟩ φ) ∧ (⟨[ revert(); ]⟩ false ∨ true ≐ true ∨ true ≐ false)) ∧
    (true ≐ false → ⟨[ x = 1; ]⟩ φ) ∧ (⟨[ revert(); ]⟩ false ∨ true ≐ true ∨ true ≐ false) }
  ~[localValueAssign]~>
    dl{
  (true ≐ true →
        (true ≐ true → { x := 2 } φ) ∧
          (true ≐ false → { x := 1 } ⟨[ ]⟩ φ) ∧ (⟨[ revert(); ]⟩ false ∨ true ≐ true ∨ true ≐ false)) ∧
    (true ≐ false → ⟨[ x = 1; ]⟩ φ) ∧ (⟨[ revert(); ]⟩ false ∨ true ≐ true ∨ true ≐ false) }
  ~[emptyModality]~>
    dl{
  (true ≐ true →
        (true ≐ true → { x := 2 } φ) ∧
          (true ≐ false → { x := 1 } φ) ∧ (⟨[ revert(); ]⟩ false ∨ true ≐ true ∨ true ≐ false)) ∧
    (true ≐ false → ⟨[ x = 1; ]⟩ φ) ∧ (⟨[ revert(); ]⟩ false ∨ true ≐ true ∨ true ≐ false) }
  ~[localValueAssign]~>
    dl{
  (true ≐ true →
        (true ≐ true → { x := 2 } φ) ∧
          (true ≐ false → { x := 1 } φ) ∧ (⟨[ revert(); ]⟩ false ∨ true ≐ true ∨ true ≐ false)) ∧
    (true ≐ false → { x := 1 } ⟨[ ]⟩ φ) ∧ (⟨[ revert(); ]⟩ false ∨ true ≐ true ∨ true ≐ false) }
  ~[emptyModality]~>
    dl{
  (true ≐ true →
        (true ≐ true → { x := 2 } φ) ∧
          (true ≐ false → { x := 1 } φ) ∧ (⟨[ revert(); ]⟩ false ∨ true ≐ true ∨ true ≐ false)) ∧
    (true ≐ false → { x := 1 } φ) ∧ (⟨[ revert(); ]⟩ false ∨ true ≐ true ∨ true ≐ false) }
-/
#guard_msgs in
#derivation dl![m]{ ⟨[ if (true) { if (true) { x = 2; } else { x = 1; } } else { x = 1; }; ]⟩ φ }

example : dl![m]{ ⟨[ if (true) { if (true) { x = 2; } else { x = 1; } } else { x = 1; }; ]⟩ φ }
    ~*> dl![m]{ (true ≐ true → (true ≐ true → { x := 2 } φ) ∧ (true ≐ false → { x := 1 } φ) ∧
            (⟨[ revert(); ]⟩ false ∨ true ≐ true ∨ true ≐ false)) ∧
          (true ≐ false → { x := 1 } φ) ∧ (⟨[ revert(); ]⟩ false ∨ true ≐ true ∨ true ≐ false) } := by
  sol_chain

end Past

end Solidity.Examples.ChainNotation
