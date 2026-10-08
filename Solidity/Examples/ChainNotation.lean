import Solidity.Calculus.Chains
import Solidity.Calculus.LastLine
import Solidity.Calculus.Close
import Solidity.Calculus.Core.LastLine
import Solidity.Calculus.Core.Surface
import Solidity.Examples.Chains.Storage
import Solidity.Examples.Chains.Payment

/-!
# Chains: `φ ~> ψ`, `φ ~[r]~> ψ`, `φ ~*> ψ`, `φ ~~> ψ`, and `calc`

A derivation, stated (`Calculus/Core/Chains.lean`): both ends written in
`dl!{ … }`, and in between as many lines as you like (mini-solkey's chain
examples).  The scoped calculus (`open scoped Solidity.Core.Surface`): a line
after the first is computed by the strategy, its text checked against the
computed line's erasure.

* `φ ~[r]~> ψ` — the rule `r` turns `φ` into `ψ`, as `#derivation` prints a
  line; a wrong `r` does not elaborate;
* `φ ~> ψ` — the strategy's step does;
* `φ ~*> ψ` — several steps;
* `φ ~*> φ₁ ~[r]~> φ₂ ~*> …` — a chain, every link holding; `sol_chain`;
* `φ ~~> ψ` — to prove `φ`, prove `ψ` (`Core.Fml.Leads`; past the program,
  where `ψ` is `Update.lean`'s line, `Core.Fml.LeadsE`): what a chain composes
  to, and how segments compose (`Fml.Leads.via`, `Fml.LeadsE.viaE`);
* `calc` — the same chain, one line per step, each with its reason, its line
  computed from the one before (`by sol_chain`).

Every line is a formula `dl!{ … }`: copy it from `#derivation` (`se1`, `sp1`
are the rules' fresh variables).  A line keeps two unknowns:
`dl![m]{ … }` reads it at a modality `m` (`⟨[ P ]⟩ ψ` is `P` under `m`, and
an update with no modality under it is judged at `m`, so a box derivation's
last line is `dl![.box]{ … }`), and a name where a formula stands is a
postcondition `φ : Core.Post C Γ`, at the context `Γ` it stands in (the
parameters a line reads and the locals its program declares, its fresh ones
dropped).  The headline (§2, §4) is the printed trace, for every `m` and `φ`
(`Examples/Chains/Storage.lean`'s `BalanceWrite.chain`); what is *proved
valid* is its instance under the box.

This file tests the notation, not the calculus: the worked examples are the
chains of `Examples/Chains/`, and are cited here, not drawn again.
-/

namespace Solidity.Examples.ChainNotation

open scoped Solidity.Core.Surface

local instance : InContract := ⟨StandardExample⟩

/-! ## 1 · One step: `~[r]~>` and `~>`

The write that `Chains.Storage.AgeWrite.chain`'s first link runs, and the strategy's `~>`
where its rule is left unnamed (§3). -/

example : dl!{ ⟨ alice.age = v; ⟩ alice.age == v }
    ~[storageFieldWriteSave]~> dl!{ { storage := save(storage, alice.age, v) } alice.age == v } :=
  rfl

-- The rule is checked: `storageRootWriteStore` writes a state variable, not a field.
/--
error: ~[storageRootWriteStore]~>: the rule for
  dl{ ∀ uint v; ⟨ alice.age = v; ⟩ find(storage, alice.age) = v }
is storageFieldWriteSave, not storageRootWriteStore
-/
#guard_msgs in
example : dl!{ ⟨ alice.age = v; ⟩ alice.age == v }
    ~[storageRootWriteStore]~> dl!{ { storage := save(storage, alice.age, v) } alice.age == v } := by
  sol_chain

-- So is the line: `sol_chain` shows the line written and the derivation it computed instead.
/--
error: sol_chain: the derivation of
  dl{ ∀ uint v; ⟨ alice.age = v; ⟩ find(storage, alice.age) = v }
does not reach
  dl!{ { storage := save(storage, alice.age, w) } alice.age == v }
Its lines:

  dl{ ∀ uint v; ⟨ alice.age = v; ⟩ find(storage, alice.age) = v }
  ~[storageFieldWriteSave]~>
  dl{ ∀ uint v; { storage := save(storage, alice.age, v) } find(storage, alice.age) = v }
-/
#guard_msgs in
example : dl!{ ⟨ alice.age = v; ⟩ alice.age == v }
    ~> dl!{ { storage := save(storage, alice.age, w) } alice.age == v } := by
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
variable (m : Modality) (φ : Core.Post StandardExample [])

/--
info:
  dl{ ⟨[ alice.account.balance = 10; ]⟩ φ }
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
  dl{ { se1 := 10 } { sp1 := alice.account } { storage := save(storage, sp1.balance, se1) } φ }
-/
#guard_msgs in
#derivation dl![m]{ ⟨[ alice.account.balance = 10; ]⟩ φ }

/-- At a modality the formula names, `φ` alone is open. -/
example : dl!{ ⟨ alice.account.balance = 10; ⟩ φ }
    ~*> dl!{ { se1 := 10 } { sp1 := alice.account } { storage := save(storage, sp1.balance, se1) } φ } := by
  sol_chain

/-- A step over `φ` needs its fresh index, which `rfl` cannot compute over `φ`, and `sol_chain`
proves it from `Core.Post.noFresh`.  (`se1` written, not declared, is a parameter, `∀ uint se1;`.) -/
example : dl![m]{ ⟨[ se1 = 10; Account storage sp1 = alice.account; sp1.balance = se1; ]⟩ φ }
    ~[localValueAssign]~>
      dl![m]{ { se1 := 10 } ⟨[ Account storage sp1 = alice.account; sp1.balance = se1; ]⟩ φ } := by
  sol_chain

-- A formula that is no `Post` may name a fresh variable, or have a modality.
/--
error: sol_chain: ψ is free in the line: only a modality `m` and postconditions `φ : Core.Post C Γ` may be
  dl{ ⟨[ alice.account.balance = 10; ]⟩ ψ }
-/
#guard_msgs in
example (ψ : Core.Fml StandardExample []) : dl![m]{ ⟨[ alice.account.balance = 10; ]⟩ ψ }
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

The headline's trace (`Chains.Storage.BalanceWrite.chain`, one chain term, for every modality
`m` and postcondition `φ`) proves its first line from its last.  Here under the box, where the
write is valid, at the postcondition the statement is written for: past the program the chain
goes on on the erasure (`Core.Fml.ViaE`), its last scoped line closed by `Core.Proves.close`
(`Core.Fml.ViaE.valid_close`), the erasure's last line by `sol_close`.  The chain keeps its
captures, which `sol_close` does not drop: `simplifyUpdate` drops them first. -/

theorem headline_valid : ⊨ dl!{ [ alice.account.balance = 10; ] alice.account.balance == 10 } := by
  refine (show dl!{ [ alice.account.balance = 10; ] alice.account.balance == 10 }
      ~*> dl![.box]{ { se1 := 10 } { sp1 := alice.account } { storage := save(storage, sp1.balance, se1) }
        alice.account.balance == 10 }
      ~[sequentialToParallel]~> dl![.box]{
        { se1 := 10 ‖ sp1 := alice.account ‖ storage := save(storage, alice.account.balance, 10) }
          alice.account.balance == 10 }
      ~[simplifyUpdate]~> dl![.box]{ { storage := save(storage, alice.account.balance, 10) }
        alice.account.balance == 10 } by sol_chain).valid_close ?_
  show Solidity.Valid _
  dsimp only [Solidity.Fml.Via.last]
  sol_close

/-- A box derivation's last line, written: an update with no modality under
it is judged at the box in `dl![.box]{ … }` (in `dl!{ … }`, at the diamond).
In a `calc` each line after the first is computed from the line before when
its step is proved (`by sol_chain`), and checked against its text. -/
example : dl!{ [ alice.age = v; ] alice.age == v }
    ~*> dl![.box]{ { storage := save(storage, alice.age, v) } alice.age == v } :=
  calc dl!{ [ alice.age = v; ] alice.age == v }
    _ ~*> dl!{ [ alice.age = v; ] alice.age == v } := by sol_chain
    _ ~[storageFieldWriteSave]~> dl![.box]{ { storage := save(storage, alice.age, v) } alice.age == v } := by
      sol_chain

/-! ## 5 · A branch

`ifElseSplit` makes the two goals one formula, `(c → …) ∧ (c' → …)`
(`Calculus/Core/Fml.lean`'s `Premise.fml`), each branch's program ending at
its block's `}` (`core_item`).  The chain runs the `then` branch, then the
`else` branch. -/

example : dl!{ ⟨ balances[a] = 1; if (true) { x = 2; } else { x = 1; }; ⟩ balances[a] == x }
    ~> dl!{ { storage := save(storage, balances[a], 1) }
            ⟨ if (true) { x = 2; } else { x = 1; }; ⟩ balances[a] == x }
    ~[ifElseSplit]~>
        dl!{ { storage := save(storage, balances[a], 1) }
            ((true ≐ true → ⟨ x = 2; } ⟩ balances[a] == x) ∧
              (true ≐ false → ⟨ x = 1; } ⟩ balances[a] == x)) }
    ~*> dl!{ { storage := save(storage, balances[a], 1) }
            ((true ≐ true → { x := 2 } balances[a] == x) ∧
              (true ≐ false → { x := 1 } balances[a] == x)) } := by
  sol_chain

/-! ## 6 · The evidence is unique

A formula has one next line and fires one statement (`Core.Fml.StepBy.unique`),
so two derivations of the same length between the same ends are one: every
one-step derivation of the first link of `Chains.Storage.AgeWrite.chain`
(`alice.age = ageVal;` with `ageVal` 42) is `ageWrite`, at the diamond and
any postcondition. -/

/-- The first link of `Chains.Storage.AgeWrite.chain`, as data: `alice.age = ageVal;` with `ageVal`
42, the write, the program done. -/
def ageWrite (φ : Core.Post StandardExample [.val .uint]) :
    dl!{ { ageVal := 42 } ⟨ alice.age = ageVal; ⟩ φ }
    ~*> dl!{ { ageVal := 42 } { storage := save(storage, alice.age, ageVal) } φ } := by
  sol_chain

example (φ : Core.Post StandardExample [.val .uint])
    (d : dl!{ { ageVal := 42 } ⟨ alice.age = ageVal; ⟩ φ }
      ~*> dl!{ { ageVal := 42 } { storage := save(storage, alice.age, ageVal) } φ })
    (h : d.length = 1) : d = ageWrite φ :=
  Core.Fml.Steps.eq_of_length d _ (h.trans rfl)

/-- The strategy of `Calculus/Core/Step.lean` (`symex`) is a chain, of the same six steps. -/
example : (Core.Fml.Steps.ofSymex 200
    dl!{ ⟨ alice.account.balance = 10; ⟩ alice.account.balance == 10 }).length = 6 := by
  decide

/-! ## 7 · What is printed reads back -/

/--
info: dl{ ∀ uint v; ⟨ alice.age = v; ⟩ find(storage, alice.age) = v }
    ~[storageFieldWriteSave]~>
      dl{ ∀ uint v; { storage := save(storage, alice.age, v) } find(storage, alice.age) = v } : Prop
-/
#guard_msgs in
#check dl!{ ⟨ alice.age = v; ⟩ alice.age == v }
    ~[storageFieldWriteSave]~> dl!{ { storage := save(storage, alice.age, v) } alice.age == v }

-- A captured equality, inequality or product prints in KeY's text and reads back.
/--
info: dl{ ∀ uint b; ∀ uint a; { x := a == b ‖ y := a != b ‖ z := a * b } true } : Core.Fml StandardExample []
-/
#guard_msgs in
#check dl!{ { x := a == b ‖ y := a != b ‖ z := a * b } true }

example : dl!{ ⟨ bool c = a == b; uint d = a * b; ⟩ true }
    ~*> dl!{ { c := a == b } { d := a * b } true } := by
  sol_chain

-- `se1` and `sp1` are the fresh variables the rule declares
example : dl!{ ⟨ alice.account.balance = 10; ⟩ true }
    ~[storageFieldWrite_unfold_leftFst]~>
      dl!{ ⟨ uint se1 = 10; Account storage sp1 = alice.account; sp1.balance = se1; ⟩ true } :=
  rfl

/--
info: dl{ ∀ uint v; ⟨[ alice.age = v; ]⟩ φ }
    ~[storageFieldWriteSave]~> dl{ ∀ uint v; { storage := save(storage, alice.age, v) } φ } : Prop
-/
#guard_msgs in
variable (m : Modality) (φ : Core.Post StandardExample [.val .uint]) in
#check dl![m]{ ⟨[ alice.age = v; ]⟩ φ }
    ~[storageFieldWriteSave]~> dl![m]{ { storage := save(storage, alice.age, v) } φ }

/-! ## 8 · Where the modality matters

A revert is the only step that looks at the modality (`revertBox` leaves
`true`, `revertDiamond` `false`): under `m` the lines go through branches and
guards and stop in front of the first `revert();` the strategy steps, which
is where the calculus's traces part too, and the chain goes on after `cases m`. -/

section Modality
variable (m : Modality)

example : dl![m]{ ⟨[ x = 1; revert(); ]⟩ true } ~> dl![m]{ { x := 1 } ⟨[ revert(); ]⟩ true } := by
  sol_chain

/--
error: sol_chain: the line after
  dl{ { x := 1 } ⟨[ revert(); ]⟩ true }
depends on the modality m, through a rule that reads it (`revertBox`, `revertDiamond`, a loop's invariant rule): go on after `cases m`
-/
#guard_msgs in
example : dl![m]{ { x := 1 } ⟨[ revert(); ]⟩ true } ~> dl![m]{ { x := 1 } true } := by
  sol_chain

/--
error: sol_chain: the line after
  dl{ ⟨[ revert(); ]⟩ true }
depends on the modality m, through a rule that reads it (`revertBox`, `revertDiamond`, a loop's invariant rule): go on after `cases m`
-/
#guard_msgs in
example : dl![m]{ ⟨[ revert(); ]⟩ true } ~[revertBox]~> dl![.box]{ true } := by
  sol_chain

/-- After `cases m`, each modality steps on. -/
example : ∃ ψ, dl![m]{ { x := 1 } ⟨[ revert(); ]⟩ true } ~> ψ := by
  cases m <;> exact ⟨_, by sol_chain⟩

-- A revert in the `then` goal stops the lines before the `else` goal.
/--
info:
  dl{ ∀ uint x; ⟨[ if (true) {revert();} else {x = 1;}; ]⟩ x = 1 }
  ~[ifElseSplit]~>
  dl{ ∀ uint x; (true ≐ true → ⟨[ revert(); } ]⟩ x = 1) ∧ (true ≐ false → ⟨[ x = 1; } ]⟩ x = 1) }
  (the line after depends on the modality m, through a rule that reads it (`revertBox`, `revertDiamond`, a loop's invariant rule): go on after `cases m`)
-/
#guard_msgs in
#derivation dl![m]{ ⟨[ if (true) { revert(); } else { x = 1; }; ]⟩ x == 1 }

end Modality

-- A line holds no other Lean term than a modality and postconditions…
/--
error: sol_chain: ψ₀ is free in the line: only a modality `m` and postconditions `φ : Core.Post C Γ` may be
  dl{ ψ₀ ∧ (∀ uint x; ⟨ x = 1; ⟩ true) }
-/
#guard_msgs in
example (ψ₀ : Core.Fml StandardExample []) : ∃ ψ, Core.Fml.and ψ₀ dl!{ ⟨ x = 1; ⟩ true } ~> ψ :=
  ⟨_, by sol_chain⟩

-- … and one modality.
/--
error: sol_chain: the line is under two modalities: take `cases` on one
  dl{ (∀ uint x; ⟨[ x = 1; ]⟩ true) ∧ (∀ uint x; ⟨[ x = 2; ]⟩ true) }
-/
#guard_msgs in
example (m m' : Modality) : ∃ ψ, Core.Fml.and dl![m]{ ⟨[ x = 1; ]⟩ true } dl![m']{ ⟨[ x = 2; ]⟩ true }
    ~> ψ := ⟨_, by sol_chain⟩

/-! ## 9 · Past a finished goal

Once the first goal of a branch is done, `(c → {U} φ) ∧ …`, the step on the
next one asks `φ` whether a modality is left, which only `Core.Post.inactive`
knows: a `require`, an `assert` and an `if`, each to its end, at a modality
and over any postcondition.  These are the calculus's traces: every rule of a
`require`, an `assert` and an `if` is the same under either modality, so the
lines are written once, up to the `revert();` of a failing branch.  There the
modalities part: after it the chain is one per modality, `revertBox` to
`true` and `revertDiamond` to `false` (`Examples/Tactics/Revert.lean` proves
the same programs by tactics).

The condition is a `bool` of the storage, `flags[a]`, which `se` stands for
once captured: `{ se1 := find(storage, flags[a]) }`.  The postcondition
stands where the parameters `y` and `a` are in scope. -/

section Past
variable (m : Modality) (φ : Core.Post StandardExample [.val .uint, .val .uint])

/-- `revert();` ends the calculus's traces: under the box it closes to `true`,
whatever follows… -/
example (φ : Core.Post StandardExample [.val .uint]) :
    dl![.box]{ ⟨[ revert(); y = 1; ]⟩ φ } ~[revertBox]~> dl![.box]{ true } := by
  sol_chain

/-- …and under the diamond to `false`. -/
example (φ : Core.Post StandardExample [.val .uint]) :
    dl!{ ⟨ revert(); y = 1; ⟩ φ } ~[revertDiamond]~> dl!{ false } := by
  sol_chain

/-- The `requireSimple` trace: the condition captured and read, the
split, the goal where it holds run to its end; the goal where it fails is
left at its revert. -/
def requireTrace : dl![m]{ ⟨[ require(flags[a]); y = 1; ]⟩ φ }
    ~*> dl![m]{ { se1 := find(storage, flags[a]) }
          ((se1 ≐ true → { y := 1 } φ) ∧ (se1 ≐ false → ⟨[ revert(); y = 1; ]⟩ φ)) } :=
  calc dl![m]{ ⟨[ require(flags[a]); y = 1; ]⟩ φ }
    _ ~[requireConditionCapture]~> dl![m]{ ⟨[ bool se1 = flags[a]; require(se1); y = 1; ]⟩ φ } := by
      sol_chain
    -- `localValueDeclInitDrop`, `storageIndexReadMappingFind`, `requireSimple`: the two
    -- lines between leave `se1` bound by an update in a statement, which `dl![m]{ … }`
    -- reads as a `uint` parameter (`Branch.lean`), so they are not written
    _ ~*> dl![m]{ { se1 := find(storage, flags[a]) }
          ((se1 ≐ true → ⟨[ y = 1; ]⟩ φ) ∧ (se1 ≐ false → ⟨[ revert(); y = 1; ]⟩ φ)) } := by
      sol_chain
    _ ~*> dl![m]{ { se1 := find(storage, flags[a]) }
          ((se1 ≐ true → { y := 1 } φ) ∧ (se1 ≐ false → ⟨[ revert(); y = 1; ]⟩ φ)) } := by
      sol_chain

/-- Under the box the failing goal closes: the trace, then `revertBox`. -/
example : dl![.box]{ ⟨[ require(flags[a]); y = 1; ]⟩ φ }
    ~*> dl![.box]{ { se1 := find(storage, flags[a]) }
          ((se1 ≐ true → { y := 1 } φ) ∧ (se1 ≐ false → true)) } :=
  (requireTrace .box φ).trans (by sol_chain)

/-- Under the diamond it leaves `false`: the condition must hold. -/
example : dl!{ ⟨ require(flags[a]); y = 1; ⟩ φ }
    ~*> dl!{ { se1 := find(storage, flags[a]) }
          ((se1 ≐ true → { y := 1 } φ) ∧ (se1 ≐ false → false)) } :=
  (requireTrace .diamond φ).trans (by sol_chain)

/-- `assert` checks instead (the table's `assertSimple`, KeY's): the rest
with the condition assumed, and the condition itself, under either modality —
no revert, so no goal the box closes. -/
theorem assertTrace : dl![m]{ ⟨[ assert(flags[a]); y = 1; ]⟩ φ }
    ~[assertConditionCapture]~> dl![m]{ ⟨[ bool se1 = flags[a]; assert(se1); y = 1; ]⟩ φ }
    ~*> dl![m]{ { se1 := find(storage, flags[a]) }
          ((se1 ≐ true → { y := 1 } φ) ∧ se1 ≐ true) } := by
  sol_chain

/-- A split behind a stack of updates, under `m`: the overflow of `Chains.CheckedArithmetic`, the lines
its box and diamond chains share, up to the revert where the two modalities part. -/
example (φ : Core.Post StandardExample [.val .uint]) : dl![m]{ ⟨[ uint8 x = 250; x += 10; ]⟩ φ }
    ~*> dl![m]{ { x := 250 } ⟨[ x += 10; require(x <= 255); ]⟩ φ }
    ~[localOpAssign]~> dl![m]{ { x := 250 } { x := x + 10 } ⟨[ require(x <= 255); ]⟩ φ }
    ~*> dl![m]{ { x := 250 } { x := x + 10 } { se1 := x <= 255 }
          ((se1 ≐ true → φ) ∧ (se1 ≐ false → ⟨[ revert(); ]⟩ φ)) } := by
  sol_chain

/-- The `ifElseSplit` trace: both goals to their end, under `m`. -/
theorem ifTrace : dl![m]{ ⟨[ if (flags[a]) { y = 1; } else { y = 2; }; ]⟩ φ }
    ~[ifElseUnfold]~> dl![m]{ ⟨[ bool se1 = flags[a]; if (se1) { y = 1; } else { y = 2; }; ]⟩ φ }
    ~*> dl![m]{ { se1 := find(storage, flags[a]) }
          ((se1 ≐ true → ⟨[ y = 1; } ]⟩ φ) ∧ (se1 ≐ false → ⟨[ y = 2; } ]⟩ φ)) }
    ~*> dl![m]{ { se1 := find(storage, flags[a]) }
          ((se1 ≐ true → { y := 1 } φ) ∧ (se1 ≐ false → { y := 2 } φ)) } := by
  sol_chain

/-- A revert in the `else` branch: the lines stop at it, the `then` goal done. -/
def ifRevertTrace : dl![m]{ ⟨[ if (flags[a]) { y = 1; } else { revert(); }; ]⟩ φ }
    ~*> dl![m]{ { se1 := find(storage, flags[a]) }
          ((se1 ≐ true → { y := 1 } φ) ∧ (se1 ≐ false → ⟨[ revert(); } ]⟩ φ)) } := by
  sol_chain

-- In the `then` branch it stops them before the `else` goal: go on after `cases m`.
/--
error: sol_chain: the derivation of
  dl{ ∀ uint y; ∀ uint a; ⟨[ if (flags[a]) {revert();} else {y = 1;}; ]⟩ φ }
does not reach
  dl![m]{ { se1 := find(storage, flags[a]) } ((se1 ≐ true → true) ∧ (se1 ≐ false → { y := 1 } φ)) }
Its lines:

  dl{ ∀ uint y; ∀ uint a; ⟨[ if (flags[a]) {revert();} else {y = 1;}; ]⟩ φ }
  ~[ifElseUnfold]~>
  dl{ ∀ uint y; ∀ uint a; ⟨[ bool se1 = flags[a]; if (se1) {revert();} else {y = 1;}; ]⟩ φ }
  ~[localValueDeclInitDrop]~>
  dl{ ∀ uint y; ∀ uint a; ⟨[ se1 = flags[a]; if (se1) {revert();} else {y = 1;}; ]⟩ φ }
  ~[storageIndexReadMappingFind]~>
  dl{ ∀ uint y; ∀ uint a; { se1 := find(storage, flags[a]) } ⟨[ if (se1) {revert();} else {y = 1;}; ]⟩ φ }
  ~[ifElseSplit]~>
  dl{
    ∀ uint y;
      ∀ uint a;
        { se1 := find(storage, flags[a]) } ((se1 ≐ true → ⟨[ revert(); } ]⟩ φ) ∧ (se1 ≐ false → ⟨[ y = 1; } ]⟩ φ)) }
  (the line after depends on the modality m, through a rule that reads it (`revertBox`, `revertDiamond`, a loop's invariant rule): go on after `cases m`)
-/
#guard_msgs in
example : dl![m]{ ⟨[ if (flags[a]) { revert(); } else { y = 1; }; ]⟩ φ }
    ~*> dl![m]{ { se1 := find(storage, flags[a]) }
          ((se1 ≐ true → true) ∧ (se1 ≐ false → { y := 1 } φ)) } := by
  sol_chain

/-- After `cases m`, each modality runs to the end. -/
example : ∃ ψ, Nonempty (dl![m]{ ⟨[ if (flags[a]) { revert(); } else { y = 1; }; ]⟩ φ } ~*> ψ) := by
  cases m <;> exact ⟨_, ⟨by sol_chain⟩⟩

-- Nested: past the done goal of the inner branch, the next step asks the goal
-- `⟨[ x = 1; } ]⟩ φ`, active whatever `φ` is.
example (φ : Core.Post StandardExample [.val .uint]) :
    dl![m]{ ⟨[ if (true) { if (true) { x = 2; } else { x = 1; } } else { x = 1; }; ]⟩ φ }
    ~*> dl![m]{ (true ≐ true → (true ≐ true → { x := 2 } φ) ∧ (true ≐ false → { x := 1 } φ)) ∧
          (true ≐ false → { x := 1 } φ) } := by
  sol_chain

end Past

/-! ## A chain ends

`#last_line chain` (`Calculus/Core/LastLine.lean`): the chain's end is a last line — no
program left, one parallel update in front of each goal, and no rewrite `~=>`
tries still applies to it.  Silent where it is; a stack of updates and an
unresolved read are reported with the rewrite that goes on. -/

section Ends
variable (m : Modality) (φ : Core.Post StandardExample [.val .uint])

#guard_msgs in
#last_line Chains.Storage.AgeWriteRead.chain

/-- `alice.age = 42; uint x = alice.age;`, stopped at the stack the program leaves. -/
def stacked : dl![m]{ ⟨[ alice.age = 42; uint x = alice.age; ]⟩ φ }
    ~*> dl![m]{ { storage := save(storage, alice.age, 42) } { x := find(storage, alice.age) } φ } := by
  sol_chain

/--
error: #last_line: stacked does not end at a last line:
  dl{ { storage := save(storage, alice.age, 42) } { x := find(storage, alice.age) } φ }
2 updates stand in front of
  ↑φ
(one parallel update does: `~[sequentialToParallel]~>`)
sequentialToParallel still applies (under either modality), and gives
  dl{ { storage := save(storage, alice.age, 42) ‖ x := find(save(storage, alice.age, 42), alice.age) } φ }
-/
#guard_msgs in
#last_line stacked

/-- The stack merged, the read of the write not yet resolved: `~~>` past the program
(`Core.Fml.LeadsE`), its last line `Update.lean`'s. -/
theorem unresolved : dl![m]{ ⟨[ alice.age = 42; uint x = alice.age; ]⟩ φ }
    ~~> dl![m]{ { storage := save(storage, alice.age, 42) ‖
          x := find(save(storage, alice.age, 42), alice.age) } φ } := by
  sol_chain

/-! A chain term ends at its last line; a long one is cut into segments, the
second starting where the first ends, composed by `Core.Fml.LeadsE.viaE` (by
`Core.Fml.Leads.via` where both are scoped). -/

/-- `uint x = alice.age;` over `alice.age` at `42`: the program and the merge. -/
theorem readSeg :
    dl![m]{ { storage := save(storage, alice.age, 42) } ⟨[ uint x = alice.age; ]⟩ φ }
    ~*> dl![m]{ { storage := save(storage, alice.age, 42) } { x := find(storage, alice.age) } φ }
    ~[sequentialToParallel]~> dl![m]{ { storage := save(storage, alice.age, 42) ‖
          x := find(save(storage, alice.age, 42), alice.age) } φ } := by
  sol_chain

/-- The read of the write resolved a member at a time. -/
theorem resolveSeg :
    dl![m]{ { storage := save(storage, alice.age, 42) ‖
          x := find(save(storage, alice.age, 42), alice.age) } φ }
    ~[findMemberCons]~> dl![m]{ { storage := save(storage, alice.age, 42) ‖
          x := find(select(save(storage, alice.age, 42), alice), age) } φ }
    ~[selectOnSaveMember]~> dl![m]{ { storage := save(storage, alice.age, 42) ‖
          x := find(save(select(storage, alice), age, 42), age) } φ }
    ~[findOnSave]~> dl![m]{ { storage := save(storage, alice.age, 42) ‖ x := 42 } φ } := by
  sol_chain

/-- The two segments composed. -/
theorem composed :
    dl![m]{ { storage := save(storage, alice.age, 42) } ⟨[ uint x = alice.age; ]⟩ φ }
    ~~> dl![m]{ { storage := save(storage, alice.age, 42) ‖ x := 42 } φ } :=
  (readSeg ..).leads.viaE (resolveSeg ..)

#guard_msgs in
#last_line resolveSeg

/-! `sol_chain?` writes a `~~>` out as the chain it is, and `sol_rws?` names the rewrites
from one line to another (`Calculus/Core/ChainGen.lean`). -/

/--
info: Try this:
  exact Solidity.Core.Fml.ViaE.leads (show cdl![m]{ { storage := save(storage, alice.age, 42) } ⟨[ uint x = alice.age; ]⟩ φ }
        ~*> cdl![m]{ { storage := save(storage, alice.age, 42) } { x := find(storage, alice.age) } φ }
        ~[sequentialToParallel]~> cdl![m]{ { storage := save(storage, alice.age, 42) ‖ x := find(save(storage, alice.age, 42), alice.age) } φ }
        ~[findOnSave]~> cdl![m]{ { storage := save(storage, alice.age, 42) ‖ x := 42 } φ } by sol_chain)
-/
#guard_msgs in
example : dl![m]{ { storage := save(storage, alice.age, 42) } ⟨[ uint x = alice.age; ]⟩ φ }
    ~~> dl![m]{ { storage := save(storage, alice.age, 42) ‖ x := 42 } φ } := by
  sol_chain?

/--
info: Try this:
  sol_rws [findOnSave]
-/
#guard_msgs in
example : dl![m]{ { storage := save(storage, alice.age, 42) ‖
          x := find(save(storage, alice.age, 42), alice.age) } φ }
    ~~> dl![m]{ { storage := save(storage, alice.age, 42) ‖ x := 42 } φ } := by
  sol_rws?

end Ends

end Solidity.Examples.ChainNotation
