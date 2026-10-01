import Solidity.Calculus.Chains
import Solidity.Calculus.Rewrite
import Solidity.Examples.ExampleNames

/-!
# The lines after the program, as chain links

Past the last statement a worked example keeps going: the
updates the program left merge into one parallel update, its right-hand
sides substituted, dead captures go, the update is
applied, and Theory laws read the terms down to values.  Each such line is a
link `~[r]~>` of a chain (`Calculus/Chains.lean`), `r` the rule KeY names
(`sequentialToParallel`, `simplifyUpdate`, `applyStorageBox`, …) or the law
(`findOnSave`); the rewrite behind it is `Calculus/ChainRewrites.lean`'s,
and a chain with one composes to `~~>`, a proof of its first line from its
last (`Fml.Leads.valid`).

* §1 — the headline as the calculus draws it, for any
  modality `m` and postcondition `φ`, down to its last line, and on to the
  write alone (`headlineWrite`), the captures dropped;
* §2 — on to the value under the box: `simplifyUpdate`, `applyStorageBox`,
  `findOnSave`, and `⊨`;
* §3 — `alice.age = 42; uint x = alice.age;` read back two ways: the law in
  the update's right-hand side, and the update applied
  first, then the law (`SelectOnSaveConsr.ageWriteReadKeY`'s order); and the
  headline's write read back;
* §4 — a rebound alias: the overwritten capture dropped, as the printed line
  has it;
* §5 — what is refused, and what is printed.

The traces picked up: `StorageSteps.deepFieldWrite` to its last line
(`headlineNamed`, `headlineWrite`) and read back (`headlineValue`, `readBackValue`),
`SelectOnSaveConsr.ageWriteReadKeY` (`ageWriteReadKeYValue`;
`ageWriteReadValue` in the printed order), and
`StorageSteps.localRebindThenWrite`'s aliases (`localRebindLastLine`).

**Which rewrite.**  A name stands for a rule at any position of the update
spine, and a law at any instance; the elaborator takes the first that gives
the line written (with the line left `_`, the first that applies:
`sequentialToParallel` then merges the whole spine).  Over `m` and `φ` a
rewrite must compute without them.  The merges do.  `simplifyUpdate` asks
`φ` only whether it reads a fresh variable, which `Post.noFresh` denies, so
it drops the rules' captures (`pv`, `acc`, `se1`) over `φ` by `sol_chain`,
not `rfl`; a user variable `φ` may read stays.  `applyOnRigidBox` asks `m`
nothing where the update cannot halt; `applyStorageBox`, `applyOnRigidBox`
of an update that may halt, and a law in an update's right-hand side are the
box's (a halting update makes the box line true), written after `cases m`.
An update `simplifyUpdate` empties goes with it (KeY's `applySkip`), since
`dl!{}` has no spelling for `skip`.

**In a `calc`** a step's line before is `_` when its arrow is read, so the
rewrite the arrow names (its label) is found only once the step is
elaborated, after its proof: a rewrite step is proved `by sol_chain` or
`by rfl`, which run after it, not by the term `rfl`, which meets the label
unknown.  A rule of the strategy has no such label: `Fml.StepBy` computes
its rule from the line by unification.  A rewrite's cannot be so computed,
since a law is any theorem stating a `TermTaclet`, which no function
enumerates.
-/

namespace Solidity.Examples.ChainRewrites

local instance : InContract := ⟨StandardExample⟩

/-! ## 1 · The headline

`alice.account.balance = 10;` unfolds (Step 2), runs to the two captures,
which are shown merged (the `⇝*` line), writes, and ends: the write
merges into the captures, its right-hand side substituted — the printed last
line, in the printed names for the rules' fresh variables (`pv`, `acc` for
`se1`, `sp1`). -/

section Headline
variable (m : Modality) (φ : Post StandardExample)

section ExampleNames

local instance : FreshNames := .ofTable ExampleNames.Headline.names

/-- `alice.account.balance = 10;`, for every modality and postcondition: the
printed trace, line by line, in its names `pv` and `acc`
(`ExampleNames.Headline.names`). -/
theorem headlineNamed :
    dl![m]{ ⟨[ alice.account.balance = 10; ]⟩ φ }
    ~~> dl![m]{ { pv := 10 ‖ acc := alice.account ‖ storage := save(storage, alice.account.balance, 10) } φ } :=
  calc dl![m]{ ⟨[ alice.account.balance = 10; ]⟩ φ }
    _ ~[storageFieldWrite_unfold_leftFst]~>
        dl![m]{ ⟨[ uint pv = 10; Account storage acc = alice.account; acc.balance = pv; ]⟩ φ } := by
      sol_chain
    _ ~*> dl![m]{ { pv := 10 } { acc := alice.account } ⟨[ acc.balance = pv; ]⟩ φ } := by sol_chain
    _ ~[sequentialToParallel]~>
        dl![m]{ { pv := 10 ‖ acc := alice.account } ⟨[ acc.balance = pv; ]⟩ φ } := by sol_chain
    _ ~[storageFieldWriteSave]~>
        dl![m]{ { pv := 10 ‖ acc := alice.account } { storage := save(storage, acc.balance, pv) } ⟨[ ]⟩ φ } :=
      rfl
    _ ~[emptyModality]~>
        dl![m]{ { pv := 10 ‖ acc := alice.account } { storage := save(storage, acc.balance, pv) } φ } := rfl
    _ ~[sequentialToParallel]~>
        dl![m]{ { pv := 10 ‖ acc := alice.account ‖ storage := save(storage, alice.account.balance, 10) } φ } := by
      sol_chain

/-- `alice.account.balance = 10;` past the printed last line, for every
modality and postcondition: `φ` names no fresh variable (`Post.noFresh`), so
it reads neither `pv` nor `acc`, and `simplifyUpdate` drops both, leaving the
write.  The printed trace stops at the merged line; KeY goes on so. -/
theorem headlineWrite :
    dl![m]{ ⟨[ alice.account.balance = 10; ]⟩ φ }
    ~~> dl![m]{ { storage := save(storage, alice.account.balance, 10) } φ } :=
  calc dl![m]{ ⟨[ alice.account.balance = 10; ]⟩ φ }
    _ ~~> dl![m]{ { pv := 10 ‖ acc := alice.account ‖ storage := save(storage, alice.account.balance, 10) } φ } :=
      headlineNamed m φ
    _ ~[simplifyUpdate]~> dl![m]{ { storage := save(storage, alice.account.balance, 10) } φ } := by
      sol_chain

end ExampleNames

/-- The three updates `headline` (`Examples/Chains.lean`) ends with merge in one
link: the whole spine, the innermost pair first. -/
example : dl![m]{ { se1 := 10 } { sp1 := alice.account } { storage := save(storage, sp1.balance, se1) } φ }
    ~[sequentialToParallel]~>
      dl![m]{ { se1 := 10 ‖ sp1 := alice.account ‖ storage := save(storage, alice.account.balance, 10) } φ } :=
  rfl

/-- The line written picks the pair: here the innermost alone, the write
merged with the alias. -/
example : dl![m]{ { se1 := 10 } { sp1 := alice.account } { storage := save(storage, sp1.balance, se1) } φ }
    ~[sequentialToParallel]~>
      dl![m]{ { se1 := 10 } { sp1 := alice.account ‖ storage := save(storage, alice.account.balance, se1) } φ } :=
  rfl

/-- A chain of both kinds, not in a `calc`. -/
example : dl![m]{ { se1 := 10 } { sp1 := alice.account } ⟨[ sp1.balance = se1; ]⟩ φ }
    ~[sequentialToParallel]~> dl![m]{ { se1 := 10 ‖ sp1 := alice.account } ⟨[ sp1.balance = se1; ]⟩ φ }
    ~*> dl![m]{ { se1 := 10 ‖ sp1 := alice.account } { storage := save(storage, sp1.balance, se1) } φ }
    ~[sequentialToParallel]~>
      dl![m]{ { se1 := 10 ‖ sp1 := alice.account ‖ storage := save(storage, alice.account.balance, 10) } φ } := by
  sol_chain

/-- `y = 3;` applied to a first-order postcondition, under either modality:
`{ y := 3 }` cannot halt (`applyOnRigid`, an equivalence). -/
example : dl![m]{ { y := 3 } y ≐ 3 } ~[applyOnRigid]~> dl!{ 3 ≐ 3 } := rfl

/-- `applyOnRigidBox` too applies under `m` where the update cannot halt. -/
example : dl![m]{ { y := 3 } y ≐ 3 } ~[applyOnRigidBox]~> dl!{ 3 ≐ 3 } := rfl

/-- A capture dropped over `φ`, and the update it empties with it (KeY's
`applySkip`): the line after has no `{}`. -/
example : dl![m]{ { se1 := 10 } φ } ~[simplifyUpdate]~> dl!{ φ } := by sol_chain

/-- A capture dropped over `φ` behind a user variable, which stays: `φ` may
read `x`. -/
example : dl![m]{ { x := 1 ‖ se1 := 10 } { sp1 := alice.account } φ }
    ~[simplifyUpdate]~> dl![m]{ { x := 1 ‖ se1 := 10 } φ } := by sol_chain

/-- Over a concrete postcondition a user variable it does not read goes too,
and the update it empties: `{ x := 10 } y ≐ 1 ⇝ y ≐ 1`. -/
example : dl![m]{ { x := 10 } { y := 1 } y ≐ 1 } ~[simplifyUpdate]~> dl![m]{ { y := 1 } y ≐ 1 } := rfl

example : dl![m]{ { x := 10 } y ≐ 1 } ~[simplifyUpdate]~> dl!{ y ≐ 1 } := rfl

end Headline

/-! ## 2 · To the value, under the box

The printed last line under the box, `simplifyUpdate` (`se1` and `sp1` are
read no more), the storage write applied (`applyStorageBox`), and
`findOnSave` reading the write back: `10 ≐ 10`.  The postcondition is `≐`,
KeY's `=`; with `==` the `defined(…)` of the read stays, which the law does
not touch (`headlineEqD`), and which applying the write would make false
where it halts. -/

/-- `alice.account.balance = 10;` under the box, from the statement to its value. -/
theorem headlineValueChain :
    dl!{ [ alice.account.balance = 10; ] alice.account.balance ≐ 10 } ~~> dl!{ 10 ≐ 10 } :=
  calc dl!{ [ alice.account.balance = 10; ] alice.account.balance ≐ 10 }
    _ ~~> dl![.box]{ { se1 := 10 ‖ sp1 := alice.account ‖ storage := save(storage, alice.account.balance, 10) }
          alice.account.balance ≐ 10 } :=
      headlineNamed .box { fml := dl!{ alice.account.balance ≐ 10 } }
    _ ~[simplifyUpdate]~>
        dl![.box]{ { storage := save(storage, alice.account.balance, 10) } alice.account.balance ≐ 10 } := by
      sol_chain
    _ ~[applyStorageBox]~>
        dl!{ find(save(storage, alice.account.balance, 10), alice.account.balance) ≐ 10 } := by sol_chain
    _ ~[findOnSave]~> dl!{ 10 ≐ 10 } := by rfl

/-- `alice.account.balance = 10;` reads back `10`: the chain is a proof. -/
theorem headlineValue : ⊨ dl!{ [ alice.account.balance = 10; ] alice.account.balance ≐ 10 } :=
  headlineValueChain.valid fun _ => Theory.StValue.Equiv.refl _

/-- `alice.account.balance = 10;` against `==`: the law rewrites the
equation, not the `defined(…)` beside it. -/
def headlineEqD :
    dl![.box]{ { storage := save(storage, alice.account.balance, 10) } alice.account.balance == 10 }
    ~[applyStorageBox]~>
      dl!{ defined(find(save(storage, alice.account.balance, 10), alice.account.balance)) ∧ defined(10) ∧
        find(save(storage, alice.account.balance, 10), alice.account.balance) ≐ 10 }
    ~[findOnSave]~>
      dl!{ defined(find(save(storage, alice.account.balance, 10), alice.account.balance)) ∧ defined(10) ∧
        10 ≐ 10 } := by
  sol_chain

/-! ## 3 · A law in an update's right-hand side

`alice.age = 42; uint x = alice.age;`, against `x ≐ 42`.  Two orders from
the merged line:

* `ageWriteReadValue`, the in-update reading (`Examples/Theory.lean`):
  `findOnSave` inside the update (onto a literal, so the rewrite of a box
  update's right-hand side, `Proves.updRw`), then the update applied
  (`applyOnRigidBox`: `x ≐ 42` reads no storage);
* `ageWriteReadKeYValue`, `ageWriteReadKeY`'s order past its `eqDSplit`: the
  update applied first (`sol_apply_upd`), leaving
  `find(save(…), alice.age) ≐ 42`, then `findOnSave` on that equation.

Then the headline's write read back (`Theory.deepFieldWriteValue`'s
program): the write sits amid captures, and the spine merges inside out. -/

/-- `alice.age = 42; uint x = alice.age;` reads back `42`: the law in the update. -/
theorem ageWriteReadValue : ⊨ dl!{ [ alice.age = 42; uint x = alice.age; ] x ≐ 42 } :=
  Fml.Leads.valid (ψ := dl!{ 42 ≐ 42 }) (calc dl!{ [ alice.age = 42; uint x = alice.age; ] x ≐ 42 }
    _ ~*> dl![.box]{ { storage := save(storage, alice.age, 42) } { x := find(storage, alice.age) } x ≐ 42 } := by
      sol_chain
    _ ~[sequentialToParallel]~>
        dl![.box]{ { storage := save(storage, alice.age, 42) ‖ x := find(save(storage, alice.age, 42), alice.age) }
          x ≐ 42 } := by sol_chain
    _ ~[findOnSave]~> dl![.box]{ { storage := save(storage, alice.age, 42) ‖ x := 42 } x ≐ 42 } := by sol_chain
    _ ~[applyOnRigidBox]~> dl!{ 42 ≐ 42 } := by sol_chain)
    fun _ => Theory.StValue.Equiv.refl _

/-- `alice.age = 42; uint x = alice.age;` reads back `42`, in
`ageWriteReadKeY`'s order: merge, apply, then the law. -/
theorem ageWriteReadKeYValue : ⊨ dl!{ [ alice.age = 42; uint x = alice.age; ] x ≐ 42 } :=
  Fml.Leads.valid (ψ := dl!{ 42 ≐ 42 }) (calc dl!{ [ alice.age = 42; uint x = alice.age; ] x ≐ 42 }
    _ ~*> _ := by sol_chain
    _ ~[sequentialToParallel]~> _ := by sol_chain
    _ ~[applyOnRigidBox]~> dl!{ find(save(storage, alice.age, 42), alice.age) ≐ 42 } := by sol_chain
    _ ~[findOnSave]~> dl!{ 42 ≐ 42 } := by sol_chain)
    fun _ => Theory.StValue.Equiv.refl _

/-- `alice.account.balance = 10; uint x = alice.account.balance;` reads back
`10`: five updates merged inside out, the read over the write first
(`withSt`), then the captures; the law in the update; the update applied. -/
theorem readBackValue :
    ⊨ dl!{ [ alice.account.balance = 10; uint x = alice.account.balance; ] x ≐ 10 } :=
  Fml.Leads.valid (ψ := dl!{ 10 ≐ 10 })
    (calc dl!{ [ alice.account.balance = 10; uint x = alice.account.balance; ] x ≐ 10 }
    _ ~*> dl![.box]{ { se1 := 10 } { sp1 := alice.account } { storage := save(storage, sp1.balance, se1) }
            { sp2 := alice.account } { x := find(storage, sp2.balance) } x ≐ 10 } := by sol_chain
    _ ~[sequentialToParallel]~>
        dl![.box]{ { se1 := 10 ‖ sp1 := alice.account ‖ storage := save(storage, alice.account.balance, 10)
          ‖ sp2 := alice.account ‖ x := find(save(storage, alice.account.balance, 10), alice.account.balance) }
          x ≐ 10 } := by sol_chain
    _ ~[findOnSave]~>
        dl![.box]{ { se1 := 10 ‖ sp1 := alice.account ‖ storage := save(storage, alice.account.balance, 10)
          ‖ sp2 := alice.account ‖ x := 10 } x ≐ 10 } := by sol_chain
    _ ~[applyOnRigidBox]~> dl!{ 10 ≐ 10 } := by sol_chain)
    fun _ => Theory.StValue.Equiv.refl _

/-! ## 4 · A rebound alias

`Account storage acc = alice.account; acc = bob.account; acc.balance = 10;`
(`StorageSteps.localRebindThenWrite` without its first capture): the printed
line keeps `acc := bob.account` and drops the capture it overwrites.
Dropping an overwritten element needs nothing of the postcondition, so it
computes over `φ` and `m`. -/

/-- `Account storage acc = alice.account; acc = bob.account; acc.balance = 10;`:
the stack the strategy leaves, merged, then the printed line. -/
def localRebindLastLine (m : Modality) (φ : Post StandardExample) :
    dl![m]{ { acc := alice.account } { acc := bob.account } { storage := save(storage, acc.balance, 10) } φ }
    ~[sequentialToParallel]~>
      dl![m]{ { acc := alice.account ‖ acc := bob.account ‖ storage := save(storage, bob.account.balance, 10) } φ }
    ~[simplifyUpdate]~>
      dl![m]{ { acc := bob.account ‖ storage := save(storage, bob.account.balance, 10) } φ } := by
  sol_chain

/-! ## 5 · What is refused, and what is printed -/

section Refused
variable (m : Modality) (φ : Post StandardExample)

/--
error: ~[fooBar]~>: fooBar is no rule: not a `Taclet` or `LeanTaclet` constructor, not an update rule (sequentialToParallel, simplifyUpdate, applySkip, applyOnRigid, applyOnRigidBox, applyStorageBox), not a term taclet (`TermTaclet`)
-/
#guard_msgs in
example : dl!{ true } ~[fooBar]~> dl!{ true } := rfl

-- A rule that does not fit: one update has no pair to merge.
/--
error: ~[sequentialToParallel]~>: sequentialToParallel does not apply to
  dl{ { se1 := 10 } ⟨ alice.account.balance = se1; ⟩ find(storage, alice.account.balance) = 10 }
-/
#guard_msgs in
example : dl!{ { se1 := 10 } ⟨ alice.account.balance = se1; ⟩ alice.account.balance == 10 }
    ~[sequentialToParallel]~> dl!{ ⟨ alice.account.balance = 10; ⟩ alice.account.balance == 10 } := rfl

-- A line the rule does not give: the error shows the lines it does.
/--
error: ~[findOnSave]~>: on
  dl{ find(save(storage, alice.age, 42), alice.age) ≐ 42 }
it gives
  dl{ 42 ≐ 42 }
not
  dl{ 43 ≐ 42 }
-/
#guard_msgs in
example : dl!{ find(save(storage, alice.age, 42), alice.age) ≐ 42 } ~[findOnSave]~> dl!{ 43 ≐ 42 } := rfl

-- `~=>` names no rewrite: a line no rewrite gives shows what those that apply give.
/--
error: ~=>: no rewrite gives
  dl{ 43 ≐ 42 }
from
  dl{ find(save(storage, alice.age, 42), alice.age) ≐ 42 }
findOnSave gives
  dl{ 42 ≐ 42 }
findMemberCons gives
  dl{ select(select(save(storage, alice.age, 42), alice), age) ≐ 42 }
-/
#guard_msgs in
example : dl!{ find(save(storage, alice.age, 42), alice.age) ≐ 42 } ~=> dl!{ 43 ≐ 42 } := by
  sol_chain

-- A law whose side condition fails: `alice.age` does not leave itself.
/--
error: ~[findOnSaveFrame]~>: findOnSaveFrame does not apply to
  dl{ find(save(storage, alice.age, 1), alice.age) ≐ 0 }
(the side condition
  ((PTerm.root "alice").field "age").diverges ((PTerm.root "alice").field "age") = true
of findOnSaveFrame closes by neither `rfl` nor `decide`)
-/
#guard_msgs in
example : dl!{ find(save(storage, alice.age, 1), alice.age) ≐ 0 }
    ~[findOnSaveFrame]~> dl!{ find(storage, alice.age) ≐ 0 } := rfl

-- `simplifyUpdate` of a capture asks the postcondition what it reads.
/--
error: ~[simplifyUpdate]~>: on
  dl{ { x := 10 } { y := 1 } φ }
it looks at the line's modality or postcondition, which are not known: state the line for a concrete one
-/
#guard_msgs in
example : dl![m]{ { x := 10 } { y := 1 } φ } ~[simplifyUpdate]~> dl![m]{ { y := 1 } φ } := rfl

-- A storage write may halt: `applyStorageBox` is the box's.
/--
error: ~[applyStorageBox]~>: applyStorageBox does not apply to
  dl{ { storage := save(storage, alice.age, 10) } find(storage, alice.age) ≐ 10 }
(it applies under the box only, where an update that halts makes the line true: go on after `cases m`)
-/
#guard_msgs in
example : dl![m]{ { storage := save(storage, alice.age, 10) } alice.age ≐ 10 }
    ~[applyStorageBox]~> dl!{ find(save(storage, alice.age, 10), alice.age) ≐ 10 } := rfl

-- So is `applyOnRigidBox` of an update that may halt.
/--
error: ~[applyOnRigidBox]~>: applyOnRigidBox does not apply to
  dl{ { x := find(storage, alice.age) } x ≐ 42 }
(it applies under the box only, where an update that halts makes the line true: go on after `cases m`)
-/
#guard_msgs in
example : dl![m]{ { x := find(storage, alice.age) } x ≐ 42 }
    ~[applyOnRigidBox]~> dl!{ find(storage, alice.age) ≐ 42 } := rfl

-- And a law in an update's right-hand side: `{ x := 42 }` runs where the read halts.
/--
error: ~[findOnSave]~>: findOnSave does not apply to
  dl{ { x := find(save(storage, alice.age, 42), alice.age) } x ≐ 42 }
(it applies under the box only, where an update that halts makes the line true: go on after `cases m`)
-/
#guard_msgs in
example : dl![m]{ { x := find(save(storage, alice.age, 42), alice.age) } x ≐ 42 }
    ~[findOnSave]~> dl![m]{ { x := 42 } x ≐ 42 } := rfl

/-- `findOnSave`, twice under one name. -/
theorem Laws.readBack {s : STerm StandardExample} {p : PTerm StandardExample} {v : Semantics.Value}
    (hp : p.hasSeg = true := by rfl) : TermTaclet (.find (.save s p (.val (.lit v))) p) (.lit v) :=
  .findOnSave hp

@[inherit_doc Laws.readBack]
theorem Laws'.readBack {s : STerm StandardExample} {p : PTerm StandardExample} {v : Semantics.Value}
    (hp : p.hasSeg = true := by rfl) : TermTaclet (.find (.save s p (.val (.lit v))) p) (.lit v) :=
  .findOnSave hp

-- Two laws by one name: the arrow says so rather than pick one.
/--
error: ~[readBack]~>: ambiguous, readBack may be Solidity.Examples.ChainRewrites.Laws.readBack, Solidity.Examples.ChainRewrites.Laws'.readBack
-/
#guard_msgs in
open Laws Laws' in
example : dl!{ find(save(storage, alice.age, 42), alice.age) ≐ 42 } ~[readBack]~> dl!{ 42 ≐ 42 } := rfl

end Refused

/--
info: dl{ { se1 := 10 } { sp1 := alice.account } true }
    ~[sequentialToParallel]~> dl{ { se1 := 10 ‖ sp1 := alice.account } true } : Prop
-/
#guard_msgs in
#check dl!{ { se1 := 10 } { sp1 := alice.account } true }
    ~[sequentialToParallel]~> dl!{ { se1 := 10 ‖ sp1 := alice.account } true }

/--
info: Solidity.Examples.ChainRewrites.headlineNamed (m : Modality) (φ : Post StandardExample) :
  dl{ ⟨[ alice.account.balance = 10; ]⟩ φ } ~~>
    dl{ { se1 := 10 ‖ sp1 := alice.account ‖ storage := save(storage, alice.account.balance, 10) } φ }
-/
#guard_msgs in
#check headlineNamed

end Solidity.Examples.ChainRewrites
