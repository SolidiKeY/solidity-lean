import Solidity.Calculus.Chains
import Solidity.Calculus.Rewrite
import Solidity.Examples.Chains.Storage

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

* §1 — the headline as the calculus draws it (`Chains.Storage.BalanceWrite.chain`),
  for any modality `m` and postcondition `φ`, down to its last line, and on to
  the write alone (`headlineWrite`), the captures dropped;
* §2 — on to the value under the box: `simplifyUpdate`, `applyStorageBox`,
  `findOnSave`, and `⊨`;
* §3 — `alice.age = 42; uint x = alice.age;` read back two ways: the law in
  the update's right-hand side, and the update applied
  first, then the law (`SelectOnSaveConsr.ageWriteReadKeY`'s order, which goes
  on to solkey's read of the write a member at a time, `ageReadMembers`); and
  the headline's write read back;
* §4 — what is refused, and what is printed.

The traces picked up: `StorageSteps.deepFieldWrite` to its last line
(`headlineWrite`) and read back (`headlineValue`, `readBackValue`),
and `SelectOnSaveConsr.ageWriteReadKeY` (`ageWriteReadKeYValue`;
`ageWriteReadValue` in the printed order).  The rebound alias of
`Chains.Storage.Rebind.chain` already ends in its merge, both bindings of `acc` kept.

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
since a law is any theorem stating a `TermTaclet` or an `EvalLaw`, which no
function enumerates.
-/

namespace Solidity.Examples.ChainRewrites

local instance : InContract := ⟨StandardExample⟩

/-! ## 1 · The headline

`Chains.Storage.BalanceWrite.chain` is `alice.account.balance = 10;` unfolded
(Step 2), run to the two captures, written, and ended: the write merges into
the captures, its right-hand side substituted — the printed last line, in the
printed names for the rules' fresh variables (`pv`, `acc` for `se1`, `sp1`).
What follows is past it. -/

section Headline
variable (m : Modality) (φ : Post StandardExample)

section ExampleNames

local instance : FreshNames := .ofTable Chains.Storage.BalanceWrite.names

/-- `alice.account.balance = 10;` to its last line, for every modality and
postcondition, and on to the write alone: `φ` names no fresh variable
(`Post.noFresh`), so it reads neither `pv` nor `acc`, which the chain keeps,
and `simplifyUpdate` drops both. -/
theorem headlineWrite :
    dl![m]{ ⟨[ alice.account.balance = 10; ]⟩ φ }
    ~~> dl![m]{ { storage := save(storage, alice.account.balance, 10) } φ } :=
  calc dl![m]{ ⟨[ alice.account.balance = 10; ]⟩ φ }
    _ ~~> dl![m]{ { pv := 10 ‖ acc := alice.account ‖ storage := save(storage, alice.account.balance, 10) } φ } :=
      (Chains.Storage.BalanceWrite.chain m φ).leads
    _ ~[simplifyUpdate]~> dl![m]{ { storage := save(storage, alice.account.balance, 10) } φ } := by sol_chain

end ExampleNames

/-- The three updates the headline's write leaves (`Chains.Storage.BalanceWrite.chain`,
before its merge) merge in one link: the whole spine, the innermost pair first. -/
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
    _ ~~> dl![.box]{ { storage := save(storage, alice.account.balance, 10) } alice.account.balance ≐ 10 } :=
      headlineWrite .box { fml := dl!{ alice.account.balance ≐ 10 } }
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

* `ageWriteReadValue`, the in-update reading (`Examples/Tactics/Theory.lean`):
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

/-- The read of the write, one member at a time instead of `findOnSave`: solkey's
`findMemberCons` reads `alice.age` from its head, `select(select(…, alice), age)`
(the `consr` path turned into `cons` form inside its proof, `consRcons` and
`consRnil`, then `findDefinitionMemberCons`), and `selectOnSaveMember`,
`selectOnSaveCons`, pushes the write into `alice`; the read of the write at the
last member is `findOnSave` again.  From the line `ageWriteReadKeYValue` reaches
before its law (`SelectOnSaveConsr.lean` has the `consr` path). -/
def ageReadMembers :
    dl!{ find(save(storage, alice.age, 42), alice.age) ≐ 42 }
    ~=> dl!{ select(select(save(storage, alice.age, 42), alice), age) ≐ 42 }
    ~=> dl!{ select(store(select(storage, alice), age, 42), age) ≐ 42 }
    ~=> dl!{ 42 ≐ 42 } := by
  sol_chain

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

/-! ## 3′ · Under any modality

A law in an update's right-hand side is the box's where the rewritten update
may run where the read halts.  Where the update itself holds the write the
law reads back — `{ storage := save(storage, alice.age, 42) ‖ x := find(save(storage, alice.age, 42), alice.age) }`,
the merged line of every write-then-read — the two updates halt alike, and
the law applies under `m` (`LineRw.lawUpdAny`, `Upd.covers`).  Two storage
writes merge under `m` too, into one element (`Upd.mergeSt`): the merge
compares the modalities, which `sol_chain` decides by `cases m`. -/

section AnyModality
variable (m : Modality) (φ : Post StandardExample)

/-- `findOnSave` in the update under `m`: the update holds the write it reads back. -/
example : dl![m]{ { storage := save(storage, alice.age, 42) ‖
      x := find(save(storage, alice.age, 42), alice.age) } x ≐ 42 }
    ~[findOnSave]~> dl![m]{ { storage := save(storage, alice.age, 42) ‖ x := 42 } x ≐ 42 } := rfl

/-- `findOnDelAtSave` likewise: the delete over the write, read at its path. -/
example : dl![m]{ { storage := delAt(save(storage, alice.age, 42), alice.age) ‖
      x := find(delAt(save(storage, alice.age, 42), alice.age), alice.age) } φ }
    ~[findOnDelAtSave]~>
      dl![m]{ { storage := delAt(save(storage, alice.age, 42), alice.age) ‖ x := 0 } φ } := rfl

/-- `findOnDelAtBelow` under `m`, its premise a hypothesis of the chain: after
`alice.account.balance = 100;` and `delete alice.account;`, the balance reads its
default, the account being no mapping (which would keep its members).  The update
holds the delete the read goes through, so the law applies under `m`. -/
example (hk : STerm.KindFreeAt st!{ save(storage, alice.account.balance, 100) } pt!{ alice.account }) :
    dl![m]{ { storage := delAt(save(storage, alice.account.balance, 100), alice.account) ‖
      b := find(delAt(save(storage, alice.account.balance, 100), alice.account), alice.account.balance) } φ }
    ~[findOnDelAtBelow]~>
      dl![m]{ { storage := delAt(save(storage, alice.account.balance, 100), alice.account) ‖ b := 0 } φ } :=
  rfl

/-- The read of the write, member-wise, inside the update under `m`: solkey's
`findMemberCons`, `selectOnSaveMember`, then `findOnSave` at the member.  Each
intermediate form reads what the first does (`Term.base_eval`), so the steps
need no modality. -/
example : dl![m]{ { storage := save(storage, alice.age, 42) ‖
      x := find(save(storage, alice.age, 42), alice.age) } φ }
    ~[findMemberCons]~>
      dl![m]{ { storage := save(storage, alice.age, 42) ‖
        x := select(select(save(storage, alice.age, 42), alice), age) } φ }
    ~[selectOnSaveMember]~>
      dl![m]{ { storage := save(storage, alice.age, 42) ‖
        x := select(save(select(storage, alice), age, 42), age) } φ }
    ~[findOnSave]~> dl![m]{ { storage := save(storage, alice.age, 42) ‖ x := 42 } φ } := by
  sol_chain

/-- Two storage writes merge under `m` into one: the shadowed write goes. -/
example : dl![m]{ { storage := save(storage, alice.age, 1) } { storage := save(storage, alice.age, 2) } φ }
    ~[sequentialToParallel]~>
      dl![m]{ { storage := save(save(storage, alice.age, 1), alice.age, 2) } φ } := by
  sol_chain

/-- A storage write among locals merged into the update after it, which
writes the storage over it: the locals are substituted into the update after,
the shadowed write goes (`Upd.mergeStL`), and an index check moves with the
storage it is performed in, `balances[10]@S`. -/
example : dl![m]{ { se1 := 10 ‖ storage := save(storage, alice.age, 1) ‖ sp1 := alice.account }
      { storage := save(storage, balances[se1], 2) ‖ x := find(storage, balances[se1]) } φ }
    ~[sequentialToParallel]~>
      dl![m]{ { se1 := 10 ‖ sp1 := alice.account ‖
        storage := save(save(storage, alice.age, 1), balances[10]@save(storage, alice.age, 1), 2) ‖
        x := find(save(storage, alice.age, 1), balances[10]@save(storage, alice.age, 1)) } φ } := by
  sol_chain

/-- `alice.age = 42; uint x = alice.age;` read back to `42` inside the chain,
for every modality and postcondition. -/
example : dl![m]{ ⟨[ alice.age = 42; uint x = alice.age; ]⟩ φ }
    ~~> dl![m]{ { storage := save(storage, alice.age, 42) ‖ x := 42 } φ } :=
  calc dl![m]{ ⟨[ alice.age = 42; uint x = alice.age; ]⟩ φ }
    _ ~*> dl![m]{ { storage := save(storage, alice.age, 42) } { x := find(storage, alice.age) } φ } := by
      sol_chain
    _ ~[sequentialToParallel]~>
        dl![m]{ { storage := save(storage, alice.age, 42) ‖
          x := find(save(storage, alice.age, 42), alice.age) } φ } := by sol_chain
    _ ~[findOnSave]~> dl![m]{ { storage := save(storage, alice.age, 42) ‖ x := 42 } φ } := by rfl

end AnyModality

/-! ## 3″ · Memory reads

A memory read denotes its run, so its laws are refinements of the
interpreter (`EvalLaw`): `readOnWrite`, `findCopyMem` (a member of a memory
object copied into storage is read out of memory), `readCopySt` (a member of
a copy of a storage struct is read out of storage), `readAddEqual` (a
primitive member of a fresh object is its default), `readAddDifferent` and
`readWriteDifferent` (an allocation, a write, leaves every other slot), and
their twins at the identity sort (`…Identity`, with `readOnWriteIdentity`).
Each applies in an update under `m` where the update holds the write or
allocation it reads back (`Upd.coversEval`), at the sort of the law
(`Tm.rwEv`).  The merges feed them: a memory write merges into the update
after it (`Upd.mergeMem`), and a storage write into one with memory terms
(`withStM`).  A reference member of a fresh root,
`read(addM(m, R), freshId(addM(m, R)).account)`, is the normal form. -/

section MemoryReads
variable (m : Modality) (φ : Post StandardExample)

/-- A memory write merged into the storage write and the read after it. -/
example : dl![m]{ { memory := write(memory, carol.age, 42) }
      { storage := save(storage, alice, copyMem(mtSt, memory, carol)) ‖
        v := find(save(storage, alice, copyMem(mtSt, memory, carol)), alice.age) } φ }
    ~[sequentialToParallel]~>
      dl![m]{ { memory := write(memory, carol.age, 42) ‖
        storage := save(storage, alice, copyMem(mtSt, write(memory, carol.age, 42), carol)) ‖
        v := find(save(storage, alice, copyMem(mtSt, write(memory, carol.age, 42), carol)), alice.age) } φ } := by
  sol_chain

/-- `findCopyMem` then `readOnWrite`, under `m`: the update holds the storage
write the first reads back and the memory write the second does. -/
example : dl![m]{ { memory := write(memory, carol.age, 42) ‖
        storage := save(storage, alice, copyMem(mtSt, write(memory, carol.age, 42), carol)) ‖
        v := find(save(storage, alice, copyMem(mtSt, write(memory, carol.age, 42), carol)), alice.age) } φ }
    ~[findCopyMem]~>
      dl![m]{ { memory := write(memory, carol.age, 42) ‖
        storage := save(storage, alice, copyMem(mtSt, write(memory, carol.age, 42), carol)) ‖
        v := read(write(memory, carol.age, 42), carol.age) } φ }
    ~[readOnWrite]~>
      dl![m]{ { memory := write(memory, carol.age, 42) ‖
        storage := save(storage, alice, copyMem(mtSt, write(memory, carol.age, 42), carol)) ‖
        v := 42 } φ } := by
  sol_chain

set_option maxHeartbeats 2000000 in
/-- A storage-to-memory copy read back: the three updates merged into one
(the copy's identity and memory into the read, the storage write into the
copy), then `readCopySt`, then `findOnSave`. -/
example : dl![m]{ { storage := save(storage, alice.age, 25) }
      { carol := freshId(copySt(memory, find(storage, alice))) ‖ memory := copySt(memory, find(storage, alice)) }
      { v := read(memory, carol.age) } φ }
    ~[sequentialToParallel]~>
      dl![m]{ { storage := save(storage, alice.age, 25) ‖
        carol := freshId(copySt(memory, find(save(storage, alice.age, 25), alice))) ‖
        memory := copySt(memory, find(save(storage, alice.age, 25), alice)) ‖
        v := read(copySt(memory, find(save(storage, alice.age, 25), alice)),
                  freshId(copySt(memory, find(save(storage, alice.age, 25), alice))).age) } φ }
    ~[readCopySt]~>
      dl![m]{ { storage := save(storage, alice.age, 25) ‖
        carol := freshId(copySt(memory, find(save(storage, alice.age, 25), alice))) ‖
        memory := copySt(memory, find(save(storage, alice.age, 25), alice)) ‖
        v := find(save(storage, alice.age, 25), alice.age) } φ }
    ~[findOnSave]~>
      dl![m]{ { storage := save(storage, alice.age, 25) ‖
        carol := freshId(copySt(memory, find(save(storage, alice.age, 25), alice))) ‖
        memory := copySt(memory, find(save(storage, alice.age, 25), alice)) ‖
        v := 25 } φ } := by
  sol_chain

/-- `readAddEqual`: a primitive member of a fresh object is its default,
under `m` where the update holds the allocation. -/
example : dl![m]{ { carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) ‖
        v := read(addM(memory, Person), freshId(addM(memory, Person)).age) } φ }
    ~[readAddEqual]~>
      dl![m]{ { carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) ‖
        v := 0 } φ } := by
  sol_chain

/-- `readAddDifferent` then `readAddEqual`: a second allocation leaves the
first object, whose member then reads its default. -/
example : dl![m]{ { carol := freshId(addM(memory, Person)) ‖
        david := freshId(addM(addM(memory, Person), Person)) ‖
        memory := addM(addM(memory, Person), Person) ‖
        v := read(addM(addM(memory, Person), Person), freshId(addM(memory, Person)).age) } φ }
    ~[readAddDifferent]~>
      dl![m]{ { carol := freshId(addM(memory, Person)) ‖
        david := freshId(addM(addM(memory, Person), Person)) ‖
        memory := addM(addM(memory, Person), Person) ‖
        v := read(addM(memory, Person), freshId(addM(memory, Person)).age) } φ }
    ~[readAddEqual]~>
      dl![m]{ { carol := freshId(addM(memory, Person)) ‖
        david := freshId(addM(addM(memory, Person), Person)) ‖
        memory := addM(addM(memory, Person), Person) ‖
        v := 0 } φ } := by
  sol_chain

/-- `readAddDifferentIdentity`: the reference member of the first object,
read past the second allocation; the read of the fresh root's member is the
normal form. -/
example : dl![m]{ { carol := freshId(addM(memory, Person)) ‖
        david := freshId(addM(addM(memory, Person), Person)) ‖
        memory := addM(addM(memory, Person), Person) ‖
        carolAcc := read(addM(addM(memory, Person), Person), freshId(addM(memory, Person)).account) } φ }
    ~[readAddDifferentIdentity]~>
      dl![m]{ { carol := freshId(addM(memory, Person)) ‖
        david := freshId(addM(addM(memory, Person), Person)) ‖
        memory := addM(addM(memory, Person), Person) ‖
        carolAcc := read(addM(memory, Person), freshId(addM(memory, Person)).account) } φ } := by
  sol_chain

/-- `readWriteDifferent` and `readWriteDifferentIdentity`: a write to
`carol.age` leaves `carol.account.balance` and `carol.account`, under `m`
where the update holds the write. -/
example : dl![m]{ { carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
      { memory := write(memory, carol.age, 42) ‖
        v := read(write(memory, carol.age, 42), carol.account.balance) ‖
        carolAcc := read(write(memory, carol.age, 42), carol.account) } φ }
    ~[readWriteDifferent]~>
      dl![m]{ { carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
      { memory := write(memory, carol.age, 42) ‖
        v := read(memory, carol.account.balance) ‖
        carolAcc := read(write(memory, carol.age, 42), carol.account) } φ }
    ~[readWriteDifferentIdentity]~>
      dl![m]{ { carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
      { memory := write(memory, carol.age, 42) ‖
        v := read(memory, carol.account.balance) ‖
        carolAcc := read(memory, carol.account) } φ } := by
  sol_chain

/-- `readOnWriteIdentity`: a reference written is read back as its identity. -/
example : dl![m]{ { carol := freshId(addM(memory, Person)) ‖
        acc := freshId(addM(addM(memory, Person), Account)) ‖
        memory := addM(addM(memory, Person), Account) }
      { memory := write(memory, carol.account, acc) ‖
        carolAcc := read(write(memory, carol.account, acc), carol.account) } φ }
    ~[readOnWriteIdentity]~>
      dl![m]{ { carol := freshId(addM(memory, Person)) ‖
        acc := freshId(addM(addM(memory, Person), Account)) ‖
        memory := addM(addM(memory, Person), Account) }
      { memory := write(memory, carol.account, acc) ‖ carolAcc := acc } φ } := by
  sol_chain

end MemoryReads

/-! ## 3‴ · Literals and branches

A check leaves its goals behind one update, as a conjunction of implications
over the captured condition.  The literals fold (`add_literals`, `leq_literals`,
`Calculus/Literals.lean`: exact laws, so in an update's right-hand side under
any modality and with no premise), the update is pushed through the
connectives (`applyOnRigid`, `Fml.push`, `Calculus/ChainBranches.lean`), the
literal connectives fold (`concrete`), and a merge finds the first spine
under a branch (`sequentialToParallel`, `LineRw.mergeIn`).  Each rewrite
under a branch reads the skeleton of the line the elaborator wrote for it, so
the postcondition `φ` is a part it never looks at, and the line is proved by
`rfl` over it. -/

section Literals
variable (m : Modality) (φ : Post StandardExample)

/-- `add_literals` in an update's right-hand side under `m`: the sum is exact. -/
example : dl![m]{ { x := 250 + 10 } φ } ~[add_literals]~> dl![m]{ { x := 260 } φ } := rfl

/-- `leq_literals` in an update: the comparison a check captured, `uint8`'s
range read as `x <= 255`. -/
example : dl![m]{ { x := 260 ‖ se1 := 260 <= 255 } φ }
    ~[leq_literals]~> dl![m]{ { x := 260 ‖ se1 := false } φ } := rfl

/-- `add_literals` in an equation of the line, and under `defined(…)`. -/
example : dl!{ defined(250 + 10) ∧ 250 + 10 ≐ 260 }
    ~[add_literals]~> dl!{ defined(260) ∧ 260 ≐ 260 } := rfl

/-- `applyOnRigid` through a conjunction under `m`: the update cannot halt,
each rigid leaf is substituted, and the goals keep the update in front. -/
example : dl![m]{ { se1 := false } ((se1 ≐ true → φ) ∧ (se1 ≐ false → ⟨[ revert(); ]⟩ φ)) }
    ~[applyOnRigid]~>
      dl![m]{ (false ≐ true → { se1 := false } φ) ∧
        (false ≐ false → { se1 := false } ⟨[ revert(); ]⟩ φ) } := rfl

/-- `concrete`: the literal equations close (`eqClose`), the connectives
fold (`concrete_impl_2`, `concrete_impl_1`, `concrete_and_1`). -/
example : dl![m]{ (false ≐ true → { se1 := false } φ) ∧
      (false ≐ false → { se1 := false } ⟨[ revert(); ]⟩ φ) }
    ~[concrete]~> dl![m]{ { se1 := false } ⟨[ revert(); ]⟩ φ } := rfl

/-- `sequentialToParallel` under a branch: the first spine the skeleton finds. -/
example : dl![m]{ (x ≐ 1 → { x := 1 } { y := x } φ) ∧ (x ≐ 2 → φ) }
    ~[sequentialToParallel]~> dl![m]{ (x ≐ 1 → { x := 1 ‖ y := 1 } φ) ∧ (x ≐ 2 → φ) } := rfl

set_option maxHeartbeats 300000 in
/-- The check's trace, folded: the captured comparison, the update pushed
through, the branch closed, and the capture dropped. -/
example : dl![m]{ { x := 260 ‖ se1 := 260 <= 255 } ((se1 ≐ true → φ) ∧ (se1 ≐ false → ⟨[ revert(); ]⟩ φ)) }
    ~[leq_literals]~> dl![m]{ { x := 260 ‖ se1 := false } ((se1 ≐ true → φ) ∧ (se1 ≐ false → ⟨[ revert(); ]⟩ φ)) }
    ~[applyOnRigid]~>
      dl![m]{ (false ≐ true → { x := 260 ‖ se1 := false } φ) ∧
        (false ≐ false → { x := 260 ‖ se1 := false } ⟨[ revert(); ]⟩ φ) }
    ~[concrete]~> dl![m]{ { x := 260 ‖ se1 := false } ⟨[ revert(); ]⟩ φ }
    ~[simplifyUpdate]~> dl![m]{ { x := 260 } ⟨[ revert(); ]⟩ φ } := by
  sol_chain

-- `add_literals` out of range: the sum reverts, and is its own normal form.
/--
error: ~[add_literals]~>: add_literals does not apply to
  dl{ { x := 115792089237316195423570985008687907853269984665640564039457584007913129639935 + 1 } φ }
(the side condition
  0 ≤ 115792089237316195423570985008687907853269984665640564039457584007913129639935 + 1 ∧
    115792089237316195423570985008687907853269984665640564039457584007913129639935 + 1 < Semantics.uintBound
of add_literals closes by neither `rfl`, `decide` nor a hypothesis)
-/
#guard_msgs in
example : dl![m]{ { x := 115792089237316195423570985008687907853269984665640564039457584007913129639935 + 1 } φ }
    ~[add_literals]~> dl![m]{ { x := 0 } φ } := rfl

end Literals

/-! ## 4 · What is refused, and what is printed -/

section Refused
variable (m : Modality) (φ : Post StandardExample)

/--
error: ~[fooBar]~>: fooBar is no rule: not a `Taclet` or `LeanTaclet` constructor, not an update rule (sequentialToParallel, simplifyUpdate, applySkip, applyOnRigid, applyOnRigidBox, applyStorageBox, applyOnPV, concrete), not a term taclet (`TermTaclet`), not a law of a memory read (`EvalLaw`), not a literal law (`LitLaw`)
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
of findOnSaveFrame closes by neither `rfl`, `decide` nor a hypothesis)
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

end Solidity.Examples.ChainRewrites
