import Solidity.Calculus.ChainRewrites
import Solidity.Calculus.TheoryLaws

/-!
# The lines after the program, as rewrites

`Calculus/ChainRewrites.lean`'s rewrites on the calculus's traces.  Each line
after the program is its rewrite's function applied to the line before,
checked by `rfl`; each rewrite's soundness (`LineRw.valid`) carries the
validity of the last line back to the first.

* §1 — the headline's last line: `sequentialToParallel` over the three
  updates `alice.account.balance = 10;` leaves;
* §2 — the same over a modality variable `m` and an opaque postcondition
  `φ`, `⟨[ p ]⟩ φ`;
* §3 — on to the value under the box: `simplifyUpdate`, `applyStorageBox`,
  `findOnSave`;
* §4 — a law in an update's right-hand side: `alice.age = 42; uint x = alice.age;`,
  and the headline's write read back;
* §5 — a rebound alias: the overwritten capture dropped, as the printed line
  has it.

**Writing the lines.**  A line with no modality left reads as a diamond in
`dl!{}` (`fmlModality?`), and `dl!{}` has no modality variable and no
formula variable.  So those lines are written `over m φ dl!{ … true }`: the
updates and programs of a `dl!{}` line, under `m`, over `φ` in place of its
postcondition `true`.  A law names its instance: `findOnSave` at the path
it reads, which a chain finds in the line (`sol_rw`'s search).
-/

namespace Solidity.Examples.ChainRewrites

local instance : InContract := ⟨StandardExample⟩

/-- The updates and programs of a line, under `m`, over `φ`: how a line reads
with the modality a variable and the postcondition opaque, and a box line
with no modality left. -/
def over (m : Modality) (φ : Fml StandardExample) : Fml StandardExample → Fml StandardExample
  | .upd _ U ψ => .upd m U (over m φ ψ)
  | .modal _ P ψ => .modal m P (over m φ ψ)
  | _ => φ

/-! ## 1 · The headline's last line

`alice.account.balance = 10;` leaves three updates (`Examples/Chains.lean`'s
`headline`).  Merged innermost pair first, `sp1` and then `se1`
substituted, they are the printed last line. -/

/-- `alice.account.balance = 10;`: the three updates into one. -/
theorem headlineLastLine :
    Fml.mergeSpine 2 dl!{ { se1 := 10 } { sp1 := alice.account } { storage := save(storage, sp1.balance, se1) }
        alice.account.balance == 10 }
      = some dl!{ { se1 := 10 ‖ sp1 := alice.account ‖ storage := save(storage, alice.account.balance, 10) }
        alice.account.balance == 10 } := rfl

/-- `alice.account.balance = 10;`: the `⇝*` line merges the two
captures while the write is still to run. -/
theorem headlineCaptures :
    Fml.mergeAt 0 dl!{ { se1 := 10 } { sp1 := alice.account } ⟨ sp1.balance = se1; ⟩ alice.account.balance == 10 }
      = some dl!{ { se1 := 10 ‖ sp1 := alice.account } ⟨ sp1.balance = se1; ⟩ alice.account.balance == 10 } := rfl

/-- `alice.account.balance = 10;`: the write, run, merges into the captures:
the same last line. -/
theorem headlineWrite :
    Fml.mergeAt 0 dl!{ { se1 := 10 ‖ sp1 := alice.account } { storage := save(storage, sp1.balance, se1) }
        alice.account.balance == 10 }
      = some dl!{ { se1 := 10 ‖ sp1 := alice.account ‖ storage := save(storage, alice.account.balance, 10) }
        alice.account.balance == 10 } := rfl

/-- The innermost pair alone: the write merges with the alias. -/
example :
    Fml.mergeAt 1 dl!{ { se1 := 10 } { sp1 := alice.account } { storage := save(storage, sp1.balance, se1) }
        alice.account.balance == 10 }
      = some dl!{ { se1 := 10 } { sp1 := alice.account ‖ storage := save(storage, alice.account.balance, se1) }
        alice.account.balance == 10 } := rfl

/-- Where the last line is valid, the first is. -/
example (h : ⊨ dl!{ { se1 := 10 ‖ sp1 := alice.account ‖ storage := save(storage, alice.account.balance, 10) }
      alice.account.balance == 10 }) :
    ⊨ dl!{ { se1 := 10 } { sp1 := alice.account } { storage := save(storage, sp1.balance, se1) }
      alice.account.balance == 10 } :=
  (LineRw.mergeSpine 2).valid headlineLastLine h

/-- A rule that does not fit gives no line: one update has no pair to merge,
and `se1` is read after it, so `simplifyUpdate` has nothing to drop. -/
example :
    Fml.mergeAt 0 dl!{ { se1 := 10 } ⟨ alice.account.balance = se1; ⟩ alice.account.balance == 10 } = none :=
  rfl

example :
    Fml.updRuleAt .simplifyUpdate 0 dl!{ { se1 := 10 } { sp1 := alice.account }
        { storage := save(storage, sp1.balance, se1) } alice.account.balance == 10 } = none := rfl

/-! ## 2 · Over a modality variable and an opaque postcondition

Written `⟨[ p ]⟩ φ`: either modality, any postcondition.  Every
update the merges consume is a capture that cannot halt (`Upd.total`), so
no modality is compared, and no merge looks at the body. -/

/-- `alice.account.balance = 10;` under `m`, over `φ`: the last line. -/
theorem headlineLastLineAny (m : Modality) (φ : Fml StandardExample) :
    Fml.mergeSpine 2 (over m φ dl!{ { se1 := 10 } { sp1 := alice.account }
        { storage := save(storage, sp1.balance, se1) } true })
      = some (over m φ dl!{ { se1 := 10 ‖ sp1 := alice.account
          ‖ storage := save(storage, alice.account.balance, 10) } true }) := rfl

/-- `alice.account.balance = 10;` under `m`, over `φ`: the `⇝*` line. -/
theorem headlineCapturesAny (m : Modality) (φ : Fml StandardExample) :
    Fml.mergeAt 0 (over m φ dl!{ { se1 := 10 } { sp1 := alice.account } ⟨ sp1.balance = se1; ⟩ true })
      = some (over m φ dl!{ { se1 := 10 ‖ sp1 := alice.account } ⟨ sp1.balance = se1; ⟩ true }) := rfl

/-- `y = 3;`: an update that cannot halt, applied to a first-order formula
under either modality (`applyOnRigid`, an equivalence). -/
example (m : Modality) :
    Fml.updRuleAt .applyOnRigid 0 (over m dl!{ y ≐ 3 } dl!{ { y := 3 } true }) = some dl!{ 3 ≐ 3 } :=
  rfl

/-! ## 3 · To the value, under the box

The box derivation's last line, `simplifyUpdate` (`se1` and `sp1` are read
no more), the storage write applied (`applyStorageBox`), and `findOnSave`
reading the write back: `10 ≐ 10`.  The postcondition is `≐`, KeY's `=`;
with `==` the `defined(…)` of the read stays, which the law does not touch
(`headlineEqD`), and which applying the write would make false where it
halts. -/

/-- `alice.account.balance = 10;` under the box: the strategy's seven steps. -/
theorem headlineBox :
    symex 7 dl!{ [ alice.account.balance = 10; ] alice.account.balance ≐ 10 }
      = over .box dl!{ alice.account.balance ≐ 10 }
          dl!{ { se1 := 10 } { sp1 := alice.account } { storage := save(storage, sp1.balance, se1) } true } :=
  rfl

/-- `alice.account.balance = 10;` under the box: merged. -/
theorem headlineMerged :
    Fml.mergeSpine 2 (over .box dl!{ alice.account.balance ≐ 10 }
        dl!{ { se1 := 10 } { sp1 := alice.account } { storage := save(storage, sp1.balance, se1) } true })
      = some (over .box dl!{ alice.account.balance ≐ 10 }
          dl!{ { se1 := 10 ‖ sp1 := alice.account
            ‖ storage := save(storage, alice.account.balance, 10) } true }) := rfl

/-- `alice.account.balance = 10;` under the box: the captures dropped. -/
theorem headlineSimplified :
    Fml.updRuleAt .simplifyUpdate 0 (over .box dl!{ alice.account.balance ≐ 10 }
        dl!{ { se1 := 10 ‖ sp1 := alice.account
          ‖ storage := save(storage, alice.account.balance, 10) } true })
      = some (over .box dl!{ alice.account.balance ≐ 10 }
          dl!{ { storage := save(storage, alice.account.balance, 10) } true }) := rfl

/-- `alice.account.balance = 10;` under the box: the write applied. -/
theorem headlineApplied :
    Fml.applyStorageBoxAt 0 (over .box dl!{ alice.account.balance ≐ 10 }
        dl!{ { storage := save(storage, alice.account.balance, 10) } true })
      = some dl!{ find(save(storage, alice.account.balance, 10), alice.account.balance) ≐ 10 } := rfl

/-- `alice.account.balance`, where `findOnSave` reads the write back. -/
abbrev balance : PTerm StandardExample := .field (.field (.root "alice") "account") "balance"

/-- `alice.account.balance = 10;`: `findOnSave` reads the write back. -/
theorem headlineRead :
    Fml.rwLaw (.find (.save .storage balance (.val (.lit (.int 10)))) balance, .lit (.int 10))
        dl!{ find(save(storage, alice.account.balance, 10), alice.account.balance) ≐ 10 }
      = some dl!{ 10 ≐ 10 } := rfl

/-- `alice.account.balance = 10;` reads back `10`, the lines above chained. -/
theorem headlineValue : ⊨ dl!{ [ alice.account.balance = 10; ] alice.account.balance ≐ 10 } := by
  apply symex_valid 7
  rw [headlineBox]
  refine (LineRw.mergeSpine 2).valid headlineMerged ?_
  refine (LineRw.updRule .simplifyUpdate 0).valid headlineSimplified ?_
  refine (LineRw.applyStorageBox 0).valid headlineApplied ?_
  refine (LineRw.law (findOnSave (s := .storage) (p := balance) (v := .int 10))).valid headlineRead ?_
  exact fun _ => Theory.StValue.Equiv.refl _

/-- `alice.account.balance = 10;` against `==`: the law rewrites the
equation, not the `defined(…)` beside it. -/
theorem headlineEqD :
    Fml.applyStorageBoxAt 0 (over .box dl!{ alice.account.balance == 10 }
        dl!{ { storage := save(storage, alice.account.balance, 10) } true }) >>=
      Fml.rwLaw (.find (.save .storage balance (.val (.lit (.int 10)))) balance, .lit (.int 10))
      = some dl!{ defined(find(save(storage, alice.account.balance, 10), alice.account.balance)) ∧
          defined(10) ∧ 10 ≐ 10 } := rfl

/-! ## 4 · A law in an update's right-hand side

`alice.age = 42; uint x = alice.age;` (`SelectOnSaveConsr.ageWriteReadKeY`,
there on `⊢`): the read merged into the write (`sequentialToParallel` over a
storage write), read back inside the update (`findOnSave`, onto a literal),
the update applied (`applyOnRigidBox`: `x ≐ 42` reads no storage).  The
calculus's traces read terms back in the update this way
(`Examples/Theory.lean`).  Then the headline's write read back
(`Theory.deepFieldWriteValue`'s program): the write sits amid captures, and
the spine merges inside out. -/

/-- `alice.age = 42; uint x = alice.age;` under the box: the strategy's four steps. -/
theorem ageWriteReadBox :
    symex 4 dl!{ [ alice.age = 42; uint x = alice.age; ] x ≐ 42 }
      = over .box dl!{ x ≐ 42 }
          dl!{ { storage := save(storage, alice.age, 42) } { x := find(storage, alice.age) } true } :=
  rfl

/-- `alice.age = 42; uint x = alice.age;`: the read merged into the write. -/
theorem ageWriteReadMerged :
    Fml.mergeSpine 1 (over .box dl!{ x ≐ 42 }
        dl!{ { storage := save(storage, alice.age, 42) } { x := find(storage, alice.age) } true })
      = some (over .box dl!{ x ≐ 42 } dl!{ { storage := save(storage, alice.age, 42)
          ‖ x := find(save(storage, alice.age, 42), alice.age) } true }) := rfl

/-- `alice.age`, where `findOnSave` reads the write back. -/
abbrev age : PTerm StandardExample := .field (.root "alice") "age"

/-- `alice.age = 42; uint x = alice.age;`: `x` reads back `42` in the update. -/
theorem ageWriteReadLaw :
    Fml.rwUpdAt (.find (.save .storage age (.val (.lit (.int 42)))) age, .lit (.int 42)) 0
        (over .box dl!{ x ≐ 42 } dl!{ { storage := save(storage, alice.age, 42)
          ‖ x := find(save(storage, alice.age, 42), alice.age) } true })
      = some (over .box dl!{ x ≐ 42 } dl!{ { storage := save(storage, alice.age, 42) ‖ x := 42 } true }) :=
  rfl

/-- `alice.age = 42; uint x = alice.age;`: the update applied. -/
theorem ageWriteReadApplied :
    Fml.applyOnRigidBoxAt 0
        (over .box dl!{ x ≐ 42 } dl!{ { storage := save(storage, alice.age, 42) ‖ x := 42 } true })
      = some dl!{ 42 ≐ 42 } := rfl

/-- `alice.age = 42; uint x = alice.age;` reads back `42`, the lines above chained. -/
theorem ageWriteReadValue : ⊨ dl!{ [ alice.age = 42; uint x = alice.age; ] x ≐ 42 } := by
  apply symex_valid 4
  rw [ageWriteReadBox]
  refine (LineRw.mergeSpine 1).valid ageWriteReadMerged ?_
  refine (LineRw.lawUpd (findOnSave (s := .storage) (p := age) (v := .int 42)) rfl 0).valid
    ageWriteReadLaw ?_
  refine (LineRw.applyOnRigidBox 0).valid ageWriteReadApplied ?_
  exact fun _ => Theory.StValue.Equiv.refl _

/-- `alice.account.balance = 10; uint x = alice.account.balance;` under the
box: the strategy's twelve steps, a storage write amid the captures. -/
theorem readBackBox :
    symex 12 dl!{ [ alice.account.balance = 10; uint x = alice.account.balance; ] x ≐ 10 }
      = over .box dl!{ x ≐ 10 }
          dl!{ { se1 := 10 } { sp1 := alice.account } { storage := save(storage, sp1.balance, se1) }
            { sp2 := alice.account } { x := find(storage, sp2.balance) } true } :=
  rfl

/-- `alice.account.balance = 10; uint x = alice.account.balance;`: merged
inside out, the read over the write first (`withSt`), then the captures. -/
theorem readBackMerged :
    Fml.mergeSpine 4 (over .box dl!{ x ≐ 10 }
        dl!{ { se1 := 10 } { sp1 := alice.account } { storage := save(storage, sp1.balance, se1) }
          { sp2 := alice.account } { x := find(storage, sp2.balance) } true })
      = some (over .box dl!{ x ≐ 10 }
          dl!{ { se1 := 10 ‖ sp1 := alice.account ‖ storage := save(storage, alice.account.balance, 10)
            ‖ sp2 := alice.account
            ‖ x := find(save(storage, alice.account.balance, 10), alice.account.balance) } true }) := rfl

/-- `alice.account.balance = 10; uint x = alice.account.balance;`: `x` reads
back `10` in the update. -/
theorem readBackLaw :
    Fml.rwUpdAt (.find (.save .storage balance (.val (.lit (.int 10)))) balance, .lit (.int 10)) 0
        (over .box dl!{ x ≐ 10 }
          dl!{ { se1 := 10 ‖ sp1 := alice.account ‖ storage := save(storage, alice.account.balance, 10)
            ‖ sp2 := alice.account
            ‖ x := find(save(storage, alice.account.balance, 10), alice.account.balance) } true })
      = some (over .box dl!{ x ≐ 10 }
          dl!{ { se1 := 10 ‖ sp1 := alice.account ‖ storage := save(storage, alice.account.balance, 10)
            ‖ sp2 := alice.account ‖ x := 10 } true }) := rfl

/-- `alice.account.balance = 10; uint x = alice.account.balance;`: the
update applied. -/
theorem readBackApplied :
    Fml.applyOnRigidBoxAt 0 (over .box dl!{ x ≐ 10 }
        dl!{ { se1 := 10 ‖ sp1 := alice.account ‖ storage := save(storage, alice.account.balance, 10)
          ‖ sp2 := alice.account ‖ x := 10 } true })
      = some dl!{ 10 ≐ 10 } := rfl

/-- `alice.account.balance = 10; uint x = alice.account.balance;` reads back
`10`, the lines above chained. -/
theorem readBackValue :
    ⊨ dl!{ [ alice.account.balance = 10; uint x = alice.account.balance; ] x ≐ 10 } := by
  apply symex_valid 12
  rw [readBackBox]
  refine (LineRw.mergeSpine 4).valid readBackMerged ?_
  refine (LineRw.lawUpd (findOnSave (s := .storage) (p := balance) (v := .int 10)) rfl 0).valid
    readBackLaw ?_
  refine (LineRw.applyOnRigidBox 0).valid readBackApplied ?_
  exact fun _ => Theory.StValue.Equiv.refl _

/-! ## 5 · A rebound alias

`Account storage acc = alice.account; acc = bob.account; acc.balance = 10;`
(`StorageSteps.localRebindThenWrite`): the printed line keeps
`acc := bob.account` and drops the capture it overwrites.  Dropping an
overwritten element needs nothing of the postcondition, so it computes over
`φ` and `m`. -/

/-- `Account storage acc = alice.account; acc = bob.account; acc.balance = 10;`: merged. -/
theorem localRebindMerged (m : Modality) (φ : Fml StandardExample) :
    Fml.mergeSpine 2 (over m φ dl!{ { acc := alice.account } { acc := bob.account }
        { storage := save(storage, acc.balance, 10) } true })
      = some (over m φ dl!{ { acc := alice.account ‖ acc := bob.account
          ‖ storage := save(storage, bob.account.balance, 10) } true }) := rfl

/-- `Account storage acc = alice.account; acc = bob.account; acc.balance = 10;`:
the printed line. -/
theorem localRebindLastLine (m : Modality) (φ : Fml StandardExample) :
    Fml.dropShadowedAt 0 (over m φ dl!{ { acc := alice.account ‖ acc := bob.account
        ‖ storage := save(storage, bob.account.balance, 10) } true })
      = some (over m φ dl!{ { acc := bob.account ‖ storage := save(storage, bob.account.balance, 10) } true }) :=
  rfl

end Solidity.Examples.ChainRewrites
