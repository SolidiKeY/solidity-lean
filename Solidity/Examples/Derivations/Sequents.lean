import Solidity.Examples.Common
import Solidity.DecEq

/-!
# The calculus's own derivations

Every worked example of the calculus is a chain of **updated sequents**: the
program shrinks on the right while the accumulated update grows on the left,
and the chain ends not at an empty program but at a formula under one parallel
update.  `Examples/Derivations/` writes the program half of that; this file
writes the whole line.

```
   ⟨[alice.account.balance = 10;]⟩φ
⇝  ⟨[uint rv = 10; Account storage sp = alice.account; sp.balance = rv;]⟩φ
⇝* {rv := 10 ‖ sp := alice·account} ⟨[sp.balance = rv;]⟩φ
⇝  {rv := 10 ‖ sp := alice·account ‖ storage := save(storage, alice·account·balance, 10)} φ
```

Each derivation below is one `sol_derivation` over `seq!` lines, and each is a
named theorem about `⇝ᵘ*`.  Three things are worth knowing before reading them.

**The merge line is `⇝≡`, not `⇝`.** The last line of a chain upstream is
usually not a rule application: it is the update calculus collapsing `{u}{v}`
into `{u ‖ {u}v}`, and its content is an equality of two updates *as state
functions* (`Upd.Par.seq_single`, and the reader lemmas of
`Update/Merge.lean`).  Writing it with `⇝` would claim a taclet fired.

**The scratch names are Lean's.** The calculus writes `pv`/`acc`; the rules
here bind `rv` (the frozen value operand) and `sp` (the storage alias), and
`Rules.lean` records why the calculus's own examples are inconsistent about
it.  The freeze also costs three administrative steps the calculus does not
draw — they are the `⇝*` lines, as upstream elides with `⇝*`.

**Every chain has a semantic twin.** `Sequent.check` runs a line against the
interpreter, so at the end of the file there are `native_decide` examples
showing that the first and the last line of a chain agree on a concrete store.
The chains themselves add no axiom of their own -- in particular the merge
lines are ordinary proofs, from `Upd.Par.seq_single` and the reader lemmas of
`Update/Merge.lean` -- but a *pinned* step goes through
`UniquenessAux.firstStepCase_box`, whose exclusivity theorem is decided by
`native_decide` in `Uniqueness.lean`.  That is the block layer's proof route,
not something this file introduces.

Out of scope, and the reason is in `Update/Eval.lean`: the storage→memory copy
examples, whose lines carry a freshness prefix `new(mem, r) →` and the lazy
`copySt` term, which has no first-order spelling here.
-/

namespace Solidity.Examples.Sequents

open Rules StandardExample SoliditySyntax Solidity.Examples Semantics

set_option maxHeartbeats 8000000

section
variable (φ : WrappedExpr)

/-! ## Storage fields -/

/-- A field write whose target is already simple: one taclet, one update.
The shortest derivation the calculus draws. -/
sol_derivation fieldWriteSimple :
    seq!{ ⟹ <[ alice.age = ageVal ]> ‹φ› }
  ⇝[.storageFieldWriteSave]
    seq!{ ⟹ { storage := save(alice.age, ageVal) } <[ ]> ‹φ› }

/-- **The headline.** A deep field write: the value is frozen into `rv`, the
path captured into `sp`, the write performed, and the four accumulated updates
merged into the one parallel update the calculus writes. -/
sol_derivation deepFieldWrite :
    seq!{ ⟹ <[ alice.account.balance = 10 ]> ‹φ› }
  ⇝[.storageFieldWriteUnfoldLeftFst]
    seq!{ ⟹ <[ uint rv = 10;
                Account storage sp = alice.account;
                sp@Account.balance = rv ]> ‹φ› }
  ⇝*[.localValueDeclInitDrop, .valueDeclSkip, .localValueAssign, .storagePlaceAlias]
    seq!{ ⟹ { rv@uint := default(uint) } { rv@uint := 10 }
              { sp@Account := path(alice.account) }
              <[ sp@Account.balance = rv@uint ]> ‹φ› }
  ⇝[.storageFieldWriteSave]
    seq!{ ⟹ { rv@uint := default(uint) } { rv@uint := 10 }
              { sp@Account := path(alice.account) }
              { storage := save(sp@Account.balance, rv@uint) } <[ ]> ‹φ› }
  ⇝≡ seq!{ ⟹ { rv@uint := 10 ‖ sp@Account := path(alice.account)
               ‖ storage := save(alice.account.balance, 10) } <[ ]> ‹φ› }

/-- The read twin.  No value operand to freeze, so the three rewrite steps are
exactly three rules, and the merge substitutes the alias into the `find`. -/
sol_derivation deepFieldRead :
    seq!{ ⟹ <[ result = alice.account.balance ]> ‹φ› }
  ⇝[.storageFieldReadUnfoldRightFst]
    seq!{ ⟹ <[ Account storage sp = alice.account;
                result = sp@Account.balance ]> ‹φ› }
  ⇝[.storagePlaceAlias]
    seq!{ ⟹ { sp@Account := path(alice.account) }
              <[ result = sp@Account.balance ]> ‹φ› }
  ⇝[.storageFieldReadFind]
    seq!{ ⟹ { sp@Account := path(alice.account) }
              { result := sp@Account.balance } <[ ]> ‹φ› }
  ⇝≡ seq!{ ⟹ { sp@Account := path(alice.account)
               ‖ result := alice.account.balance } <[ ]> ‹φ› }

/-! ## Storage roots -/

/-- A root write and a post-increment: two terminal rules, two update lines,
and no capture to elide. -/
sol_derivation rootWriteThenIncrement :
    seq!{ ⟹ <[ age = 10; age++ ]> ‹φ› }
  ⇝[.storageRootWriteStore]
    seq!{ ⟹ { storage := save(age, 10) } <[ age++ ]> ‹φ› }
  ⇝[.storageRootIncDec .postInc]
    seq!{ ⟹ { storage := save(age, 10) } { bump(age++) } <[ ]> ‹φ› }

/-! ## Storage arrays: the branching line

An indexed access is guarded, and the calculus draws its last line as two
stacked sequents -- the in-bounds goal and the out-of-bounds one.  Here the
guard becomes the antecedent of each successor, and the `else` branch is the
generated `revert();` that `revertBox`/`revertDiamond` then close with `⊤`/`⊥`.
The calculus draws the split and that closure as one line; they are two steps. -/

/-- Box: out of bounds is vacuously fine. -/
sol_derivation arrayReadBox :
    seq!{ ⟹ [ v = values[i] ] ‹φ› }
  ⇝[.storageIndexReadArrayFindBox]
    [ seq!{ inBounds(values[i]) ⟹ { v := values[i] } [ ] ‹φ› },
      seq!{ ¬inBounds(values[i]) ⟹ [ revert() ] ‹φ› } ]
  ⇝[.revertBox]
    [ seq!{ inBounds(values[i]) ⟹ { v := values[i] } [ ] ‹φ› },
      seq!{ ¬inBounds(values[i]) ⟹ ⊤ } ]

/-- Diamond: out of bounds refutes the judgment. -/
sol_derivation arrayReadDiamond :
    seq!{ ⟹ < v = values[i] > ‹φ› }
  ⇝[.storageIndexReadArrayFindDiamond]
    [ seq!{ inBounds(values[i]) ⟹ { v := values[i] } < > ‹φ› },
      seq!{ ¬inBounds(values[i]) ⟹ < revert() > ‹φ› } ]
  ⇝[.revertDiamond]
    [ seq!{ inBounds(values[i]) ⟹ { v := values[i] } < > ‹φ› },
      seq!{ ¬inBounds(values[i]) ⟹ ⊥ } ]

/-- The write twin, box. -/
sol_derivation arrayWriteBox :
    seq!{ ⟹ [ values[i] = 100 ] ‹φ› }
  ⇝[.storageIndexWriteArraySaveBox]
    [ seq!{ inBounds(values[i]) ⟹ { storage := save(values[i], 100) } [ ] ‹φ› },
      seq!{ ¬inBounds(values[i]) ⟹ [ revert() ] ‹φ› } ]
  ⇝[.revertBox]
    [ seq!{ inBounds(values[i]) ⟹ { storage := save(values[i], 100) } [ ] ‹φ› },
      seq!{ ¬inBounds(values[i]) ⟹ ⊤ } ]

/-- A mapping key uses the same selector and has **no** bounds goal, so the
line does not branch at all. -/
sol_derivation mappingRead :
    seq!{ ⟹ <[ v = balances[i] ]> ‹φ› }
  ⇝[.storageIndexReadMappingFind]
    seq!{ ⟹ { v := balances[i] } <[ ]> ‹φ› }

/-! ## Push and pop -/

sol_derivation arrayPush :
    seq!{ ⟹ <[ values.push(42) ]> ‹φ› }
  ⇝[.storagePushValueSave]
    seq!{ ⟹ { storage := push(values, 42) } <[ ]> ‹φ› }

/-- `pop` is guarded on the array being non-empty, so it branches like an
indexed access. -/
sol_derivation arrayPop :
    seq!{ ⟹ [ values.pop() ] ‹φ› }
  ⇝[.storagePopSaveBox]
    [ seq!{ nonEmpty(values) ⟹ { storage := pop(values) } [ ] ‹φ› },
      seq!{ ¬nonEmpty(values) ⟹ [ revert() ] ‹φ› } ]
  ⇝[.revertBox]
    [ seq!{ nonEmpty(values) ⟹ { storage := pop(values) } [ ] ‹φ› },
      seq!{ ¬nonEmpty(values) ⟹ ⊤ } ]

/-! ## Delete -/

sol_derivation deleteField :
    seq!{ ⟹ <[ delete alice.account ]> ‹φ› }
  ⇝[.storageDeleteSimpleTarget]
    seq!{ ⟹ { storage := clear(alice.account) } <[ ]> ‹φ› }

/-! ## Payment

Upstream states the transfer rule as a box taclet with a single update and a
diamond taclet that splits off a funds *obligation*.  Lean merges the two into
one guarded pair, so the diamond line branches into the booking and a revert
rather than into a booking and an obligation -- the difference is recorded in
`docs/lean-key-rule-map.md`, and it is the interpreter's reading: an unfunded
`transfer` reverts. -/

sol_derivation transferBox :
    seq!{ ⟹ [ to.transfer(amount) ] ‹φ› }
  ⇝[.transferNoCallback]
    [ seq!{ funded(amount) ⟹ { transfer(to, amount) } [ ] ‹φ› },
      seq!{ ¬funded(amount) ⟹ [ revert() ] ‹φ› } ]
  ⇝[.revertBox]
    [ seq!{ funded(amount) ⟹ { transfer(to, amount) } [ ] ‹φ› },
      seq!{ ¬funded(amount) ⟹ ⊤ } ]

/-- A non-simple amount is captured first, exactly as upstream's
`transferUnfoldRightSndArgument` does -- and the capture's update is what the
funds guard is then read under.  The chain stops at the capture: the split's
antecedent would carry that stack (`seq!` writes it as a `{…}` prefix on the
formula, see `Update/SequentSyntax.lean`), and the calculus abbreviates it by
substituting instead -- it writes `0 ≤ x + 2 ≤ selfBalance`.

The second line also shows what KeY's guarded pair costs on an operator that
does not need a guard: `binopAssignment` is stated as `\if(se2 != 0)` for every
operator and specialises the condition, so `+` still produces a `\else` branch
-- with the antecedent `¬⊤`, which is what makes it vacuous. -/
sol_derivation transferCapturedAmount :
    seq!{ ⟹ [ to.transfer(i + 2) ] ‹φ› }
  ⇝*[.transferUnfoldRightSndArgument, .localValueDeclInitDrop, .valueDeclSkip,
     .binopAssignment .add]
    [ seq!{ ⟹ { pv@uint := default(uint) } { pv@uint := i + 2 }
                [ to.transfer(pv@uint) ] ‹φ› },
      seq!{ { pv@uint := default(uint) } ¬⊤ ⟹ { pv@uint := default(uint) }
                [ revert(); to.transfer(pv@uint) ] ‹φ› } ]

/-! ## Require -/

/-- `require` is the calculus's own guarded pair, and the only rule whose
guard is a program expression rather than a property of the store. -/
sol_derivation requireSimple :
    seq!{ ⟹ [ require(flag) ] ‹φ› }
  ⇝[.requireSimple]
    [ seq!{ flag ⟹ [ ] ‹φ› },
      seq!{ ¬flag ⟹ [ revert() ] ‹φ› } ]
  ⇝[.revertBox]
    [ seq!{ flag ⟹ [ ] ‹φ› },
      seq!{ ¬flag ⟹ ⊤ } ]

end

/-! ## The lines, run

`Sequent.check` is the semantics of a line: apply the accumulated update, then
run what is left of the program, then read the postcondition.  So a derivation
can be checked end to end against the interpreter -- the first line and the
last agree on a concrete store.

These are the only `native_decide` in this file; the derivations above are
ordinary proofs. -/

/-- The store the calculus's examples are read in, with the frozen value
operand bound: `rv` is what the freeze introduces, and a line written *after*
the freeze mentions it. -/
def store : Semantics.State :=
  State.exampleStore.setEnv "rv" (Semantics.Binding.val (Semantics.PrimVal.int 10))

/-- The headline: the merged parallel update produces the same verdict as the
program it came from. -/
example :
    (seq!{ ⟹ <[ alice.account.balance = 10 ]>
            (alice.account.balance == 10) }).check store
      = (seq!{ ⟹ { rv@uint := 10 ‖ sp@Account := path(alice.account)
                   ‖ storage := save(alice.account.balance, 10) } <[ ]>
              (alice.account.balance == 10) }).check store := by
  native_decide

/-- …and both of them hold. -/
example :
    (seq!{ ⟹ { rv@uint := 10 ‖ sp@Account := path(alice.account)
               ‖ storage := save(alice.account.balance, 10) } <[ ]>
            (alice.account.balance == 10) }).Holds store := by
  native_decide

/-- The root chain, first line against last. -/
example :
    (seq!{ ⟹ <[ age = 10; age++ ]> (age == 11) }).check State.exampleStore
      = (seq!{ ⟹ { storage := save(age, 10) } { bump(age++) } <[ ]>
              (age == 11) }).check State.exampleStore := by
  native_decide

/-- A *branching* line: on a store where `values` is empty the in-bounds goal
is vacuous and the box line holds, which is the content of the `⊤`. -/
example :
    (Frontier.check
      [ seq!{ inBounds(values[i]) ⟹ { v := values[i] } [ ] (v == 0) },
        seq!{ ¬inBounds(values[i]) ⟹ ⊤ } ]
      (State.exampleStore.setEnv "i" (Semantics.Binding.val
        (Semantics.PrimVal.int 3)))) = true := by
  native_decide

end Solidity.Examples.Sequents
