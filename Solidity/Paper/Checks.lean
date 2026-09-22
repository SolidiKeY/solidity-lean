import Solidity.Paper.Storage
import Solidity.Paper.Memory
import Solidity.Paper.CrossDomain
import Solidity.Paper.Control

/-!
# The calculus's worked examples — the lines, run

The semantic twins of the chains: `Sequent.check` applied to the first line of
a chain and to its last, on a concrete store.  One per section, which is what
`docs/paper-parity.md` counts.
-/

namespace Solidity.Examples.Paper

open Rules StandardExample SoliditySyntax Solidity.Examples Semantics

set_option maxHeartbeats 8000000


/-! ## The lines, run

`Sequent.check` is the semantics of a line: apply the accumulated update, then
run what is left of the program, then read the postcondition.  So a chain can
be checked end to end against the interpreter — the first line and the last
agree on a concrete store.

These are the only `native_decide` in this file; the chains above are ordinary
proofs.  They write `<[ ]>` out: a *comparison* postcondition keeps its
modality, because its parentheses belong to the comparison
(`Update/SequentSyntax.lean`).  The bare line is for the calculus's `φ`. -/

/-- The store the calculus's examples are read in, with the frozen value
operand bound: `se` is what the freeze introduces, and a line written *after*
the freeze mentions it. -/
def store : Semantics.State :=
  State.exampleStore.setEnv "se" (Semantics.Binding.val (Semantics.PrimVal.int 10))

/-- The headline: the merged parallel update produces the same verdict as the
program it came from. -/
example :
    (seq!{ => <[ alice.account.balance = 10 ]>(alice.account.balance == 10) }).check store
      = (seq!{ => { se@uint := 10 ‖ sp@Account := alice.account
                    ‖ storage := save(storage, alice.account.balance, 10) }
               <[ ]>(alice.account.balance == 10) }).check store := by
  native_decide

/-- …and both of them hold. -/
example :
    (seq!{ => { se@uint := 10 ‖ sp@Account := alice.account
                ‖ storage := save(storage, alice.account.balance, 10) }
            <[ ]>(alice.account.balance == 10) }).Holds store := by
  native_decide

/-- The root chain, first line against last. -/
example :
    (seq!{ => <[ age = 10; age++ ]>(age == 11) }).check State.exampleStore
      = (seq!{ => { storage := save(storage, age, 10) } { bump(age++) }
               <[ ]>(age == 11) }).check State.exampleStore := by
  native_decide

/-- A *branching* line: on a store where `values` is empty the in-bounds goal
is vacuous and the box line holds, which is the content of the `⊤`. -/
example :
    (Frontier.check
      [ seq!{ inBounds(values[i]) => { v := values[i] } [ ](v == 0) },
        seq!{ ¬inBounds(values[i]) => ⊤ } ]
      (State.exampleStore.setEnv "i" (Semantics.Binding.val
        (Semantics.PrimVal.int 3)))) = true := by
  native_decide

/-- The store the array and delete chains are read in: the calculus's store
with the index bound, so a branching line has a verdict. -/
def storeI0 : Semantics.State :=
  State.exampleStore.setEnv "i" (Semantics.Binding.val (Semantics.PrimVal.int 0))

/-- **Allocation, run.** A freshly allocated memory array is empty, so the
in-bounds goal of a write into it is vacuous and the box line holds.  That `⊤`
is the whole reason the calculus's `memoryArrayFreshAlloc` writes a length:
`memoryArrayAlloc` above allocates, and without a size nothing can be stored. -/
example :
    (Frontier.check
      [ seq!{ { mv := freshId(alloc(UintArray)) ‖ memory := alloc(UintArray) } inBounds(mv@UintArray[i]) =>
                { mv := freshId(alloc(UintArray)) ‖ memory := alloc(UintArray) }
                { memory := write(memory, mv@UintArray[i], 100) } [ ](i == 0) },
        seq!{ { mv := freshId(alloc(UintArray)) ‖ memory := alloc(UintArray) } ¬inBounds(mv@UintArray[i]) =>
                { mv := freshId(alloc(UintArray)) ‖ memory := alloc(UintArray) } ⊤ } ]
      storeI0) = true := by
  native_decide

/-- **Memory, run.** The aliasing chain: a write through the alias is a write
at the identity `carol.account` names, so the path itself reads it back. -/
example :
    (seq!{ => <[ Account memory mv = carol.account;
                 mv@Account.balance = 100 ]>(carol.account.balance == 100) }).check
        State.exampleStore
      = (seq!{ => { mv@Account := ref(carol.account) }
                  { memory := write(memory, mv@Account.balance, 100) }
                  <[ ]>(carol.account.balance == 100) }).check
          State.exampleStore := by
  native_decide

/-- **Cross-domain, run.** The storage-to-memory copy: `alloc` takes the
storage image, so the memory read afterwards finds what the storage write
put there. -/
example :
    (seq!{ => <[ alice.age = 34; Person memory mv2 = alice;
                 v = mv2@Person.age ]>(v == 34) }).check State.exampleStore
      = (seq!{ => { storage := save(storage, alice.age, 34) } { mv2 := freshId(alloc(Person, alice)) ‖ memory := alloc(Person, alice) }
                  { v := mv2@Person.age } <[ ]>(v == 34) }).check
          State.exampleStore := by
  native_decide

/-- **Push after pop, run.** The calculus's `sec:push-pop-example`: a slot the
`pop()` cleared is not restored by the next `push()`, so the value written
before the pop is not observable through the returned reference.  Written in
the *diamond*, which is the claim's other half — the program reaches the read
without reverting.  Run on `testSuiteStore`, the store that has `tokens`.

The two companion programs of that section, which write through a storage
alias to the popped slot, are not here; `docs/paper-parity.md` says what
happens to them. -/
theorem pushPopSlotCleared :
    (Frontier.check
      [ seq!{ => < (tokens@@TokenArray).push();
                   (tokens@@TokenArray)[0].value = 7;
                   (tokens@@TokenArray).pop();
                   uint r = (tokens@@TokenArray).push().value >(r == 0) } ]
      State.testSuiteStore) = true := by
  native_decide

/-- **Payment, run.** The unconditional booking against the program it came
from: the box rule carries no funds check, and on a store where the transfer
is covered the two agree. -/
example :
    (Frontier.check [ seq!{ => [ to.transfer(5) ](i == 0) } ] storeI0)
      = (Frontier.check
          [ seq!{ => { transfer(to, 5) } [ ](i == 0) } ] storeI0) := by
  native_decide

/-- The delete chain, first line against last, on the calculus's store: the
member read after `delete alice.account;` is the type's default. -/
example :
    (seq!{ => <[ alice.account.balance = 100; alice.account.token.value = 7;
                 delete alice.account; b = alice.account.balance;
                 v = alice.account.token.value ]>(v == 0) }).check
        State.exampleStore
      = (seq!{ => { se@uint := defVal(uint) } { se@uint := 100 }
                  { sp@Account := alice.account }
                  { storage := save(storage, sp@Account.balance, se@uint) }
                  { se@uint := defVal(uint) } { se@uint := 7 }
                  { sp@Token := alice.account.token }
                  { storage := save(storage, sp@Token.value, se@uint) }
                  { storage := delAt(storage, alice.account) }
                  { sp@Account := alice.account } { b := sp@Account.balance }
                  { sp@Token := alice.account.token }
                  { v := sp@Token.value } <[ ]>(v == 0) }).check
          State.exampleStore := by
  native_decide

end Solidity.Examples.Paper
