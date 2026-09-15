import Solidity.Examples.Common
import Solidity.DecEq

/-!
# The calculus's worked examples

One chain per worked example of the calculus, written the way the calculus
writes them: the program shrinks on the right while the accumulated update
grows on the left, and the chain ends not at an empty program but at a formula
under one update.

```
    => <[ alice.account.balance = 10 ]>(φ)
~>  => <[ uint rv = 10; Account storage sp = alice.account; sp.balance = rv ]>(φ)
~*> => { rv := 10 ‖ sp := alice·account } <[ sp.balance = rv ]>(φ)
~>  => { rv := 10 ‖ sp := alice·account ‖ storage := save(alice·account·balance, 10) } (φ)
```

Each is one `sol_derivation` and each is a named theorem about `⇝ᵘ*`, so a
derivation is a reusable fact rather than a picture.  **No rule names appear
on the arrows**: `~>` and `~*>` ask `UniquenessAux.candidate` for the rule at
each step, so a rule rename or a changed residual is a build failure here, not
a stale list to re-derive.  To see what fired, put
`set_option trace.solidity.steps true in` above a chain.

## How to read a line

`=>` is the turnstile the calculus draws only when a line branches; writing it
on every line is what makes a chain uniform.  What precedes it is the
antecedent, each formula under the update stack it is read in; what follows is
the accumulated update and then the goal.  The last line drops the modality,
as the calculus does, and `(φ)` is the opaque postcondition
(`Update/SequentSyntax.lean` for the grammar, `.claude/rules/derivations.md`
for the conventions).

A **branching line is a bracketed list**: a guarded rule leaves one sequent
open per goal whose mode applies, which is how the calculus draws an array
access.  In the combined modality `⟨[ … ]⟩` both modes apply, so an
out-of-bounds branch appears twice — closed with `⊤` for the box reading and
`⊥` for the diamond one.  A chain written in one modality shows one of them.

## Where this differs from the calculus, and why

**The scratch names are Lean's.**  The calculus writes `pv` for a frozen value
operand and `acc` for a storage alias; the rules here bind `rv` and `sp`, and
`Rules.lean` records why the calculus's own examples are inconsistent about
it.  A stack scratch name carries its type — `rv@uint`, `pv@bool`,
`sp@UintArray` — because `SoliditySyntax.aliasKind` is a name-only table that
cannot see it.

**The freeze costs three steps the calculus does not draw.**  A value operand
is frozen before the target is captured (`Counterexamples/ErrorOrder.lean` is
why), which is `localValueDeclInitDrop` → `valueDeclSkip` → `localValueAssign`.
They are inside a `~*>`, as the calculus elides them.

**The merge is part of an arrow, not a line of its own.**  The calculus's last
line is usually not a rule application but the update calculus collapsing
`{u}{v}` into `{u ‖ {u}v}`.  `~>`/`~*>` absorb it: a step lands on the target
as soon as the two agree on every antecedent and goal, and what is left is
`Upd.Par.seq_single` and the reader lemmas of `Update/Merge.lean`.  Where those
lemmas do not reach — an earlier `storage`/`memory` write, a `push`, an
`alloc` — the line stays in the stacked `{U₁}{U₂}` form the derivation
accumulated, which is equally what the calculus writes before it merges.

**Every chain has a semantic twin.**  `Sequent.check` runs a line against the
interpreter, and the end of this file checks the first and the last line of
the headline chains against each other on a concrete store.  The chains
themselves add no axiom: a pinned step goes through
`UniquenessAux.firstStepCase_box`, whose exclusivity theorem is decided by
`native_decide` in `Uniqueness.lean`, which is the block layer's proof route.

## What has no chain here

Four kinds of program the calculus draws cannot be written in the surface
notation, and the reason is informative in each case.

1. **Call-valued operands** — `values.push(makeValue());`,
   `choosePersonMem().account = makeAccount();`.  `Stmt.callStmt` has no
   surface syntax at all (`Examples/Taclets/FunctionCallOps.lean` drops to
   constructors for the same reason).  The rules exist
   (`functionCallArgCapture`, `functionBodyExpand`); the notation does not.
2. **Bare memory declarations** — `Person memory carol;`.  `carol` is already
   a memory root in `SoliditySyntax.rootExpr`, so the chains here start after
   the declaration.  `memoryDeclFreshAlloc` is exercised in
   `Examples/MemoryBasic.lean`.
3. **First-order side conditions** — `sizeNotNegative`, which the pop-after-push
   example needs.  It adds `0 ≤ find(storage, sp·length)` to the antecedent
   rather than rewriting a program, so it has no `RuleName`; its content is
   `WellFormedConsumers.lean`'s row for `pop`.
4. **The memory identity layer** — the calculus's `new(mem, r) →` freshness
   prefix, `idC`/`add`, and the lazy `copySt`/`copyMem` views.  Those have no
   first-order spelling here (`Update/Eval.lean`); the cross-domain chains
   below end at the `alloc`/`copyMem` element the Lean rule states instead.

Also not a chain: **the unfunded transfer**.  It is `to.transfer(5);` again and
what differs is the *state*, not the derivation — the semantic layer covers it
(`Evm/Examples.lean`, `Examples/Taclets/NetOps.lean`).
-/

namespace Solidity.Examples.Paper

open Rules StandardExample SoliditySyntax Solidity.Examples Semantics

set_option maxHeartbeats 8000000

section
variable (φ : WrappedExpr)

/-! ## 1 · Storage fields and roots -/

/-! ### `alice.age = ageVal;`
The shortest derivation the calculus draws: the target is already simple, so
one taclet produces one update. -/

sol_derivation fieldWriteSimple :
    => <[ alice.age = ageVal ]>(φ)
  ~> => { storage := save(alice.age, ageVal) } (φ)

/-! ### `Account storage acc = bob.account; alice.account = acc;`
The write stores the value found at the alias path, not the alias path itself
— which is why the second update is a `copy` and not a `save` of `acc`. -/

sol_derivation fieldWriteFromAlias :
    => <[ Account storage acc = bob.account; alice.account = acc ]>(φ)
  ~*> => { acc := path(bob.account) } { storage := copy(alice.account, acc) } (φ)

/-! ### `alice.account.balance = 10;` — **the headline**
The value is frozen into `rv`, the path captured into `sp`, the write
performed, and the accumulated updates merged into the one parallel update the
calculus writes. -/

sol_derivation deepFieldWrite :
    => <[ alice.account.balance = 10 ]>(φ)
  ~> => <[ uint rv = 10;
           Account storage sp = alice.account;
           sp@Account.balance = rv ]>(φ)
  ~*> => { rv@uint := 10 ‖ sp@Account := path(alice.account) }
          <[ sp@Account.balance = rv@uint ]>(φ)
  ~> => { rv@uint := 10 ‖ sp@Account := path(alice.account)
          ‖ storage := save(alice.account.balance, 10) } (φ)

/-! ### `v = alice.account.balance;`
The read twin.  No value operand to freeze, so the three rewrite steps are
exactly three rules, and the merge substitutes the alias into the `find`. -/

sol_derivation deepFieldRead :
    => <[ v = alice.account.balance ]>(φ)
  ~> => <[ Account storage sp = alice.account; v = sp@Account.balance ]>(φ)
  ~> => { sp@Account := path(alice.account) } <[ v = sp@Account.balance ]>(φ)
  ~> => { sp@Account := path(alice.account) ‖ v := alice.account.balance } (φ)

/-! ### `alice.account.token.value = 5;`
One selector deeper, and yet the *same* chain: the unfold rule hoists the whole
path prefix in one step, so depth costs nothing.  The calculus takes seven
lines here because it unfolds one selector at a time. -/

sol_derivation deeperFieldWrite :
    => <[ alice.account.token.value = 5 ]>(φ)
  ~*> => { rv@uint := 5 ‖ sp@Token := path(alice.account.token)
           ‖ storage := save(alice.account.token.value, 5) } (φ)

/-! ### `uint v = total;` — reading a storage root -/

sol_derivation rootRead :
    => <[ uint v = total ]>(φ)
  ~*> => { v := default(uint) } { v := total } (φ)

/-! ### `alice = bob;` / `alice = pp;` — whole-struct write
A root write from another root is a deep *copy*, and that is the whole content
of the line: `store(storage, alice, select(storage, bob))` in the calculus's
spelling. -/

sol_derivation rootWriteFromGlobal :
    => <[ alice = bob ]>(φ)
  ~> => { storage := copy(alice, bob) } (φ)

sol_derivation rootWriteFromAlias :
    => <[ alice = pp ]>(φ)
  ~> => { storage := copy(alice, pp) } (φ)

/-! ### local storage rebinding versus global root copy
The calculus's point, in two chains that share no rule: the same syntactic
form is a *rebind* for a local reference and a deep copy for a global root.
Note that the rebind leaves **two** `acc` bindings on the stack — the merge
law absorbs them, but only once the second is read in the first's state. -/

sol_derivation localRebindThenWrite :
    => <[ Account storage acc = alice.account; acc = bob.account;
          acc.balance = 10 ]>(φ)
  ~*> => { acc := path(alice.account) } { acc := path(bob.account) }
          { storage := save(acc.balance, 10) } (φ)

sol_derivation globalRootCopy :
    => <[ account@@Account = bob.account ]>(φ)
  ~> => { storage := copy(account@@Account, bob.account) } (φ)

/-! ## 2 · Storage arrays

An indexed access is guarded, and the calculus draws its last line as two
stacked sequents: the in-bounds goal and the out-of-bounds one, which executes
the generated `revert();` that `revertBox`/`revertDiamond` then close with
`⊤`/`⊥`.  The calculus draws the split and that closure as one line; they are
two steps, and `~*>` runs both. -/

/-! ### `v = values[i];` — box and diamond
Out of bounds is vacuously fine for the box and refutes the diamond.  That is
the only difference between the two, which is why the calculus draws them as
one example. -/

sol_derivation arrayIndexReadBox :
    => [ v = values[i] ](φ)
  ~*> [ inBounds(values[i]) => { v := values[i] } [ ](φ),
        ¬inBounds(values[i]) => ⊤ ]

sol_derivation arrayIndexReadDiamond :
    => < v = values[i] >(φ)
  ~*> [ inBounds(values[i]) => { v := values[i] } < >(φ),
        ¬inBounds(values[i]) => ⊥ ]

/-! ### `values[i] = 100;` — the write twin -/

sol_derivation arrayIndexWrite :
    => [ values[i] = 100 ](φ)
  ~*> [ inBounds(values[i]) => { storage := save(values[i], 100) } [ ](φ),
        ¬inBounds(values[i]) => ⊤ ]

/-! ### `v = balances[i];`
A mapping key uses the same selector and has **no** bounds goal, so the line
does not branch at all. -/

sol_derivation mappingIndexRead :
    => <[ v = balances[i] ]>(φ)
  ~> => { v := balances[i] } (φ)

/-! ### `Token storage tokRef = bob.account.token; tokens[i] = tokRef;`
A struct-valued element assigned from a storage alias copies the value found
at that path.  Written in the box, so the out-of-bounds branch is the `⊤` —
and note it carries the capture that preceded the split. -/

sol_derivation arrayIndexWriteRefSource :
    => [ Token storage tokRef = bob.account.token;
         (tokens@@TokenArray)[i] = tokRef ](φ)
  ~*> [ { tokRef := path(bob.account.token) } inBounds((tokens@@TokenArray)[i]) =>
          { tokRef := path(bob.account.token) }
          { storage := copy((tokens@@TokenArray)[i], tokRef) } [ ](φ),
        { tokRef := path(bob.account.token) } ¬inBounds((tokens@@TokenArray)[i]) =>
          { tokRef := path(bob.account.token) } ⊤ ]

/-! ### `alice.accounts[i] = 100;` — a nonsimple path under an index
The value is frozen, then the path captured into `sp`, and only then is the
bounds goal read — under everything accumulated before it, which is what the
`{…}` prefix on the antecedent says.

Written **unmerged**, which is also what a branching line has to be: the merge
closes the first sequent of a frontier and the rest of the list has to be the
line the derivation actually accumulated (`upd_merge` in `Examples/Common.lean`
opens one update equality, and `Frontier.Equiv` on the tail is reflexivity).
The calculus merges the in-bounds line only after it has dropped the other. -/

sol_derivation nonsimplePathIndexWrite :
    => [ alice.accounts[i] = 100 ](φ)
  ~*> [ { rv@uint := default(uint) } { rv@uint := 100 }
          { sp@UintArray := path(alice.accounts) } inBounds(sp@UintArray[i]) =>
          { rv@uint := default(uint) } { rv@uint := 100 }
          { sp@UintArray := path(alice.accounts) }
          { storage := save(sp@UintArray[i], rv@uint) } [ ](φ),
        { rv@uint := default(uint) } { rv@uint := 100 }
          { sp@UintArray := path(alice.accounts) } ¬inBounds(sp@UintArray[i]) =>
          { rv@uint := default(uint) } { rv@uint := 100 }
          { sp@UintArray := path(alice.accounts) } ⊤ ]

/-! ### `values.push(42);` and `tokens.pop();`
`push` is unguarded; `pop` is guarded on the array being non-empty, so it
branches like an indexed access. -/

sol_derivation arrayPush :
    => <[ values.push(42) ]>(φ)
  ~> => { storage := push(values, 42) } (φ)

sol_derivation arrayPopBox :
    => [ (tokens@@TokenArray).pop() ](φ)
  ~*> [ nonEmpty((tokens@@TokenArray)) =>
          { storage := pop((tokens@@TokenArray)) } [ ](φ),
        ¬nonEmpty((tokens@@TokenArray)) => ⊤ ]

sol_derivation arrayPopDiamond :
    => < (tokens@@TokenArray).pop() >(φ)
  ~*> [ nonEmpty((tokens@@TokenArray)) =>
          { storage := pop((tokens@@TokenArray)) } < >(φ),
        ¬nonEmpty((tokens@@TokenArray)) => ⊥ ]

/-! ### the push family
`push(arr)` with no value is the bare `arr.push();`; `push(arr, v)` the
one-argument form.  A nonsimple receiver is captured into `sp` first, and the
*slot* the push returns is a path like any other, which is what lets
`tokens.push().value = 11;` write through it. -/

sol_derivation pushRefSource :
    => <[ (tokens@@TokenArray).push(tokRef) ]>(φ)
  ~*> => { storage := push((tokens@@TokenArray), tokRef) } (φ)

sol_derivation pushNonsimpleReceiver :
    => <[ alice.account.tokens.push(tokRef) ]>(φ)
  ~*> => { sp@TokenArray := path(alice.account.tokens) }
          { storage := push(sp@TokenArray, tokRef) } (φ)

sol_derivation pushBare :
    => <[ (tokens@@TokenArray).push() ]>(φ)
  ~> => { storage := push((tokens@@TokenArray)) } (φ)

sol_derivation pushSlotWrite :
    => <[ (tokens@@TokenArray).push().value = 11 ]>(φ)
  ~*> => { rv@uint := default(uint) } { rv@uint := 11 }
          { sp@Token := path((tokens@@TokenArray).push()) }
          { storage := save(sp@Token.value, rv@uint) } (φ)

/-! ### `values.push(); values.pop();` — pop after push
The smallest program whose *diamond* proof needs the calculus's
`sizeNotNegative`, a first-order side condition with no `RuleName` here (see
the header).  What the rules give is the guarded pair, with the `pop` guard
read under the `push` that precedes it. -/

sol_derivation popAfterPush :
    => <[ values.push(); values.pop() ]>(φ)
  ~*> [ { storage := push(values) } nonEmpty(values) =>
          { storage := push(values) } { storage := pop(values) } <[ ]>(φ),
        { storage := push(values) } ¬nonEmpty(values) =>
          { storage := push(values) } ⊤,
        { storage := push(values) } ¬nonEmpty(values) =>
          { storage := push(values) } ⊥ ]

/-! ### `age = 10; age++;` — a root write and a post-increment
Two terminal rules, two update lines, and no capture to elide.  The second is
the pair `{age := age + 1 ‖ …}` that `bump` names. -/

sol_derivation rootWriteThenIncrement :
    => <[ age = 10; age++ ]>(φ)
  ~> => { storage := save(age, 10) } <[ age++ ]>(φ)
  ~> => { storage := save(age, 10) } { bump(age++) } (φ)

/-! ## 3 · Delete -/

sol_derivation deleteField :
    => <[ delete alice.account ]>(φ)
  ~> => { storage := clear(alice.account) } (φ)

/-! ### `ledger.nonce = 42; delete ledger; v = ledger.nonce;`
The calculus's struct-reset program: `delete` on a struct keeps its mapping
members and resets the rest, so the read afterwards succeeds — and the three
updates stay stacked, because the merge law has no reader for a `find` over a
`clear`. -/

sol_derivation deleteStructThenRead :
    => <[ (ledger@@Ledger).nonce = 42; delete (ledger@@Ledger);
          v = (ledger@@Ledger).nonce ]>(φ)
  ~*> => { storage := save((ledger@@Ledger).nonce, 42) }
          { storage := clear((ledger@@Ledger)) }
          { v := (ledger@@Ledger).nonce } (φ)

/-! ## 4 · Compound assignment

`alice.age += 1;` is one write-back of `alice.age + 1` computed at the
target's type, not a read–compute–write desugaring.  KeY states the family
with a divisor guard for every operator and specialises the condition, so `+`
still produces a `\else` branch — with the antecedent `¬⊤`, which is what
makes it vacuous, and in the combined modality it appears once per mode. -/

sol_derivation fieldCompoundAssign :
    => <[ alice.age += 1 ]>(φ)
  ~*> [ => { alice.age += 1 } (φ),
        ¬⊤ => ⊤,
        ¬⊤ => ⊥ ]

/-! ## 5 · Memory

A memory alias is a *reference*: the alias update binds the identity the path
reads (`ref`), not a copy of the value, so a write through the alias and a
write through the original path are the same write.  That is the whole point
of the calculus's memory-aliasing example, and it is what makes the second
update below a `write` at `mv`'s identity rather than at `carol`'s. -/

/-! ### `Account memory carolAcc = carol.account; carolAcc.balance = 100;`
The calculus starts this one with `Person memory carol;`, which allocates a
fresh identity; `carol` is already a memory root here, so the chain starts
after the declaration. -/

sol_derivation memoryAliasWrite :
    => <[ Account memory mv = carol.account; mv@Account.balance = 100 ]>(φ)
  ~*> => { mv@Account := ref(carol.account) }
          { memory := write(mv@Account.balance, 100) } (φ)

/-! ### `carol.account = david.account;`
A reference-valued field assignment: the source is *aliased*, not snapshotted,
so both fields end up at one identity.  `writeRef`, not `write`. -/

sol_derivation memoryFieldCopy :
    => <[ carol.account = david.account ]>(φ)
  ~*> => { pv@Account := ref(david.account) }
          { memory := writeRef(carol.account, pv@Account) } (φ)

/-! ### `carol.account.balance = 10;` — the memory twin of the headline -/

sol_derivation memoryDeepFieldWrite :
    => <[ carol.account.balance = 10 ]>(φ)
  ~*> => { rv@uint := default(uint) } { rv@uint := 10 }
          { mv@Account := ref(carol.account) }
          { memory := write(mv@Account.balance, rv@uint) } (φ)

/-! ### `v = carol.account.balance;` — the memory twin of the read -/

sol_derivation memoryDeepFieldRead :
    => <[ v = carol.account.balance ]>(φ)
  ~*> => { mv@Account := ref(carol.account) } { v := mv@Account.balance } (φ)

/-! ### `Person memory carolAlias = carol;` — aliasing by declaration drop
One update and no heap write at all: an alias shares the identity. -/

sol_derivation memoryDeclAlias :
    => <[ Person memory mv2 = carol ]>(φ)
  ~*> => { mv2@Person := ref(carol) } (φ)

/-! ### `Token memory t = carol.account.token;`
The memory twin of the declaration drop, one selector deeper: two `ref`
bindings and still no heap write. -/

sol_derivation memoryDeclDeepAlias :
    => <[ Token memory mv3 = carol.account.token ]>(φ)
  ~*> => { mv@Account := ref(carol.account) }
          { mv3@Token := ref(mv@Account.token) } (φ)

/-! ### `carolAcc = david.account;`
A memory field on the right is **not** captured as an expression: the root is
rebound to the identity the read yields, and the heap is untouched. -/

sol_derivation memoryRootRebind :
    => <[ mv@Account = david.account ]>(φ)
  ~*> => { mv@Account := ref(david.account) } (φ)

/-! ### `v = carol;` and `carol = david;`
A memory root read binds an identity, and a root *assignment* is a rebinding
of exactly the same kind — the heap is untouched in both. -/

sol_derivation memoryRootRead :
    => <[ mv2@Person = carol ]>(φ)
  ~> => { mv2@Person := ref(carol) } (φ)

sol_derivation memoryRootAssign :
    => <[ carol = david ]>(φ)
  ~> => { carol := ref(david) } (φ)

/-! ## 6 · Memory delete

The calculus's point: `delete carol` resets the *identity's* members, so an
alias taken beforehand observes the reset.  The chains stay stacked: the merge
law has no reader for a `read` over a `clear`. -/

sol_derivation memoryDeleteRoot :
    => <[ Person memory mv2 = carol; carol.age = 34; delete carol;
          v = mv2@Person.age ]>(φ)
  ~*> => { mv2@Person := ref(carol) } { memory := write(carol.age, 34) }
          { clear(carol) } { v := mv2@Person.age } (φ)

sol_derivation memoryDeleteField :
    => <[ Account memory mv = carol.account; mv@Account.balance = 34;
          delete carol.account; v = mv@Account.balance ]>(φ)
  ~*> => { mv@Account := ref(carol.account) }
          { memory := write(mv@Account.balance, 34) }
          { clear(carol.account) } { v := mv@Account.balance } (φ)

/-! ## 7 · Memory arrays

A memory index access is bounds-guarded exactly as a storage one is, and a
nested path is two `ref` bindings before the write. -/

sol_derivation memoryArrayReadBox :
    => [ v = mv@UintArray[i] ](φ)
  ~*> [ inBounds(mv@UintArray[i]) => { v := mv@UintArray[i] } [ ](φ),
        ¬inBounds(mv@UintArray[i]) => ⊤ ]

sol_derivation memoryArrayWriteBox :
    => [ mv@UintArray[i] = 100 ](φ)
  ~*> [ inBounds(mv@UintArray[i]) =>
          { memory := write(mv@UintArray[i], 100) } [ ](φ),
        ¬inBounds(mv@UintArray[i]) => ⊤ ]

/-! ### `carol.account.values[i] = 42;` — a nested memory path under an index -/

sol_derivation memoryNestedArrayWrite :
    => [ carol.account.values[i] = 42 ](φ)
  ~*> [ { rv@uint := default(uint) } { rv@uint := 42 }
          { mv@Account := ref(carol.account) }
          { mv@UintArray := ref(mv@Account.values) } inBounds(mv@UintArray[i]) =>
          { rv@uint := default(uint) } { rv@uint := 42 }
          { mv@Account := ref(carol.account) }
          { mv@UintArray := ref(mv@Account.values) }
          { memory := write(mv@UintArray[i], rv@uint) } [ ](φ),
        { rv@uint := default(uint) } { rv@uint := 42 }
          { mv@Account := ref(carol.account) }
          { mv@UintArray := ref(mv@Account.values) } ¬inBounds(mv@UintArray[i]) =>
          { rv@uint := default(uint) } { rv@uint := 42 }
          { mv@Account := ref(carol.account) }
          { mv@UintArray := ref(mv@Account.values) } ⊤ ]

/-! ## 8 · Cross-domain copies

Where the calculus needs its identity layer — a freshness premise
`new(mem, r) →`, the identity constructor `idC`, and the lazy `copySt` view —
Lean's rule states one `alloc` element: a memory declaration initialised from
a storage path.  The chains below therefore end one line earlier than the
calculus's, and the difference is the header's point 4, not a disagreement
about the program. -/

/-! ### `Token memory t = alice.account.token;` — storage to memory
The source path is captured into a storage alias first, exactly as the
calculus does, and the declaration then allocates from it. -/

sol_derivation storageToMemoryNonsimplePath :
    => <[ Token memory mv3 = alice.account.token ]>(φ)
  ~*> => { sp@Account := path(alice.account) }
          { alloc(Token, mv3, sp@Account.token) } (φ)

/-! ### `alice.age = 25; Person memory carol = alice; v = carol.age;`
Six lines upstream, three rules here: the calculus spells out the `readCopySt`
resolution and the read-over-write that the terminal memory read already
performs. -/

sol_derivation storageToMemoryRootCopy :
    => <[ alice.age = 34; Person memory mv2 = alice; v = mv2@Person.age ]>(φ)
  ~*> => { storage := save(alice.age, 34) } { alloc(Person, mv2, alice) }
          { v := mv2@Person.age } (φ)

/-! ### the same at a *member* source, which needs the storage alias first -/

sol_derivation storageToMemoryMemberCopy :
    => <[ alice.account.balance = 10; Account memory mv = alice.account;
          v = mv@Account.balance ]>(φ)
  ~*> => { rv@uint := default(uint) } { rv@uint := 10 }
          { sp@Account := path(alice.account) }
          { storage := save(sp@Account.balance, rv@uint) }
          { alloc(Account, mv, alice.account) } { v := mv@Account.balance } (φ)

/-! ### `carol.age = 42; alice = carol; v = alice.age;` — memory to storage
The other direction, where the calculus's lazy `copyMem` view is one element
here. -/

sol_derivation memoryToStorageRootCopy :
    => <[ carol.age = 34; alice = carol; v = alice.age ]>(φ)
  ~*> => { memory := write(carol.age, 34) } { storage := copyMem(alice, carol) }
          { v := alice.age } (φ)

/-! ### the same from an alias, at a storage *field* target -/

sol_derivation memoryToStorageFromAlias :
    => <[ mv@Account.balance = 10; alice.account = mv@Account;
          v = alice.account.balance ]>(φ)
  ~*> => { memory := write(mv@Account.balance, 10) }
          { storage := copyMem(alice.account, mv@Account) }
          { sp@Account := path(alice.account) } { v := sp@Account.balance } (φ)

/-! ## 9 · Payment

Upstream states the transfer rule as a box taclet with a single update and a
diamond taclet that splits off a funds *obligation*.  Lean merges the two into
one guarded pair, so the diamond line branches into the booking and a revert
rather than into a booking and an obligation — the difference is recorded in
`docs/lean-key-rule-map.md`, and it is the interpreter's reading: an unfunded
`transfer` reverts.  The calculus writes the booking as the pair
`{selfBalance := selfBalance − se ‖ net := store(net, at(to), … − se)}`; here
it is the one element `transfer(to, se)`, which is that pair named. -/

sol_derivation transferBox :
    => [ to.transfer(5) ](φ)
  ~*> [ funded(5) => { transfer(to, 5) } [ ](φ),
        ¬funded(5) => ⊤ ]

sol_derivation transferDiamond :
    => < to.transfer(5) >(φ)
  ~*> [ funded(5) => { transfer(to, 5) } < >(φ),
        ¬funded(5) => ⊥ ]

/-! ### `owner.transfer(5);` — a storage receiver
The calculus cites `transfer_unfold_leftFstReceiver` because a storage root is
not a stack word.  In Lean `owner` is an atom (`WrappedExpr.simple`), so the
receiver needs no capture and the transfer rule fires directly — a genuine
difference in where the "simple operand" line is drawn. -/

sol_derivation transferStorageReceiverBox :
    => [ owner.transfer(5) ](φ)
  ~*> [ funded(5) => { transfer(owner, 5) } [ ](φ),
        ¬funded(5) => ⊤ ]

sol_derivation transferStorageReceiverDiamond :
    => < owner.transfer(5) >(φ)
  ~*> [ funded(5) => { transfer(owner, 5) } < >(φ),
        ¬funded(5) => ⊥ ]

/-! ### `to.transfer(x + 2);` — a nonsimple amount
The amount is captured into `pv` first, exactly as upstream's
`transferUnfoldRightSndArgument` does, and the funds guard is then read *under*
that capture — which is what the `{…}` prefix on the antecedent says.  The
calculus abbreviates the same thing by substituting: it writes
`0 ≤ x + 2 ≤ selfBalance`.

The third line is what KeY's guarded pair costs on an operator that does not
need a guard: `binopAssignment` is stated as `\if(se2 != 0)` for every operator
and specialises the condition, so `+` still produces a `\else` branch — with
the antecedent `¬⊤`, which is what makes it vacuous. -/

sol_derivation transferCapturedAmount :
    => [ to.transfer(x + 2) ](φ)
  ~*> [ { pv@uint := default(uint) } { pv@uint := (x + 2) } funded(pv@uint) =>
          { pv@uint := default(uint) } { pv@uint := (x + 2) }
          { transfer(to, pv@uint) } [ ](φ),
        { pv@uint := default(uint) } { pv@uint := (x + 2) } ¬funded(pv@uint) =>
          { pv@uint := default(uint) } { pv@uint := (x + 2) } ⊤,
        { pv@uint := default(uint) } ¬⊤ => { pv@uint := default(uint) } ⊤ ]

/-! ## 10 · Require

`require` is the calculus's own guarded pair, and the only rule whose guard is
a program expression rather than a property of the store. -/

sol_derivation requireSimple :
    => [ require(flag) ](φ)
  ~*> [ flag => [ ](φ),
        ¬flag => ⊤ ]

end

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
operand bound: `rv` is what the freeze introduces, and a line written *after*
the freeze mentions it. -/
def store : Semantics.State :=
  State.exampleStore.setEnv "rv" (Semantics.Binding.val (Semantics.PrimVal.int 10))

/-- The headline: the merged parallel update produces the same verdict as the
program it came from. -/
example :
    (seq!{ => <[ alice.account.balance = 10 ]>(alice.account.balance == 10) }).check store
      = (seq!{ => { rv@uint := 10 ‖ sp@Account := path(alice.account)
                    ‖ storage := save(alice.account.balance, 10) }
               <[ ]>(alice.account.balance == 10) }).check store := by
  native_decide

/-- …and both of them hold. -/
example :
    (seq!{ => { rv@uint := 10 ‖ sp@Account := path(alice.account)
                ‖ storage := save(alice.account.balance, 10) }
            <[ ]>(alice.account.balance == 10) }).Holds store := by
  native_decide

/-- The root chain, first line against last. -/
example :
    (seq!{ => <[ age = 10; age++ ]>(age == 11) }).check State.exampleStore
      = (seq!{ => { storage := save(age, 10) } { bump(age++) }
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

end Solidity.Examples.Paper
