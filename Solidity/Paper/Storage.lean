import Solidity.Tactics.Derivation
import Solidity.Semantics.DecEq

/-!
# The calculus's worked examples — storage

Sections 1–4 of `SolidityPaper.lean`: storage fields and roots,
storage arrays, `delete`, and compound assignment.  The conventions the chains
are written in are that file's docstring; which paper example each chain is,
and which ones have no chain, is `docs/paper-parity.md`.
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
  ~> => { storage := save(storage, alice.age, ageVal) } (φ)

/-! ### `Account storage acc = bob.account; alice.account = acc;`
The write stores the value found at the alias path, not the alias path itself
— which is why the second update is a `copy` and not a `save` of `acc`.  Two
lines, because the declaration dropping into an update is a step of its own
and seeing it is how one sees that `acc` is a *path*, not a value. -/

sol_derivation fieldWriteFromAlias :
    => <[ Account storage acc = bob.account; alice.account = acc ]>(φ)
  ~> => { acc := bob.account } <[ alice.account = acc ]>(φ)
  ~> => { acc := bob.account } { storage := save(storage, alice.account, find(storage, acc)) } (φ)

/-! ### `alice.account.balance = 10;` — **the headline**
The value is frozen into `se`, the path captured into `sp`, the write
performed, and the accumulated updates merged into the one parallel update the
calculus writes. -/

sol_derivation deepFieldWrite :
    => <[ alice.account.balance = 10 ]>(φ)
  ~> => <[ uint se = 10;
           Account storage sp = alice.account;
           sp@Account.balance = se ]>(φ)
  ~*> => { se@uint := 10 ‖ sp@Account := alice.account }
          <[ sp@Account.balance = se@uint ]>(φ)
  ~> => { se@uint := 10 ‖ sp@Account := alice.account }
         { storage := save(storage, sp@Account.balance, se@uint) } (φ)
   = => { se@uint := 10 ‖ sp@Account := alice.account
          ‖ storage := save(storage, alice.account.balance, 10) } (φ)

/-! ### `v = alice.account.balance;`
The read twin.  No value operand to freeze, so the three rewrite steps are
exactly three rules, and the merge substitutes the alias into the `find`. -/

sol_derivation deepFieldRead :
    => <[ v = alice.account.balance ]>(φ)
  ~> => <[ Account storage sp = alice.account; v = sp@Account.balance ]>(φ)
  ~> => { sp@Account := alice.account } <[ v = sp@Account.balance ]>(φ)
  ~> => { sp@Account := alice.account } { v := find(storage, sp@Account.balance) } (φ)
   = => { sp@Account := alice.account ‖ v := find(storage, alice.account.balance) } (φ)

/-! ### `alice.account.token.value = 5;`
One selector deeper, and yet the *same* chain — which is the claim, so the
chain is written out at the same length as `deepFieldWrite` above rather than
collapsed into one arrow.  Line for line the two are identical up to the
selector: the unfold rule hoists the whole path prefix in one step, so depth
costs nothing.  The calculus takes seven lines here because it unfolds one
selector at a time. -/

sol_derivation deeperFieldWrite :
    => <[ alice.account.token.value = 5 ]>(φ)
  ~> => <[ uint se = 5;
           Token storage sp = alice.account.token;
           sp@Token.value = se ]>(φ)
  ~*> => { se@uint := 5 ‖ sp@Token := alice.account.token }
          <[ sp@Token.value = se@uint ]>(φ)
  ~> => { se@uint := 5 ‖ sp@Token := alice.account.token }
         { storage := save(storage, sp@Token.value, se@uint) } (φ)
   = => { se@uint := 5 ‖ sp@Token := alice.account.token
          ‖ storage := save(storage, alice.account.token.value, 5) } (φ)

/-! ### `uint v = total;` — reading a storage root -/

sol_derivation rootRead :
    => <[ uint v = total ]>(φ)
  ~*> => { v := defVal(uint) } { v := select(storage, total) } (φ)

/-! ### `alice = bob;` / `alice = pp;` — whole-struct write
A root write from another root is a deep *copy*, and that is the whole content
of the line: `store(storage, alice, select(storage, bob))` in the calculus's
spelling. -/

sol_derivation rootWriteFromGlobal :
    => <[ alice = bob ]>(φ)
  ~> => { storage := save(storage, alice, find(storage, bob)) } (φ)

sol_derivation rootWriteFromAlias :
    => <[ alice = pp ]>(φ)
  ~> => { storage := save(storage, alice, find(storage, pp)) } (φ)

/-! ### local storage rebinding versus global root copy
The calculus's point, in two chains that share no rule: the same syntactic
form is a *rebind* for a local reference and a deep copy for a global root.
Note that the rebind leaves **two** `acc` bindings on the stack — the merge
law absorbs them, but only once the second is read in the first's state. -/

sol_derivation localRebindThenWrite :
    => <[ Account storage acc = alice.account; acc = bob.account;
          acc.balance = 10 ]>(φ)
  ~*> => { acc := alice.account } { acc := bob.account }
          { storage := save(storage, acc.balance, 10) } (φ)
    = => { acc := alice.account }
          { acc := bob.account ‖ storage := save(storage, bob.account.balance, 10) } (φ)

sol_derivation globalRootCopy :
    => <[ account@@Account = bob.account ]>(φ)
  ~> => { storage := save(storage, account@@Account, find(storage, bob.account)) } (φ)

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
  ~*> [ inBounds(values[i]) => { v := find(storage, values[i]) } [ ](φ),
        ¬inBounds(values[i]) => ⊤ ]

sol_derivation arrayIndexReadDiamond :
    => < v = values[i] >(φ)
  ~*> [ inBounds(values[i]) => { v := find(storage, values[i]) } < >(φ),
        ¬inBounds(values[i]) => ⊥ ]

/-! ### `values[i] = 100;` — the write twin -/

sol_derivation arrayIndexWrite :
    => [ values[i] = 100 ](φ)
  ~*> [ inBounds(values[i]) => { storage := save(storage, values[i], 100) } [ ](φ),
        ¬inBounds(values[i]) => ⊤ ]

/-! ### `v = balances[i];`
A mapping key uses the same selector and has **no** bounds goal, so the line
does not branch at all. -/

sol_derivation mappingIndexRead :
    => <[ v = balances[i] ]>(φ)
  ~> => { v := find(storage, balances[i]) } (φ)

/-! ### `Token storage tokRef = bob.account.token; tokens[i] = tokRef;`
A struct-valued element assigned from a storage alias copies the value found
at that path.  Written in the box, so the out-of-bounds branch is the `⊤` —
and note it carries the capture that preceded the split. -/

sol_derivation arrayIndexWriteRefSource :
    => [ Token storage tokRef = bob.account.token;
         (tokens@@TokenArray)[i] = tokRef ](φ)
  ~*> [ { tokRef := bob.account.token } inBounds((tokens@@TokenArray)[i]) =>
          { tokRef := bob.account.token }
          { storage := save(storage, (tokens@@TokenArray)[i], find(storage, tokRef)) } [ ](φ),
        { tokRef := bob.account.token } ¬inBounds((tokens@@TokenArray)[i]) =>
          { tokRef := bob.account.token } ⊤ ]

/-! ### `alice.accounts[i] = 100;` — a nonsimple path under an index
The value is frozen, then the path captured into `sp`, and only then is the
bounds goal read — under everything accumulated before it, which is what the
`{…}` prefix on the antecedent says.

Written **unmerged**, which is also what a branching line has to be: the merge
closes the first sequent of a frontier and the rest of the list has to be the
line the derivation actually accumulated (`upd_merge` in `Tactics/Derivation.lean`
opens one update equality, and `Frontier.Equiv` on the tail is reflexivity).
The calculus merges the in-bounds line only after it has dropped the other. -/

sol_derivation nonsimplePathIndexWrite :
    => [ alice.accounts[i] = 100 ](φ)
  ~*> [ { se@uint := defVal(uint) } { se@uint := 100 }
          { sp@UintArray := alice.accounts } inBounds(sp@UintArray[i]) =>
          { se@uint := defVal(uint) } { se@uint := 100 }
          { sp@UintArray := alice.accounts }
          { storage := save(storage, sp@UintArray[i], se@uint) } [ ](φ),
        { se@uint := defVal(uint) } { se@uint := 100 }
          { sp@UintArray := alice.accounts } ¬inBounds(sp@UintArray[i]) =>
          { se@uint := defVal(uint) } { se@uint := 100 }
          { sp@UintArray := alice.accounts } ⊤ ]

/-! ### `alice.accounts[++i] = valueVal;` — the index is nonsimple too
The value is frozen, the path captured, and only then is the index captured —
that order is what keeps the written value the one `valueVal` held before
`++i` ran.  The calculus draws only the first step of this one; the rest is
the same guarded pair as the example above, with the index capture inside the
prefix. -/

sol_derivation nonsimplePathIncIndexWrite :
    => [ alice.accounts[++i] = amount ](φ)
  ~*> [ { se@uint := defVal(uint) } { se@uint := amount }
          { sp@UintArray := alice.accounts }
          { ie@uint := defVal(uint) } { bump(++i) ‖ ie@uint := ++i }
          inBounds(sp@UintArray[ie@uint]) =>
          { se@uint := defVal(uint) } { se@uint := amount }
          { sp@UintArray := alice.accounts }
          { ie@uint := defVal(uint) } { bump(++i) ‖ ie@uint := ++i }
          { storage := save(storage, sp@UintArray[ie@uint], se@uint) } [ ](φ),
        { se@uint := defVal(uint) } { se@uint := amount }
          { sp@UintArray := alice.accounts }
          { ie@uint := defVal(uint) } { bump(++i) ‖ ie@uint := ++i }
          ¬inBounds(sp@UintArray[ie@uint]) =>
          { se@uint := defVal(uint) } { se@uint := amount }
          { sp@UintArray := alice.accounts }
          { ie@uint := defVal(uint) } { bump(++i) ‖ ie@uint := ++i } ⊤ ]

/-! ### `matrix[i++][i++] = 77;` — a side effect in the receiver *and* in the
index.  Solidity runs the receiver's increment first, so the write lands at
`matrix[i][i+1]` and `i` ends two higher.  One step decomposes the statement
into the four the calculus draws, and that decomposition is what carries the
order: the value is snapshotted, the receiver aliased, the index captured.

Only that step is written.  The tail is not, and the reason is worth knowing
before someone writes it: the frontier the rules reach binds the receiver
alias *before* capturing the receiver's own index, which is not the order
`sections/storage-examples.tex` draws its `idx1`/`sp`/`idx2` in. -/

sol_derivation receiverAndIndexSideEffects :
    => [ matrix[i++][i++] = 77 ](φ)
  ~> => [ uint se = 77;
          UintArray storage sp = matrix[i++];
          uint ie = i++;
          sp@UintArray[ie@uint] = se@uint ](φ)

/-! ### `values.push(42);` and `tokens.pop();`
`push` is unguarded; `pop` is guarded on the array being non-empty, so it
branches like an indexed access. -/

sol_derivation arrayPush :
    => <[ values.push(42) ]>(φ)
  ~> => { storage := save(save(storage, values[values.length], 42), values.length, values.length + 1) } (φ)

sol_derivation arrayPopBox :
    => [ (tokens@@TokenArray).pop() ](φ)
  ~*> [ nonEmpty((tokens@@TokenArray)) =>
          { storage := save(delAt(storage, (tokens@@TokenArray)[(tokens@@TokenArray).length - 1]), (tokens@@TokenArray).length, (tokens@@TokenArray).length - 1) } [ ](φ),
        ¬nonEmpty((tokens@@TokenArray)) => ⊤ ]

sol_derivation arrayPopDiamond :
    => < (tokens@@TokenArray).pop() >(φ)
  ~*> [ nonEmpty((tokens@@TokenArray)) =>
          { storage := save(delAt(storage, (tokens@@TokenArray)[(tokens@@TokenArray).length - 1]), (tokens@@TokenArray).length, (tokens@@TokenArray).length - 1) } < >(φ),
        ¬nonEmpty((tokens@@TokenArray)) => ⊥ ]

/-! ### the push family
`push(arr)` with no value is the bare `arr.push();`; `push(arr, v)` the
one-argument form.  A nonsimple receiver is captured into `sp` first, and the
*slot* the push returns is a path like any other, which is what lets
`tokens.push().value = 11;` write through it. -/

sol_derivation pushRefSource :
    => <[ (tokens@@TokenArray).push(tokRef) ]>(φ)
  ~*> => { storage := save(save(storage, (tokens@@TokenArray)[(tokens@@TokenArray).length], tokRef), (tokens@@TokenArray).length, (tokens@@TokenArray).length + 1) } (φ)

sol_derivation pushNonsimpleReceiver :
    => <[ alice.account.tokens.push(tokRef) ]>(φ)
  ~*> => { sp@TokenArray := alice.account.tokens }
          { storage := save(save(storage, sp@TokenArray[sp@TokenArray.length], tokRef), sp@TokenArray.length, sp@TokenArray.length + 1) } (φ)

/-! ### `bucket.tokens.push();` — a nonsimple receiver on a *state variable*
The calculus's `bucket`, whose `tokens` member is the array.  Written
`(bucket@@TokenBucket.tokens)`: `@@` binds the whole path, and the parentheses
are needed because `.push()` cannot follow a field access directly in the
surface grammar. -/

sol_derivation bucketPushBare :
    => <[ (bucket@@TokenBucket.tokens).push() ]>(φ)
  ~*> => { sp@TokenArray := bucket@@TokenBucket.tokens }
          { storage := save(delAt(storage, sp@TokenArray[sp@TokenArray.length]), sp@TokenArray.length, sp@TokenArray.length + 1) } (φ)

sol_derivation pushBare :
    => <[ (tokens@@TokenArray).push() ]>(φ)
  ~> => { storage := save(delAt(storage, (tokens@@TokenArray)[(tokens@@TokenArray).length]), (tokens@@TokenArray).length, (tokens@@TokenArray).length + 1) } (φ)

sol_derivation pushSlotWrite :
    => <[ (tokens@@TokenArray).push().value = 11 ]>(φ)
  ~*> => { se@uint := defVal(uint) } { se@uint := 11 }
          { sp@Token := (tokens@@TokenArray).push() }
          { storage := save(storage, sp@Token.value, se@uint) } (φ)

/-! ### `tokens.push(); uint i = tokens.push().value;`
The read twin of the line above, and the calculus's point about the slot a
bare `push` returns: it is a path like any other, so *reading* through it is
the same alias binding that writing through it was. -/

sol_derivation pushThenPushSlotRead :
    => <[ (tokens@@TokenArray).push();
          uint i = (tokens@@TokenArray).push().value ]>(φ)
  ~*> => { storage := save(delAt(storage, (tokens@@TokenArray)[(tokens@@TokenArray).length]), (tokens@@TokenArray).length, (tokens@@TokenArray).length + 1) } { i := defVal(uint) }
          { sp@Token := (tokens@@TokenArray).push() }
          { i := find(storage, sp@Token.value) } (φ)

/-! ### `values.push(); values.pop();` — pop after push
The smallest program whose *diamond* proof needs the calculus's
`sizeNotNegative`, a first-order side condition with no `RuleName` here (see
the header).  What the rules give is the guarded pair, with the `pop` guard
read under the `push` that precedes it. -/

sol_derivation popAfterPush :
    => <[ values.push(); values.pop() ]>(φ)
  ~*> [ { storage := save(delAt(storage, values[values.length]), values.length, values.length + 1) } nonEmpty(values) =>
          { storage := save(delAt(storage, values[values.length]), values.length, values.length + 1) } { storage := save(delAt(storage, values[values.length - 1]), values.length, values.length - 1) } <[ ]>(φ),
        { storage := save(delAt(storage, values[values.length]), values.length, values.length + 1) } ¬nonEmpty(values) =>
          { storage := save(delAt(storage, values[values.length]), values.length, values.length + 1) } ⊤,
        { storage := save(delAt(storage, values[values.length]), values.length, values.length + 1) } ¬nonEmpty(values) =>
          { storage := save(delAt(storage, values[values.length]), values.length, values.length + 1) } ⊥ ]

/-! ### `age = 10; age++;` — a root write and a post-increment
Two terminal rules, two update lines, and no capture to elide.  The second is
the pair `{age := age + 1 ‖ …}` that `bump` names. -/

sol_derivation rootWriteThenIncrement :
    => <[ age = 10; age++ ]>(φ)
  ~> => { storage := save(storage, age, 10) } <[ age++ ]>(φ)
  ~> => { storage := save(storage, age, 10) } { bump(age++) } (φ)

/-! ## 3 · Delete -/

sol_derivation deleteField :
    => <[ delete alice.account ]>(φ)
  ~> => { storage := delAt(storage, alice.account) } (φ)

/-! ### `delete alice.account;` between writes and reads
The calculus's longer delete program: two members written, the struct above
them cleared, and both read back.  Nothing merges — the merge law has no
reader for a `find` over a `clear` — so the chain is the five updates the
derivation accumulated, in order. -/

sol_derivation deleteAccountThenReadLeaves :
    => <[ alice.account.balance = 100; alice.account.token.value = 7;
          delete alice.account; b = alice.account.balance;
          v = alice.account.token.value ]>(φ)
  ~*> => { se@uint := defVal(uint) } { se@uint := 100 }
          { sp@Account := alice.account }
          { storage := save(storage, sp@Account.balance, se@uint) }
          { se@uint := defVal(uint) } { se@uint := 7 }
          { sp@Token := alice.account.token }
          { storage := save(storage, sp@Token.value, se@uint) }
          { storage := delAt(storage, alice.account) }
          { sp@Account := alice.account } { b := find(storage, sp@Account.balance) }
          { sp@Token := alice.account.token } { v := find(storage, sp@Token.value) } (φ)

/-! ### `delete alice.account.tokens[++i]; len = alice.account.tokens.length;`
An index delete under a nonsimple path, with an impure index — so the path is
captured, then the index frozen, and only then is the slot cleared.  The
`.length` read afterwards is an ordinary field read through a second capture
of the same path, which is why `len` is a `find` and not a rule of its own. -/

sol_derivation deleteIncIndexThenLength :
    => <[ delete alice.account.tokens[++i];
          len = alice.account.tokens.length ]>(φ)
  ~*> => { sp@TokenArray := alice.account.tokens }
          { ie@uint := defVal(uint) } { bump(++i) ‖ ie@uint := ++i }
          { storage := delAt(storage, sp@TokenArray[ie@uint]) }
          { sp@TokenArray := alice.account.tokens }
          { len := find(storage, sp@TokenArray.length) } (φ)

/-! ### `ledger.nonce = 42; delete ledger; v = ledger.nonce;`
The calculus's struct-reset program: `delete` on a struct keeps its mapping
members and resets the rest, so the read afterwards succeeds — and the three
updates stay stacked, because the merge law has no reader for a `find` over a
`clear`. -/

sol_derivation deleteStructThenRead :
    => <[ (ledger@@Ledger).nonce = 42; delete (ledger@@Ledger);
          v = (ledger@@Ledger).nonce ]>(φ)
  ~*> => { storage := save(storage, (ledger@@Ledger).nonce, 42) }
          { storage := delAt(storage, (ledger@@Ledger)) }
          { v := find(storage, (ledger@@Ledger).nonce) } (φ)

/-! ### the whole of the calculus's `delete ledger;` program
`delete` on a struct resets its members and *keeps* its mappings, so the read
after it still finds what was put there; deleting the mapping entry itself is
what clears it.  Both halves in one chain, and it stays stacked for the same
reason as the shorter one above. -/

sol_derivation deleteLedgerMappingSurvives :
    => <[ (ledger@@Ledger).nonce = 5; (ledger@@Ledger).balances[1] = 10;
          delete (ledger@@Ledger); kept = (ledger@@Ledger).balances[1];
          delete (ledger@@Ledger).balances[1]; nonce = (ledger@@Ledger).nonce;
          gone = (ledger@@Ledger).balances[1] ]>(φ)
  ~*> => { storage := save(storage, (ledger@@Ledger).nonce, 5) }
          { se@uint := defVal(uint) } { se@uint := 10 }
          { sp@UintMap := (ledger@@Ledger).balances }
          { storage := save(storage, sp@UintMap[1], se@uint) }
          { storage := delAt(storage, (ledger@@Ledger)) }
          { sp@UintMap := (ledger@@Ledger).balances }
          { kept := find(storage, sp@UintMap[1]) }
          { sp@UintMap := (ledger@@Ledger).balances }
          { storage := delAt(storage, sp@UintMap[1]) }
          { nonce := find(storage, (ledger@@Ledger).nonce) }
          { sp@UintMap := (ledger@@Ledger).balances }
          { gone := find(storage, sp@UintMap[1]) } (φ)

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

end

end Solidity.Examples.Paper
