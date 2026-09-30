import Solidity.Calculus.Chains
import Solidity.Calculus.Close

/-!
# Call-valued operands: `values.push(makeValue());`

The programs whose operand is a call of the contract's function
`makeValue()`, in the storage and memory array examples.
A value holds no call: a call is a
statement carrying its callee's body (`Stmt.call`), so the first
step, the call captured into `pv`, is the elaborator's (`hoist`), in solc's
order.  The two lines are one formula, equal by `rfl`, with the fresh `se1`
for `pv`.  From there the rules run: `valueDeclSkip`, `functionBodyExpand`
(the body inlined, `makeValue`'s return variable the next fresh `se2`), the
body's own steps, and the push or the write.  The opaque
`{pv := makeValue()}` is the updates of the body,
`{ se2 := select(storage, seed) } { se1 := se2 }`.

A push used as a target, `values.push() = e;`, is the push `values.push(e);`,
as the front end normalises it, on a
receiver that is a name or a member chain (`bucket.tokens`).

A line holding a call not yet inlined reads back only if it writes no fresh
index above the callee's: reading it back numbers the callee's locals past
the largest index the line writes, so
`⟨ se1 = makeValue(); uint se3; se3 = ++i; … ⟩` would give the callee `se4`,
not `se2`.  The first step of `carolValues[++i] = makeValue();` is therefore
written with its `++i` left in place, and that program is pinned
(`Prog.toStr`) and proved by the strategy rather than drawn line by line.
`carolValues[i] = makeValue();` is a chain from its first step to its last
line (`memoryIndexWriteCallChain` says why not every line between).

The push rows are chains, not box theorems about the pushed value:
`sol_close` does not read back what a push wrote into an array known only by
its shape (pinned at the end of §3; `Calculus/Close.lean`).

Where the printed rules differ, to be taken to them (Lean is the source of truth):

* its coverage tables cite call operands (`values.push(makeValue())`,
  `values[i] = makeValue()`, `total = makeValue()`,
  `carolValues[i] = makeValue()`) as instances of the unfold-source rules,
  which never fire on a call here: the elaborator has captured it, and they
  fire on a pure operand such as `values.push(v + 1)`;
* its last line of `values.push() = makeValue();` saves the length before the
  element, `storagePushValueSave` the element first: the same store, another
  term;
* its first step of `carolValues[++i] = makeValue();` re-aliases the receiver
  (`uint[] memory mv1 = carolValues;`), which the elaborator does not (§6);
* its last line of `bucket.tokens.push() = tokRef;` writes the original path
  (`save(save(storage, bucket.tokens.length, q+1), bucket.tokens[q],
  find(bob, token(account)))`), where `bucketPushLvalueRefSource` keeps what
  the rules bind, the receiver's alias `sp2` and the source's `tokRef`: the
  printed line is that one with the alias updates applied, which no rule of
  the chain does;
* both push-as-target chains with a storage source (`pushLvalueRefSource`,
  `bucketPushLvalueRefSource`) start with `{sp1 := bob.account}
  {tokRef := sp1.token}` where the printed chain writes `{tokRef := bob.account.token}`:
  the declaration's nested initialiser is aliased one member at a time.
-/

namespace Solidity.Examples.CallOperands

open Proves

/-- `makeValue()` reads a state variable: its value is symbolic, as close to
an opaque value as a body gets. -/
def Operands : Contract := contract!{
  uint seed; uint total; uint[] values;
  function makeValue() returns (uint) { return seed; }
}

local instance : InContract := ⟨Operands⟩

/-! ## 1 · `values.push(makeValue());`

The call is captured, then inlined, then its value pushed
(`storagePushValueSave`). -/

example : Prog.toStr (sol{ values.push(makeValue()); } : Prog Operands) =
    "uint se1; se1 = makeValue(); values.push(se1);" := rfl

/-- The first step, `uint pv = makeValue(); values.push(pv);`, is the
elaborator's: one formula. -/
example : dl!{ ⟨ values.push(makeValue()); ⟩ true } =
    dl!{ ⟨ uint se1 = makeValue(); values.push(se1); ⟩ true } := rfl

/-- `values.push(makeValue());`: the capture, the call
inlined and run, the push. -/
def pushCallValue : dl!{ ⟨ values.push(makeValue()); ⟩ true }
    ~*> dl!{ { se1 := 0 } { se2 := 0 } { se2 := select(storage, seed) } { se1 := se2 }
            { storage := save(save(storage, values[values.length], se1), values.length,
                values.length + 1) } true } :=
  calc dl!{ ⟨ values.push(makeValue()); ⟩ true }
    _ = dl!{ ⟨ uint se1 = makeValue(); values.push(se1); ⟩ true } := rfl
    _ ~[valueDeclSkip]~> dl!{ { se1 := 0 } ⟨ se1 = makeValue(); values.push(se1); ⟩ true } := rfl
    _ ~[functionBodyExpand]~>
        dl!{ { se1 := 0 } ⟨ uint se2; se2 = seed; se1 = se2; values.push(se1); ⟩ true } := rfl
    _ ~*> dl!{ { se1 := 0 } { se2 := 0 } { se2 := select(storage, seed) } { se1 := se2 }
            ⟨ values.push(se1); ⟩ true } := by sol_chain
    _ ~[storagePushValueSave]~>
        dl!{ { se1 := 0 } { se2 := 0 } { se2 := select(storage, seed) } { se1 := se2 }
            { storage := save(save(storage, values[values.length], se1), values.length,
                values.length + 1) } ⟨⟩ true } := rfl
    _ ~[emptyModality]~>
        dl!{ { se1 := 0 } { se2 := 0 } { se2 := select(storage, seed) } { se1 := se2 }
            { storage := save(save(storage, values[values.length], se1), values.length,
                values.length + 1) } true } := rfl

/--
info:     dl{ ⟨ uint se1; se1 = makeValue(); values .push(se1); ⟩ true }
  ~[valueDeclSkip]~>
    dl{ { se1 := 0 } ⟨ se1 = makeValue(); values .push(se1); ⟩ true }
  ~[functionBodyExpand]~>
    dl{ { se1 := 0 } ⟨ uint se2; se2 = seed; se1 = se2; values .push(se1); ⟩ true }
  ~[valueDeclSkip]~>
    dl{ { se1 := 0 } { se2 := 0 } ⟨ se2 = seed; se1 = se2; values .push(se1); ⟩ true }
  ~[storageRootReadSelect]~>
    dl{ { se1 := 0 } { se2 := 0 } { se2 := select(storage, seed) } ⟨ se1 = se2; values .push(se1); ⟩ true }
  ~[localValueAssign]~>
    dl{ { se1 := 0 } { se2 := 0 } { se2 := select(storage, seed) } { se1 := se2 } ⟨ values .push(se1); ⟩ true }
  ~[storagePushValueSave]~>
    dl{
  { se1 := 0 }
    { se2 := 0 }
      { se2 := select(storage, seed) }
        { se1 := se2 }
          { storage := save(save(storage, values[values.length], se1), values.length, values.length + 1) } ⟨ ⟩ true }
  ~[emptyModality]~>
    dl{
  { se1 := 0 }
    { se2 := 0 }
      { se2 := select(storage, seed) }
        { se1 := se2 }
          { storage := save(save(storage, values[values.length], se1), values.length, values.length + 1) } true }
-/
#guard_msgs in #derivation dl!{ ⟨ values.push(makeValue()); ⟩ true }

/-! ## 2 · `values.push() = makeValue();`

The push used as a target is the push of its right-hand side: the same
formula as §1, so the same chain. -/

example : dl!{ ⟨ values.push() = makeValue(); ⟩ true } =
    dl!{ ⟨ values.push(makeValue()); ⟩ true } := rfl

/-- `values.push() = makeValue();`: the first
step to `uint pv = makeValue(); values.push(pv);`, then §1's chain. -/
def pushLvalueCallValue : dl!{ ⟨ values.push() = makeValue(); ⟩ true }
    ~*> dl!{ { se1 := 0 } { se2 := 0 } { se2 := select(storage, seed) } { se1 := se2 }
            { storage := save(save(storage, values[values.length], se1), values.length,
                values.length + 1) } true } :=
  calc dl!{ ⟨ values.push() = makeValue(); ⟩ true }
    _ = dl!{ ⟨ uint se1 = makeValue(); values.push(se1); ⟩ true } := rfl
    _ ~*> dl!{ { se1 := 0 } { se2 := 0 } { se2 := select(storage, seed) } { se1 := se2 }
            { storage := save(save(storage, values[values.length], se1), values.length,
                values.length + 1) } true } := pushCallValue

-- Spelt with the `.push()` token, as the printer spaces it: the same push.
example : dl!{ ⟨ values .push() = makeValue(); ⟩ true } =
    dl!{ ⟨ values.push(makeValue()); ⟩ true } := rfl

/-- `values.push() = 42; uint result = values[0];` from the example store,
whose `values` is empty: the push used as a target appends `42`. -/
theorem pushLvalueRun :
    Prog.localAfter Semantics.State.exampleStore
      sol{ values.push() = 42; uint result = values[0]; } "result" =
      .ok (.val (.int 42)) := rfl

/-- `values.push() = 42;` (solkey's `storage-push-return-assign`): one rule. -/
def pushLvaluePrimitive : dl!{ ⟨ values.push() = 42; ⟩ true }
    ~[storagePushValueSave]~>
      dl!{ { storage := save(save(storage, values[values.length], 42), values.length,
            values.length + 1) } ⟨⟩ true } :=
  rfl

/-! ## 3 · A push used as a target, with a storage source (`TestSuite`)

`tokens.push() = tokRef;` copies what the alias finds
(`storagePushValueCopySource`); on the member chain `bucket.tokens` the
receiver is aliased first (`storagePushValue_unfold_leftFstReceiver`). -/

example : Prog.toStr (sol[TestSuite]{ Token storage tokRef = bob.account.token;
    bucket.tokens.push() = tokRef; } : Prog TestSuite) =
    "Token storage tokRef = bob.account.token; bucket.tokens.push(tokRef);" := rfl

-- The member chain spelt with the `.push()` token: the same push.
example : Prog.toStr (sol[TestSuite]{ Token storage tokRef = bob.account.token;
    bucket .tokens.push() = tokRef; } : Prog TestSuite) =
    "Token storage tokRef = bob.account.token; bucket.tokens.push(tokRef);" := rfl

/-- `Token storage tokRef = bob.account.token; tokens.push() = tokRef;` -/
def pushLvalueRefSource :
    dl[TestSuite]{ ⟨ Token storage tokRef = bob.account.token; tokens.push() = tokRef; ⟩ true }
    ~*> dl[TestSuite]{ { sp1 := bob.account } { tokRef := sp1.token }
          { storage := save(save(storage, tokens[tokens.length], find(storage, tokRef)),
              tokens.length, tokens.length + 1) } true } := by
  sol_chain

/-- `Token storage tokRef = bob.account.token; bucket.tokens.push() = tokRef;` —
the receiver aliased to `sp2` first.  The last line keeps the aliases `sp2`
and `tokRef`, where the printed chain writes the paths they are bound to. -/
def bucketPushLvalueRefSource :
    dl[TestSuite]{ ⟨ Token storage tokRef = bob.account.token;
      bucket.tokens.push() = tokRef; ⟩ true }
    ~*> dl[TestSuite]{ { sp1 := bob.account } { tokRef := sp1.token } { sp2 := bucket.tokens }
          { storage := save(save(storage, sp2[sp2.length], find(storage, tokRef)), sp2.length,
              sp2.length + 1) } true } := by
  sol_chain

-- A dotted push bound by an assignment, the alias rebound to the new slot.
example : Prog.toStr (sol[TestSuite]{ Token storage t = bucket.tokens[0];
    t = bucket.tokens.push(); } : Prog TestSuite) =
    "Token storage t = bucket.tokens[0]; t = bucket.tokens.push();" := rfl

/-- `Token storage t = bucket.tokens.push(); t.value = 11;` — the slot a push
on a member chain returns, bound and written (the printed
`bucket.tokens.push().value = valueVal;`, whose member of `push()` does not
parse). -/
theorem bucketPushSlotWrite :
    ⊨ dl[TestSuite]{ [ Token storage t = bucket.tokens.push(); t.value = 11; ]
      t.value == 11 } := by
  sol_symex
  sol_close

/-- `[ uint n = values.length; values.push(42); ] values.length == n + 1` is
valid, but the strategy leaves it open: the push's write is not read back
(`Calculus/Close.lean`).  Pinned, so that closing it shows here. -/
example : True := by
  fail_if_success
    have : ⊨ dl!{ [ uint n = values.length; values.push(42); ] values.length == n + 1 } := by
      sol_symex
      sol_close
  trivial

/-! ## 4 · Storage writes: `values[i] = makeValue();`, `total = makeValue();`

These are the call-valued operands
for the index and root writes' unfold rules; here the call is captured by the
elaborator, and the write is the simple one. -/

example : Prog.toStr (sol{ uint i = 1; values[i] = makeValue(); } : Prog Operands) =
    "uint i = 1; uint se1; se1 = makeValue(); values[i] = se1;" := rfl

example : Prog.toStr (sol{ total = makeValue(); } : Prog Operands) =
    "uint se1; se1 = makeValue(); total = se1;" := rfl

/-- `values[i] = makeValue();` — the element holds `makeValue()`'s value. -/
theorem arrayIndexWriteCall :
    ⊨ dl!{ [ values[i] = makeValue(); uint x = values[i]; ] x == seed } := by
  sol_symex
  sol_close

/-- `total = makeValue();` -/
theorem rootWriteCall : ⊨ dl!{ [ total = makeValue(); ] total == seed } := by
  sol_symex
  sol_close

/-! ## 5 · `carolValues[i] = makeValue();`

A memory array's element written with a call's value
(`memoryIndexWriteStore`); `carolValues` is declared first, a copy of
`values`: a chain, and the box theorem that the element holds the value. -/

example : Prog.toStr (sol{ uint i = 0; uint[] memory carolValues = values;
    carolValues[i] = makeValue(); } : Prog Operands) =
    "uint i = 0; uint[] memory carolValues = values; uint se1; se1 = makeValue(); carolValues[i] = se1;" :=
  rfl

/-- The first step, `uint pv = makeValue(); carolValues[i] = pv;`. -/
example : dl!{ ⟨ uint[] memory carolValues = values; carolValues[i] = makeValue(); ⟩ true } =
    dl!{ ⟨ uint[] memory carolValues = values; uint se1 = makeValue(); carolValues[i] = se1; ⟩
      true } := rfl

/-- `uint[] memory carolValues = values; carolValues[i] = makeValue();`: the
capture, then the copy (`memoryStorageCopy`), the call inlined and run, and
the write (`memoryIndexWriteStore`), left to `sol_chain`.  The lines between
do not read back: with its declaration dropped, `carolValues` is a free name
in the program, which reads as a `uint` (`Calculus/Notation.lean`), and the
update `carolValues := freshId(…)` does not type the program under it. -/
def memoryIndexWriteCallChain :
    dl!{ ⟨ uint[] memory carolValues = values; carolValues[i] = makeValue(); ⟩ true }
    ~*> dl!{ { carolValues := freshId(copySt(memory, find(storage, values))) ‖
              memory := copySt(memory, find(storage, values)) }
          { se1 := 0 } { se2 := 0 } { se2 := select(storage, seed) } { se1 := se2 }
          { memory := write(memory, carolValues[i], se1) } true } :=
  calc dl!{ ⟨ uint[] memory carolValues = values; carolValues[i] = makeValue(); ⟩ true }
    _ = dl!{ ⟨ uint[] memory carolValues = values; uint se1 = makeValue();
            carolValues[i] = se1; ⟩ true } := rfl
    _ ~*> dl!{ { carolValues := freshId(copySt(memory, find(storage, values))) ‖
              memory := copySt(memory, find(storage, values)) }
          { se1 := 0 } { se2 := 0 } { se2 := select(storage, seed) } { se1 := se2 }
          { memory := write(memory, carolValues[i], se1) } true } := by sol_chain

/-- `carolValues[i] = makeValue();` — the element holds `makeValue()`'s value. -/
theorem memoryIndexWriteCall :
    ⊨ dl!{ [ uint[] memory carolValues = values; carolValues[i] = makeValue();
             uint x = carolValues[i]; ] x == seed } := by
  sol_symex
  sol_close

/-! ## 6 · `carolValues[++i] = makeValue();`

solc's order: the right-hand side, then the index.  The printed chain also re-aliases
the receiver (`uint[] memory mv1 = carolValues;`), since in KeY evaluating the
index may rebind it; here no operand rebinds a local (an assignment is no
expression, and a callee's locals are its own), so there is no re-alias
(`captureExpr`). -/

example : Prog.toStr (sol{ uint i = 0; uint[] memory carolValues = values;
    carolValues[++i] = makeValue(); } : Prog Operands) =
    "uint i = 0; uint[] memory carolValues = values; uint se1; se1 = makeValue(); uint se3; se3 = ++i; carolValues[se3] = se1;" :=
  rfl

/-- The first step, the call captured before the index. -/
example : dl!{ ⟨ uint[] memory carolValues = values; carolValues[++i] = makeValue(); ⟩ true } =
    dl!{ ⟨ uint[] memory carolValues = values; uint se1 = makeValue(); carolValues[++i] = se1; ⟩
      true } := rfl

/-- `carolValues[++i] = makeValue();` — the element at the incremented index
holds `makeValue()`'s value. -/
theorem memoryIndexWriteCallIncrement :
    ⊨ dl!{ [ uint[] memory carolValues = values; carolValues[++i] = makeValue();
             uint x = carolValues[i]; ] x == seed } := by
  sol_symex
  sol_close

/-! ## 7 · Calls among other operands, in solc's order

The right-hand side before the target, the right operand of a binary
operator before the left (`docs/solc-alignment.md`); each call a capture of
its own, its callee's return variable the next fresh index. -/

example : Prog.toStr (sol{ values[makeValue()] = makeValue(); } : Prog Operands) =
    "uint se1; se1 = makeValue(); uint se3; se3 = makeValue(); values[se3] = se1;" := rfl

example : Prog.toStr (sol{ uint i = 0; values.push(makeValue() + i++); } : Prog Operands) =
    "uint i = 0; uint se1; se1 = i++; uint se2; se2 = makeValue(); values.push(se2 + se1);" :=
  rfl

example : Prog.toStr (sol{ uint i = 0; uint[] memory carolValues = values;
    carolValues[i++] = makeValue() + i; } : Prog Operands) =
    "uint i = 0; uint[] memory carolValues = values; uint se1 = i; uint se2; se2 = makeValue(); uint se4 = se2 + se1; uint se5; se5 = i++; carolValues[se5] = se4;" :=
  rfl

/-! ## What cannot be written

A function returning a memory reference, as in
`choosePersonMem().account = makeAccount();`: a call's value is a value type
(`CallRet`), and a member of a call does not parse.  Nor is a memory return
declared: `returns (Account memory)` parses, but reads `memory` as the return
variable's name, not as a location. -/

/-- A function whose return is a struct: a call of it is refused, a call's
value being a value type. -/
def MemReturn : Contract := contract!{
  uint seed;
  function makeAccount() returns (Account r) { Account memory a; return a; }
}

/--
error: Solidity elaboration failed: makeAccount returns a reference (Account): a call's value is a value type
-/
#guard_msgs in #check sol[MemReturn]{ Account memory acc = makeAccount(); }

-- A push used as a target on an entry: its receiver is evaluated after the
-- right-hand side, and `b.push(e)` evaluates it before.
/--
error: `b.push() = e;` is written on a name or a member chain, `bucket.tokens`
---
error: cannot evaluate code because 'sorryAx' uses 'sorry' and/or contains errors
-/
#guard_msgs in #check sol[TestSuite]{ matrix[0].push() = 5; }

end Solidity.Examples.CallOperands
