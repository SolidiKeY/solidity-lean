import Solidity.Calculus.Chains
import Solidity.Calculus.Close

/-!
# Call-valued operands: `values.push(makeValue());`

The programs whose operand is a call of the contract's function
`makeValue()`, in the storage and memory array examples.  Their chains are
`Examples/Chains/StorageArrays.lean`, `Chains/Storage.lean` and `Chains/Memory*.lean`
(with the places they differ from the printed rules); what is here is the
rest: the programs as the elaborator reads them, pinned (`Prog.toStr`), and the
box theorems that the value written is read back.

A value holds no call: a call is a statement carrying its callee's body
(`Stmt.call`), so the first step, the call captured into `pv`, is the
elaborator's (`hoist`), in solc's order.  The two lines are one formula, equal
by `rfl`, with the fresh `se1` for `pv`; from there the rules inline the body
(`internalCallExpand`) and run it.

A push used as a target, `values.push() = e;`, is the push `values.push(e);`,
as the front end normalises it, on a receiver that is a name or a member chain
(`bucket.tokens`).

A line holding a call not yet inlined reads back only if it writes no fresh
index above the callee's: reading it back numbers the callee's locals past
the largest index the line writes, so
`⟨ se1 = makeValue(); uint se3; se3 = ++i; … ⟩` would give the callee `se4`,
not `se2`.  The first step of `carolValues[++i] = makeValue();` is therefore
written with its `++i` left in place, and that program is pinned and proved by
the strategy rather than drawn line by line.

A function returning a memory reference (§8) needs no rule of its own: the
elaborator declares the callee's return variable at the head of its body and
binds the caller's local to it after the call (`Syntax.lean`), and the
printers write the pair as the call it came from.

`sol_close` does not read back what a push wrote into an array known only by
its shape (pinned at the end of §3; `Calculus/Close.lean`), so the push rows
have no box theorem about the pushed value.
-/

namespace Solidity.Examples.Tactics.CallOperands

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
(`storagePushValueSave`); the chain is `Chains.StorageArrays`'s. -/

example : Prog.toStr (sol{ values.push(makeValue()); } : Prog Operands) =
    "uint se1; se1 = makeValue(); values.push(se1);" := rfl

/-- The first step, `uint pv = makeValue(); values.push(pv);`, is the
elaborator's: one formula. -/
example : dl!{ ⟨ values.push(makeValue()); ⟩ true } =
    dl!{ ⟨ uint se1 = makeValue(); values.push(se1); ⟩ true } := rfl

/-! ## 2 · `values.push() = makeValue();`

The push used as a target is the push of its right-hand side: the same
formula as §1, so the same chain (`Chains.StorageArrays`). -/

example : dl!{ ⟨ values.push() = makeValue(); ⟩ true } =
    dl!{ ⟨ values.push(makeValue()); ⟩ true } := rfl

-- Spelt with the `.push()` token, as the printer spaces it: the same push.
example : dl!{ ⟨ values .push() = makeValue(); ⟩ true } =
    dl!{ ⟨ values.push(makeValue()); ⟩ true } := rfl

/-- `values.push() = 42; uint result = values[0];` from the example store,
whose `values` is empty: the push used as a target appends `42`. -/
theorem pushLvalueRun :
    Prog.localAfter Semantics.State.exampleStore
      sol{ values.push() = 42; uint result = values[0]; } "result" =
      .ok (.val (.int 42)) := rfl

/-! ## 3 · A push used as a target, with a storage source (`TestSuite`)

`tokens.push() = tokRef;` copies what the alias finds
(`storagePushValueCopySource`); on the member chain `bucket.tokens` the
receiver is aliased first (`storagePushValue_unfold_leftFstReceiver`); their
chains are `Chains.StorageArrays`'s. -/

example : Prog.toStr (sol[TestSuite]{ Token storage tokRef = bob.account.token;
    bucket.tokens.push() = tokRef; } : Prog TestSuite) =
    "Token storage tokRef = bob.account.token; bucket.tokens.push(tokRef);" := rfl

-- The member chain spelt with the `.push()` token: the same push.
example : Prog.toStr (sol[TestSuite]{ Token storage tokRef = bob.account.token;
    bucket .tokens.push() = tokRef; } : Prog TestSuite) =
    "Token storage tokRef = bob.account.token; bucket.tokens.push(tokRef);" := rfl

-- A dotted push bound by an assignment, the alias rebound to the new slot.
example : Prog.toStr (sol[TestSuite]{ Token storage t = bucket.tokens[0];
    t = bucket.tokens.push(); } : Prog TestSuite) =
    "Token storage t = bucket.tokens[0]; t = bucket.tokens.push();" := rfl

/-- `Token storage t = bucket.tokens.push(); t.value = 11;` — the slot a push
on a member chain returns, bound and written (the printed
`bucket.tokens.push().value = valueVal;`, whose member of `push()` is
refused: a member of a call is one of a function's value). -/
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
(`memoryIndexWriteArray`); `carolValues` is declared first, a copy of
`values`: the box theorem that the element holds the value. -/

example : Prog.toStr (sol{ uint i = 0; uint[] memory carolValues = values;
    carolValues[i] = makeValue(); } : Prog Operands) =
    "uint i = 0; uint[] memory carolValues = values; uint se1; se1 = makeValue(); carolValues[i] = se1;" :=
  rfl

/-- The first step, `uint pv = makeValue(); carolValues[i] = pv;`. -/
example : dl!{ ⟨ uint[] memory carolValues = values; carolValues[i] = makeValue(); ⟩ true } =
    dl!{ ⟨ uint[] memory carolValues = values; uint se1 = makeValue(); carolValues[i] = se1; ⟩
      true } := rfl

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

/-! ## 8 · A function returning a memory reference

The program `choosePersonMem().account = makeAccount();`
(a memory example; its chain is `Chains.Memory`'s).  A call of a function returning a memory
reference is KeY's expansion written out (`Syntax.lean`'s docstring): the
callee's return variable, fresh, is declared at the head of its body (a
fresh default object, as solc allocates one on entry), and the statement
after the call binds the caller's local to its identity.  The two print, and
read back, as the one statement `Person memory p = choosePersonMem();`.  No
statement, rule or semantics is added: `internalCallExpand` inlines the
body, and the rest are the memory rules.

`makeAccount` writes its named return variable; `choosePersonMem` returns a
copy of the state variable `alice`. -/

def MemCalls : Contract := contract!{
  Person alice;
  function makeAccount() returns (Account memory a) { a.balance = 100; }
  function choosePersonMem() returns (Person memory) { return alice; }
}

/-- A declaration from a memory-returning call: one statement, printed as
written. -/
example : Prog.toStr (sol[MemCalls]{ Person memory p = choosePersonMem(); } : Prog MemCalls) =
    "Person memory p = choosePersonMem();" := rfl

/-- An assignment to a memory local, the same. -/
example : Prog.toStr (sol[MemCalls]{ Person memory p; p = choosePersonMem(); } : Prog MemCalls) =
    "Person memory p; p = choosePersonMem();" := rfl

-- The call inlined (`Prog.inlined`): the return variable `mv1` declared, the
-- body (`return alice;` a copy into it), `p` bound to it.
/-- info: Person memory mv1; mv1 = alice; Person memory p = mv1; -/
#guard_msgs in
#eval IO.println (Prog.toStr (Prog.inlined (sol[MemCalls]{ Person memory p = choosePersonMem(); } :
    Prog MemCalls)))

/-- The call's first step, `internalCallExpand`. -/
example : dl[MemCalls]{ ⟨ Person memory p = choosePersonMem(); ⟩ true }
    ~[internalCallExpand]~>
      dl[MemCalls]{ ⟨ Person memory mv1; mv1 = alice; Person memory p = mv1; ⟩ true } :=
  rfl

/-- A declaration from a memory-returning call: the copy of `alice`. -/
theorem memCallDecl :
    ⊨ dl[MemCalls]{ [ alice.age = 34; Person memory p = choosePersonMem(); uint v = p.age; ]
      v == 34 } := by
  sol_symex
  sol_close

/-- The write through a bound result: the member holds what
`makeAccount` built. -/
theorem memCallMemberWrite :
    ⊨ dl[MemCalls]{ [ Person memory p = choosePersonMem(); p.account = makeAccount();
      uint b = p.account.balance; ] b == 100 } := by
  sol_symex
  sol_close

/-! What is refused: a reference return not declared `memory` (solc's
rule), and a memory reference where a value is expected. -/

def NoLocation : Contract := contract!{
  function makeAccount() returns (Account a) { a.balance = 1; }
}

/--
error: Solidity elaboration failed: makeAccount: its return of reference type Account needs the location `memory`
-/
#guard_msgs in #check sol[NoLocation]{ Account memory acc = makeAccount(); }

/-- error: Solidity elaboration failed: makeAccount returns a memory Account, not a uint -/
#guard_msgs in #check sol[MemCalls]{ uint x = makeAccount(); }

-- A push used as a target on an entry: its receiver is evaluated after the
-- right-hand side, and `b.push(e)` evaluates it before.
/--
error: `b.push() = e;` is written on a name or a member chain, `bucket.tokens`
---
error: cannot evaluate code because 'sorryAx' uses 'sorry' and/or contains errors
-/
#guard_msgs in #check sol[TestSuite]{ matrix[0].push() = 5; }

-- A member of `push()`: a member of a call is one of a function's value.
/--
error: a call's callee is a function's name
---
error: cannot evaluate code because 'sorryAx' uses 'sorry' and/or contains errors
-/
#guard_msgs in #check sol[TestSuite]{ bucket.tokens.push().value = 1; }

end Solidity.Examples.Tactics.CallOperands
