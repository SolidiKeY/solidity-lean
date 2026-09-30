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
written with its `++i` left in place, and the memory programs are pinned
(`Prog.toStr`) and proved by the strategy rather than drawn line by line.
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

/-! ## 2 · `values.push() = makeValue();`

The push used as a target is the push of its right-hand side: the same
formula as §1, so the same chain. -/

example : dl!{ ⟨ values.push() = makeValue(); ⟩ true } =
    dl!{ ⟨ values.push(makeValue()); ⟩ true } := rfl

/-- `values.push() = makeValue();` — §1's chain, whose first line this is. -/
def pushLvalueCallValue : dl!{ ⟨ values.push() = makeValue(); ⟩ true }
    ~*> dl!{ { se1 := 0 } { se2 := 0 } { se2 := select(storage, seed) } { se1 := se2 }
            { storage := save(save(storage, values[values.length], se1), values.length,
                values.length + 1) } true } :=
  pushCallValue

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

/-- `Token storage tokRef = bob.account.token; tokens.push() = tokRef;` -/
def pushLvalueRefSource :
    dl[TestSuite]{ ⟨ Token storage tokRef = bob.account.token; tokens.push() = tokRef; ⟩ true }
    ~*> dl[TestSuite]{ { sp1 := bob.account } { tokRef := sp1.token }
          { storage := save(save(storage, tokens[tokens.length], find(storage, tokRef)),
              tokens.length, tokens.length + 1) } true } := by
  sol_chain

/-- `Token storage tokRef = bob.account.token; bucket.tokens.push() = tokRef;` —
the receiver aliased to `sp2` first. -/
def bucketPushLvalueRefSource :
    dl[TestSuite]{ ⟨ Token storage tokRef = bob.account.token;
      bucket.tokens.push() = tokRef; ⟩ true }
    ~*> dl[TestSuite]{ { sp1 := bob.account } { tokRef := sp1.token } { sp2 := bucket.tokens }
          { storage := save(save(storage, sp2[sp2.length], find(storage, tokRef)), sp2.length,
              sp2.length + 1) } true } := by
  sol_chain

/-- `Token storage t = bucket.tokens.push(); t.value = 11;` — the slot a push
on a member chain returns, bound and written (the printed
`bucket.tokens.push().value = valueVal;`, whose member of `push()` does not
parse). -/
theorem bucketPushSlotWrite :
    ⊨ dl[TestSuite]{ [ Token storage t = bucket.tokens.push(); t.value = 11; ]
      t.value == 11 } := by
  sol_symex
  sol_close

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
`values`. -/

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

/-! ## What cannot be written

A function returning a memory reference, as in
`choosePersonMem().account = makeAccount();`: a call's value is a value type
(`CallRet`), and `returns (Account memory)` reads `memory` as the return
variable's name. -/

/-- A function returning a memory struct. -/
def MemReturn : Contract := contract!{
  uint seed;
  function makeAccount() returns (Account memory) { Account memory a; return a; }
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
