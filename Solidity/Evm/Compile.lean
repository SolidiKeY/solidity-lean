import Solidity.Evm.Machine

/-!
# Solidity → EVM compilation

A verified-fragment compiler from the project's Solidity AST
(`AST.lean`) to the EVM machine of `Evm/Machine.lean`, following the
code-generation discipline of solc for value types:

- **locals live on the EVM stack**: the compile-time context `Γ` lists
  the declared stack locals, most recent first; reading local `i` under
  `t` temporaries emits `DUP (t+i+1)`, writing it emits
  `SWAP (i+1); POP`. Depths are checked against the EVM's `DUP16`/
  `SWAP16` limit;
- **primitive storage roots get one slot each**: the layout `L` lists
  the contract's storage roots in slot order; reads are
  `PUSH slot; SLOAD`, writes `PUSH slot; SSTORE`;
- **strict binary operators** compile right-then-left so the
  left operand ends on top, matching the EVM's `μ₀ op μ₁` operand
  order (`SUB` is top-minus-second, `LT` is top-less-than-second, …);
- `/` and `%` emit an explicit zero-divisor guard
  (`DUP1; JUMPI +1; REVERT`) because the source semantics reverts where
  the bare EVM opcodes return `0`; `+`, `-`, `*` at `uint` emit an
  overflow guard (`checkedOpCode`) because the source semantics reverts
  where the bare opcodes wrap around (solc ≥ 0.8 checked arithmetic);
- `to.transfer(amt)` loads the reserved balance word `balanceSlotW`,
  reverts unless it covers `amt`, then debits it and the recipient's
  net-ledger slot (`transferTail`);
- `&&`/`||` and `cond ? a : b` short-circuit with forward jumps,
  mirroring `Semantics.evalValue`;
- `if`/`require`/`assert`/`revert` compile to the standard jump
  skeletons.

`compile*` are partial (`Option`): `none` means the construct is
outside the verified fragment (memory, nested structured element
types, increments; direct calls compile via inlining — see
`docs/compiler-verification.md` § "Remaining boundary").
Everything the compiler accepts is covered by the preservation proof in
`Evm/Correctness.lean`.
-/

namespace Solidity
namespace Evm

/-- `2^256` as an `Int` bound for compile-time literal checks (cast
from `Nat`, where kernel arithmetic on the literal is fast). -/
def wordSizeI : Int := ((2 ^ 256 : Nat) : Int)

/-- Bound on mapping keys in the verified fragment: keys live in
`[0, 2^224)` so that `mapSlotW` slot derivation is injective (see
`Machine.mapSlotW`). -/
def keyBound : Nat := 2 ^ 224

/-- `keyBound` as an `Int`. -/
def keyBoundI : Int := ((2 ^ 224 : Nat) : Int)

/-- Bound on the number of storage roots: keeps direct slots below the
mapping-slot region and the slot factor of `mapSlotW` overflow-free. -/
def layoutBound : Nat := 2 ^ 31

/-- Slot index of a storage root in the layout. -/
def slotOf? (L : List Name) (name : Name) : Option Nat :=
  L.findIdx? (· = name)

/-- Is this the type of a storage array root? (The compiler and the
bounded semantics dispatch on this same predicate, so the code shape
and the semantic formula always agree.) -/
def isArrayTy : Ty → Bool
  | Ty.ref (RefTy.array _) => true
  | _ => false

/-- Is this the type of a storage struct root? -/
def isStructTy : Ty → Bool
  | Ty.ref (RefTy.struct _) => true
  | _ => false

theorem isArrayTy_eq_false_of_isStructTy {ty : Ty}
    (h : isStructTy ty = true) : isArrayTy ty = false := by
  cases ty with
  | prim p => rfl
  | ref r => cases r <;> simp_all [isStructTy, isArrayTy]

/-- Index of a field in a struct's declaration (`structDef`); the
compiler derives the field's slot from this static position, and the
bounded semantics checks at run time that the stored struct's field
spine matches the declaration. -/
def structIdx? (sname fname : Name) : Option Nat :=
  (Semantics.structDef sname).findIdx? (·.1 = fname)

/-- The declared field-name spine of a struct type (empty for
non-struct types). The bounded semantics claims a struct-field access
only when the stored struct's spine matches this declaration, which
ties the compiler's static field index to the run-time position. -/
def structSpineOf : Ty → List Name
  | Ty.ref (RefTy.struct sname) =>
      (Semantics.structDef sname).map Prod.fst
  | _ => []

/-- Storage slot key of layout index `i`. -/
def slotWord (i : Nat) : Word :=
  BitVec.ofNat 256 i

/-- Base of the net-ledger region: the interpreter's abstract `net`
transfer ledger lives in machine storage at `netBase + address`. The
base sits above every direct slot (`< 2^31`) and every derived slot
(`< 2^255 + 2^224`), so the three regions are provably disjoint. -/
def netBase : Word := BitVec.ofNat 256 (2 ^ 255 + 2 ^ 225)

/-- Net-ledger slot of an address word (addresses are bounded by
`keyBound`, like keys). -/
def netSlotW (aw : Word) : Word := netBase + aw

/-- Reserved storage word holding the contract's own balance
(`State.selfBalance`): the machine's stand-in for `SELFBALANCE` and for the
value debit a real `CALL` performs. Sits above the net-ledger region
(`< 2^255 + 2^225 + 2^224`), so the four storage regions are provably
disjoint. -/
def balanceSlotW : Word := BitVec.ofNat 256 (2 ^ 255 + 2 ^ 226)

/-- Instruction tail of a strict (non-short-circuit, unguarded) binary
operator. Operands are compiled left-then-right (source evaluation
order), so at the tail the stack is `right :: left :: …` — the
*mirror* of the EVM's `μ₀ op μ₁` layout. Symmetric operators need no
fix-up; `SUB`/`EXP` get a `SWAP1`; comparisons use the flipped opcode
(`LT` with the right operand on top *is* `left > right`). `&&`/`||`
(short-circuit) and `/`/`%` (zero guard) are handled by `compileExpr`
itself. -/
def strictOpCode : BinOp → Option Code
  | .add => some [.add]
  | .sub => some [.swap 1, .sub]
  | .mul => some [.mul]
  | .pow => some [.swap 1, .exp]
  | .lt => some [.gt]
  | .gt => some [.lt]
  | .le => some [.lt, .iszero]
  | .ge => some [.gt, .iszero]
  | .eqB => some [.eq]
  | .neB => some [.eq, .iszero]
  | _ => none

/-- The operators whose result the compiled code overflow-checks:
`+`, `-`, `*` at operand type `uint` (solc ≥ 0.8 checked arithmetic,
`Semantics.checkArith` at `Ty.uint`). Their word-level overflow is
decidable from the operand words, so the compiled code reverts exactly
where the source semantics does. `**`, the comparisons and every `int`
operator keep the unchecked `strictOpCode` tail (their overflow stays a
fragment boundary, see `BoundedSemantics.checkArithW`). -/
def uintChecked : BinOp → Ty → Bool
  | .add, Ty.uint => true
  | .sub, Ty.uint => true
  | .mul, Ty.uint => true
  | _, _ => false

/-- Overflow-checked instruction tails, entered with `right :: left :: σ`
and leaving the result word on `σ`, or reaching `REVERT` on overflow
(stack after each instruction, `l`/`r` the operands):

- `+`: `DUP2, ADD` gives `(l+r) :: l`; `SWAP1, DUP2, LT` computes
  `(l+r) < l`, true exactly on wrap-around; `ISZERO, JUMPI 1, REVERT`
  skips the revert when the sum did not wrap and leaves `l+r`;
- `-`: `DUP2, DUP2, GT` computes `l < r` (the EVM `GT` on `r :: l` is
  `r > l`), true exactly on underflow; after the guard `SWAP1, SUB`
  leaves `l - r`;
- `*`: `DUP1, DUP3, MUL` gives `p :: r :: l` with `p = l * r mod 2^256`;
  `SWAP2, DUP2, DUP4, DIV, EQ` computes `p / r = l` (with `p / 0 = 0`);
  `SWAP1, ISZERO, OR` disjoins it with `r = 0` — the disjunction holds
  exactly when `l * r < 2^256` (`Correctness.mul_overflow_iff`); the
  guard leaves `p`. -/
def checkedOpCode : BinOp → Code
  | .add => [.dup 2, .add, .swap 1, .dup 2, .lt, .iszero, .jumpi 1, .revert]
  | .sub => [.dup 2, .dup 2, .gt, .iszero, .jumpi 1, .revert, .swap 1, .sub]
  | .mul => [.dup 1, .dup 3, .mul, .swap 2, .dup 2, .dup 4, .div, .eq,
             .swap 1, .iszero, .or, .jumpi 1, .revert]
  | _ => []

/-- The instruction tail of a non-short-circuit, non-guarded binary
operator at operand type `ty`: the overflow-checked tail for
`uintChecked` operators, the strict tail otherwise. -/
def binopTail (op : BinOp) (ty : Ty) : Option Code :=
  if uintChecked op ty then some (checkedOpCode op) else strictOpCode op

/-- Tail of `to.transfer(amt)`, entered with `amt :: ns :: σ` (`ns` the
recipient's net-ledger slot): load the balance word, revert unless it
covers `amt`, store the debited balance, then debit the ledger word.
Stack after each instruction (`bal := st[balanceSlotW]`):
`bal :: amt :: ns`, `amt :: bal :: amt :: ns`, `bal :: amt :: bal :: amt :: ns`,
`(bal < amt) :: bal :: amt :: ns`, `(amt ≤ bal) :: …`, then `JUMPI` over
the `REVERT` leaves `bal :: amt :: ns`; `DUP2, SWAP1, SUB` gives
`(bal - amt) :: amt :: ns`, `PUSH balanceSlotW, SSTORE` stores it and leaves
`amt :: ns`; the last five instructions are the ledger debit. -/
def transferTail : Code :=
  [ .push balanceSlotW, .sload,
    .dup 2, .dup 2, .lt, .iszero, .jumpi 1, .revert,
    .dup 2, .swap 1, .sub, .push balanceSlotW, .sstore,
    .dup 2, .sload, .sub, .swap 1, .sstore ]

/-- Compile an expression. `Γ` is the stack-local context (most recent
first), `t` the number of temporaries currently above the locals region.
The generated code pushes exactly one word — the expression's value —
and touches nothing below the temporaries. -/
def compileExpr (L Γ : List Name) : Nat → WrappedExpr → Option Code
  | _, .bool b => some [.push (wBool b)]
  | _, .intLit _ v =>
      if 0 ≤ v ∧ v < wordSizeI then
        some [.push (BitVec.ofNat 256 v.toNat)]
      else none
  | t, .var .stack ty fld =>
      if ty.isPrimitive then
        match Γ.findIdx? (· = fld.name) with
        | some i => if t + i + 1 ≤ 16 then some [.dup (t + i + 1)] else none
        | none => none
      else none
  | _, .var .storage ty fld =>
      if fld.origin = some .global ∧ ty.isPrimitive then
        match slotOf? L fld.name with
        | some i => some [.push (slotWord i), .sload]
        | none => none
      else none
  | t, .index .storage _ (.var .storage tyM fld) key =>
      -- `m[k]` for a global mapping root: derive the entry slot and
      -- load it. `a[k]` for a global array root: load the length from
      -- the direct slot, bounds-check (out of bounds reverts, as in
      -- the source semantics), then load the element's derived slot.
      if fld.origin = some .global then
        match slotOf? L fld.name with
        | some i =>
            if isArrayTy tyM then do
              let ck ← compileExpr L Γ t key
              pure (ck ++ [.push (slotWord i), .sload, .dup 2, .lt,
                .jumpi 1, .revert, .push (slotWord i), .mapslot,
                .sload])
            else do
              let ck ← compileExpr L Γ t key
              pure (ck ++ [.push (slotWord i), .mapslot, .sload])
        | none => none
      else none
  | t, .mkBinop .and l r => do
      let cl ← compileExpr L Γ t l
      let cr ← compileExpr L Γ t r
      pure (cl ++ [.dup 1, .iszero, .jumpi (cr.length + 1), .pop] ++ cr)
  | t, .mkBinop .or l r => do
      let cl ← compileExpr L Γ t l
      let cr ← compileExpr L Γ t r
      pure (cl ++ [.dup 1, .jumpi (cr.length + 1), .pop] ++ cr)
  | t, .mkBinop .div l r => do
      let cl ← compileExpr L Γ t l
      let cr ← compileExpr L Γ (t + 1) r
      pure (cl ++ cr ++ [.dup 1, .jumpi 1, .revert, .swap 1, .div])
  | t, .mkBinop .mod l r => do
      let cl ← compileExpr L Γ t l
      let cr ← compileExpr L Γ (t + 1) r
      pure (cl ++ cr ++ [.dup 1, .jumpi 1, .revert, .swap 1, .mod])
  | t, .mkBinop op l r => do
      let tail ← binopTail op l.ty
      let cl ← compileExpr L Γ t l
      let cr ← compileExpr L Γ (t + 1) r
      pure (cl ++ cr ++ tail)
  | t, .mkUnop .not arg => do
      let ca ← compileExpr L Γ t arg
      pure (ca ++ [.iszero])
  | t, .mkTernary c thn els => do
      let cc ← compileExpr L Γ t c
      let ct ← compileExpr L Γ t thn
      let ce ← compileExpr L Γ t els
      pure (cc ++ [.iszero, .jumpi (ct.length + 1)] ++ ct
              ++ [.jump ce.length] ++ ce)
  | _, .field .storage _ (.var .storage tyA fld) lfld =>
      -- `a.length` for a global array root: the length is the word at
      -- the root's direct slot. `r.f` for a global struct root: the
      -- field's word sits at the derived slot of the field's static
      -- index, a compile-time constant.
      if fld.origin = some .global ∧ lfld.name = "length" ∧
          isArrayTy tyA then
        match slotOf? L fld.name with
        | some i => some [.push (slotWord i), .sload]
        | none => none
      else if fld.origin = some .global ∧ isStructTy tyA then
        match slotOf? L fld.name, tyA with
        | some i, Ty.ref (RefTy.struct sname) =>
            (match structIdx? sname lfld.name with
            | some j =>
                if j < keyBound then
                  some [.push (mapSlotW (slotWord i)
                    (BitVec.ofNat 256 j)), .sload]
                else none
            | none => none)
        | _, _ => none
      else none
  | _, _ => none

/-- Compile an assignment of expression `rhs` into the place `lhs`
(shared by `assign`, `compoundAssign`, and re-declarations). -/
def compileAssign (L Γ : List Name) (lhs rhs : WrappedExpr) :
    Option Code :=
  match lhs with
  | .var .stack ty fld =>
      if ty.isPrimitive then
        match Γ.findIdx? (· = fld.name) with
        | some i =>
            if i + 1 ≤ 16 then do
              let cr ← compileExpr L Γ 0 rhs
              pure (cr ++ [.swap (i + 1), .pop])
            else none
        | none => none
      else none
  | .var .storage _ fld =>
      if fld.origin = some .global ∧ rhs.ty.isPrimitive then
        match slotOf? L fld.name with
        | some i => do
            let cr ← compileExpr L Γ 0 rhs
            pure (cr ++ [.push (slotWord i), .sstore])
        | none => none
      else none
  | .index .storage _ (.var .storage tyM fld) key =>
      -- `m[k] = e` for a global mapping root `m`: the code evaluates
      -- the key first, then the value; `SWAP1` re-orders for `SSTORE`.
      -- (The interpreter, following solc, evaluates the value first —
      -- the fragment's expressions are pure, and `assignW` claims only
      -- executions whose key evaluates, where the orders agree.)
      -- `a[k] = e` for a global array root additionally bounds-checks
      -- after the value (the interpreter's save reverts out of bounds
      -- only after evaluating the right-hand side).
      if fld.origin = some .global ∧ rhs.ty.isPrimitive then
        match slotOf? L fld.name with
        | some i =>
            if isArrayTy tyM then do
              let ck ← compileExpr L Γ 0 key
              let cr ← compileExpr L Γ 1 rhs
              pure (ck ++ cr ++
                [.push (slotWord i), .sload, .dup 3, .lt, .jumpi 1,
                 .revert, .swap 1, .push (slotWord i), .mapslot,
                 .sstore])
            else do
              let ck ← compileExpr L Γ 0 key
              let cr ← compileExpr L Γ 1 rhs
              pure (ck ++ cr ++
                [.swap 1, .push (slotWord i), .mapslot, .sstore])
        | none => none
      else none
  | .field .storage _ (.var .storage tyA fld) lfld =>
      -- `r.f = e` for a global struct root: store at the field's
      -- derived slot (a compile-time constant).
      if fld.origin = some .global ∧ isStructTy tyA ∧
          rhs.ty.isPrimitive then
        match slotOf? L fld.name, tyA with
        | some i, Ty.ref (RefTy.struct sname) =>
            (match structIdx? sname lfld.name with
            | some j =>
                if j < keyBound then do
                  let cr ← compileExpr L Γ 0 rhs
                  pure (cr ++ [.push (mapSlotW (slotWord i)
                    (BitVec.ofNat 256 j)), .sstore])
                else none
            | none => none)
        | _, _ => none
      else none
  | _ => none

mutual

/-- Compile a statement, returning the code and the updated local
context (`stackDecl` of a new name extends `Γ`; everything else leaves
it unchanged). -/
def compileStmt (L Γ : List Name) : Stmt → Option (Code × List Name)
  | .expr e => do
      let c ← compileExpr L Γ 0 e
      pure (c ++ [.pop], Γ)
  | .assign lhs rhs => do
      let c ← compileAssign L Γ lhs.expr rhs
      pure (c, Γ)
  | .compoundAssign op lhs rhs =>
      if op.hasCompoundAssign then do
        let c ← compileAssign L Γ lhs.expr (.mkBinop op lhs.expr rhs)
        pure (c, Γ)
      else none
  | .stackDecl ty name init =>
      if ty.isPrimitive ∧ ¬L.contains name then
        match Γ.findIdx? (· = name) with
        | some i =>
            -- Re-declaration of an existing local: reuse its slot.
            if i + 1 ≤ 16 then do
              let cr ← match init with
                | none => pure [Instr.push 0]
                | some rhs => compileExpr L Γ 0 rhs
              pure (cr ++ [.swap (i + 1), .pop], Γ)
            else none
        | none => do
            let cr ← match init with
              | none => pure [Instr.push 0]
              | some rhs => compileExpr L Γ 0 rhs
            pure (cr, name :: Γ)
      else none
  | .ite cond thn els => do
      let cc ← compileExpr L Γ 0 cond
      let (ct, Γt) ← compileBlock L Γ thn
      let (ce, Γe) ← compileBlock L Γ els
      -- Branches may not declare new locals: the stack shapes of the
      -- two arms must agree at the join point.
      if Γt = Γ ∧ Γe = Γ then
        pure (cc ++ [.iszero, .jumpi (ct.length + 1)] ++ ct
                ++ [.jump ce.length] ++ ce, Γ)
      else none
  | .requireStmt cond => do
      let cc ← compileExpr L Γ 0 cond
      pure (cc ++ [.jumpi 1, .revert], Γ)
  | .assertStmt cond => do
      let cc ← compileExpr L Γ 0 cond
      pure (cc ++ [.jumpi 1, .revert], Γ)
  | .revert _ => pure ([.revert], Γ)
  | .push target value =>
      -- `a.push(e)` / `a.push()` on a global array root: load the
      -- length, evaluate the element (default `0` for a valueless
      -- push), store it at the derived slot of index `length`, then
      -- store `length + 1` back at the root slot.
      (match target.expr with
      | .var .storage tyA fld =>
          (match tyA with
          | Ty.ref (RefTy.array elemTy) =>
              if fld.origin = some .global ∧ elemTy.isPrimitive then
                match slotOf? L fld.name with
                | some i => do
                    let cv ← match value with
                      | none => pure [Instr.push 0]
                      | some rhs =>
                          if rhs.ty.isPrimitive then
                            compileExpr L Γ 1 rhs
                          else none
                    pure ([Instr.push (slotWord i), .sload] ++ cv ++
                      [.dup 2, .push (slotWord i), .mapslot, .sstore,
                       .push 1, .add, .push (slotWord i), .sstore], Γ)
                | none => none
              else none
          | _ => none)
      | _ => none)
  | .transfer recipient amount => do
      -- `to.transfer(amt)`: evaluate the recipient, derive its
      -- net-ledger slot, evaluate the amount, then `transferTail`:
      -- check the contract balance (`REVERT` when it does not cover
      -- the amount — the EVM value-transfer check `Semantics.execStmt`
      -- reverts on), debit the balance word, debit the ledger.
      let ca ← compileExpr L Γ 0 recipient
      let cm ← compileExpr L Γ 1 amount
      pure (ca ++ [Instr.push netBase, .add] ++ cm ++ transferTail, Γ)
  | .pop target =>
      -- `a.pop()` on a global array root: load the length, revert if
      -- zero, store `length - 1` back at the root slot (the stale
      -- element slot is unobservable — reads bounds-check first).
      (match target.expr with
      | .var .storage tyA fld =>
          (match tyA with
          | Ty.ref (RefTy.array _) =>
              if fld.origin = some .global then
                match slotOf? L fld.name with
                | some i =>
                    pure ([Instr.push (slotWord i), .sload, .dup 1,
                      .jumpi 1, .revert, .push 1, .swap 1, .sub,
                      .push (slotWord i), .sstore], Γ)
                | none => none
              else none
          | _ => none)
      | _ => none)
  | _ => none

/-- Compile a statement list, threading the local context. -/
def compileBlock (L Γ : List Name) : List Stmt → Option (Code × List Name)
  | [] => pure ([], Γ)
  | stmt :: rest => do
      let (c₁, Γ₁) ← compileStmt L Γ stmt
      let (c₂, Γ₂) ← compileBlock L Γ₁ rest
      pure (c₁ ++ c₂, Γ₂)

end

/-- Compile a whole block against a storage layout, starting with no
locals. The machine entry configuration is `⟨0, [], st⟩`. -/
def compileProgram (L : List Name) (b : Block) : Option Code := do
  let (c, _) ← compileBlock L [] b
  pure c

end Evm
end Solidity
