import Solidity.Evm.Compile

/-!
# Bounded (uint256) source semantics and its agreement theorems

The official interpreter (`Semantics.lean`) computes over unbounded
`Int`s; the EVM computes modulo `2^256`. The two agree exactly on
executions whose intermediate arithmetic stays inside `[0, 2^256)`.
This file defines the mediating semantics that captures those
executions:

- `evalW` / `execW` / `execWBlock` mirror `Semantics.evalValue` /
  `execStmt` / `execBlock` case for case on the compiled fragment, with
  one difference: an arithmetic result outside `[0, 2^256)` on an
  operator the compiled code does *not* guard (`**`, the `int`-typed
  operators) is `.stuck` (out of scope) instead of a value. `.stuck`
  here means "no claim" — the preservation theorem quantifies only over
  `.ok` and `.revert` outcomes of the bounded semantics. The operators
  the compiled code does guard — `uint` `+`/`-`/`*`
  (`Compile.uintChecked`, `checkedOpCode`) and the balance check of
  `transfer` (`transferTail`) — follow the official semantics exactly:
  overflow and an unfunded transfer are `.revert`, not `.stuck`
  (`applyCheckedW`, the `transfer` arm of `execW`).

- The agreement theorems (`evalW_agree`, `execW_agree`,
  `execWBlock_agree`) prove the mirror faithful: whenever the bounded
  semantics produces `.ok`/`.revert`, the *official* interpreter
  produces the same result. Composed with the machine simulation in
  `Evm/Correctness.lean`, this yields preservation against the
  project's actual Solidity semantics, not against a private variant.
-/

-- The agreement/simulation proofs below use uniform, defensive
-- `simp` lists across dozens of structurally similar cases; the
-- unused-argument lint would demand bespoke lists per case.
set_option linter.unusedSimpArgs false

namespace Solidity
namespace Evm

open Semantics

/-- Bound check on a single value: integers must fit a uint256 word,
booleans always do. -/
def checkW : Value → Res Value
  | Value.int n =>
      if 0 ≤ n ∧ n < wordSizeI then .ok (Value.int n) else .error .stuck
  | v => .ok v

theorem checkW_ok {v v' : Value} (h : checkW v = .ok v') : v' = v := by
  cases v with
  | int n =>
      simp only [checkW] at h
      split at h <;> simp_all
  | bool b => simpa [checkW] using h.symm

theorem checkW_not_revert {v : Value} :
    checkW v ≠ .error .revert := by
  cases v with
  | int n =>
      simp only [checkW]
      split <;> simp
  | bool b => simp [checkW]

/-- Do two values have the same primitive shape (`int`/`int` or
`bool`/`bool`)? The EVM's `EQ` compares raw words, so the compiled
fragment only claims `==`/`!=` on same-shaped operands (`int 1` and
`bool true` share the word `1` but are unequal as source values). -/
def sameShape : Value → Value → Bool
  | Value.int _, Value.int _ => true
  | Value.bool _, Value.bool _ => true
  | _, _ => false

/-- Is `op` a value equality (`==`/`!=`)? -/
def isEqOp : BinOp → Bool
  | .eqB | .neB => true
  | _ => false

/-- Is a run-time value a boolean? -/
def isBoolV : Value → Bool
  | Value.bool _ => true
  | Value.int _ => false

/-- `applyBinOp`, restricted to what a uint256 word machine can claim:
an arithmetic result outside `[0, 2^256)` becomes `.stuck` (out of the
verified fragment), as does `==`/`!=` on differently-shaped operands.
Comparisons and boolean connectives are unchanged; `/` and `%` keep
their zero-divisor revert. -/
def applyBinOpW (op : BinOp) (l r : Value) : Res Value := do
  let v ← applyBinOp op l r
  if op.isArith then checkW v
  else if isEqOp op && !sameShape l r then .error .stuck
  else pure v

theorem applyBinOpW_ok {op : BinOp} {l r v : Value}
    (h : applyBinOpW op l r = .ok v) : applyBinOp op l r = .ok v := by
  unfold applyBinOpW at h
  cases hab : applyBinOp op l r with
  | error e => rw [hab] at h; simp [bind, Except.bind] at h
  | ok v' =>
      -- `cases hab :` also rewrote the goal to `.ok v' = .ok v`.
      rw [hab] at h
      simp only [bind, Except.bind] at h
      by_cases hA : op.isArith = true
      · rw [if_pos hA] at h
        rw [checkW_ok h]
      · rw [if_neg hA] at h
        by_cases hE : (isEqOp op && !sameShape l r) = true
        · rw [if_pos hE] at h
          exact absurd h (by simp)
        · rw [if_neg hE] at h
          exact h

theorem applyBinOpW_revert {op : BinOp} {l r : Value}
    (h : applyBinOpW op l r = .error .revert) :
    applyBinOp op l r = .error .revert := by
  unfold applyBinOpW at h
  cases hab : applyBinOp op l r with
  | error e =>
      rw [hab] at h
      simp only [bind, Except.bind] at h
      exact h
  | ok v' =>
      rw [hab] at h
      simp only [bind, Except.bind] at h
      by_cases hA : op.isArith = true
      · rw [if_pos hA] at h
        exact absurd h checkW_not_revert
      · rw [if_neg hA] at h
        by_cases hE : (isEqOp op && !sameShape l r) = true
        · rw [if_pos hE] at h
          exact absurd h (by simp)
        · rw [if_neg hE] at h
          exact h

/-- The official checked-arithmetic guard (`Semantics.checkArith`),
weakened to a fragment boundary: what the official semantics rejects
with a revert (the executable `Panic(0x11)`) the word machine makes no
claim about, on the operators whose compiled code carries no overflow
check (`**`, `int`-typed operators; the `uint` `+`/`-`/`*` tails are
checked and take the official `checkArith` path in `applyCheckedW`
instead). On `uint` this never fires after `checkW` (same bounds); on
`int` it cuts `[2^255, 2^256)` out of the fragment. -/
def checkArithW (ty : Ty) (v : Value) : Res Value :=
  match checkArith ty v with
  | .ok v => .ok v
  | .error _ => .error .stuck

/-- The operator step shared by `evalW`'s binary-operator arm and
`execW`'s compound-assignment arm, at operand type `ty`: for the
overflow-checked operators (`uintChecked`, compiled with
`checkedOpCode`) this is literally the official
`applyBinOp` followed by `checkArith Ty.uint` — overflow *reverts*, as in
the source semantics, and the compiled guard reverts with it; for every
other operator it is the word-bounded `applyBinOpW` followed by the
fragment-boundary `checkArithW` at the result type. -/
def applyCheckedW (op : BinOp) (ty : Ty) (l r : Value) : Res Value :=
  if uintChecked op ty then do
    let v ← applyBinOp op l r
    checkArith Ty.uint v
  else do
    let v ← applyBinOpW op l r
    checkArithW (op.retTy ty) v

theorem uintChecked_cases {op : BinOp} {ty : Ty}
    (h : uintChecked op ty = true) :
    (op = .add ∨ op = .sub ∨ op = .mul) ∧ ty = Ty.uint := by
  cases op <;> cases ty with
  | prim pt => cases pt <;> simp_all [uintChecked]
  | ref rt => simp_all [uintChecked]

theorem uintChecked_retTy {op : BinOp} {ty : Ty}
    (h : uintChecked op ty = true) : op.retTy ty = Ty.uint := by
  obtain ⟨hop, rfl⟩ := uintChecked_cases h
  rcases hop with rfl | rfl | rfl <;> rfl

/-- An `applyCheckedW` value is an official `applyBinOp` value that
passes the official check at the result type. -/
theorem applyCheckedW_ok {op : BinOp} {ty : Ty} {l r v : Value}
    (h : applyCheckedW op ty l r = .ok v) :
    applyBinOp op l r = .ok v ∧ checkArith (op.retTy ty) v = .ok v := by
  unfold applyCheckedW at h
  split at h
  case isTrue huc =>
      rw [uintChecked_retTy huc]
      cases hab : applyBinOp op l r with
      | error e => rw [hab] at h; simp [bind, Except.bind] at h
      | ok u =>
          rw [hab] at h
          simp only [bind, Except.bind] at h
          have := checkArith_ok_eq h
          subst this
          exact ⟨rfl, h⟩
  case isFalse =>
      cases hab : applyBinOpW op l r with
      | error e => rw [hab] at h; simp [bind, Except.bind] at h
      | ok u =>
          rw [hab] at h
          simp only [bind, Except.bind] at h
          cases hc : checkArith (op.retTy ty) u with
          | error e => rw [checkArithW, hc] at h; exact absurd h (by simp)
          | ok w =>
              rw [checkArithW, hc] at h
              cases h
              have := checkArith_ok_eq hc
              subst this
              exact ⟨applyBinOpW_ok hab, hc⟩

/-- An `applyCheckedW` revert is an official revert: of the operator
itself, or of the official check on its value. -/
theorem applyCheckedW_revert {op : BinOp} {ty : Ty} {l r : Value}
    (h : applyCheckedW op ty l r = .error .revert) :
    applyBinOp op l r = .error .revert ∨
      ∃ u, applyBinOp op l r = .ok u ∧
        checkArith (op.retTy ty) u = .error .revert := by
  unfold applyCheckedW at h
  split at h
  case isTrue huc =>
      rw [uintChecked_retTy huc]
      cases hab : applyBinOp op l r with
      | error e =>
          rw [hab] at h
          simp only [bind, Except.bind, Except.error.injEq] at h
          exact Or.inl (by rw [h])
      | ok u =>
          rw [hab] at h
          simp only [bind, Except.bind] at h
          exact Or.inr ⟨u, rfl, h⟩
  case isFalse =>
      cases hab : applyBinOpW op l r with
      | error e =>
          rw [hab] at h
          simp only [bind, Except.bind, Except.error.injEq] at h
          subst h
          exact Or.inl (applyBinOpW_revert hab)
      | ok u =>
          rw [hab] at h
          simp only [bind, Except.bind] at h
          cases hc : checkArith (op.retTy ty) u with
          | error e => rw [checkArithW, hc] at h; exact absurd h (by simp)
          | ok w => rw [checkArithW, hc] at h; exact absurd h (by simp)

/-- The short-circuit arms shared by `Semantics.evalValue` and `evalW`:
`false && _` and `true || _` return without evaluating the right
operand. -/
def scArm (op : BinOp) (lv : Value) : Option Value :=
  match op, lv with
  | BinOp.and, Value.bool false => some (Value.bool false)
  | BinOp.or, Value.bool true => some (Value.bool true)
  | _, _ => none

/-- Normal form of the official evaluator's binop arm, phrased through
`scArm` so proofs can split on short-circuiting once instead of on the
`op × value` grid. -/
theorem evalValue_mkBinop (s : State) (op : BinOp) (l r : WrappedExpr) :
    evalValue s (.mkBinop op l r) =
      (do
        let (s₁, lv) ← evalValue s l
        match scArm op lv with
        | some v => .ok (s₁, v)
        | none => do
            let (s₂, rv) ← evalValue s₁ r
            let v ← applyBinOp op lv rv
            let v' ← checkArith (op.retTy l.ty) v
            .ok (s₂, v')) := by
  cases h : evalValue s l with
  | error e => simp [evalValue, h, bind, Except.bind]
  | ok p =>
      obtain ⟨s₁, lv⟩ := p
      cases op <;> cases lv <;>
        (first
          | (simp [evalValue, h, scArm, bind, Except.bind]; done)
          | (rename_i b; cases b <;>
              simp [evalValue, h, scArm, bind, Except.bind]))

/-- Bounded expression evaluation: mirrors `Semantics.evalValue` on the
compiled fragment (literals, stack locals, primitive global storage
roots, binary/unary operators, ternaries), is `.stuck` elsewhere, and
uses `applyBinOpW` so out-of-range arithmetic is out of scope. The
fragment's expressions are pure, so no state is threaded back. -/
def evalW (s : State) : WrappedExpr → Res Value
  | .bool b => .ok (Value.bool b)
  | .intLit _ v => .ok (Value.int v)
  | .var .stack _ fld =>
      match lookupBy fld.name s.env with
      | some (Binding.val v) => .ok v
      | _ => .error .stuck
  | .var .storage _ fld =>
      match lookupBy fld.name s.env with
      | none =>
          if fld.origin = some StorageOrigin.global then
            match lookupBy fld.name s.storage with
            | some sv => sv.asValue
            | none => .error .stuck
          else .error .stuck
      | some _ => .error .stuck
  | .index .storage _ (.var .storage tyM fld) key =>
      -- `m[k]` on a global mapping root: the interpreter resolves the
      -- base (alias-free, global), evaluates the key, and reads the
      -- entry (absent keys read the mapping's default). Keys outside
      -- `[0, keyBound)` are out of the fragment. `a[k]` on a global
      -- array root reads the element, reverting out of bounds like the
      -- interpreter's `SVal.find`. Which formula applies is decided by
      -- the *type* annotation (the same `isArrayTy` the compiler
      -- dispatches on); a type/storage-shape mismatch is stuck.
      (match lookupBy fld.name s.env with
      | none =>
          if fld.origin = some StorageOrigin.global then do
            let kv ← evalW s key
            match kv with
            | Value.int k =>
                if isArrayTy tyM then
                  if 0 ≤ k then
                    match lookupBy fld.name s.storage with
                    | some (SVal.array elems) =>
                        if k.toNat < elems.length then
                          (elems.getD k.toNat (SVal.int 0)).asValue
                        else .error .revert
                    | _ => .error .stuck
                  else .error .stuck
                else
                  if 0 ≤ k ∧ k < keyBoundI then
                    match lookupBy fld.name s.storage with
                    | some (SVal.map entries dflt) =>
                        ((lookupBy k entries).getD dflt).asValue
                    | _ => .error .stuck
                  else .error .stuck
            | _ => .error .stuck
          else .error .stuck
      | some _ => .error .stuck)
  | .mkBinop op l r => do
      let lv ← evalW s l
      match scArm op lv with
      | some v => .ok v
      | none =>
          -- The machine short-circuits `&&`/`||` on the raw word, so
          -- a non-boolean left operand is out of the fragment (the
          -- official semantics evaluates the right operand first and
          -- only then sticks on the operator).
          if op.shortCircuits && !isBoolV lv then .error .stuck
          else do
            let rv ← evalW s r
            -- The operator step at the left operand's type: checked
            -- `uint` `+ - *` revert on overflow like the official
            -- semantics; everything else is word-bounded, with the
            -- official check at the result type as a fragment boundary.
            applyCheckedW op l.ty lv rv
  | .mkUnop op arg => do
      let v ← evalW s arg
      let v' ← applyUnOp op v
      match op, arg.ty with
      | UnOp.neg, Ty.int => checkArithW Ty.int v'
      | _, _ => .ok v'
  | .mkTernary c t e => do
      let cv ← evalW s c
      match cv with
      | Value.bool true => evalW s t
      | Value.bool false => evalW s e
      | _ => .error .stuck
  | .field .storage _ (.var .storage tyA fld) lfld =>
      -- `a.length` on a global array root: the interpreter's `find`
      -- answers `length` on arrays directly. `r.f` on a global struct
      -- root: read the field (the spine check ties the stored struct's
      -- field positions to the static declaration the compiler indexed
      -- by).
      (match lookupBy fld.name s.env with
      | none =>
          if fld.origin = some StorageOrigin.global ∧
              lfld.name = "length" ∧ isArrayTy tyA then
            match lookupBy fld.name s.storage with
            | some (SVal.array elems) => .ok (Value.int elems.length)
            | _ => .error .stuck
          else if fld.origin = some StorageOrigin.global ∧
              isStructTy tyA then
            match lookupBy fld.name s.storage with
            | some (SVal.struct sfields) =>
                if sfields.map Prod.fst = structSpineOf tyA then
                  match lookupBy lfld.name sfields with
                  | some v => v.asValue
                  | none => .error .stuck
                else .error .stuck
            | _ => .error .stuck
          else .error .stuck
      | some _ => .error .stuck)
  | _ => .error .stuck

/-- Bounded primitive write: stack locals and primitive global storage
roots, mirroring `Semantics.writeValue` on those two place shapes. -/
def writeW (s : State) (lhs : WrappedExpr) (v : Value) : Res State :=
  match lhs with
  | .var .stack _ fld => .ok (s.setEnv fld.name (Binding.val v))
  | .var .storage _ fld =>
      if fld.origin = some StorageOrigin.global then
        match lookupBy fld.name s.storage with
        | some _ =>
            .ok { s with storage := setBy fld.name v.toSVal s.storage }
        | none => .error .stuck
      else .error .stuck
  | .index .storage _ (.var .storage tyM fld) key =>
      -- `m[k] = v` on a global mapping root (the write path *does*
      -- consult the environment, via `resolveS` on the base);
      -- `a[k] = v` on a global array root reverts out of bounds like
      -- the interpreter's `SVal.save`.
      (match lookupBy fld.name s.env with
      | none =>
          if fld.origin = some StorageOrigin.global then do
            let kv ← evalW s key
            match kv with
            | Value.int k =>
                if isArrayTy tyM then
                  if 0 ≤ k then
                    match lookupBy fld.name s.storage with
                    | some (SVal.array elems) =>
                        if k.toNat < elems.length then
                          .ok { s with storage := (setBy fld.name (SVal.array (elems.set k.toNat v.toSVal)) s.storage) }
                        else .error .revert
                    | _ => .error .stuck
                  else .error .stuck
                else
                  if 0 ≤ k ∧ k < keyBoundI then
                    match lookupBy fld.name s.storage with
                    | some (SVal.map entries dflt) =>
                        .ok { s with storage := (setBy fld.name (SVal.map (setBy k v.toSVal entries) dflt) s.storage) }
                    | _ => .error .stuck
                  else .error .stuck
            | _ => .error .stuck
          else .error .stuck
      | some _ => .error .stuck)
  | .field .storage _ (.var .storage tyA fld) lfld =>
      -- `r.f = v` on a global struct root.
      (match lookupBy fld.name s.env with
      | none =>
          if fld.origin = some StorageOrigin.global ∧
              isStructTy tyA then
            match lookupBy fld.name s.storage with
            | some (SVal.struct sfields) =>
                if sfields.map Prod.fst = structSpineOf tyA then
                  match lookupBy lfld.name sfields with
                  | some _ =>
                      .ok { s with storage := (setBy fld.name (SVal.struct (setBy lfld.name v.toSVal sfields)) s.storage) }
                  | none => .error .stuck
                else .error .stuck
            | _ => .error .stuck
          else .error .stuck
      | some _ => .error .stuck)
  | _ => .error .stuck

/-- Bounded assignment: stack locals and primitive global storage
roots, mirroring the corresponding branches of `Semantics.execAssign`
(resolve, primitivity check, evaluate, write). -/
def assignW (s : State) (lhs rhs : WrappedExpr) : Res State :=
  match lhs with
  | .var .stack _ fld => do
      let v ← evalW s rhs
      .ok (s.setEnv fld.name (Binding.val v))
  | .var .storage _ fld =>
      if fld.origin = some StorageOrigin.global ∧ rhs.ty.isPrimitive then do
        let v ← evalW s rhs
        match lookupBy fld.name s.storage with
        | some _ =>
            .ok { s with storage := setBy fld.name v.toSVal s.storage }
        | none => .error .stuck
      else .error .stuck
  | .index .storage _ (.var .storage tyM fld) key =>
      -- `m[k] = e`: the compiled code evaluates the key first, the
      -- official interpreter (like solc) the right-hand side first.
      -- The fragment claims only executions whose key evaluates (and
      -- whose target shape checks pass) — there the orders agree, and
      -- only the array bounds revert is observed after the right-hand
      -- side, as in both the machine code and the interpreter's save.
      (match lookupBy fld.name s.env with
      | none =>
          if fld.origin = some StorageOrigin.global then
            if rhs.ty.isPrimitive then
              match evalW s key with
              | .error _ => .error .stuck
              | .ok kv =>
                  match kv with
                  | Value.int k =>
                      if isArrayTy tyM then
                        if 0 ≤ k then
                          match lookupBy fld.name s.storage with
                          | some (SVal.array elems) => do
                              let v ← evalW s rhs
                              if k.toNat < elems.length then
                                .ok { s with storage := (setBy fld.name (SVal.array (elems.set k.toNat v.toSVal)) s.storage) }
                              else .error .revert
                          | _ => .error .stuck
                        else .error .stuck
                      else
                        if 0 ≤ k ∧ k < keyBoundI then
                          match lookupBy fld.name s.storage with
                          | some (SVal.map entries dflt) => do
                              let v ← evalW s rhs
                              .ok { s with storage := (setBy fld.name (SVal.map (setBy k v.toSVal entries) dflt) s.storage) }
                          | _ => .error .stuck
                        else .error .stuck
                  | _ => .error .stuck
            else .error .stuck
          else .error .stuck
      | some _ => .error .stuck)
  | .field .storage _ (.var .storage tyA fld) lfld =>
      -- `r.f = e` on a global struct root: the target resolves without
      -- reverting, then the right-hand side is evaluated.
      (match lookupBy fld.name s.env with
      | none =>
          if fld.origin = some StorageOrigin.global ∧
              isStructTy tyA then
            if rhs.ty.isPrimitive then do
              let v ← evalW s rhs
              match lookupBy fld.name s.storage with
              | some (SVal.struct sfields) =>
                  if sfields.map Prod.fst = structSpineOf tyA then
                    match lookupBy lfld.name sfields with
                    | some _ =>
                        .ok { s with storage := (setBy fld.name (SVal.struct (setBy lfld.name v.toSVal sfields)) s.storage) }
                    | none => .error .stuck
                  else .error .stuck
              | _ => .error .stuck
            else .error .stuck
          else .error .stuck
      | some _ => .error .stuck)
  | _ => .error .stuck

mutual

/-- Bounded statement execution, mirroring `Semantics.execStmt` on the
compiled fragment. -/
def execW (s : State) : Stmt → Res State
  | .expr e => do
      let _ ← evalW s e
      .ok s
  | .assign lhs rhs => assignW s lhs.expr rhs
  | .compoundAssign op lhs rhs =>
      if op.hasCompoundAssign then
        -- The machine reads the target first (`a op= e` compiles as
        -- `a = a op e`), the official interpreter evaluates the
        -- right-hand side first. The fragment claims only executions
        -- whose target read succeeds — there the two orders are
        -- observationally equal, the fragment's expressions being
        -- pure.
        match evalW s lhs.expr with
        | .error _ => .error .stuck
        | .ok old => do
            let v ← evalW s rhs
            -- The operator step at the target's type (solc's checked
            -- `op=`): the same `applyCheckedW` the operator expression
            -- `a op e` uses, so `a op= e` and `a = a op e` agree.
            let new' ← applyCheckedW op lhs.expr.ty old v
            writeW s lhs.expr new'
      else .error .stuck
  | .stackDecl ty name init =>
      if ty.isPrimitive then
        match init with
        | none =>
            match ty with
            | Ty.bool => .ok (s.setEnv name (Binding.val (Value.bool false)))
            | _ => .ok (s.setEnv name (Binding.val (Value.int 0)))
        | some rhs => do
            let v ← evalW s rhs
            .ok (s.setEnv name (Binding.val v))
      else .error .stuck
  | .ite cond thn els => do
      let c ← evalW s cond
      match c with
      | Value.bool true => execWBlock s thn
      | Value.bool false => execWBlock s els
      | _ => .error .stuck
  | .assertStmt cond => do
      let c ← evalW s cond
      match c with
      | Value.bool true => .ok s
      | Value.bool false => .error .revert
      | _ => .error .stuck
  | .requireStmt cond => do
      let c ← evalW s cond
      match c with
      | Value.bool true => .ok s
      | Value.bool false => .error .revert
      | _ => .error .stuck
  | .revert _ => .error .revert
  | .transfer recipient amount => do
      -- `to.transfer(amt)`: **revert** when the contract balance does
      -- not cover the amount (the compiled code checks the balance
      -- word, agreeing with the official semantics), else debit the
      -- balance and the net ledger. A negative amount is stuck (the
      -- official semantics is stuck too), and a ledger entry that would
      -- leave `[0, 2^256)` is out of the fragment: the official ledger
      -- is an unbounded `Int` and does not revert there, which a word
      -- machine cannot represent.
      let av ← evalW s recipient
      match av with
      | Value.int a =>
          if 0 ≤ a ∧ a < keyBoundI then do
            let mv ← evalW s amount
            match mv with
            | Value.int amt =>
                if amt < 0 then .error .stuck
                else if s.selfBalance < amt then .error .revert
                else if 0 ≤ s.getNet a - amt then
                  .ok { s.setNet a (s.getNet a - amt) with
                    selfBalance := s.selfBalance - amt }
                else .error .stuck
            | _ => .error .stuck
          else .error .stuck
      | _ => .error .stuck
  | .push target value =>
      -- `a.push(e)` / `a.push()` on a global array root: append the
      -- element (the default for a valueless push). Arrays longer than
      -- `keyBound` are out of the fragment (their element slots would
      -- leave the injective region).
      (match target.expr with
      | .var .storage tyA fld =>
          (match lookupBy fld.name s.env with
          | none =>
              (match tyA with
              | Ty.ref (RefTy.array elemTy) =>
                  if fld.origin = some StorageOrigin.global ∧
                      elemTy.isPrimitive then
                    match lookupBy fld.name s.storage with
                    | some (SVal.array elems) => do
                        let sv ← (match value with
                          | none => .ok (defaultForTy elemTy)
                          | some rhs =>
                              if rhs.ty.isPrimitive then do
                                let v ← evalW s rhs
                                .ok v.toSVal
                              else .error .stuck)
                        if elems.length + 1 ≤ keyBound then
                          .ok { s with storage := (setBy fld.name (SVal.array (elems ++ [sv])) s.storage) }
                        else .error .stuck
                    | _ => .error .stuck
                  else .error .stuck
              | _ => .error .stuck)
          | some _ => .error .stuck)
      | _ => .error .stuck)
  | .pop target =>
      -- `a.pop()` on a global array root: drop the last element,
      -- reverting on an empty array like the interpreter.
      (match target.expr with
      | .var .storage tyA fld =>
          (match lookupBy fld.name s.env with
          | none =>
              (match tyA with
              | Ty.ref (RefTy.array _) =>
                  if fld.origin = some StorageOrigin.global then
                    match lookupBy fld.name s.storage with
                    | some (SVal.array elems) =>
                        (match elems.reverse with
                        | [] => .error .revert
                        | _ :: restRev =>
                            .ok { s with storage := (setBy fld.name (SVal.array restRev.reverse) s.storage) })
                    | _ => .error .stuck
                  else .error .stuck
              | _ => .error .stuck)
          | some _ => .error .stuck)
      | _ => .error .stuck)
  | _ => .error .stuck

def execWBlock (s : State) : List Stmt → Res State
  | [] => .ok s
  | stmt :: rest => do
      let s' ← execW s stmt
      execWBlock s' rest

end

/-! ## Agreement with the official interpreter -/

/-- The two claims the bounded semantics makes about an official-
interpreter computation: `.ok` and `.revert` transfer; `.stuck` claims
nothing. -/
def Agrees {α β : Type} (proj : α → β) : Res α → Res β → Prop
  | .ok a, official => official = .ok (proj a)
  | .error .revert, official => official = .error .revert
  | .error .stuck, _ => True

@[simp] theorem Agrees_ok {α β : Type} {proj : α → β} {a : α}
    {official : Res β} :
    Agrees proj (.ok a) official ↔ official = .ok (proj a) := Iff.rfl

@[simp] theorem Agrees_revert {α β : Type} {proj : α → β}
    {official : Res β} :
    Agrees proj (.error .revert) official ↔
      official = .error .revert := Iff.rfl

@[simp] theorem Agrees_stuck {α β : Type} {proj : α → β}
    {official : Res β} : Agrees proj (.error .stuck) official :=
  trivial

/-- Any result agrees with itself under the identity projection. -/
theorem Agrees_rfl {α : Type} {x : Res α} : Agrees id x x := by
  cases x with
  | ok a => exact rfl
  | error e =>
      cases e
      · exact rfl
      · exact trivial

theorem evalW_agree (e : WrappedExpr) (s : State) :
    Agrees (fun v => (s, v)) (evalW s e) (evalValue s e) := by
  match e with
  | .bool b => simp [evalW, evalValue, Agrees]
  | .intLit ty v => simp [evalW, evalValue, Agrees]
  | .var kind ty fld =>
      cases kind with
      | stack =>
          cases h : lookupBy fld.name s.env with
          | none => simp [evalW, h]
          | some b =>
              cases b with
              | val v =>
                  simp [evalW, evalValue, State.getEnv, h, bind, Except.bind,
                    Agrees]
              | spath root segs => simp [evalW, h]
              | mref id => simp [evalW, h]
      | storage =>
          cases h : lookupBy fld.name s.env with
          | some b => simp [evalW, h]
          | none =>
              by_cases horig : fld.origin = some StorageOrigin.global
              · cases hs : lookupBy fld.name s.storage with
                | none => simp [evalW, h, horig, hs]
                | some sv =>
                    cases hav : sv.asValue with
                    | error err =>
                        cases err
                        · cases sv with
                          | prim p => cases p <;> simp [SVal.asValue] at hav
                          | _ => simp [SVal.asValue] at hav
                        · simp [evalW, h, horig, hs, hav]
                    | ok val =>
                        simp [evalW, h, horig, hs, hav, evalValue, resolveS,
                          State.findStorage, SVal.find, bind, Except.bind,
                          Agrees]
              · simp [evalW, h, horig, Agrees]
      | memory => simp [evalW]
  | .mkBinop op l r =>
      have ihl := evalW_agree l s
      have ihr := evalW_agree r s
      rw [evalValue_mkBinop]
      simp only [evalW]
      cases hl : evalW s l with
      | error e =>
          cases e
          · rw [hl] at ihl
            simp only [Agrees_revert] at ihl
            simp [hl, ihl, bind, Except.bind, Agrees]
          · simp [hl, bind, Except.bind, Agrees]
      | ok lv =>
          rw [hl] at ihl
          simp only [Agrees_ok] at ihl
          simp only [hl, ihl, bind, Except.bind]
          cases hsc : scArm op lv with
          | some v => simp [Agrees]
          | none =>
              by_cases hg : (op.shortCircuits && !isBoolV lv) = true
              case pos => simp [hg, Agrees]
              simp only [hg, Bool.false_eq_true, if_false]
              cases hr : evalW s r with
              | error e =>
                  cases e
                  · rw [hr] at ihr
                    simp only [Agrees_revert] at ihr
                    simp [hr, ihr, bind, Except.bind, Agrees]
                  · simp [hr, bind, Except.bind, Agrees]
              | ok rv =>
                  rw [hr] at ihr
                  simp only [Agrees_ok] at ihr
                  simp only [hr, ihr, bind, Except.bind]
                  cases hab : applyCheckedW op l.ty lv rv with
                  | error e =>
                      cases e
                      · rcases applyCheckedW_revert hab with h | ⟨u, hu, hc⟩
                        · simp [h, bind, Except.bind, Agrees]
                        · simp [hu, hc, bind, Except.bind, Agrees]
                      · simp [bind, Except.bind, Agrees]
                  | ok v =>
                      obtain ⟨hu, hc⟩ := applyCheckedW_ok hab
                      simp [hu, hc, bind, Except.bind, Agrees]
  | .mkUnop op arg =>
      have iha := evalW_agree arg s
      simp only [evalW]
      cases ha : evalW s arg with
      | error e =>
          cases e
          · rw [ha] at iha
            simp only [Agrees_revert] at iha
            simp [evalValue, ha, iha, bind, Except.bind, Agrees]
          · simp [ha, bind, Except.bind, Agrees]
      | ok v =>
          rw [ha] at iha
          simp only [Agrees_ok] at iha
          simp only [ha, bind, Except.bind]
          cases hu : applyUnOp op v with
          | error e =>
              cases e
              · simp [evalValue, iha, hu, bind, Except.bind, Agrees]
              · simp [hu, bind, Except.bind, Agrees]
          | ok v' =>
              cases op with
              | not =>
                  simp [evalValue, iha, hu, bind, Except.bind, Agrees]
              | neg =>
                  cases harg : arg.ty with
                  | prim p =>
                      cases p with
                      | int =>
                          cases hc : checkArith Ty.int v' with
                          | error e =>
                              simp [evalValue, iha, hu, harg, hc, checkArithW,
                                bind, Except.bind, Agrees]
                          | ok w =>
                              simp [evalValue, iha, hu, harg, hc, checkArithW,
                                bind, Except.bind, Agrees]
                      | uint =>
                          simp [evalValue, iha, hu, harg, bind, Except.bind,
                            Agrees]
                      | bool =>
                          simp [evalValue, iha, hu, harg, bind, Except.bind,
                            Agrees]
                  | ref r =>
                      simp [evalValue, iha, hu, harg, bind, Except.bind,
                        Agrees]
  | .mkTernary c t e =>
      have ihc := evalW_agree c s
      have iht := evalW_agree t s
      have ihe := evalW_agree e s
      simp only [evalW]
      cases hc : evalW s c with
      | error err =>
          cases err
          · rw [hc] at ihc
            simp only [Agrees_revert] at ihc
            simp [evalValue, hc, ihc, bind, Except.bind, Agrees]
          · simp [hc, bind, Except.bind, Agrees]
      | ok cv =>
          rw [hc] at ihc
          simp only [Agrees_ok] at ihc
          simp only [hc, bind, Except.bind]
          cases cv with
          | int n => simp [Agrees]
          | bool b =>
              cases b with
              | true =>
                  cases ht : evalW s t with
                  | error err =>
                      cases err
                      · rw [ht] at iht
                        simp only [Agrees_revert] at iht
                        simp [evalValue, ihc, ht, iht, bind, Except.bind,
                          Agrees]
                      · simp [ht, Agrees]
                  | ok tv =>
                      rw [ht] at iht
                      simp only [Agrees_ok] at iht
                      simp [evalValue, ihc, ht, iht, bind, Except.bind, Agrees]
              | false =>
                  cases he : evalW s e with
                  | error err =>
                      cases err
                      · rw [he] at ihe
                        simp only [Agrees_revert] at ihe
                        simp [evalValue, ihc, he, ihe, bind, Except.bind,
                          Agrees]
                      · simp [he, Agrees]
                  | ok ev =>
                      rw [he] at ihe
                      simp only [Agrees_ok] at ihe
                      simp [evalValue, ihc, he, ihe, bind, Except.bind, Agrees]
  | .field kind fty fbase lfld =>
      cases kind with
      | memory => simp [evalW]
      | stack => simp [evalW]
      | storage =>
        match fbase with
        | .field .. => simp [evalW]
        | .index .. => simp [evalW]
        | .pushPlace .. => simp [evalW]
        | .bool .. => simp [evalW]
        | .intLit .. => simp [evalW]
        | .mkCall .. => simp [evalW]
        | .mkBinop .. => simp [evalW]
        | .mkUnop .. => simp [evalW]
        | .mkIncDec .. => simp [evalW]
        | .mkTernary .. => simp [evalW]
        | .var bkind bty fld =>
          cases bkind with
          | stack => simp [evalW]
          | memory => simp [evalW]
          | storage =>
            cases h : lookupBy fld.name s.env with
            | some b => simp [evalW, h]
            | none =>
              by_cases hcond : fld.origin = some StorageOrigin.global ∧
                  lfld.name = "length" ∧ isArrayTy bty = true
              case neg =>
                by_cases hcondS : fld.origin = some StorageOrigin.global
                    ∧ isStructTy bty = true
                case neg =>
                    simp [evalW, h, if_neg hcond, if_neg hcondS]
                case pos =>
                cases hs : lookupBy fld.name s.storage with
                | none =>
                    simp [evalW, h, isArrayTy_eq_false_of_isStructTy hcondS.2, hcondS.1, hcondS.2,
                      hs]
                | some sv =>
                  cases sv with
                  | prim p =>
                      cases p <;>
                        simp [evalW, h, isArrayTy_eq_false_of_isStructTy hcondS.2, hcondS.1, hcondS.2,
                          hs]
                  | array elems =>
                      simp [evalW, h, isArrayTy_eq_false_of_isStructTy hcondS.2, hcondS.1, hcondS.2,
                        hs]
                  | map entries dflt =>
                      simp [evalW, h, isArrayTy_eq_false_of_isStructTy hcondS.2, hcondS.1, hcondS.2,
                        hs]
                  | struct sfields =>
                    by_cases hspine : sfields.map Prod.fst
                        = structSpineOf bty
                    case neg =>
                        simp [evalW, h, isArrayTy_eq_false_of_isStructTy hcondS.2, hcondS.1,
                          hcondS.2, hs, hspine]
                    case pos =>
                    cases hlf : lookupBy lfld.name sfields with
                    | none =>
                        simp [evalW, h, isArrayTy_eq_false_of_isStructTy hcondS.2, hcondS.1,
                          hcondS.2, hs, hspine, hlf]
                    | some v =>
                      cases hav : v.asValue with
                      | error err =>
                          cases err
                          · cases v with
                            | prim p => cases p <;> simp [SVal.asValue] at hav
                            | _ => simp [SVal.asValue] at hav
                          · simp [evalW, h, isArrayTy_eq_false_of_isStructTy hcondS.2, hcondS.1,
                              hcondS.2, hs, hspine, hlf, hav]
                      | ok val =>
                          cases v with
                          | prim p =>
                              cases p <;>
                                (simp only [SVal.asValue,
                                   Except.ok.injEq] at hav;
                                 subst hav;
                                 simp_all [evalW, h,
                                   isArrayTy_eq_false_of_isStructTy hcondS.2,
                                   hcondS.1, hcondS.2, hs, hspine, hlf,
                                   evalValue, resolveS, State.findStorage,
                                   SVal.find, SVal.asValue, bind,
                                   Except.bind, pure, Except.pure, Agrees])
                          | _ =>
                              simp_all [evalW, h,
                                isArrayTy_eq_false_of_isStructTy hcondS.2,
                                hcondS.1, hcondS.2, hs, hspine, hlf,
                                evalValue, resolveS, State.findStorage,
                                SVal.find, SVal.asValue, bind,
                                Except.bind, pure, Except.pure, Agrees]
              case pos =>
              cases hs : lookupBy fld.name s.storage with
              | none =>
                  simp [evalW, h, hcond.1, hcond.2.1, hcond.2.2, hs]
              | some sv =>
                cases sv with
                | prim p =>
                    cases p <;>
                      simp [evalW, h, hcond.1, hcond.2.1, hcond.2.2, hs]
                | struct fields =>
                    simp [evalW, h, hcond.1, hcond.2.1, hcond.2.2, hs]
                | map entries dflt =>
                    simp [evalW, h, hcond.1, hcond.2.1, hcond.2.2, hs]
                | array elems =>
                    simp [evalW, h, hcond.1, hcond.2.1, hcond.2.2, hs,
                      evalValue, resolveS, State.findStorage, SVal.find,
                      SVal.asValue, bind, Except.bind, pure, Except.pure,
                      Agrees]
  | .index kind ty base key =>
      cases kind with
      | memory => simp [evalW]
      | stack => simp [evalW]
      | storage =>
          match base with
          | .field .. => simp [evalW]
          | .index .. => simp [evalW]
          | .pushPlace .. => simp [evalW]
          | .bool .. => simp [evalW]
          | .intLit .. => simp [evalW]
          | .mkCall .. => simp [evalW]
          | .mkBinop .. => simp [evalW]
          | .mkUnop .. => simp [evalW]
          | .mkIncDec .. => simp [evalW]
          | .mkTernary .. => simp [evalW]
          | .var bkind bty fld =>
            cases bkind with
            | stack => simp [evalW]
            | memory => simp [evalW]
            | storage =>
              have ihk := evalW_agree key s
              cases h : lookupBy fld.name s.env with
              | some b => simp [evalW, h]
              | none =>
                by_cases horig : fld.origin = some StorageOrigin.global
                case neg => simp [evalW, h, horig]
                case pos =>
                cases hk : evalW s key with
                | error err =>
                    cases err
                    · rw [hk] at ihk
                      simp only [Agrees_revert] at ihk
                      simp [evalW, h, horig, hk, evalValue, resolveS,
                        evalInt, ihk, bind, Except.bind, Agrees]
                    · simp [evalW, h, horig, hk, bind, Except.bind, Agrees]
                | ok kv =>
                    rw [hk] at ihk
                    simp only [Agrees_ok] at ihk
                    cases kv with
                    | bool b =>
                        simp [evalW, h, horig, hk, bind, Except.bind,
                          Agrees]
                    | int k =>
                      by_cases htyA : isArrayTy bty = true
                      case pos =>
                        by_cases hk0 : 0 ≤ k
                        case neg =>
                            simp [evalW, h, horig, hk, htyA, hk0, bind,
                              Except.bind, Agrees]
                        case pos =>
                        cases hs : lookupBy fld.name s.storage with
                        | none =>
                            simp [evalW, h, horig, hk, htyA, hk0, hs,
                              bind, Except.bind, Agrees]
                        | some sv =>
                          cases sv with
                          | prim p =>
                              cases p <;>
                                simp [evalW, h, horig, hk, htyA, hk0, hs,
                                  bind, Except.bind, Agrees]
                          | struct fields =>
                              simp [evalW, h, horig, hk, htyA, hk0, hs,
                                bind, Except.bind, Agrees]
                          | map entries dflt =>
                              simp [evalW, h, horig, hk, htyA, hk0, hs,
                                bind, Except.bind, Agrees]
                          | array elems =>
                            by_cases hlt : k.toNat < elems.length
                            case neg =>
                                simp [evalW, h, horig, hk, htyA, hk0,
                                  hs, hlt, evalValue, resolveS, evalInt,
                                  State.findStorage, SVal.find,
                                  Value.asInt, ihk, bind, Except.bind,
                                  Agrees]
                            case pos =>
                              have hgetd : elems.getD k.toNat
                                  (SVal.int 0) = elems[k.toNat] := by
                                simp [List.getD_eq_getElem?_getD,
                                  List.getElem?_eq_getElem hlt]
                              cases hav : elems[k.toNat].asValue with
                              | error err =>
                                  cases err
                                  · cases hgd : elems[k.toNat] with
                                    | prim p =>
                                        cases p <;>
                                          (rw [hgd] at hav;
                                           simp [SVal.asValue] at hav)
                                    | _ =>
                                        (rw [hgd] at hav;
                                         simp [SVal.asValue] at hav)
                                  · simp [evalW, h, horig, hk, htyA,
                                      hk0, hs, hlt, hgetd, hav, bind,
                                      Except.bind, Agrees]
                              | ok val =>
                                  simp [evalW, h, horig, hk, htyA, hk0,
                                    hs, hlt, hgetd, hav, evalValue,
                                    resolveS, evalInt, State.findStorage,
                                    SVal.find, Value.asInt,
                                    List.get_eq_getElem, ihk, bind,
                                    Except.bind, Agrees]
                      case neg =>
                      by_cases hkb : 0 ≤ k ∧ k < keyBoundI
                      case neg =>
                          simp [evalW, h, horig, hk, htyA, hkb, bind,
                            Except.bind, Agrees]
                      case pos =>
                      cases hs : lookupBy fld.name s.storage with
                      | none =>
                          simp [evalW, h, horig, hk, htyA, hkb, hs, bind,
                            Except.bind, Agrees]
                      | some sv =>
                        cases sv with
                        | prim p =>
                            cases p <;>
                              simp [evalW, h, horig, hk, htyA, hkb, hs, bind,
                                Except.bind, Agrees]
                        | struct fields =>
                            simp [evalW, h, horig, hk, htyA, hkb, hs, bind,
                              Except.bind, Agrees]
                        | array elems =>
                            simp [evalW, h, horig, hk, htyA, hkb, hs, bind,
                              Except.bind, Agrees]
                        | map entries dflt =>
                          cases he : lookupBy k entries with
                          | some v0 =>
                              cases hav : v0.asValue with
                              | error err =>
                                  cases err
                                  · cases v0 with
                                    | prim p =>
                                        cases p <;>
                                          simp [SVal.asValue] at hav
                                    | _ => simp [SVal.asValue] at hav
                                  · simp [evalW, h, horig, hk, htyA, hkb,
                                      hs, he, hav, bind, Except.bind,
                                      Agrees]
                              | ok val =>
                                  simp [evalW, h, horig, hk, htyA, hkb,
                                    hs, he, hav, evalValue, resolveS,
                                    evalInt, State.findStorage, SVal.find,
                                    Value.asInt, ihk, bind, Except.bind,
                                    Agrees]
                          | none =>
                              cases hav : dflt.asValue with
                              | error err =>
                                  cases err
                                  · cases dflt with
                                    | prim p =>
                                        cases p <;>
                                          simp [SVal.asValue] at hav
                                    | _ => simp [SVal.asValue] at hav
                                  · simp [evalW, h, horig, hk, htyA, hkb,
                                      hs, he, hav, bind, Except.bind,
                                      Agrees]
                              | ok val =>
                                  simp [evalW, h, horig, hk, htyA, hkb,
                                    hs, he, hav, evalValue, resolveS,
                                    evalInt, State.findStorage, SVal.find,
                                    Value.asInt, ihk, bind, Except.bind,
                                    Agrees]
  | .pushPlace .. => simp [evalW]
  | .mkCall .. => simp [evalW]
  | .mkIncDec .. => simp [evalW]
termination_by e.size
decreasing_by all_goals
  first
  | omega
  | (simp [Typed.WrappedExpr.size] <;> omega)

/-- An arithmetic operator never short-circuits. -/
theorem scArm_arith {op : BinOp} (h : op.isArith = true) (lv : Value) :
    scArm op lv = none := by
  cases op <;> cases lv <;>
    (first
      | rfl
      | (rename_i b; cases b <;> rfl)
      | simp [BinOp.isArith] at h)

theorem writeW_agree (s : State) (lhs : WrappedExpr) (v : Value) :
    Agrees id (writeW s lhs v) (writeValue s lhs v) := by
  match lhs with
  | .var kind ty fld =>
      cases kind with
      | stack =>
          simp [writeW, writeValue, Semantics.writeLoc, resolveLoc, bind, Except.bind, Agrees]
      | storage =>
          by_cases horig : fld.origin = some StorageOrigin.global
          · cases hs : lookupBy fld.name s.storage with
            | some cur =>
                simp [writeW, writeValue, Semantics.writeLoc, resolveLoc, horig, hs,
                  State.saveStorage, SVal.save, bind, Except.bind, Agrees]
            | none =>
                simp [writeW, horig, hs, Agrees]
          · simp [writeW, horig, Agrees]
      | memory => simp [writeW, Agrees]
  | .field kind fty fbase lfld =>
      cases kind with
      | memory => simp [writeW, Agrees]
      | stack => simp [writeW, Agrees]
      | storage =>
        match fbase with
        | .field .. => simp [writeW, Agrees]
        | .index .. => simp [writeW, Agrees]
        | .pushPlace .. => simp [writeW, Agrees]
        | .bool .. => simp [writeW, Agrees]
        | .intLit .. => simp [writeW, Agrees]
        | .mkCall .. => simp [writeW, Agrees]
        | .mkBinop .. => simp [writeW, Agrees]
        | .mkUnop .. => simp [writeW, Agrees]
        | .mkIncDec .. => simp [writeW, Agrees]
        | .mkTernary .. => simp [writeW, Agrees]
        | .var bkind bty fld =>
          cases bkind with
          | stack => simp [writeW, Agrees]
          | memory => simp [writeW, Agrees]
          | storage =>
            cases h : lookupBy fld.name s.env with
            | some b => simp [writeW, h, Agrees]
            | none =>
              by_cases hcondS : fld.origin = some StorageOrigin.global
                  ∧ isStructTy bty = true
              case neg => simp [writeW, h, if_neg hcondS, Agrees]
              case pos =>
              cases hs : lookupBy fld.name s.storage with
              | none =>
                  simp [writeW, h, hcondS.1, hcondS.2, hs, Agrees]
              | some sv =>
                cases sv with
                | prim p =>
                    cases p <;>
                      simp [writeW, h, hcondS.1, hcondS.2, hs, Agrees]
                | array elems =>
                    simp [writeW, h, hcondS.1, hcondS.2, hs, Agrees]
                | map entries dflt =>
                    simp [writeW, h, hcondS.1, hcondS.2, hs, Agrees]
                | struct sfields =>
                  by_cases hspine : sfields.map Prod.fst
                      = structSpineOf bty
                  case neg =>
                      simp [writeW, h, hcondS.1, hcondS.2, hs, hspine,
                        Agrees]
                  case pos =>
                  cases hlf : lookupBy lfld.name sfields with
                  | none =>
                      simp [writeW, h, hcondS.1, hcondS.2, hs, hspine,
                        hlf, Agrees]
                  | some old =>
                      simp [writeW, h, hcondS.1, hcondS.2, hs, hspine,
                        hlf, writeValue, Semantics.writeLoc, resolveLoc, resolveS,
                        State.saveStorage, SVal.save, bind, Except.bind,
                        pure, Except.pure, Agrees]
  | .index kind ty base key =>
      cases kind with
      | memory => simp [writeW, Agrees]
      | stack => simp [writeW, Agrees]
      | storage =>
          match base with
          | .field .. => simp [writeW, Agrees]
          | .index .. => simp [writeW, Agrees]
          | .pushPlace .. => simp [writeW, Agrees]
          | .bool .. => simp [writeW, Agrees]
          | .intLit .. => simp [writeW, Agrees]
          | .mkCall .. => simp [writeW, Agrees]
          | .mkBinop .. => simp [writeW, Agrees]
          | .mkUnop .. => simp [writeW, Agrees]
          | .mkIncDec .. => simp [writeW, Agrees]
          | .mkTernary .. => simp [writeW, Agrees]
          | .var bkind bty fld =>
            cases bkind with
            | stack => simp [writeW, Agrees]
            | memory => simp [writeW, Agrees]
            | storage =>
              have ihk := evalW_agree key s
              cases h : lookupBy fld.name s.env with
              | some b => simp [writeW, h, Agrees]
              | none =>
                by_cases horig : fld.origin = some StorageOrigin.global
                case neg => simp [writeW, h, horig, Agrees]
                case pos =>
                cases hk : evalW s key with
                | error err =>
                    cases err
                    · rw [hk] at ihk
                      simp only [Agrees_revert] at ihk
                      simp [writeW, h, horig, hk, writeValue, Semantics.writeLoc, resolveLoc,
                        resolveS, evalInt, ihk, bind, Except.bind, Agrees]
                    · simp [writeW, h, horig, hk, bind, Except.bind,
                        Agrees]
                | ok kv =>
                    rw [hk] at ihk
                    simp only [Agrees_ok] at ihk
                    cases kv with
                    | bool b =>
                        simp [writeW, h, horig, hk, bind, Except.bind,
                          Agrees]
                    | int k =>
                      by_cases htyA : isArrayTy bty = true
                      case pos =>
                        by_cases hk0 : 0 ≤ k
                        case neg =>
                            simp [writeW, h, horig, hk, htyA, hk0, bind,
                              Except.bind, Agrees]
                        case pos =>
                        cases hs : lookupBy fld.name s.storage with
                        | none =>
                            simp [writeW, h, horig, hk, htyA, hk0, hs,
                              bind, Except.bind, Agrees]
                        | some sv =>
                          cases sv with
                          | prim p =>
                              cases p <;>
                                simp [writeW, h, horig, hk, htyA, hk0, hs,
                                  bind, Except.bind, Agrees]
                          | struct fields =>
                              simp [writeW, h, horig, hk, htyA, hk0, hs,
                                bind, Except.bind, Agrees]
                          | map entries dflt =>
                              simp [writeW, h, horig, hk, htyA, hk0, hs,
                                bind, Except.bind, Agrees]
                          | array elems =>
                              by_cases hlt : k.toNat < elems.length
                              case neg =>
                                  simp [writeW, h, horig, hk, htyA, hk0,
                                    hs, hlt, writeValue, Semantics.writeLoc, resolveLoc,
                                    resolveS, evalInt, State.saveStorage,
                                    SVal.save, Value.asInt, ihk, bind,
                                    Except.bind, Agrees]
                              case pos =>
                                  simp [writeW, h, horig, hk, htyA, hk0,
                                    hs, hlt, writeValue, Semantics.writeLoc, resolveLoc,
                                    resolveS, evalInt, State.saveStorage,
                                    SVal.save, Value.asInt,
                                    List.get_eq_getElem, ihk, bind,
                                    Except.bind, Agrees]
                      case neg =>
                      by_cases hkb : 0 ≤ k ∧ k < keyBoundI
                      case neg =>
                          simp [writeW, h, horig, hk, htyA, hkb, bind,
                            Except.bind, Agrees]
                      case pos =>
                      cases hs : lookupBy fld.name s.storage with
                      | none =>
                          simp [writeW, h, horig, hk, htyA, hkb, hs, bind,
                            Except.bind, Agrees]
                      | some sv =>
                        cases sv with
                        | prim p =>
                            cases p <;>
                              simp [writeW, h, horig, hk, htyA, hkb, hs,
                                bind, Except.bind, Agrees]
                        | struct fields =>
                            simp [writeW, h, horig, hk, htyA, hkb, hs,
                              bind, Except.bind, Agrees]
                        | array elems =>
                            simp [writeW, h, horig, hk, htyA, hkb, hs,
                              bind, Except.bind, Agrees]
                        | map entries dflt =>
                            cases he : lookupBy k entries with
                            | some v0 =>
                                simp [writeW, h, horig, hk, htyA, hkb, hs,
                                  he, writeValue, Semantics.writeLoc, resolveLoc, resolveS,
                                  evalInt, State.saveStorage, SVal.save,
                                  Value.asInt, ihk, bind, Except.bind,
                                  Agrees]
                            | none =>
                                simp [writeW, h, horig, hk, htyA, hkb, hs,
                                  he, writeValue, Semantics.writeLoc, resolveLoc, resolveS,
                                  evalInt, State.saveStorage, SVal.save,
                                  Value.asInt, ihk, bind, Except.bind,
                                  Agrees]
  | .pushPlace .. => simp [writeW, Agrees]
  | .bool .. => simp [writeW, Agrees]
  | .intLit .. => simp [writeW, Agrees]
  | .mkCall .. => simp [writeW, Agrees]
  | .mkBinop .. => simp [writeW, Agrees]
  | .mkUnop .. => simp [writeW, Agrees]
  | .mkIncDec .. => simp [writeW, Agrees]
  | .mkTernary .. => simp [writeW, Agrees]

theorem assignW_agree (s : State) (lhs : PlaceExpr) (rhs : WrappedExpr) :
    Agrees id (assignW s lhs.expr rhs) (execAssign s lhs rhs) := by
  obtain ⟨lexpr, hassignable⟩ := lhs
  match lexpr with
  | .var kind ty fld =>
      cases kind with
      | stack =>
          have ihr := evalW_agree rhs s
          cases hr : evalW s rhs with
          | error err =>
              cases err
              · rw [hr] at ihr
                simp only [Agrees_revert] at ihr
                simp [assignW, hr, execAssign, Semantics.execAssignNested, Typed.WrappedExpr.kind, Semantics.rhsToSVal, Semantics.rhsToMVal, resolveLoc, ihr, bind,
                  Except.bind, Agrees]
              · simp [assignW, hr, bind, Except.bind, Agrees]
          | ok v =>
              rw [hr] at ihr
              simp only [Agrees_ok] at ihr
              simp [assignW, hr, execAssign, Semantics.execAssignNested, Typed.WrappedExpr.kind, Semantics.rhsToSVal, Semantics.rhsToMVal, resolveLoc, ihr, bind,
                Except.bind, Agrees]
      | storage =>
          by_cases horig : fld.origin = some StorageOrigin.global
          · by_cases hprim : rhs.ty.isPrimitive = true
            · have ihr := evalW_agree rhs s
              cases hr : evalW s rhs with
              | error err =>
                  cases err
                  · rw [hr] at ihr
                    simp only [Agrees_revert] at ihr
                    simp [assignW, hr, horig, hprim, execAssign, Semantics.execAssignNested, Typed.WrappedExpr.kind, Semantics.rhsToSVal, Semantics.rhsToMVal, resolveLoc,
                      ihr, bind, Except.bind, Agrees]
                  · simp [assignW, hr, horig, hprim, bind, Except.bind,
                      Agrees]
              | ok v =>
                  rw [hr] at ihr
                  simp only [Agrees_ok] at ihr
                  cases hs : lookupBy fld.name s.storage with
                  | some cur =>
                      simp [assignW, hr, horig, hprim, hs, execAssign, Semantics.execAssignNested, Typed.WrappedExpr.kind, Semantics.rhsToSVal, Semantics.rhsToMVal,
                        resolveLoc, ihr, State.saveStorage, SVal.save, bind,
                        Except.bind, Agrees]
                  | none =>
                      simp [assignW, hr, horig, hprim, hs, bind, Except.bind,
                        Agrees]
            · simp [assignW, horig, hprim, Agrees]
          · simp [assignW, horig, Agrees]
      | memory => simp [assignW, Agrees]
  | .field kind fty fbase lfld =>
      cases kind with
      | memory => simp [assignW, Agrees]
      | stack => simp [assignW, Agrees]
      | storage =>
        match fbase with
        | .field .. => simp [assignW, Agrees]
        | .index .. => simp [assignW, Agrees]
        | .pushPlace .. => simp [assignW, Agrees]
        | .bool .. => simp [assignW, Agrees]
        | .intLit .. => simp [assignW, Agrees]
        | .mkCall .. => simp [assignW, Agrees]
        | .mkBinop .. => simp [assignW, Agrees]
        | .mkUnop .. => simp [assignW, Agrees]
        | .mkIncDec .. => simp [assignW, Agrees]
        | .mkTernary .. => simp [assignW, Agrees]
        | .var bkind bty fld =>
          cases bkind with
          | stack => simp [assignW, Agrees]
          | memory => simp [assignW, Agrees]
          | storage =>
            cases h : lookupBy fld.name s.env with
            | some b => simp [assignW, h, Agrees]
            | none =>
              by_cases hcondS : fld.origin = some StorageOrigin.global
                  ∧ isStructTy bty = true
              case neg => simp [assignW, h, if_neg hcondS, Agrees]
              case pos =>
              by_cases hprim : rhs.ty.isPrimitive = true
              case neg =>
                  simp [assignW, h, hcondS.1, hcondS.2, hprim, Agrees]
              case pos =>
              have ihr := evalW_agree rhs s
              cases hr : evalW s rhs with
              | error err =>
                  cases err
                  · rw [hr] at ihr
                    simp only [Agrees_revert] at ihr
                    simp [assignW, h, hcondS.1, hcondS.2, hprim, hr,
                      execAssign, Semantics.execAssignNested, Typed.WrappedExpr.kind, Semantics.rhsToSVal, Semantics.rhsToMVal, resolveLoc, resolveS, ihr, bind,
                      Except.bind, Agrees]
                  · simp [assignW, h, hcondS.1, hcondS.2, hprim, hr,
                      bind, Except.bind, Agrees]
              | ok v =>
                  rw [hr] at ihr
                  simp only [Agrees_ok] at ihr
                  cases hs : lookupBy fld.name s.storage with
                  | none =>
                      simp [assignW, h, hcondS.1, hcondS.2, hprim, hr,
                        hs, bind, Except.bind, Agrees]
                  | some sv =>
                    cases sv with
                    | prim p =>
                        cases p <;>
                          simp [assignW, h, hcondS.1, hcondS.2, hprim,
                            hr, hs, bind, Except.bind, Agrees]
                    | array elems =>
                        simp [assignW, h, hcondS.1, hcondS.2, hprim,
                          hr, hs, bind, Except.bind, Agrees]
                    | map entries dflt =>
                        simp [assignW, h, hcondS.1, hcondS.2, hprim,
                          hr, hs, bind, Except.bind, Agrees]
                    | struct sfields =>
                      by_cases hspine : sfields.map Prod.fst
                          = structSpineOf bty
                      case neg =>
                          simp [assignW, h, hcondS.1, hcondS.2, hprim,
                            hr, hs, hspine, bind, Except.bind, Agrees]
                      case pos =>
                      cases hlf : lookupBy lfld.name sfields with
                      | none =>
                          simp [assignW, h, hcondS.1, hcondS.2, hprim,
                            hr, hs, hspine, hlf, bind, Except.bind,
                            Agrees]
                      | some old =>
                          simp [assignW, h, hcondS.1, hcondS.2, hprim,
                            hr, hs, hspine, hlf, execAssign, Semantics.execAssignNested, Typed.WrappedExpr.kind, Semantics.rhsToSVal, Semantics.rhsToMVal, resolveLoc,
                            resolveS, State.saveStorage, SVal.save,
                            ihr, bind, Except.bind, pure, Except.pure,
                            Agrees]
  | .index kind ty base key =>
      cases kind with
      | memory => simp [assignW, Agrees]
      | stack => simp [assignW, Agrees]
      | storage =>
          match base with
          | .field .. => simp [assignW, Agrees]
          | .index .. => simp [assignW, Agrees]
          | .pushPlace .. => simp [assignW, Agrees]
          | .bool .. => simp [assignW, Agrees]
          | .intLit .. => simp [assignW, Agrees]
          | .mkCall .. => simp [assignW, Agrees]
          | .mkBinop .. => simp [assignW, Agrees]
          | .mkUnop .. => simp [assignW, Agrees]
          | .mkIncDec .. => simp [assignW, Agrees]
          | .mkTernary .. => simp [assignW, Agrees]
          | .var bkind bty fld =>
            cases bkind with
            | stack => simp [assignW, Agrees]
            | memory => simp [assignW, Agrees]
            | storage =>
              have ihk := evalW_agree key s
              cases h : lookupBy fld.name s.env with
              | some b => simp [assignW, h, Agrees]
              | none =>
                by_cases horig : fld.origin = some StorageOrigin.global
                case neg => simp [assignW, h, horig, Agrees]
                case pos =>
                by_cases hprim : rhs.ty.isPrimitive = true
                case neg => simp [assignW, h, horig, hprim, Agrees]
                case pos =>
                have ihr := evalW_agree rhs s
                cases hk : evalW s key with
                | error err =>
                    simp [assignW, h, horig, hprim, hk, bind, Except.bind,
                      Agrees]
                | ok kv =>
                    rw [hk] at ihk
                    simp only [Agrees_ok] at ihk
                    cases kv with
                    | bool b =>
                        simp [assignW, h, horig, hprim, hk, bind,
                          Except.bind, Agrees]
                    | int k =>
                      by_cases htyA : isArrayTy bty = true
                      case pos =>
                        by_cases hk0 : 0 ≤ k
                        case neg =>
                            simp [assignW, h, horig, hprim, hk, htyA,
                              hk0, bind, Except.bind, Agrees]
                        case pos =>
                        cases hsl : lookupBy fld.name s.storage with
                        | none =>
                            simp [assignW, h, horig, hprim, hk, htyA,
                              hk0, hsl, bind, Except.bind, Agrees]
                        | some sv =>
                          cases sv with
                          | prim p =>
                              cases p <;>
                                simp [assignW, h, horig, hprim, hk, htyA,
                                  hk0, hsl, bind, Except.bind, Agrees]
                          | struct fields =>
                              simp [assignW, h, horig, hprim, hk, htyA,
                                hk0, hsl, bind, Except.bind, Agrees]
                          | map entries dflt =>
                              simp [assignW, h, horig, hprim, hk, htyA,
                                hk0, hsl, bind, Except.bind, Agrees]
                          | array elems =>
                            cases hr : evalW s rhs with
                            | error err =>
                                cases err
                                · rw [hr] at ihr
                                  simp only [Agrees_revert] at ihr
                                  simp [assignW, h, horig, hprim, hk,
                                    htyA, hk0, hsl, hr, execAssign,
                                    Semantics.execAssignNested,
                                    Typed.WrappedExpr.kind,
                                    Semantics.rhsToSVal, ihr, bind,
                                    Except.bind, Agrees]
                                · simp [assignW, h, horig, hprim, hk,
                                    htyA, hk0, hsl, hr, bind,
                                    Except.bind, Agrees]
                            | ok v =>
                                rw [hr] at ihr
                                simp only [Agrees_ok] at ihr
                                by_cases hlt : k.toNat < elems.length
                                case neg =>
                                    simp [assignW, h, horig, hprim, hk,
                                      htyA, hk0, hsl, hr, hlt,
                                      execAssign,
                                      Semantics.execAssignNested,
                                      Typed.WrappedExpr.kind,
                                      Semantics.rhsToSVal,
                                      Semantics.rhsToMVal, resolveLoc,
                                      resolveS, evalInt,
                                      State.saveStorage, SVal.save,
                                      Value.asInt, ihk, ihr, bind,
                                      Except.bind, Agrees]
                                case pos =>
                                    simp [assignW, h, horig, hprim, hk,
                                      htyA, hk0, hsl, hr, hlt,
                                      execAssign,
                                      Semantics.execAssignNested,
                                      Typed.WrappedExpr.kind,
                                      Semantics.rhsToSVal,
                                      Semantics.rhsToMVal, resolveLoc,
                                      resolveS, evalInt,
                                      State.saveStorage, SVal.save,
                                      Value.asInt, List.get_eq_getElem,
                                      ihk, ihr, bind, Except.bind,
                                      Agrees]
                      case neg =>
                      by_cases hkb : 0 ≤ k ∧ k < keyBoundI
                      case neg =>
                          simp [assignW, h, horig, hprim, hk, htyA, hkb,
                            bind, Except.bind, Agrees]
                      case pos =>
                      cases hsl : lookupBy fld.name s.storage with
                      | none =>
                          simp [assignW, h, horig, hprim, hk, htyA, hkb,
                            hsl, bind, Except.bind, Agrees]
                      | some sv =>
                        cases sv with
                        | prim p =>
                            cases p <;>
                              simp [assignW, h, horig, hprim, hk, htyA,
                                hkb, hsl, bind, Except.bind, Agrees]
                        | struct fields =>
                            simp [assignW, h, horig, hprim, hk, htyA,
                              hkb, hsl, bind, Except.bind, Agrees]
                        | array elems =>
                            simp [assignW, h, horig, hprim, hk, htyA,
                              hkb, hsl, bind, Except.bind, Agrees]
                        | map entries dflt =>
                          cases hr : evalW s rhs with
                          | error err =>
                              cases err
                              · rw [hr] at ihr
                                simp only [Agrees_revert] at ihr
                                simp [assignW, h, horig, hprim, hk,
                                  htyA, hkb, hsl, hr, execAssign,
                                  Semantics.execAssignNested,
                                  Typed.WrappedExpr.kind,
                                  Semantics.rhsToSVal, ihr, bind,
                                  Except.bind, Agrees]
                              · simp [assignW, h, horig, hprim, hk,
                                  htyA, hkb, hsl, hr, bind, Except.bind,
                                  Agrees]
                          | ok v =>
                              rw [hr] at ihr
                              simp only [Agrees_ok] at ihr
                              cases he : lookupBy k entries with
                              | some v0 =>
                                  simp [assignW, h, horig, hprim, hk,
                                    htyA, hkb, hsl, hr, he, execAssign,
                                    Semantics.execAssignNested,
                                    Typed.WrappedExpr.kind,
                                    Semantics.rhsToSVal,
                                    Semantics.rhsToMVal, resolveLoc,
                                    resolveS, evalInt,
                                    State.saveStorage, SVal.save,
                                    Value.asInt, ihk, ihr, bind,
                                    Except.bind, Agrees]
                              | none =>
                                  simp [assignW, h, horig, hprim, hk,
                                    htyA, hkb, hsl, hr, he, execAssign,
                                    Semantics.execAssignNested,
                                    Typed.WrappedExpr.kind,
                                    Semantics.rhsToSVal,
                                    Semantics.rhsToMVal, resolveLoc,
                                    resolveS, evalInt,
                                    State.saveStorage, SVal.save,
                                    Value.asInt, ihk, ihr, bind,
                                    Except.bind, Agrees]
  | .pushPlace .. => simp [assignW, Agrees]
  | .bool .. => simp [assignW, Agrees]
  | .intLit .. => simp [assignW, Agrees]
  | .mkCall .. => simp [assignW, Agrees]
  | .mkBinop .. => simp [assignW, Agrees]
  | .mkUnop .. => simp [assignW, Agrees]
  | .mkIncDec .. => simp [assignW, Agrees]
  | .mkTernary .. => simp [assignW, Agrees]

/-- The compound-assignment claim, assembled from per-target facts: the
right-hand side evaluated (`hr`/`ihr`), the official target resolved
purely to `loc` (`hRL`), and the bounded old-value read agreeing with
`readLoc` at that `loc` (`hread`). The write side is generic: with the
pure resolution, `writeValue` collapses to `writeLoc` at `loc`, and
`writeW_agree` supplies the rest. -/
theorem compoundW_claim (s : State) (op : BinOp) (lhs : PlaceExpr)
    (rhs : WrappedExpr) (hop : op.hasCompoundAssign = true)
    {v : Value} {loc : Loc}
    (hr : evalW s rhs = .ok v)
    (ihr : evalValue s rhs = .ok (s, v))
    (hRL : resolveLoc s lhs.expr = .ok (s, loc))
    (hread : Agrees id (evalW s lhs.expr) (Semantics.readLoc s loc)) :
    Agrees id (execW s (.compoundAssign op lhs rhs))
      (execStmt s (.compoundAssign op lhs rhs)) := by
  have hwv : ∀ w, writeValue s lhs.expr w = Semantics.writeLoc s loc w := by
    intro w
    rw [writeValue, hRL]
    rfl
  cases hold : evalW s lhs.expr with
  | error e =>
      -- The bounded semantics claims nothing when the target read
      -- fails: the guard is `.stuck`.
      simp [execW, hop, hold, bind, Except.bind, Agrees]
  | ok old =>
      rw [hold] at hread
      simp only [Agrees_ok, id_eq] at hread
      have hret : op.retTy lhs.expr.ty = lhs.expr.ty := by
        cases op <;> simp_all [BinOp.retTy, BinOp.isArith,
          BinOp.hasCompoundAssign]
      cases hab : applyCheckedW op lhs.expr.ty old v with
      | error e =>
          cases e
          · rcases applyCheckedW_revert hab with hoff | ⟨u, hu, hc⟩
            · simp [execW, execStmt, hop, hr, ihr, hRL, hold, hread, hab,
                hoff, bind, Except.bind, Agrees]
            · rw [hret] at hc
              simp [execW, execStmt, hop, hr, ihr, hRL, hold, hread, hab,
                hu, hc, bind, Except.bind, Agrees]
          · simp [execW, hop, hr, hold, hab, bind, Except.bind, Agrees]
      | ok w =>
          obtain ⟨hoff, hc⟩ := applyCheckedW_ok hab
          rw [hret] at hc
          have hw := writeW_agree s lhs.expr w
          rw [hwv w] at hw
          cases hww : writeW s lhs.expr w with
          | error e =>
              cases e
              · rw [hww] at hw
                simp only [Agrees_revert] at hw
                simp [execW, execStmt, hop, hr, ihr, hRL, hold, hread,
                  hab, hoff, hc, hww, hw, bind, Except.bind, Agrees]
              · simp [execW, hop, hr, hold, hab, hww, bind, Except.bind,
                  Agrees]
          | ok s' =>
              rw [hww] at hw
              simp only [Agrees_ok, id_eq] at hw
              simp [execW, execStmt, hop, hr, ihr, hRL, hold, hread,
                hab, hoff, hc, hww, hw, bind, Except.bind, Agrees]

mutual

theorem execW_agree (s : State) (stmt : Stmt) :
    Agrees id (execW s stmt) (execStmt s stmt) := by
  match stmt with
  | .expr e =>
      have ih := evalW_agree e s
      cases he : evalW s e with
      | error err =>
          cases err
          · rw [he] at ih
            simp only [Agrees_revert] at ih
            simp [execW, he, execStmt, ih, bind, Except.bind, Agrees]
          · simp [execW, he, bind, Except.bind, Agrees]
      | ok v =>
          rw [he] at ih
          simp only [Agrees_ok] at ih
          simp [execW, he, execStmt, ih, bind, Except.bind, Agrees]
  | .assign lhs rhs =>
      have := assignW_agree s lhs rhs
      simpa [execW, execStmt] using this
  | .compoundAssign op lhs rhs =>
      by_cases hop : op.hasCompoundAssign = true
      case neg => simp [execW, hop, Agrees]
      case pos =>
      cases hold : evalW s lhs.expr with
      | error e =>
          -- the bounded compound is stuck when the target read fails
          simp [execW, hop, hold, bind, Except.bind, Agrees]
      | ok old =>
        have ihr := evalW_agree rhs s
        cases hr : evalW s rhs with
        | error err =>
            cases err
            · rw [hr] at ihr
              simp only [Agrees_revert] at ihr
              simp [execW, hop, hold, hr, execStmt, ihr, bind, Except.bind,
              Agrees]
            · simp [execW, hop, hold, hr, bind, Except.bind, Agrees]
        | ok v =>
            rw [hr] at ihr
            simp only [Agrees_ok] at ihr
            obtain ⟨lexpr, hassign⟩ := lhs
            -- Per target shape: out-of-fragment targets are stuck on the
            -- bounded read or write; fragment targets resolve purely, and
            -- the claim goes through `compoundW_claim`.
            match lexpr with
            | .bool b => exact Bool.noConfusion hassign
            | .intLit ty n => exact Bool.noConfusion hassign
            | .mkCall .. => exact Bool.noConfusion hassign
            | .mkBinop .. => exact Bool.noConfusion hassign
            | .mkUnop .. => exact Bool.noConfusion hassign
            | .mkIncDec .. => exact Bool.noConfusion hassign
            | .mkTernary .. => exact Bool.noConfusion hassign
            | .pushPlace target =>
                simp [evalW, bind, Except.bind] at hold
            | .var kind ty fld =>
                cases kind with
                | memory => simp [evalW, bind, Except.bind] at hold
                | stack =>
                    cases hb : lookupBy fld.name s.env with
                    | none =>
                        simp [execW, hop, hr, evalW, State.getEnv, hb, bind,
                          Except.bind, Agrees]
                    | some b =>
                      cases b with
                      | spath root segs =>
                          simp [evalW, State.getEnv, hb, bind, Except.bind] at hold
                      | mref id =>
                          simp [evalW, State.getEnv, hb, bind, Except.bind] at hold
                      | val w =>
                          have hRL : resolveLoc s
                              (WrappedExpr.var Kind.stack ty fld) =
                              .ok (s, Loc.stack fld.name) := by
                            rw [resolveLoc]
                          refine compoundW_claim s op ⟨_, hassign⟩ rhs hop
                            hr ihr hRL ?_
                          simp [evalW, Semantics.readLoc, State.getEnv, hb,
                            bind, Except.bind, Agrees]
                | storage =>
                    cases hb : lookupBy fld.name s.env with
                    | some b =>
                        simp [evalW, hb, bind, Except.bind] at hold
                    | none =>
                      by_cases horig : fld.origin = some StorageOrigin.global
                      case neg =>
                          simp [execW, hop, hr, evalW, hb, horig, bind,
                            Except.bind, Agrees]
                      case pos =>
                      have hRL : resolveLoc s
                          (WrappedExpr.var Kind.storage ty fld) =
                          .ok (s, Loc.storage fld.name []) := by
                        rw [resolveLoc]
                        simp [horig]
                      refine compoundW_claim s op ⟨_, hassign⟩ rhs hop
                        hr ihr hRL ?_
                      cases hsl : lookupBy fld.name s.storage with
                      | none =>
                          simp [evalW, hb, horig, hsl, Agrees]
                      | some sv =>
                          cases hav : sv.asValue with
                          | error err =>
                              cases err
                              · cases sv with
                                | prim p =>
                                    cases p <;> simp [SVal.asValue] at hav
                                | _ => simp [SVal.asValue] at hav
                              · simp [evalW, hb, horig, hsl, hav, Agrees]
                          | ok val =>
                              simp [evalW, Semantics.readLoc,
                                State.findStorage, SVal.find, hb, horig,
                                hsl, hav, bind, Except.bind, Agrees]
            | .field kind fty fbase lfld =>
                cases kind with
                | memory => simp [evalW, bind, Except.bind] at hold
                | stack => simp [evalW, bind, Except.bind] at hold
                | storage =>
                  match fbase with
                  | .field .. => simp [evalW, bind, Except.bind] at hold
                  | .index .. => simp [evalW, bind, Except.bind] at hold
                  | .pushPlace .. => simp [evalW, bind, Except.bind] at hold
                  | .bool .. => simp [evalW, bind, Except.bind] at hold
                  | .intLit .. => simp [evalW, bind, Except.bind] at hold
                  | .mkCall .. => simp [evalW, bind, Except.bind] at hold
                  | .mkBinop .. => simp [evalW, bind, Except.bind] at hold
                  | .mkUnop .. => simp [evalW, bind, Except.bind] at hold
                  | .mkIncDec .. => simp [evalW, bind, Except.bind] at hold
                  | .mkTernary .. => simp [evalW, bind, Except.bind] at hold
                  | .var bkind bty fld =>
                    cases bkind with
                    | stack => simp [evalW, bind, Except.bind] at hold
                    | memory => simp [evalW, bind, Except.bind] at hold
                    | storage =>
                      cases hb : lookupBy fld.name s.env with
                      | some b =>
                          simp [evalW, hb, bind, Except.bind] at hold
                      | none =>
                        by_cases hcond : fld.origin =
                            some StorageOrigin.global ∧
                            lfld.name = "length" ∧ isArrayTy bty = true
                        case pos =>
                          have hRL' : resolveLoc s
                              (WrappedExpr.field Kind.storage fty
                                (WrappedExpr.var Kind.storage bty fld)
                                lfld) =
                              .ok (s, Loc.storage fld.name
                                [Seg.field lfld.name]) := by
                            rw [resolveLoc, resolveS, resolveS]
                            simp [hb, hcond.1, bind, Except.bind]
                          refine compoundW_claim s op ⟨_, hassign⟩ rhs hop
                            hr ihr hRL' ?_
                          cases hsl : lookupBy fld.name s.storage with
                          | none =>
                              simp [evalW, hb, hcond.1, hcond.2.1,
                                hcond.2.2, hsl, Agrees]
                          | some sv =>
                            cases sv with
                            | prim p =>
                                cases p <;>
                                  simp [evalW, hb, hcond.1, hcond.2.1,
                                    hcond.2.2, hsl, Agrees]
                            | struct sfields =>
                                simp [evalW, hb, hcond.1, hcond.2.1,
                                  hcond.2.2, hsl, Agrees]
                            | map entries dflt =>
                                simp [evalW, hb, hcond.1, hcond.2.1,
                                  hcond.2.2, hsl, Agrees]
                            | array elems =>
                                simp [evalW, Semantics.readLoc,
                                  State.findStorage, SVal.find, hb,
                                  hcond.1, hcond.2.1, hcond.2.2, hsl,
                                  SVal.asValue, bind, Except.bind, Agrees]
                        case neg =>
                        by_cases hcondS : fld.origin =
                            some StorageOrigin.global ∧ isStructTy bty = true
                        case neg =>
                            simp [evalW, hb, if_neg hcond, if_neg hcondS, bind, Except.bind] at hold
                        case pos =>
                        have hRL' : resolveLoc s
                            (WrappedExpr.field Kind.storage fty
                              (WrappedExpr.var Kind.storage bty fld)
                              lfld) =
                            .ok (s, Loc.storage fld.name
                              [Seg.field lfld.name]) := by
                          rw [resolveLoc, resolveS, resolveS]
                          simp [hb, hcondS.1, bind, Except.bind]
                        refine compoundW_claim s op ⟨_, hassign⟩ rhs hop
                          hr ihr hRL' ?_
                        cases hsl : lookupBy fld.name s.storage with
                        | none =>
                            simp [evalW, hb, if_neg hcond, hcondS.1,
                              hcondS.2,
                              isArrayTy_eq_false_of_isStructTy hcondS.2,
                              hsl, Agrees]
                        | some sv =>
                          cases sv with
                          | prim p =>
                              cases p <;>
                                simp [evalW, hb, if_neg hcond, hcondS.1,
                                  hcondS.2,
                                  isArrayTy_eq_false_of_isStructTy hcondS.2,
                                  hsl, Agrees]
                          | array elems =>
                              simp [evalW, hb, if_neg hcond, hcondS.1,
                                hcondS.2,
                                isArrayTy_eq_false_of_isStructTy hcondS.2,
                                hsl, Agrees]
                          | map entries dflt =>
                              simp [evalW, hb, if_neg hcond, hcondS.1,
                                hcondS.2,
                                isArrayTy_eq_false_of_isStructTy hcondS.2,
                                hsl, Agrees]
                          | struct sfields =>
                            by_cases hspine : sfields.map Prod.fst
                                = structSpineOf bty
                            case neg =>
                                simp [evalW, hb, if_neg hcond, hcondS.1,
                                  hcondS.2,
                                  isArrayTy_eq_false_of_isStructTy hcondS.2,
                                  hsl, hspine, Agrees]
                            case pos =>
                            cases hlf : lookupBy lfld.name sfields with
                            | none =>
                                simp [evalW, hb, if_neg hcond, hcondS.1,
                                  hcondS.2,
                                  isArrayTy_eq_false_of_isStructTy hcondS.2,
                                  hsl, hspine, hlf, Agrees]
                            | some mv =>
                              cases hav : mv.asValue with
                              | error err =>
                                  cases err
                                  · cases mv with
                                    | prim p =>
                                        cases p <;>
                                          simp [SVal.asValue] at hav
                                    | _ => simp [SVal.asValue] at hav
                                  · simp [evalW, hb, if_neg hcond, hcondS.1,
                                      hcondS.2,
                                      isArrayTy_eq_false_of_isStructTy
                                        hcondS.2,
                                      hsl, hspine, hlf, hav, Agrees]
                              | ok val =>
                                  simp [evalW, Semantics.readLoc,
                                    State.findStorage, SVal.find, hb,
                                    if_neg hcond, hcondS.1, hcondS.2,
                                    isArrayTy_eq_false_of_isStructTy
                                      hcondS.2,
                                    hsl, hspine, hlf, hav, bind,
                                    Except.bind, Agrees]
            | .index kind ty base key =>
                cases kind with
                | memory => simp [evalW, bind, Except.bind] at hold
                | stack => simp [evalW, bind, Except.bind] at hold
                | storage =>
                  match base with
                  | .field .. => simp [evalW, bind, Except.bind] at hold
                  | .index .. => simp [evalW, bind, Except.bind] at hold
                  | .pushPlace .. => simp [evalW, bind, Except.bind] at hold
                  | .bool .. => simp [evalW, bind, Except.bind] at hold
                  | .intLit .. => simp [evalW, bind, Except.bind] at hold
                  | .mkCall .. => simp [evalW, bind, Except.bind] at hold
                  | .mkBinop .. => simp [evalW, bind, Except.bind] at hold
                  | .mkUnop .. => simp [evalW, bind, Except.bind] at hold
                  | .mkIncDec .. => simp [evalW, bind, Except.bind] at hold
                  | .mkTernary .. => simp [evalW, bind, Except.bind] at hold
                  | .var bkind bty fld =>
                    cases bkind with
                    | stack => simp [evalW, bind, Except.bind] at hold
                    | memory => simp [evalW, bind, Except.bind] at hold
                    | storage =>
                      have ihk := evalW_agree key s
                      cases hb : lookupBy fld.name s.env with
                      | some b =>
                          simp [evalW, hb, bind, Except.bind] at hold
                      | none =>
                        by_cases horig : fld.origin =
                            some StorageOrigin.global
                        case neg =>
                            simp [execW, hop, hr, evalW, hb, horig, bind,
                              Except.bind, Agrees]
                        case pos =>
                        cases hk : evalW s key with
                        | error err =>
                            cases err
                            · rw [hk] at ihk
                              simp only [Agrees_revert] at ihk
                              simp [evalW, hb, horig, hk, execStmt, ihr, ihk, resolveLoc, resolveS, evalInt, bind, Except.bind] at hold
                            · simp [evalW, hb, horig, hk, bind, Except.bind] at hold
                        | ok kv =>
                            rw [hk] at ihk
                            simp only [Agrees_ok] at ihk
                            cases kv with
                            | bool b =>
                                simp [evalW, hb, horig, hk, execStmt, ihr, ihk, resolveLoc, resolveS, evalInt, Value.asInt, bind, Except.bind] at hold
                            | int k =>
                              have hRL : resolveLoc s
                                  (WrappedExpr.index Kind.storage ty
                                    (WrappedExpr.var Kind.storage bty fld)
                                    key) =
                                  .ok (s, Loc.storage fld.name
                                    [Seg.at k]) := by
                                rw [resolveLoc, resolveS]
                                simp [hb, horig, evalInt, ihk, Value.asInt,
                                  bind, Except.bind]
                              by_cases htyA : isArrayTy bty = true
                              case pos =>
                                by_cases hk0 : 0 ≤ k
                                case neg =>
                                    simp [evalW, hb, horig, hk, htyA, hk0, bind, Except.bind] at hold
                                case pos =>
                                refine compoundW_claim s op ⟨_, hassign⟩
                                  rhs hop hr ihr hRL ?_
                                cases hsl : lookupBy fld.name s.storage with
                                | none =>
                                    simp [evalW, hb, horig, hk, htyA, hk0,
                                      hsl, bind, Except.bind, Agrees]
                                | some sv =>
                                  cases sv with
                                  | prim p =>
                                      cases p <;>
                                        simp [evalW, hb, horig, hk, htyA,
                                          hk0, hsl, bind, Except.bind, Agrees]
                                  | struct sfields =>
                                      simp [evalW, hb, horig, hk, htyA,
                                        hk0, hsl, bind, Except.bind, Agrees]
                                  | map entries dflt =>
                                      simp [evalW, hb, horig, hk, htyA,
                                        hk0, hsl, bind, Except.bind, Agrees]
                                  | array elems =>
                                      by_cases hlt : k.toNat < elems.length
                                      case neg =>
                                          simp [evalW, Semantics.readLoc,
                                            State.findStorage, SVal.find,
                                            hb, horig, hk, htyA, hk0, hsl,
                                            hlt, bind, Except.bind, Agrees]
                                      case pos =>
                                          simp [evalW, Semantics.readLoc,
                                            State.findStorage, SVal.find,
                                            hb, horig, hk, htyA, hk0, hsl,
                                            hlt, SVal.asValue,
                                            List.get_eq_getElem,
                                            List.getD_eq_getElem?_getD,
                                            bind, Except.bind, Agrees]
                                          exact Agrees_rfl
                              case neg =>
                              by_cases hkb : 0 ≤ k ∧ k < keyBoundI
                              case neg =>
                                  simp [evalW, hb, horig, hk, htyA, hkb, bind, Except.bind] at hold
                              case pos =>
                              refine compoundW_claim s op ⟨_, hassign⟩
                                rhs hop hr ihr hRL ?_
                              cases hsl : lookupBy fld.name s.storage with
                              | none =>
                                  simp [evalW, hb, horig, hk, htyA, hkb,
                                    hsl, bind, Except.bind, Agrees]
                              | some sv =>
                                cases sv with
                                | prim p =>
                                    cases p <;>
                                      simp [evalW, hb, horig, hk, htyA, hkb,
                                        hsl, bind, Except.bind, Agrees]
                                | struct sfields =>
                                    simp [evalW, hb, horig, hk, htyA, hkb,
                                      hsl, bind, Except.bind, Agrees]
                                | array elems =>
                                    simp [evalW, hb, horig, hk, htyA, hkb,
                                      hsl, bind, Except.bind, Agrees]
                                | map entries dflt =>
                                    cases he : lookupBy k entries with
                                    | some v0 =>
                                        simp [evalW, Semantics.readLoc,
                                          State.findStorage, SVal.find,
                                          hb, horig, hk, htyA, hkb, hsl,
                                          he, bind, Except.bind, Agrees]
                                        exact Agrees_rfl
                                    | none =>
                                        simp [evalW, Semantics.readLoc,
                                          State.findStorage, SVal.find,
                                          hb, horig, hk, htyA, hkb, hsl,
                                          he, bind, Except.bind, Agrees]
                                        exact Agrees_rfl
  | .stackDecl ty name init =>
      by_cases hprim : ty.isPrimitive = true
      · match init with
        | none =>
            cases ty with
            | prim p =>
                cases p <;>
                  simp_all [execW, execStmt, Ty.isPrimitive, Agrees]
            | ref r =>
                simp_all [execW, execStmt, Ty.isPrimitive, Agrees]
        | some rhs =>
            have ih := evalW_agree rhs s
            cases hr : evalW s rhs with
            | error err =>
                cases err
                · rw [hr] at ih
                  simp only [Agrees_revert] at ih
                  simp [execW, hprim, hr, execStmt, ih, bind, Except.bind,
                    Agrees]
                · simp [execW, hprim, hr, bind, Except.bind, Agrees]
            | ok v =>
                rw [hr] at ih
                simp only [Agrees_ok] at ih
                simp [execW, hprim, hr, execStmt, ih, bind, Except.bind,
                  Agrees]
      · simp [execW, hprim, Agrees]
  | .ite cond thn els =>
      have ihc := evalW_agree cond s
      cases hc : evalW s cond with
      | error err =>
          cases err
          · rw [hc] at ihc
            simp only [Agrees_revert] at ihc
            simp [execW, hc, execStmt, ihc, bind, Except.bind, Agrees]
          · simp [execW, hc, bind, Except.bind, Agrees]
      | ok cv =>
          rw [hc] at ihc
          simp only [Agrees_ok] at ihc
          cases cv with
          | int n => simp [execW, hc, bind, Except.bind, Agrees]
          | bool b =>
              cases b
              · have ihb := execWBlock_agree s els
                simp only [execW, execStmt, hc, ihc, bind, Except.bind]
                exact ihb
              · have ihb := execWBlock_agree s thn
                simp only [execW, execStmt, hc, ihc, bind, Except.bind]
                exact ihb
  | .assertStmt cond =>
      have ihc := evalW_agree cond s
      cases hc : evalW s cond with
      | error err =>
          cases err
          · rw [hc] at ihc
            simp only [Agrees_revert] at ihc
            simp [execW, hc, execStmt, ihc, bind, Except.bind, Agrees]
          · simp [execW, hc, bind, Except.bind, Agrees]
      | ok cv =>
          rw [hc] at ihc
          simp only [Agrees_ok] at ihc
          cases cv with
          | int n => simp [execW, hc, bind, Except.bind, Agrees]
          | bool b =>
              cases b <;>
                simp [execW, hc, execStmt, ihc, bind, Except.bind, Agrees]
  | .requireStmt cond =>
      have ihc := evalW_agree cond s
      cases hc : evalW s cond with
      | error err =>
          cases err
          · rw [hc] at ihc
            simp only [Agrees_revert] at ihc
            simp [execW, hc, execStmt, ihc, bind, Except.bind, Agrees]
          · simp [execW, hc, bind, Except.bind, Agrees]
      | ok cv =>
          rw [hc] at ihc
          simp only [Agrees_ok] at ihc
          cases cv with
          | int n => simp [execW, hc, bind, Except.bind, Agrees]
          | bool b =>
              cases b <;>
                simp [execW, hc, execStmt, ihc, bind, Except.bind, Agrees]
  | .revert msg => simp [execW, execStmt, Agrees]
  | .storageDecl ty name init => simp [execW, Agrees]
  | .storagePlaceAlias ty name init => simp [execW, Agrees]
  | .memoryDecl ty name init => simp [execW, Agrees]
  | .delete target => simp [execW, Agrees]
  | .push target value =>
      obtain ⟨texpr, hassign⟩ := target
      match texpr with
      | .field .. => simp [execW, Agrees]
      | .index .. => simp [execW, Agrees]
      | .pushPlace .. => simp [execW, Agrees]
      | .bool .. => simp [execW, Agrees]
      | .intLit .. => simp [execW, Agrees]
      | .mkCall .. => simp [execW, Agrees]
      | .mkBinop .. => simp [execW, Agrees]
      | .mkUnop .. => simp [execW, Agrees]
      | .mkIncDec .. => simp [execW, Agrees]
      | .mkTernary .. => simp [execW, Agrees]
      | .var kind tyA fld =>
        cases kind with
        | stack => simp [execW, Agrees]
        | memory => simp [execW, Agrees]
        | storage =>
          cases h : lookupBy fld.name s.env with
          | some b => simp [execW, h, Agrees]
          | none =>
            match tyA with
            | Ty.bool => simp [execW, h, Agrees]
            | Ty.uint => simp [execW, h, Agrees]
            | Ty.int => simp [execW, h, Agrees]
            | Ty.ref (RefTy.struct nm) => simp [execW, h, Agrees]
            | Ty.ref (RefTy.mapping kt vt) => simp [execW, h, Agrees]
            | Ty.ref (RefTy.array elemTy) =>
              by_cases hcond : fld.origin = some StorageOrigin.global ∧
                  elemTy.isPrimitive = true
              case neg => simp [execW, h, hcond, Agrees]
              case pos =>
              cases hs : lookupBy fld.name s.storage with
              | none =>
                  simp [execW, h, hcond.1, hcond.2, hs, bind,
                    Except.bind, Agrees]
              | some sv =>
                cases sv with
                | prim p =>
                    cases p <;>
                      simp [execW, h, hcond.1, hcond.2, hs, bind,
                        Except.bind, Agrees]
                | struct fields =>
                    simp [execW, h, hcond.1, hcond.2, hs, bind,
                      Except.bind, Agrees]
                | map entries dflt =>
                    simp [execW, h, hcond.1, hcond.2, hs, bind,
                      Except.bind, Agrees]
                | array elems =>
                  cases value with
                  | none =>
                      by_cases hlen1 : elems.length + 1 ≤ keyBound
                      · simp [execW, execStmt, h, hcond.1, hcond.2, hs,
                          hlen1, resolveS, State.findStorage, SVal.find,
                          State.saveStorage, SVal.save,
                          Typed.WrappedExpr.ty, bind,
                          Except.bind, pure, Except.pure, Agrees]
                      · simp [execW, h, hcond.1, hcond.2, hs, hlen1,
                          bind, Except.bind, Agrees]
                  | some rhs =>
                      by_cases hprim : rhs.ty.isPrimitive = true
                      case neg =>
                          simp [execW, h, hcond.1, hcond.2, hs, hprim,
                            bind, Except.bind, Agrees]
                      case pos =>
                      have ihr := evalW_agree rhs s
                      cases hr : evalW s rhs with
                      | error err =>
                          cases err
                          · rw [hr] at ihr
                            simp only [Agrees_revert] at ihr
                            simp [execW, execStmt, h, hcond.1, hcond.2,
                              hs, hprim, hr, ihr, Semantics.rhsToSVal,
                              resolveS, State.findStorage, SVal.find,
                              Typed.WrappedExpr.ty, bind,
                              Except.bind, Agrees]
                          · simp [execW, h, hcond.1, hcond.2, hs,
                              hprim, hr, bind, Except.bind, Agrees]
                      | ok v =>
                          rw [hr] at ihr
                          simp only [Agrees_ok] at ihr
                          by_cases hlen1 : elems.length + 1 ≤ keyBound
                          · simp [execW, execStmt, h, hcond.1, hcond.2,
                              hs, hprim, hr, ihr, hlen1,
                              Semantics.rhsToSVal, resolveS,
                              State.findStorage, SVal.find,
                              State.saveStorage, SVal.save,
                              Typed.WrappedExpr.ty, bind,
                              Except.bind, pure, Except.pure, Agrees]
                          · simp [execW, h, hcond.1, hcond.2, hs,
                              hprim, hr, hlen1, bind, Except.bind,
                              Agrees]
  | .pushAssign target value => simp [execW, Agrees]
  | .pushFieldAssign target fld value => simp [execW, Agrees]
  | .pop target =>
      obtain ⟨texpr, hassign⟩ := target
      match texpr with
      | .field .. => simp [execW, Agrees]
      | .index .. => simp [execW, Agrees]
      | .pushPlace .. => simp [execW, Agrees]
      | .bool .. => simp [execW, Agrees]
      | .intLit .. => simp [execW, Agrees]
      | .mkCall .. => simp [execW, Agrees]
      | .mkBinop .. => simp [execW, Agrees]
      | .mkUnop .. => simp [execW, Agrees]
      | .mkIncDec .. => simp [execW, Agrees]
      | .mkTernary .. => simp [execW, Agrees]
      | .var kind tyA fld =>
        cases kind with
        | stack => simp [execW, Agrees]
        | memory => simp [execW, Agrees]
        | storage =>
          cases h : lookupBy fld.name s.env with
          | some b => simp [execW, h, Agrees]
          | none =>
            match tyA with
            | Ty.bool => simp [execW, h, Agrees]
            | Ty.uint => simp [execW, h, Agrees]
            | Ty.int => simp [execW, h, Agrees]
            | Ty.ref (RefTy.struct nm) => simp [execW, h, Agrees]
            | Ty.ref (RefTy.mapping kt vt) => simp [execW, h, Agrees]
            | Ty.ref (RefTy.array elemTy) =>
              by_cases horig : fld.origin = some StorageOrigin.global
              case neg => simp [execW, h, horig, Agrees]
              case pos =>
              cases hs : lookupBy fld.name s.storage with
              | none =>
                  simp [execW, h, horig, hs, bind, Except.bind, Agrees]
              | some sv =>
                cases sv with
                | prim p =>
                    cases p <;>
                      simp [execW, h, horig, hs, bind, Except.bind,
                        Agrees]
                | struct fields =>
                    simp [execW, h, horig, hs, bind, Except.bind,
                      Agrees]
                | map entries dflt =>
                    simp [execW, h, horig, hs, bind, Except.bind,
                      Agrees]
                | array elems =>
                  cases hrev : elems.reverse with
                  | nil =>
                      simp [execW, execStmt, h, horig, hs, hrev,
                        resolveS, State.findStorage, SVal.find, bind,
                        Except.bind, Agrees]
                  | cons x restRev =>
                      simp [execW, execStmt, h, horig, hs, hrev,
                        resolveS, State.findStorage, SVal.find,
                        State.saveStorage, SVal.save, bind, Except.bind,
                        pure, Except.pure, Agrees]
  | .transfer recipient amount =>
      have iha := evalW_agree recipient s
      cases ha : evalW s recipient with
      | error err =>
          cases err
          · rw [ha] at iha
            simp only [Agrees_revert] at iha
            simp [execW, execStmt, evalInt, ha, iha, bind, Except.bind,
              Agrees]
          · simp [execW, ha, bind, Except.bind, Agrees]
      | ok av =>
        rw [ha] at iha
        simp only [Agrees_ok] at iha
        cases av with
        | bool b => simp [execW, ha, bind, Except.bind, Agrees]
        | int a =>
          by_cases hab : 0 ≤ a ∧ a < keyBoundI
          case neg =>
              simp [execW, ha, hab, bind, Except.bind, Agrees]
          case pos =>
          have ihm := evalW_agree amount s
          cases hm : evalW s amount with
          | error err =>
              cases err
              · rw [hm] at ihm
                simp only [Agrees_revert] at ihm
                simp [execW, execStmt, evalInt, Value.asInt, ha, iha,
                  hab, hm, ihm, bind, Except.bind, pure, Except.pure,
                  Agrees]
              · simp [execW, ha, hab, hm, bind, Except.bind, Agrees]
          | ok mv =>
            rw [hm] at ihm
            simp only [Agrees_ok] at ihm
            cases mv with
            | bool b =>
                simp [execW, ha, hab, hm, bind, Except.bind, Agrees]
            | int amt =>
              by_cases hneg : amt < 0
              case pos =>
                  simp [execW, ha, hab, hm, hneg, bind, Except.bind, Agrees]
              case neg =>
              by_cases hbal : s.selfBalance < amt
              case pos =>
                  simp [execW, execStmt, evalInt, Value.asInt, ha, iha,
                    hab, hm, ihm, hneg, hbal, bind, Except.bind, pure,
                    Except.pure, Agrees]
              case neg =>
              by_cases hled : 0 ≤ s.getNet a - amt
              case pos =>
                  have hled' : amt ≤ s.getNet a := by omega
                  simp [execW, execStmt, evalInt, Value.asInt, ha, iha,
                    hab, hm, ihm, hneg, hbal, hled, hled', bind, Except.bind,
                    pure, Except.pure, Agrees]
              case neg =>
                  have hled' : ¬ amt ≤ s.getNet a := by omega
                  simp [execW, ha, hab, hm, hneg, hbal, hled, hled', bind,
                    Except.bind, Agrees]
  | .callStmt result fn args => simp [execW, Agrees]
termination_by sizeOf stmt

theorem execWBlock_agree (s : State) (stmts : List Stmt) :
    Agrees id (execWBlock s stmts) (execBlock s stmts) := by
  match stmts with
  | [] => simp [execWBlock, execBlock, Agrees]
  | stmt :: rest =>
      have ih1 := execW_agree s stmt
      cases h1 : execW s stmt with
      | error err =>
          cases err
          · rw [h1] at ih1
            simp only [Agrees_revert] at ih1
            simp [execWBlock, h1, execBlock, ih1, bind, Except.bind, Agrees]
          · simp [execWBlock, h1, bind, Except.bind, Agrees]
      | ok s' =>
          rw [h1] at ih1
          simp only [Agrees_ok] at ih1
          have ih2 := execWBlock_agree s' rest
          simp only [execWBlock, execBlock, h1, ih1, bind, Except.bind]
          simpa using ih2
termination_by sizeOf stmts

end

end Evm
end Solidity
