import Solidity.Kernel.Erase

/-!
# The denotation of kernel terms

A kernel term means what the interpreter does with its erasure.  This file
writes that meaning down by structural recursion on the typed syntax —
`SPath.resolve`, `Val.eval`, `Src.value`, `Stmt.run`, `Prog.run` — and proves
it **is** the interpreter's: `Stmt.run_eq` says `execStmt σ s.erase = s.run σ`
for every state `σ`, typed or not.

The interpreter's functions (`resolveS`, `evalValue`, `execAssign`, …) are
well-founded recursion over the untyped AST and branch on kinds, origins and
types at every node; over a kernel term those branches are decided by the
index, so each denotation is one line of the arm the interpreter takes.  The
two places the interpreter is not uniform are kept, not smoothed over:

* a *read* of a state variable looks in the environment first (`resolveS`),
  while a *write* to one goes straight to the storage root (`execAssign`),
  so `Loc.target` differs from `Loc.resolve` at a root;
* evaluation is pure on this slice (no `++`, no calls, no `push` place), so a
  denotation returns a value, not a state.

The taclets' soundness (`Kernel/Taclet.lean`) is proved over these, which is
where the typing pays: a proof never meets a stack-kind field or a
reference-typed operator.
-/

namespace Solidity
namespace Kernel

open Semantics

/-- What `resolveS` does with a variable: an alias in the environment is its
path, a state variable (`global`) not shadowed is its root. -/
def envPath (σ : State) (x : Name) (global : Bool) : Res (Name × List Seg) :=
  match lookupBy x σ.env with
  | some (.spath root segs) => .ok (root, segs)
  | some (.val _) => .error .stuck
  | some (.mref _) => .error .stuck
  | none => if global then .ok (x, []) else .error .stuck

/-- `-x` is range-checked at `int` only (`evalValue`'s `mkUnop` arm). -/
def unopCheck (op : UnOp) (p : PrimTy) (v : Value) : Res Value :=
  match op, p with
  | .neg, .int => checkArith .int v
  | _, _ => pure v

variable {C : Contract} {Γ : Ctx}

/-- The value a simple value denotes: a literal, or a stack local's
binding. -/
def Simple.eval (σ : State) {p : PrimTy} : Simple C Γ p → Res Value
  | .lit n _ => pure (.int n)
  | .bool b => pure (.bool b)
  | .local x _ => do
    match ← σ.getEnv x with
    | .val v => pure v
    | .spath .. => .error .stuck
    | .mref _ => .error .stuck

mutual

/-- The storage path a path denotes, read in `σ`. -/
def SPath.resolve (σ : State) : {T : Ty} → SPath C Γ T → Res (Name × List Seg)
  | _, .alias x _ => envPath σ x false
  | _, .loc l => l.resolve σ

def Loc.resolve (σ : State) : {T : Ty} → Loc C Γ T → Res (Name × List Seg)
  | _, .root r _ _ => envPath σ r true
  | _, .field b f _ => do
    let (r, segs) ← b.resolve σ
    pure (r, segs ++ [.field f])
  | _, .mapIndex b i => do
    let (r, segs) ← b.resolve σ
    let i ← (← i.eval σ).asInt
    pure (r, segs ++ [.at i])
  | _, .arrIndex b i => do
    let (r, segs) ← b.resolve σ
    let i ← (← i.eval σ).asInt
    pure (r, segs ++ [.at i])

/-- The value a value expression denotes in `σ`. -/
def Val.eval (σ : State) : {p : PrimTy} → Val C Γ p → Res Value
  | _, .simple s => s.eval σ
  | _, .read l => do
    let (r, segs) ← l.resolve σ
    (← σ.findStorage r segs).asValue
  | _, @Val.binop _ _ p op _ a b => do
    let lv ← a.eval σ
    match op, lv with
    | .and, .bool false => pure (.bool false)
    | .or, .bool true => pure (.bool true)
    | _, _ => do
      let rv ← b.eval σ
      checkArith (op.retTy (.prim p)) (← applyBinOp op lv rv)
  | _, @Val.unop _ _ p op _ a => do unopCheck op p (← applyUnOp op (← a.eval σ))

end

/-- Where a write to a location goes: a state variable is written at its
root whatever the environment says (`execAssign`); anything else is
resolved. -/
def Loc.target (σ : State) {T : Ty} : Loc C Γ T → Res (Name × List Seg)
  | .root r _ _ => .ok (r, [])
  | l => l.resolve σ

/-- The storage value a source stores: a value, or the copied subtree. -/
def Src.value (σ : State) {T : Ty} : Src C Γ T → Res SVal
  | .val v => do pure (← v.eval σ).toSVal
  | .copy p _ => do
    let (r, segs) ← p.resolve σ
    σ.findStorage r segs

/-- The default a `uint x;` binds. -/
def PrimTy.default : PrimTy → Value
  | .bool => .bool false
  | .uint | .int => .int 0

mutual

/-- The state a statement leaves, from `σ`. -/
def Stmt.run (σ : State) {Γ Γ' : Ctx} : Stmt C Γ Γ' → Res State
  | .assign l r => do
    let sv ← r.value σ
    let (root, segs) ← l.target σ
    σ.saveStorage root segs sv
  | .rebind x _ r => do
    let (root, segs) ← r.resolve σ
    pure (σ.setEnv x (.spath root segs))
  | .assignLocal x _ r => do pure (σ.setEnv x (.val (← r.eval σ)))
  | .declLocal p x _ init => do
    let v ← match init with
      | none => pure (PrimTy.default p)
      | some e => e.eval σ
    pure (σ.setEnv x (.val v))
  | .declStorage _ _ x _ init => do
    let (root, segs) ← init.resolve σ
    pure (σ.setEnv x (.spath root segs))
  | .delete l => do
    let (root, segs) ← l.resolve σ
    let cur ← σ.findStorage root segs
    σ.saveStorage root segs cur.defaultOf
  | .ite c thn els => do
    match ← c.eval σ with
    | .bool true => thn.run σ
    | .bool false => els.run σ
    | .int _ => .error .stuck
  | .require c => do
    match ← c.eval σ with
    | .bool true => pure σ
    | .bool false => .error .revert
    | .int _ => .error .stuck
  | .assert c => do
    match ← c.eval σ with
    | .bool true => pure σ
    | .bool false => .error .revert
    | .int _ => .error .stuck
  | .revert => .error .revert

def Prog.run (σ : State) {Γ Γ' : Ctx} : Prog C Γ Γ' → Res State
  | .nil => pure σ
  | .cons s P => do P.run (← s.run σ)

end

/-! ## Adequacy: the denotation is the interpreter's -/

@[simp] theorem fieldFor_name (n : Name) (T : Ty) (o : Option StorageOrigin) :
    (SoliditySyntax.fieldFor n T o).name = n := by
  cases T <;> rfl

/-- `evalInt` of an expression whose evaluation is pure. -/
theorem evalInt_pure {σ : State} {e : WrappedExpr} {x : Res Value}
    (h : evalValue σ e = x.map (σ, ·)) :
    evalInt σ e = (do (← x).asInt).map (σ, ·) := by
  rw [evalInt, h]
  cases x with
  | error _ => rfl
  | ok v => cases v <;> rfl

/-- A storage read of a location: resolve, find, take the value. -/
theorem Loc.evalValue_erase_read (σ : State) {T : Ty} (l : Loc C Γ T) :
    evalValue σ l.erase = (do
      let (s, r, segs) ← resolveS σ l.erase
      let v ← s.findStorage r segs
      .ok (s, ← v.asValue)) := by
  cases l <;> rw [Loc.erase, evalValue]

theorem envPath_resolveS (σ : State) (x : Name) (T : Ty) (fld : Field) (hx : fld.name = x) :
    resolveS σ (.var .storage T fld) =
      (envPath σ x (fld.origin = some .global)).map (σ, ·) := by
  subst hx
  rw [resolveS]
  unfold envPath
  cases lookupBy fld.name σ.env with
  | none => by_cases hg : fld.origin = some .global <;> simp [hg] <;> rfl
  | some b => cases b <;> rfl

/-- A simple value evaluates as `evalValue` evaluates its erasure. -/
theorem Simple.evalValue_erase (σ : State) {p : PrimTy} :
    (s : Simple C Γ p) → evalValue σ s.erase = (s.eval σ).map (σ, ·)
  | .lit n _ => by rw [Simple.erase, evalValue]; rfl
  | .bool b => by rw [Simple.erase, evalValue]; rfl
  | .local x _ => by
    rw [Simple.erase, evalValue]
    simp only [Field.primitive, Simple.eval]
    cases σ.getEnv x with
    | error _ => rfl
    | ok b => cases b <;> rfl

mutual

theorem SPath.resolveS_erase (σ : State) : {T : Ty} → (p : SPath C Γ T) →
    resolveS σ p.erase = (p.resolve σ).map (σ, ·)
  | _, .alias x _ => by
    rw [SPath.erase, envPath_resolveS σ x _ _ rfl]; simp [Field.identity, SPath.resolve]
  | _, .loc l => l.resolveS_erase σ

theorem Loc.resolveS_erase (σ : State) : {T : Ty} → (l : Loc C Γ T) →
    resolveS σ l.erase = (l.resolve σ).map (σ, ·)
  | _, .root r _ _ => by
    rw [Loc.erase, envPath_resolveS σ r _ _ (by cases ‹Ty› <;> rfl)]
    cases ‹Ty› <;> simp [SoliditySyntax.fieldFor, Field.identity, Field.primitive, Loc.resolve]
  | _, .field b f _ => by
    rw [Loc.erase, resolveS, b.resolveS_erase σ]
    simp only [Loc.resolve]
    cases b.resolve σ with
    | error _ => rfl
    | ok r => simp [Except.map]; rfl
  | _, .mapIndex b i => by
    rw [Loc.erase, resolveS, b.resolveS_erase σ]
    simp only [Loc.resolve]
    cases b.resolve σ with
    | error _ => rfl
    | ok r =>
      simp only [Except.map, bind, Except.bind]
      rw [evalInt_pure (i.evalValue_erase σ)]
      cases i.eval σ with
      | error _ => rfl
      | ok v => cases v <;> rfl
  | _, .arrIndex b i => by
    rw [Loc.erase, resolveS, b.resolveS_erase σ]
    simp only [Loc.resolve]
    cases b.resolve σ with
    | error _ => rfl
    | ok r =>
      simp only [Except.map, bind, Except.bind]
      rw [evalInt_pure (i.evalValue_erase σ)]
      cases i.eval σ with
      | error _ => rfl
      | ok v => cases v <;> rfl

theorem Val.evalValue_erase (σ : State) : {p : PrimTy} → (v : Val C Γ p) →
    evalValue σ v.erase = (v.eval σ).map (σ, ·)
  | _, .simple s => s.evalValue_erase σ
  | _, .read l => by
    rw [Val.erase, l.evalValue_erase_read, l.resolveS_erase σ]
    simp only [Val.eval]
    cases l.resolve σ with
    | error _ => rfl
    | ok r =>
      simp only [Except.map, bind, Except.bind]
      cases σ.findStorage r.1 r.2 with
      | error _ => rfl
      | ok v => cases v.asValue <;> rfl
  | _, .binop op _ a b => by
    rw [Val.erase, evalValue, a.evalValue_erase σ, a.erase_ty]
    simp only [Val.eval]
    cases a.eval σ with
    | error _ => rfl
    | ok lv =>
      simp only [Except.map, bind, Except.bind]
      rw [b.evalValue_erase σ]
      cases op <;> cases lv <;> (try rename_i bv; cases bv) <;> (try simp only) <;>
        cases b.eval σ <;> (try simp only [Except.map]) <;> (try rfl) <;> rename_i rv <;>
        cases applyBinOp _ _ rv <;> (try simp only) <;> (try rfl) <;> rename_i w <;>
        cases checkArith _ w <;> rfl
  | _, .unop op _ a => by
    rw [Val.erase, evalValue, a.evalValue_erase σ, a.erase_ty]
    simp only [Val.eval]
    cases a.eval σ with
    | error _ => rfl
    | ok v =>
      simp only [Except.map, bind, Except.bind]
      cases applyUnOp op v with
      | error _ => rfl
      | ok w =>
        cases op <;> cases ‹PrimTy› <;> simp only [unopCheck] <;> (try rfl) <;>
          cases checkArith _ w <;> rfl

end

/-- Every path erases to a storage-kind expression. -/
theorem SPath.erase_kind {T : Ty} : (p : SPath C Γ T) → p.erase.kind = .storage
  | .alias .. => rfl
  | .loc l => by cases l <;> rfl

theorem Loc.erase_kind {T : Ty} (l : Loc C Γ T) : l.erase.kind = .storage :=
  SPath.erase_kind (.loc l)

/-- A source is read into a storage value as `rhsToSVal` reads it. -/
theorem Src.rhsToSVal_erase (σ : State) {T : Ty} :
    (r : Src C Γ T) → rhsToSVal σ r.erase = (r.value σ).map (σ, ·)
  | .val v => by
    rw [rhsToSVal, if_pos (by rw [Src.erase, v.erase_ty]; rfl)]
    simp only [Src.erase, v.evalValue_erase σ, Src.value]
    cases v.eval σ <;> rfl
  | .copy p h => by
    rw [rhsToSVal, if_neg (by rw [Src.erase, p.erase_ty]; simp [Ty.isPrimitive])]
    simp only [Src.erase, p.erase_kind, p.erase_ty, Ty.mapFree_sound h, Bool.false_eq_true,
      if_false, p.resolveS_erase σ, Src.value]
    cases p.resolve σ <;> rfl

/-- The place a write to a location reaches, as `resolveLoc` finds it. -/
theorem Loc.resolveLoc_erase (σ : State) {T : Ty} :
    (l : Loc C Γ T) → resolveLoc σ l.erase =
      (l.target σ).map fun r => (σ, Semantics.Loc.storage r.1 r.2)
  | .root r _ _ => by
    rw [Loc.erase, resolveLoc]
    cases ‹Ty› <;> rfl
  | .field b f h => by
    rw [Loc.erase, resolveLoc]
    simp only
    rw [resolveS, b.resolveS_erase σ]
    simp only [Loc.target, Loc.resolve]
    cases b.resolve σ <;> simp [Except.map] <;> rfl
  | .mapIndex b i => by
    rw [Loc.erase, resolveLoc]
    simp only
    rw [b.resolveS_erase σ]
    simp only [Loc.target, Loc.resolve]
    cases b.resolve σ with
    | error _ => rfl
    | ok r =>
      simp only [Except.map, bind, Except.bind]
      rw [evalInt_pure (i.evalValue_erase σ)]
      cases i.eval σ with
      | error _ => rfl
      | ok v => cases v <;> rfl
  | .arrIndex b i => by
    rw [Loc.erase, resolveLoc]
    simp only
    rw [b.resolveS_erase σ]
    simp only [Loc.target, Loc.resolve]
    cases b.resolve σ with
    | error _ => rfl
    | ok r =>
      simp only [Except.map, bind, Except.bind]
      rw [evalInt_pure (i.evalValue_erase σ)]
      cases i.eval σ with
      | error _ => rfl
      | ok v => cases v <;> rfl

/-- A nested storage write, as `execAssignNested` does it: the source
first, then the target (solc's order). -/
theorem Loc.execAssignNested_erase (σ : State) {T : Ty} (l : Loc C Γ T) (r : Src C Γ T) :
    execAssignNested σ l.erase r.erase = (Stmt.assign l r : Stmt C Γ Γ).run σ := by
  rw [execAssignNested, Loc.erase_kind]
  simp only [Stmt.run]
  rw [r.rhsToSVal_erase σ]
  cases r.value σ with
  | error _ => rfl
  | ok sv =>
    simp only [Except.map, bind, Except.bind]
    rw [Loc.resolveLoc_erase σ]
    cases Loc.target σ l <;> rfl

/-- A storage write, as `execAssign` does it: a state variable at its root,
anything else through `execAssignNested`. -/
theorem Loc.execAssign_erase (σ : State) {T : Ty} (l : Loc C Γ T) (r : Src C Γ T) :
    execAssign σ l.toPlace r.erase = (Stmt.assign l r : Stmt C Γ Γ).run σ := by
  cases l with
  | root x hΓ h =>
    simp only [Stmt.run, Loc.toPlace, SPath.toPlace, SPath.erase, Loc.erase]
    rw [execAssign]
    simp only
    rw [if_pos (by cases T <;> rfl), r.rhsToSVal_erase σ]
    cases r.value σ <;> simp [Except.map, Loc.target] <;> rfl
  | field b f h => exact Loc.execAssignNested_erase σ (.field b f h) r
  | mapIndex b i => exact Loc.execAssignNested_erase σ (.mapIndex b i) r
  | arrIndex b i => exact Loc.execAssignNested_erase σ (.arrIndex b i) r

mutual

/-- **Adequacy.** A kernel statement runs as the interpreter runs its erasure,
from every state.  `alice.age = x + 1;` saves `x + 1` at `alice.age`;
`Person storage p = alice;` binds `p` to `alice`'s path. -/
theorem Stmt.run_eq (σ : State) {Γ Γ' : Ctx} : (s : Stmt C Γ Γ') → execStmt σ s.erase = s.run σ
  | .assign l r => by rw [Stmt.erase, execStmt, l.execAssign_erase σ r]
  | .rebind x _ r => by
    simp only [Stmt.run]
    rw [Stmt.erase, execStmt, execAssign]
    simp only [PlaceExpr.var, Field.identity]
    rw [if_neg (by simp), r.resolveS_erase σ]
    cases r.resolve σ <;> rfl
  | .assignLocal x _ r => by
    simp only [Stmt.run]
    rw [Stmt.erase, execStmt, execAssign]
    simp only [PlaceExpr.var, Field.primitive]
    rw [r.evalValue_erase σ]
    cases r.eval σ <;> rfl
  | .declLocal p x _ none => by
    simp only [Stmt.erase, Option.map]
    cases p <;> (rw [execStmt]; rfl)
  | .declLocal _ x _ (some e) => by
    simp only [Stmt.run, Stmt.erase, Option.map]
    rw [execStmt]
    simp only [e.evalValue_erase σ]
    cases e.eval σ <;> rfl
  | .declStorage capture _ x _ init => by
    simp only [Stmt.run]
    cases capture <;>
    · simp only [Stmt.erase, Bool.false_eq_true, if_false, if_true]
      rw [execStmt]
      simp only [init.resolveS_erase σ]
      cases init.resolve σ <;> rfl
  | .delete l => by
    simp only [Stmt.run]
    rw [Stmt.erase, execStmt]
    simp only [Loc.toPlace, SPath.toPlace]
    rw [SPath.erase_kind (.loc l)]
    simp only
    rw [SPath.resolveS_erase σ (.loc l)]
    simp only [SPath.resolve]
    cases l.resolve σ <;> rfl
  | .ite c thn els => by
    simp only [Stmt.run]
    rw [Stmt.erase, execStmt, c.evalValue_erase σ]
    cases c.eval σ with
    | error _ => rfl
    | ok v =>
      cases v with
      | int _ => rfl
      | bool b =>
        cases b
        · exact els.run_eq σ
        · exact thn.run_eq σ
  | .require c => by
    simp only [Stmt.run]
    rw [Stmt.erase, execStmt, c.evalValue_erase σ]
    cases c.eval σ with
    | error _ => rfl
    | ok v => cases v with
      | int _ => rfl
      | bool b => cases b <;> rfl
  | .assert c => by
    simp only [Stmt.run]
    rw [Stmt.erase, execStmt, c.evalValue_erase σ]
    cases c.eval σ with
    | error _ => rfl
    | ok v => cases v with
      | int _ => rfl
      | bool b => cases b <;> rfl
  | .revert => by rw [Stmt.erase, execStmt]; rfl

/-- Adequacy for a block. -/
theorem Prog.run_eq (σ : State) {Γ Γ' : Ctx} : (P : Prog C Γ Γ') → execBlock σ P.erase = P.run σ
  | .nil => by rw [Prog.erase, execBlock]; rfl
  | .cons s P => by
    rw [Prog.erase, execBlock, s.run_eq σ, Prog.run]
    cases s.run σ with
    | error _ => rfl
    | ok σ' => exact P.run_eq σ'

end

end Kernel
end Solidity
