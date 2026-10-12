import Solidity.Semantics.Run

/-!
# The value-level erasure

The typed run's values against the untyped interpreter's, below the
statements: an expression's evaluators do not panic (`Val.evalT_noPanic`
and kin), and the value-level erasure lemmas the EVM backend and the
Theory's abstraction read (`MAddr.erase`, `newArrT_erase`, `compound_erase`,
`evalBinop_short`/`_long`, …), from `Semantics/StorageErase.lean` and
`Semantics/HeapErase.lean`.  Since W9.8.3 the rules' soundness reads the
typed run against typed terms with nothing erased (`Calculus/LowerRun.lean`,
`TRes.AgreesO`); the statement-level erasure lemmas (`TRes.Agrees`,
`opStoreT_erase`, …) are gone.

A storage copy overlays a struct by position in the typed run and by name in
the erasure (`SVal.overlay_erase`), which agree since no struct repeats a
member name (`structDef_nodup`, decision 16).  A `bool` mapping key is
hashed as `0`/`1` by both (`Value.keyAt`, `PrimTy.key`; decisions 10 and 14).
-/

namespace Solidity

open Semantics (Value Res lookupBy)

variable {C : Contract}

/-! ## Typed results -/

/-- A typed result that does not panic (an expression's: it reverts or
diverges only). -/
def TRes.NoPanic {α : Type} (t : TRes α) : Prop := t ≠ .error .panic

theorem ok_bind {ε α β : Type} (a : α) (k : α → Except ε β) :
    (Except.ok a : Except ε α) >>= k = k a := rfl

theorem TRes.NoPanic.bind {α γ : Type} {t : TRes α} (h : t.NoPanic) {k : α → TRes γ}
    (hk : ∀ a, (k a).NoPanic) : (t >>= k).NoPanic := by
  match t with
  | .ok a => exact hk a
  | .error e => exact fun h' => h (by cases h'; rfl)

theorem TRes.NoPanic.ofOpt {α : Type} (x : Option α) : (TRes.ofOpt x).NoPanic := by
  cases x <;> exact fun h => nomatch h

/-! ## Expressions -/

section Eval

variable {Γ : Ctx}

theorem SVal.asValue_erase_prim {p : PrimTy} (v : SVal (.prim p)) :
    v.erase.asValue = .ok (PrimTy.erase (SVal.view v)) := by
  cases v with
  | prim x => rw [SVal.erase_prim]; cases p <;> rfl

theorem MVal.asValue_erase_prim {H : HTy} {p : PrimTy} (x : MVal H (.prim p)) :
    (MVal.erase (.prim p) x).asValue = .ok (PrimTy.erase (p := p) x) := by
  cases p <;> rfl

theorem SRef.erase_index {R : RefTy} {k : PrimTy} {V : Ty} (r : SRef C (.ref R))
    (it : IndexTy R k V) (i : Int) : (r.index it i).erase = (r.root, r.path.erase ++ [.at i]) := by
  simp only [SRef.index, SRef.erase, SRef.append, Path.erase_append, Path.erase_index]

/-- `a && b`/`a || b` decided by `a`: the untyped operator does not read `b`. -/
theorem evalBinop_short {op : BinOp} {p : PrimTy} {x : p.Denote} {y : (op.ret p).Denote}
    (hs : op.shortT x = some y) (u : Res Value) :
    evalBinop op p (PrimTy.erase x) u = .ok (PrimTy.erase y) := by
  cases op <;> cases p <;> simp only [BinOp.shortT, reduceCtorEq] at hs <;> cases x <;>
    simp only [boolT, Bool.false_eq_true, ↓reduceIte, reduceCtorEq, Option.some.injEq] at hs <;>
    subst hs <;> rfl

/-- Otherwise the untyped operator reads `b` first. -/
theorem evalBinop_long {op : BinOp} {p : PrimTy} {x : p.Denote} (hs : op.shortT x = none)
    (u : Res Value) :
    evalBinop op p (PrimTy.erase x) u = u >>= fun w => evalBinop op p (PrimTy.erase x) (.ok w) := by
  cases op <;> cases p <;> cases u <;> first
    | rfl
    | (cases x <;> first | rfl | simp only [BinOp.shortT, boolT, ↓reduceIte, reduceCtorEq,
        Bool.false_eq_true] at hs)

/-! ### An expression does not panic -/

mutual

theorem SPath.resolveT_noPanic (σ : State C Γ) : {T : Ty} → (b : SPath C Γ T) →
    (b.resolveT σ).NoPanic
  | _, .alias i => by
    show (match (TEnv.get i σ.env : Option (SRef C _)) with
      | some r => .ok r
      | none => .error .revert : TRes _).NoPanic
    cases (TEnv.get i σ.env : Option (SRef C _)) <;> exact fun h => nomatch h
  | _, .loc l => l.resolveT_noPanic σ

theorem Loc.resolveT_noPanic (σ : State C Γ) : {T : Ty} → (l : Loc C Γ T) →
    (l.resolveT σ).NoPanic
  | _, .root .. => fun h => nomatch h
  | _, .field b _ _ => (b.resolveT_noPanic σ).bind fun _ => fun h => nomatch h
  | _, .index _ b i => (b.resolveT_noPanic σ).bind fun _ => (i.evalT_noPanic σ).bind fun _ =>
      (TRes.NoPanic.ofOpt _).bind fun _ => fun h => nomatch h

theorem MPath.mvalT_noPanic (σ : State C Γ) : {T : Ty} → (b : MPath C Γ T) →
    (b.mvalT σ).NoPanic
  | _, .var i _ => by
    show (match (TEnv.get i σ.env : Option (HRef σ.H _)) with
      | some r => .ok r
      | none => .error .revert : TRes _).NoPanic
    cases (TEnv.get i σ.env : Option (HRef σ.H _)) <;> exact fun h => nomatch h
  | _, .loc l => (l.addrT_noPanic σ).bind fun _ => TRes.NoPanic.ofOpt _

theorem MLoc.addrT_noPanic (σ : State C Γ) : {T : Ty} → (l : MLoc C Γ T) →
    (l.addrT σ).NoPanic
  | _, .field b _ _ => (b.mvalT_noPanic σ).bind fun _ => fun h => nomatch h
  | _, .index _ b i => (b.mvalT_noPanic σ).bind fun _ => (i.evalT_noPanic σ).bind fun _ =>
      fun h => nomatch h

theorem Val.evalT_noPanic (σ : State C Γ) : {p : PrimTy} → (v : Val C Γ p) →
    (v.evalT σ).NoPanic
  | _, .simple _ => fun h => nomatch h
  | _, .read l => (l.resolveT_noPanic σ).bind fun _ => (TRes.NoPanic.ofOpt _).bind fun _ =>
      fun h => nomatch h
  | _, .binop op _ hq a b => by
    subst hq
    refine (a.evalT_noPanic σ).bind fun x => ?_
    show (match op.shortT x with
      | some y => pure y
      | none => do
        let y ← b.evalT σ
        TRes.ofOpt (op.evalT x y) : TRes _).NoPanic
    cases op.shortT x with
    | some _ => exact fun h => nomatch h
    | none => exact (b.evalT_noPanic σ).bind fun _ => TRes.NoPanic.ofOpt _
  | _, .unop op _ hq a => by
    subst hq
    exact (a.evalT_noPanic σ).bind fun _ => TRes.NoPanic.ofOpt _
  | _, .ternary c a b => (c.evalT_noPanic σ).bind fun x => by
    cases x
    · exact b.evalT_noPanic σ
    · exact a.evalT_noPanic σ
  | _, .readMem l => (l.addrT_noPanic σ).bind fun _ => TRes.NoPanic.ofOpt _
  | _, .len b hp => by
    subst hp
    exact (b.resolveT_noPanic σ).bind fun _ => (TRes.NoPanic.ofOpt _).bind fun _ =>
      fun h => nomatch h
  | _, .mlen b hp => by
    subst hp
    exact (b.mvalT_noPanic σ).bind fun _ => fun h => nomatch h

end

/-! ### Sources and right-hand sides -/

theorem Value.toSVal_erase {p : PrimTy} (x : p.Denote) :
    (PrimTy.erase x).toSVal = (SVal.prim x).erase := by
  rw [SVal.erase_prim]; cases p <;> rfl

theorem Src.valueT_noPanic (σ : State C Γ) {T : Ty} (r : Src C Γ T) : (r.valueT σ).NoPanic := by
  cases r with
  | val v => exact (v.evalT_noPanic σ).bind fun _ => fun h => nomatch h
  | copy p _ => exact (p.resolveT_noPanic σ).bind fun _ => TRes.NoPanic.ofOpt _

theorem newArrT_erase : (R : RefTy) → (n : PrimTy.uint.Denote) → (h : R.newArrOk = true) →
    (newArrT R n h).erase = newArrVal R n.1
  | .array E, n, _ => by
    simp only [newArrT, newArrVal, SVal.erase, SVec.erase_ofList, SList.erase_nil,
      List.map_replicate, SVal.dflt_erase]
  | .struct _, _, h | .fixed .., _, h | .mapping .., _, h => by
    simp only [RefTy.newArrOk, Bool.false_eq_true] at h

/-! ### Memory addresses -/

/-- The untyped address. -/
def MAddr.erase {H : HTy} {T : Ty} : MAddr H T → Semantics.Addr
  | .field (f := f) r _ => .memoryField r.id f
  | .index r _ i => .memoryIndex r.id i

theorem MAddr.erase_wk {H H' : HTy} (e : H <+: H') {T : Ty} (a : MAddr H T) :
    (a.wk e).erase = a.erase := by
  cases a <;> rfl

theorem writeLoc_eq (s : Semantics.State) (a : Semantics.Addr) (v : Value) :
    Semantics.writeLoc s a v = writeAddr s v.toMVal a := by
  cases a <;> rfl

/-! ### Compound assignments and `++` -/

theorem PrimTy.erase_numeric {p : PrimTy} (hp : p.isNumeric = true) (x : p.Denote) :
    PrimTy.erase x = .int (PrimTy.key x) := by
  cases p <;> first | rfl | cases hp

theorem compound_erase {op : BinOp} (hop : op.hasCompoundAssign = true) {p : PrimTy}
    (hp : p.isNumeric = true) (x y : Int) :
    (Semantics.applyBinOp op (.int x) (.int y) >>= Semantics.checkArith (.prim p)) =
      toRes PrimTy.erase (compoundT op p x y) := by
  have hA : op.isArith = true := by
    cases op <;> simp only [BinOp.hasCompoundAssign, Bool.false_eq_true] at hop <;> rfl
  rw [BinOp.applyBinOp_int hA]
  unfold compoundT
  cases BinOp.arithInt op x y with
  | none => rfl
  | some n => exact PrimTy.checkArith_ofInt hp n

theorem bump_erase {p : PrimTy} (hp : p.isNumeric = true) (op : IncDec) (x : Int) :
    Semantics.checkArith (.prim p) (.int (if op.isIncrement then x + 1 else x - 1)) =
      toRes PrimTy.erase (bumpT op p x) :=
  PrimTy.checkArith_ofInt hp _

theorem LTy.TDenote.erase_val {H : HTy} {p : PrimTy} (x : (LTy.val p).TDenote C H) :
    LTy.TDenote.erase (.val p) x = PrimTy.erase (p := p) x := rfl

end Eval

end Solidity
