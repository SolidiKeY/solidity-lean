import Solidity.Semantics.Run

/-!
# The value-level erasure

What the closer's terms, read on the erasure (`EState`, an update's result
under decision U1 of `docs/intrinsic.md`), see of the typed run, below the
statements: a typed result against an untyped one (`TRes.Agrees`: the
value erased, the same `revert` or `panic`; a typed `diverge` and a typed
`exhausted` against anything), and each storage, heap and state operation
against its untyped namesake (`SRef.erase_field`, `MAddr.erase`,
`writeAddr_erase`, `opStoreT_erase`, `bumpStoreT_erase`,
`TRun.clearT_erase`, …), from `Semantics/StorageErase.lean` and
`Semantics/HeapErase.lean`.  The rules' soundness (`Calculus/Sound*.lean`)
reads the typed run against the rules' terms through these
(`Calculus/LowerRun.lean`); no program is evaluated on the erasure.

A storage copy overlays a struct by position in the typed run and by name in
the erasure (`SVal.overlay_erase`), which agree since no struct repeats a
member name (`structDef_nodup`, decision 16).  A `bool` mapping key is
hashed as `0`/`1` by both (`Value.keyAt`, `PrimTy.key`; decisions 10 and 14).
-/

namespace Solidity

open Semantics (Value Res lookupBy)

variable {C : Contract}

/-! ## Agreement of results -/

/-- A typed result against an untyped one: the value erased, the same
`revert` or `panic`; a typed `diverge` or `exhausted` against anything. -/
def TRes.Agrees {α β : Type} (f : α → β) : TRes α → Res β → Prop
  | .ok a, u => u = .ok (f a)
  | .error .revert, u => u = .error .revert
  | .error .panic, u => u = .error .panic
  | .error .diverge, _ => True
  | .error .exhausted, _ => True

namespace TRes.Agrees

variable {α β γ δ : Type} {f : α → β} {g : γ → δ}

theorem pure (a : α) : TRes.Agrees f (.ok a) (.ok (f a)) := rfl

theorem bind {t : TRes α} {u : Res β} (h : TRes.Agrees f t u) {k : α → TRes γ}
    {k' : β → Res δ} (hk : ∀ a, TRes.Agrees g (k a) (k' (f a))) :
    TRes.Agrees g (t >>= k) (u >>= k') := by
  match t, h with
  | .ok a, h => subst h; exact hk a
  | .error .revert, h => subst h; rfl
  | .error .panic, h => subst h; rfl
  | .error .diverge, _ => trivial
  | .error .exhausted, _ => trivial

theorem map {t : TRes α} {u : Res β} (h : TRes.Agrees f t u) {k : α → γ} {k' : β → δ}
    (hk : ∀ a, k' (f a) = g (k a)) : TRes.Agrees g (k <$> t) (k' <$> u) := by
  match t, h with
  | .ok a, h => subst h; exact congrArg Except.ok (hk a)
  | .error .revert, h => subst h; rfl
  | .error .panic, h => subst h; rfl
  | .error .diverge, _ => trivial
  | .error .exhausted, _ => trivial

theorem ofOpt (x : Option α) : TRes.Agrees f (TRes.ofOpt x) (toRes f x) := by
  cases x <;> rfl

theorem of_eq {a : α} {u : Res β} (h : u = .ok (f a)) : TRes.Agrees f (.ok a) u := h

/-- A typed result against an untyped one followed by a step that only
converts the value. -/
theorem bind_pure {t : TRes α} {u : Res β} (h : TRes.Agrees f t u) {k' : β → Res δ}
    {g' : α → δ} (hk : ∀ a, k' (f a) = .ok (g' a)) : TRes.Agrees g' t (u >>= k') := by
  match t, h with
  | .ok a, h => subst h; exact hk a
  | .error .revert, h => subst h; rfl
  | .error .panic, h => subst h; rfl
  | .error .diverge, _ => trivial
  | .error .exhausted, _ => trivial

theorem congr {f' : α → β} {t : TRes α} {u : Res β} (h : TRes.Agrees f t u)
    (hf : ∀ a, f a = f' a) : TRes.Agrees f' t u := by
  match t, h with
  | .ok a, h => subst h; exact congrArg Except.ok (hf a)
  | .error .revert, h => exact h
  | .error .panic, h => exact h
  | .error .diverge, _ => trivial
  | .error .exhausted, _ => trivial

end TRes.Agrees

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

theorem SRef.erase_field {s f : Name} {T : Ty} (r : SRef C (.ref (.struct s)))
    (h : C.fieldType s f = some T) :
    (r.field h).erase = (r.root, r.path.erase ++ [.field f]) := by
  simp only [SRef.field, SRef.erase, SRef.append, Path.erase_append]
  rfl

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

theorem Value.toMVal_erase {H : HTy} {p : PrimTy} (x : p.Denote) :
    (PrimTy.erase x).toMVal = MVal.erase (H := H) (.prim p) x := by
  cases p <;> rfl

theorem Src.valueT_noPanic (σ : State C Γ) {T : Ty} (r : Src C Γ T) : (r.valueT σ).NoPanic := by
  cases r with
  | val v => exact (v.evalT_noPanic σ).bind fun _ => fun h => nomatch h
  | copy p _ => exact (p.resolveT_noPanic σ).bind fun _ => TRes.NoPanic.ofOpt _

theorem State.withHeap_erase (σ : State C Γ) (hp : Heap σ.H) :
    (σ.withHeap hp).erase = σ.erase.withGlob { σ.erase.glob with heap := hp.erase } := rfl

theorem State.withGlob_adopt {α : HTy → Type} (σ : State C Γ) (g : Grown σ.H α) :
    σ.erase.withGlob (σ.adopt g).1.erase.glob = (σ.adopt g).1.erase := by
  simp only [State.adopt, State.erase, EState.withGlob, EState.ofGlob, EState.glob,
    TEnv.erase_wk]

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

theorem writeAddr_erase (σ : State C Γ) {T : Ty} (a : MAddr σ.H T) (v : MVal σ.H T) :
    writeAddr σ.erase.glob (MVal.erase T v) a.erase =
      toRes (fun hp : Heap σ.H => { σ.erase.glob with heap := hp.erase }) (σ.heap.writeAddr a v) := by
  cases a with
  | field r h => exact Heap.memWriteField_erase (σ := σ.erase.glob) rfl r h v
  | index r a i => exact Heap.memWriteIndex_erase (σ := σ.erase.glob) rfl r a i v

theorem readLoc_erase (σ : State C Γ) {p : PrimTy} (a : MAddr σ.H (.prim p)) :
    Semantics.readLoc σ.erase.glob a.erase = toRes PrimTy.erase (σ.heap.readAddr a) := by
  cases a with
  | field r h =>
    simp only [Semantics.readLoc, MAddr.erase, Heap.getObj_erase (σ := σ.erase.glob) rfl r, bind,
      Except.bind]
    show (match lookupBy _ (MFields.erase _ (σ.heap.get r)) with
      | some v => v.asValue | none => .error .undef) = _
    rw [MFields.lookupBy_erase _ (σ.heap.get r) h]
    exact MVal.asValue_erase_prim _
  | index r a i =>
    simp only [Semantics.readLoc, MAddr.erase, Heap.getObj_erase (σ := σ.erase.glob) rfl r, bind,
      Except.bind, MObj.erase_arr a (σ.heap.get r), Heap.readAddr, Heap.index]
    by_cases h0 : 0 ≤ i
    · by_cases hl : i.toNat < (MObj.elems a (σ.heap.get r)).length
      · simp only [List.length_map, h0, hl, and_self, ↓reduceDIte, ↓reduceIte,
          List.get_eq_getElem, List.getElem_map, List.getElem?_eq_getElem hl, toRes]
        exact MVal.asValue_erase_prim _
      · simp only [List.length_map, h0, hl, and_false, ↓reduceDIte, ↓reduceIte,
          List.getElem?_eq_none (Nat.le_of_not_lt hl), toRes]
    · simp only [h0, false_and, ↓reduceDIte, ↓reduceIte, toRes]

theorem writeLoc_eq (s : Semantics.State) (a : Semantics.Addr) (v : Value) :
    Semantics.writeLoc s a v = writeAddr s v.toMVal a := by
  cases a <;> rfl

/-! ### Compound assignments and `++` -/

theorem bind_bind_eq {ε α β γ : Type} {x : Except ε α} {f : α → Except ε β}
    {K : β → Except ε γ} {y : Except ε β} (h : x >>= f = y) :
    (x >>= fun a => f a >>= K) = y >>= K := by
  rw [← h, bind_assoc]

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

theorem compound_erase' {op : BinOp} (hop : op.hasCompoundAssign = true) {p : PrimTy}
    (hp : p.isNumeric = true) (x y : p.Denote) :
    (Semantics.applyBinOp op (PrimTy.erase x) (PrimTy.erase y) >>= Semantics.checkArith (.prim p)) =
      toRes PrimTy.erase (compoundT op p (PrimTy.key x) (PrimTy.key y)) := by
  rw [PrimTy.erase_numeric hp x, PrimTy.erase_numeric hp y]
  exact compound_erase hop hp _ _

theorem asInt_erase_numeric {p : PrimTy} (hp : p.isNumeric = true) (x : p.Denote) :
    (PrimTy.erase x).asInt = .ok (PrimTy.key x) := by
  rw [PrimTy.erase_numeric hp x]
  rfl

theorem bump_erase {p : PrimTy} (hp : p.isNumeric = true) (op : IncDec) (x : Int) :
    Semantics.checkArith (.prim p) (.int (if op.isIncrement then x + 1 else x - 1)) =
      toRes PrimTy.erase (bumpT op p x) :=
  PrimTy.checkArith_ofInt hp _

theorem opStoreT_erase (σ : State C Γ) {op : BinOp} (hop : op.hasCompoundAssign = true)
    {p : PrimTy} (hp : p.isNumeric = true) (r : SRef C (.prim p)) (v : p.Denote) :
    TRes.Agrees (fun o : Out C σ.H Γ => o.st.erase) (opStoreT σ op r v)
      (σ.erase.withGlob <$> opStore σ.erase.glob op p r.root r.path.erase (PrimTy.erase v)) := by
  simp only [opStoreT, opStore, Storage.findStorage_erase (σ := σ.erase.glob) rfl r]
  cases σ.storage.find r with
  | none => rfl
  | some old =>
    simp only [TRes.ofOpt, toRes, ok_bind, SVal.asValue_erase_prim]
    rw [bind_bind_eq (compound_erase' hop hp _ _)]
    cases compoundT op p (PrimTy.key (SVal.view old)) (PrimTy.key v) with
    | none => rfl
    | some new =>
      simp only [toRes, ok_bind, Value.toSVal_erase,
        Storage.saveStorage_erase (σ := σ.erase.glob) rfl r]
      cases σ.storage.save r (SVal.prim new) <;> rfl

theorem opMemT_erase (σ : State C Γ) {op : BinOp} (hop : op.hasCompoundAssign = true)
    {p : PrimTy} (hp : p.isNumeric = true) (a : MAddr σ.H (.prim p)) (v : p.Denote) :
    TRes.Agrees (fun o : Out C σ.H Γ => o.st.erase) (opMemT σ op a v)
      (σ.erase.withGlob <$> opMem σ.erase.glob op p a.erase (PrimTy.erase v)) := by
  simp only [opMemT, opMem, readLoc_erase σ a]
  cases σ.heap.readAddr a with
  | none => rfl
  | some old =>
    simp only [TRes.ofOpt, toRes, ok_bind]
    rw [bind_bind_eq (compound_erase' hop hp _ _)]
    cases compoundT op p (PrimTy.key (p := p) old) (PrimTy.key v) with
    | none => rfl
    | some new =>
      simp only [toRes, ok_bind, writeLoc_eq, Value.toMVal_erase (H := σ.H),
        writeAddr_erase σ a]
      cases σ.heap.writeAddr a new <;> rfl

theorem bumpStoreT_erase (σ : State C Γ) (op : IncDec) {p : PrimTy} (hp : p.isNumeric = true)
    (r : SRef C (.prim p)) {k' : Semantics.State × Value → EState C Γ × Value}
    (hk : ∀ τ v, k' (τ, v) = (σ.erase.withGlob τ, v)) :
    TRes.Agrees (fun x : Out C σ.H Γ × p.Denote => (x.1.st.erase, PrimTy.erase x.2))
      (bumpStoreT σ op r) (k' <$> bumpStore σ.erase.glob op p r.root r.path.erase) := by
  simp only [bumpStoreT, bumpStore, Storage.findStorage_erase (σ := σ.erase.glob) rfl r]
  cases σ.storage.find r with
  | none => rfl
  | some old =>
    simp only [TRes.ofOpt, toRes, ok_bind, SVal.asValue_erase_prim, asInt_erase_numeric hp,
      bump_erase hp]
    cases bumpT op p (PrimTy.key (SVal.view old)) with
    | none => rfl
    | some new =>
      simp only [toRes, ok_bind, Value.toSVal_erase,
        Storage.saveStorage_erase (σ := σ.erase.glob) rfl r]
      cases σ.storage.save r (SVal.prim new) with
      | none => rfl
      | some st =>
        refine TRes.Agrees.of_eq ?_
        simp only [ok_bind]
        cases op.isPre <;> exact congrArg Except.ok (hk _ _)

theorem bumpMemT_erase (σ : State C Γ) (op : IncDec) {p : PrimTy} (hp : p.isNumeric = true)
    (a : MAddr σ.H (.prim p)) {k' : Semantics.State × Value → EState C Γ × Value}
    (hk : ∀ τ v, k' (τ, v) = (σ.erase.withGlob τ, v)) :
    TRes.Agrees (fun x : Out C σ.H Γ × p.Denote => (x.1.st.erase, PrimTy.erase x.2))
      (bumpMemT σ op a) (k' <$> bumpMem σ.erase.glob op p a.erase) := by
  simp only [bumpMemT, bumpMem, readLoc_erase σ a]
  cases σ.heap.readAddr a with
  | none => rfl
  | some old =>
    simp only [TRes.ofOpt, toRes, ok_bind, asInt_erase_numeric hp, bump_erase hp]
    cases bumpT op p (PrimTy.key (p := p) old) with
    | none => rfl
    | some new =>
      simp only [toRes, ok_bind, writeLoc_eq, Value.toMVal_erase (H := σ.H), writeAddr_erase σ a]
      cases σ.heap.writeAddr a new with
      | none => rfl
      | some hp' =>
        refine TRes.Agrees.of_eq ?_
        simp only [ok_bind]
        cases op.isPre <;> exact congrArg Except.ok (hk _ _)

theorem LTy.TDenote.erase_val {H : HTy} {p : PrimTy} (x : (LTy.val p).TDenote C H) :
    LTy.TDenote.erase (.val p) x = PrimTy.erase (p := p) x := rfl

theorem State.erase_get (σ : State C Γ) {t : LTy} (i : Idx Γ t) :
    Env.get i σ.erase.env = LTy.TDenote.erase t (TEnv.get i σ.env) :=
  TEnv.get_erase i σ.env

/-! ### Calls and payments -/

theorem State.withEnv_erase {Δ : Ctx} (σ : State C Γ) (e : TEnv C σ.H Δ) :
    (σ.withEnv e).erase = σ.erase.withEnv (TEnv.erase Δ e) := rfl

end Eval

/-! ## Statements -/

theorem PrimTy.uint_nonneg (x : PrimTy.uint.Denote) : 0 ≤ x.1 := by
  have h := x.2
  simp only [PrimTy.inRange, decide_eq_true_eq] at h
  exact h.1

namespace TRun

variable {Γ : Ctx}

theorem State.allocDefault_glob (σ : State C Γ) (R : RefTy) (hm : (Ty.ref R).mapFree = true) :
    σ.erase.withGlob (σ.allocDefault R hm).1.erase.glob = (σ.allocDefault R hm).1.erase :=
  State.withGlob_adopt σ _

theorem State.erase_env_adopt {α : HTy → Type} (σ : State C Γ) (g : Grown σ.H α) :
    (σ.adopt g).1.erase.env = σ.erase.env := TEnv.erase_wk g.ext Γ σ.env

theorem clearT_erase (σ : State C Γ) {T : Ty} (a : MAddr σ.H T) (hm : T.mapFree = true) :
    TRes.Agrees (fun o : Out C σ.H Γ => o.st.erase) (clearT σ a hm)
      (σ.erase.withGlob <$> memClear σ.erase.glob a.erase T) := by
  cases T with
  | prim p =>
    show TRes.Agrees _ (do
        let hp ← TRes.ofOpt (σ.heap.writeAddr a (PrimTy.dflt p))
        pure (⟨σ.withHeap hp, List.prefix_refl _⟩ : Out C σ.H Γ))
      (σ.erase.withGlob <$> writeAddr σ.erase.glob (PrimTy.default p).toMVal a.erase)
    rw [← PrimTy.erase_dflt, Value.toMVal_erase (H := σ.H), writeAddr_erase σ a]
    cases σ.heap.writeAddr a (PrimTy.dflt p) <;> rfl
  | ref R =>
    simp only [clearT, memClear]
    rw [State.allocDefault_erase σ R hm, ok_bind]
    dsimp only
    have hw := writeAddr_erase (σ.allocDefaultG R hm).st (a.wk (σ.allocDefaultG R hm).ext)
      (σ.allocDefaultG R hm).val
    rw [MAddr.erase_wk] at hw
    rw [show writeAddr (σ.allocDefault R hm).1.erase.glob (.ref (σ.allocDefault R hm).2.id)
      a.erase = _ from hw]
    cases (σ.allocDefaultG R hm).st.heap.writeAddr (a.wk (σ.allocDefaultG R hm).ext)
      (σ.allocDefaultG R hm).val with
    | none => rfl
    | some hp =>
      refine TRes.Agrees.of_eq (congrArg Except.ok ?_)
      show σ.erase.withGlob _ = ((σ.allocDefaultG R hm).st.withHeap hp).erase
      rw [State.withHeap_erase]
      simp only [EState.withGlob]
      rw [show (σ.allocDefaultG R hm).st.erase.env = σ.erase.env from State.erase_env_adopt σ _]

end TRun

namespace TRes.Agrees

variable {α β γ : Type} {f : α → β}

/-- An agreement ending in a value: the untyped side ends there too. -/
theorem eq_ok {t : TRes α} {u : Res β} (h : TRes.Agrees f t u) {a : α} (ht : t = .ok a) :
    u = .ok (f a) := by
  subst ht; exact h

/-- An agreement with a typed halt that is not a divergence nor an
exhaustion: the untyped side halts too. -/
theorem eq_error {t : TRes α} {u : Res β} (h : TRes.Agrees f t u) {e : THalt}
    (ht : t = .error e) (hd : e ≠ .diverge) (hx : e ≠ .exhausted) : ∃ e', u = .error e' := by
  subst ht
  cases e with
  | revert => exact ⟨_, h⟩
  | panic => exact ⟨_, h⟩
  | diverge => exact absurd rfl hd
  | exhausted => exact absurd rfl hx

/-- An agreement read through an equation of the untyped side. -/
theorem of_eq_right {t : TRes α} {u u' : Res β} (h : TRes.Agrees f t u) (e : u = u') :
    TRes.Agrees f t u' := e ▸ h

/-- A pair's agreement read at its first component. -/
theorem bind_fst {α₁ α₂ β₁ β₂ : Type} {f₁ : α₁ → β₁} {f₂ : α₂ → β₂} {t : TRes (α₁ × α₂)}
    {u : Res (β₁ × β₂)} (h : TRes.Agrees (fun x => (f₁ x.1, f₂ x.2)) t u) :
    TRes.Agrees f₁ (t >>= fun x => Pure.pure x.1) (u >>= fun y => Pure.pure y.1) :=
  TRes.Agrees.bind h fun _ => rfl

end TRes.Agrees

end Solidity
