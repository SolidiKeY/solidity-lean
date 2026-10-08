import Solidity.Semantics.Core.TypedRun

/-!
# The typed run erases to the scoped run

`Prog.trun_erase` (`docs/intrinsic.md`, "M4 lane", wiring item 4): running
`P` on a typed state `σ` (`Semantics/Core/TypedRun.lean`) and erasing the
state it ends in agrees with running `P` on `σ.erase` with
`Semantics/Core.lean`'s interpreter.  The relation is `TRes.Agrees`: the
same state, the same `revert` or `panic`; a typed `diverge` (a loop with no
last iteration) and a typed `exhausted` (a push onto an array of
`2^256 - 1` elements, `Storage.full`, where the untyped run, which has no
bound, goes on) are matched by any untyped outcome.  So the untyped run is
never stuck where the typed one ends.

Every program is on the bridge: a storage copy overlays a struct by position
in the typed run and by name in the untyped one (`SVal.overlay_erase`), which
agree since no struct repeats a member name (`TyNodup.all`, decision 16).  A
`bool` mapping key is hashed as `0`/`1` by both runs (`Value.keyAt`,
`PrimTy.key`; decisions 10 and 14).

Each operation's agreement is one lemma, from the storage and heap ones of
`Semantics/Core/StorageErase.lean` and `Semantics/Core/HeapErase.lean`; the
statements are each `TRun.*` step against its `Run.*` namesake, given its
sub-programs' agreement (`StepAgrees`), and the run is the recursor over
them.
-/

namespace Solidity.Core

open Semantics (Value Seg Halt Res lookupBy setBy ExtKey ExtResult structDef)

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

theorem Simple.evalT_erase (σ : TState C Γ) {p : PrimTy} (s : Simple C Γ p) :
    s.eval σ.erase = .ok (PrimTy.erase (s.evalT σ)) := by
  cases s with
  | lit n h => cases p <;> first | rfl | simp only [PrimTy.inRange, Bool.false_eq_true] at h
  | bool b => rfl
  | «local» i =>
    show Except.ok (Env.get i (TEnv.erase Γ σ.env)) = _
    rw [TEnv.get_erase]
    rfl
  | env k hp => subst hp; cases k <;> rfl

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


mutual

theorem SPath.resolveT_erase (σ : TState C Γ) : {T : Ty} → (b : SPath C Γ T) →
    TRes.Agrees SRef.erase (b.resolveT σ) (b.resolve σ.erase)
  | _, .alias i => by
    show TRes.Agrees SRef.erase
      (match (TEnv.get i σ.env : Option (SRef C _)) with
        | some r => .ok r
        | none => .error .revert)
      (match (Env.get i (TEnv.erase Γ σ.env) : Option (Name × List Seg)) with
        | some p => pure p
        | none => .error .revert)
    rw [TEnv.get_erase]
    cases (TEnv.get i σ.env : Option (SRef C _)) <;> rfl
  | _, .loc l => l.resolveT_erase σ

theorem Loc.resolveT_erase (σ : TState C Γ) : {T : Ty} → (l : Loc C Γ T) →
    TRes.Agrees SRef.erase (l.resolveT σ) (l.resolve σ.erase)
  | _, .root r h => rfl
  | _, .field b f h => by
    refine TRes.Agrees.bind (b.resolveT_erase σ) fun r => ?_
    exact TRes.Agrees.of_eq (congrArg Except.ok (SRef.erase_field r h).symm)
  | _, .index (k := k) it b i => by
    refine TRes.Agrees.bind (b.resolveT_erase σ) fun r => ?_
    refine TRes.Agrees.bind (i.evalT_erase σ) fun x => ?_
    show TRes.Agrees SRef.erase
      (do TRes.ofOpt (σ.storage.checkIndex r it (PrimTy.key x)); pure (r.atKey it x))
      (do
        let i ← (PrimTy.erase x).keyAt k
        σ.erase.glob.checkIndex r.root r.path.erase i
        pure (r.root, r.path.erase ++ [.at i]))
    rw [PrimTy.keyAt_erase_key, ok_bind,
      Storage.checkIndex_erase (σ := σ.erase.glob) rfl r it]
    refine TRes.Agrees.bind (TRes.Agrees.ofOpt _) fun _ => ?_
    exact TRes.Agrees.of_eq (congrArg Except.ok (SRef.erase_index r it _).symm)

theorem MPath.mvalT_erase (σ : TState C Γ) : {T : Ty} → (b : MPath C Γ T) →
    TRes.Agrees (MVal.erase T) (b.mvalT σ) (b.mval σ.erase)
  | _, .var i _ => by
    refine TRes.Agrees.of_eq ?_
    show Except.ok (Semantics.MVal.ref (Env.get i (TEnv.erase Γ σ.env))) = _
    rw [TEnv.get_erase]
    rfl
  | _, .loc l => l.readT_erase σ

theorem MLoc.readT_erase (σ : TState C Γ) : {T : Ty} → (l : MLoc C Γ T) →
    TRes.Agrees (MVal.erase T) (do TRes.ofOpt (σ.heap.readAddr (← l.addrT σ))) (l.read σ.erase)
  | _, .field b f h => by
    simp only [MLoc.addrT, MLoc.read, bind_assoc, pure_bind]
    refine TRes.Agrees.bind (b.mvalT_erase σ) fun r => ?_
    show TRes.Agrees _ (.ok (σ.heap.field r h)) (do
      match ← σ.erase.glob.getObj r.id with
      | .struct fields =>
        match lookupBy f fields with
        | some v => pure v
        | none => .error .stuck
      | .array _ _ => .error .stuck)
    exact TRes.Agrees.of_eq (Heap.readField_erase (σ := σ.erase.glob) rfl r h)
  | _, .index a b i => by
    simp only [MLoc.addrT, MLoc.read, bind_assoc, pure_bind]
    refine TRes.Agrees.bind (b.mvalT_erase σ) fun r => ?_
    refine TRes.Agrees.bind (i.evalT_erase σ) fun k => ?_
    show TRes.Agrees _ (TRes.ofOpt (σ.heap.index r a k.1)) (do
      match ← σ.erase.glob.getObj r.id with
      | .array elems _ =>
        if h : 0 ≤ k.1 ∧ k.1.toNat < elems.length then pure (elems.get ⟨k.1.toNat, h.2⟩)
        else .error .revert
      | .struct _ => .error .stuck)
    have e := Heap.readIndex_erase (σ := σ.erase.glob) rfl r a k.1
    exact e ▸ TRes.Agrees.ofOpt _

theorem Val.evalT_erase (σ : TState C Γ) : {p : PrimTy} → (v : Val C Γ p) →
    TRes.Agrees PrimTy.erase (v.evalT σ) (v.eval σ.erase)
  | _, .simple s => TRes.Agrees.of_eq (Simple.evalT_erase σ s)
  | _, .read l => by
    refine TRes.Agrees.bind (l.resolveT_erase σ) fun r => ?_
    show TRes.Agrees _ (do let v ← TRes.ofOpt (σ.storage.find r); pure (SVal.view v))
      (do let v ← σ.erase.glob.findStorage r.root r.path.erase; v.asValue)
    rw [Storage.findStorage_erase (σ := σ.erase.glob) rfl r]
    exact TRes.Agrees.bind (TRes.Agrees.ofOpt _) fun v =>
      TRes.Agrees.of_eq (SVal.asValue_erase_prim v)
  | _, .binop op h hq a b => by
    subst hq
    refine TRes.Agrees.bind (a.evalT_erase σ) fun x => ?_
    show TRes.Agrees _ (match op.shortT x with
      | some y => pure y
      | none => do
        let y ← b.evalT σ
        TRes.ofOpt (op.evalT x y)) (evalBinop op _ (PrimTy.erase x) (b.eval σ.erase))
    cases hs : op.shortT x with
    | some y => rw [evalBinop_short hs]; rfl
    | none =>
      rw [evalBinop_long hs]
      refine TRes.Agrees.bind (b.evalT_erase σ) fun y => ?_
      rw [BinOp.evalT_erase op h x y]
      exact TRes.Agrees.ofOpt _
  | _, .unop op h hq a => by
    subst hq
    refine TRes.Agrees.bind (a.evalT_erase σ) fun x => ?_
    show TRes.Agrees _ (TRes.ofOpt (op.evalT x)) _
    rw [UnOp.evalT_erase op h x]
    exact TRes.Agrees.ofOpt _
  | _, .ternary c a b => by
    refine TRes.Agrees.bind (c.evalT_erase σ) fun x => ?_
    cases x
    · exact b.evalT_erase σ
    · exact a.evalT_erase σ
  | _, .readMem l => by
    show TRes.Agrees _ (do TRes.ofOpt (σ.heap.readAddr (← l.addrT σ)))
      (do (← l.read σ.erase).asValue)
    exact TRes.Agrees.bind_pure (l.readT_erase σ) fun x => MVal.asValue_erase_prim x
  | _, .len b hp => by
    subst hp
    refine TRes.Agrees.bind (b.resolveT_erase σ) fun r => ?_
    show TRes.Agrees _ (do let n ← TRes.ofOpt (σ.storage.len r); pure n)
      (arrayLen σ.erase.glob r.root r.path.erase)
    rw [Storage.arrayLen_erase (σ := σ.erase.glob) rfl r]
    cases σ.storage.len r <;> rfl
  | _, .mlen b hp => by
    subst hp
    refine TRes.Agrees.bind (b.mvalT_erase σ) fun r => ?_
    show TRes.Agrees _ (.ok (σ.heap.lenU r)) (memArrayLen σ.erase.glob r.id)
    rw [Heap.memArrayLen_erase (σ := σ.erase.glob) rfl r .dyn]
    rfl

end

/-! ### An expression does not panic -/

mutual

theorem SPath.resolveT_noPanic (σ : TState C Γ) : {T : Ty} → (b : SPath C Γ T) →
    (b.resolveT σ).NoPanic
  | _, .alias i => by
    show (match (TEnv.get i σ.env : Option (SRef C _)) with
      | some r => .ok r
      | none => .error .revert : TRes _).NoPanic
    cases (TEnv.get i σ.env : Option (SRef C _)) <;> exact fun h => nomatch h
  | _, .loc l => l.resolveT_noPanic σ

theorem Loc.resolveT_noPanic (σ : TState C Γ) : {T : Ty} → (l : Loc C Γ T) →
    (l.resolveT σ).NoPanic
  | _, .root .. => fun h => nomatch h
  | _, .field b _ _ => (b.resolveT_noPanic σ).bind fun _ => fun h => nomatch h
  | _, .index _ b i => (b.resolveT_noPanic σ).bind fun _ => (i.evalT_noPanic σ).bind fun _ =>
      (TRes.NoPanic.ofOpt _).bind fun _ => fun h => nomatch h

theorem MPath.mvalT_noPanic (σ : TState C Γ) : {T : Ty} → (b : MPath C Γ T) →
    (b.mvalT σ).NoPanic
  | _, .var .. => fun h => nomatch h
  | _, .loc l => (l.addrT_noPanic σ).bind fun _ => TRes.NoPanic.ofOpt _

theorem MLoc.addrT_noPanic (σ : TState C Γ) : {T : Ty} → (l : MLoc C Γ T) →
    (l.addrT σ).NoPanic
  | _, .field b _ _ => (b.mvalT_noPanic σ).bind fun _ => fun h => nomatch h
  | _, .index _ b i => (b.mvalT_noPanic σ).bind fun _ => (i.evalT_noPanic σ).bind fun _ =>
      fun h => nomatch h

theorem Val.evalT_noPanic (σ : TState C Γ) : {p : PrimTy} → (v : Val C Γ p) →
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

theorem Src.valueT_erase (σ : TState C Γ) {T : Ty} (r : Src C Γ T) :
    TRes.Agrees SVal.erase (r.valueT σ) (r.value σ.erase) := by
  cases r with
  | val v =>
    exact TRes.Agrees.bind (v.evalT_erase σ) fun x =>
      TRes.Agrees.of_eq (congrArg Except.ok (Value.toSVal_erase x))
  | copy p _ =>
    refine TRes.Agrees.bind (p.resolveT_erase σ) fun r => ?_
    show TRes.Agrees _ (TRes.ofOpt (σ.storage.find r))
      (σ.erase.glob.findStorage r.root r.path.erase)
    rw [Storage.findStorage_erase (σ := σ.erase.glob) rfl r]
    exact TRes.Agrees.ofOpt _

theorem Src.valueT_noPanic (σ : TState C Γ) {T : Ty} (r : Src C Γ T) : (r.valueT σ).NoPanic := by
  cases r with
  | val v => exact (v.evalT_noPanic σ).bind fun _ => fun h => nomatch h
  | copy p _ => exact (p.resolveT_noPanic σ).bind fun _ => TRes.NoPanic.ofOpt _

theorem MSrc.mvalT_erase (σ : TState C Γ) {T : Ty} (r : MSrc C Γ T) :
    TRes.Agrees (MVal.erase T) (r.mvalT σ) (r.mval σ.erase) := by
  cases r with
  | val v =>
    exact TRes.Agrees.bind_pure (v.evalT_erase σ) fun x =>
      congrArg Except.ok (Value.toMVal_erase x)
  | ref p =>
    exact TRes.Agrees.bind_pure (p.mvalT_erase σ) fun _ => rfl

/-- The typed state with its storage replaced erases to the untyped one with
the erased storage. -/
theorem TState.withStorage_into (σ : TState C Γ) (st : Storage C) :
    (σ.withStorage st).erase = σ.erase.withGlob (Storage.into σ.erase.glob st) := rfl

theorem TState.withHeap_erase (σ : TState C Γ) (hp : Heap σ.H) :
    (σ.withHeap hp).erase = σ.erase.withGlob { σ.erase.glob with heap := hp.erase } := rfl

theorem TState.withGlob_adopt {α : HTy → Type} (σ : TState C Γ) (g : Grown σ.H α) :
    σ.erase.withGlob (σ.adopt g).1.erase.glob = (σ.adopt g).1.erase := by
  simp only [TState.adopt, TState.erase, State.withGlob, State.ofGlob, State.glob,
    TEnv.erase_wk]

theorem ARhs.evalT_erase (σ : TState C Γ) {R : RefTy} (r : ARhs C Γ R) :
    TRes.Agrees (fun x : Storage C × SRef C (.ref R) => ((σ.withStorage x.1).erase, x.2.erase))
      (r.evalT σ) (r.eval σ.erase) := by
  cases r with
  | path p =>
    exact TRes.Agrees.bind (p.resolveT_erase σ) fun _ => rfl
  | push b _ =>
    refine TRes.Agrees.bind (b.resolveT_erase σ) fun r => ?_
    show TRes.Agrees _ (if σ.storage.full r then .error .exhausted else do
        let (st, n) ← TRes.ofOpt (σ.storage.pushPlace r)
        pure (st, r.index (.arr .dyn) n))
      (do
        let (τ, n) ← pushPlaceAt σ.erase.glob (.ref R) r.root r.path.erase
        pure (σ.erase.withGlob τ, (r.root, r.path.erase ++ [.at n])))
    cases hfull : σ.storage.full r
    · rw [if_neg Bool.false_ne_true]
      rw [Storage.pushPlaceAt_erase (σ := σ.erase.glob) rfl r hfull]
      refine TRes.Agrees.bind (TRes.Agrees.ofOpt _) fun x => ?_
      exact TRes.Agrees.of_eq (by rw [SRef.erase_index]; rfl)
    · trivial

theorem newArrT_erase : (R : RefTy) → (n : PrimTy.uint.Denote) → (h : R.newArrOk = true) →
    (newArrT R n h).erase = newArrVal R n.1
  | .array E, n, _ => by
    simp only [newArrT, newArrVal, SVal.erase, SVec.erase_ofList, SList.erase_nil,
      List.map_replicate, SVal.dflt_erase]
  | .struct _, _, h | .fixed .., _, h | .mapping .., _, h => by
    simp only [RefTy.newArrOk, Bool.false_eq_true] at h

theorem MRhs.evalT_erase (σ : TState C Γ) {R : RefTy} (r : MRhs C Γ R) :
    TRes.Agrees (fun g : Grew C Γ σ.H (HRef · R) => (g.st.erase, (g.val : HRef _ R).id))
      (r.evalT σ) (r.eval σ.erase) := by
  cases r with
  | alias p =>
    exact TRes.Agrees.bind (p.mvalT_erase σ) fun _ => rfl
  | copy p hm =>
    refine TRes.Agrees.bind (p.resolveT_erase σ) fun r => ?_
    show TRes.Agrees _ (do
        let sv ← TRes.ofOpt (σ.storage.find r)
        let g := σ.copyStToMG sv hm
        pure (⟨g.st, g.ext, g.val⟩ : Grew C Γ σ.H (HRef · R)))
      (do
        let sv ← σ.erase.glob.findStorage r.root r.path.erase
        let (τ, mv) ← Semantics.copyStToM σ.erase.glob sv
        pure (σ.erase.withGlob τ, ← mv.asRef))
    rw [Storage.findStorage_erase (σ := σ.erase.glob) rfl r]
    refine TRes.Agrees.bind (TRes.Agrees.ofOpt _) fun sv => ?_
    rw [TState.copyStToM_erase σ sv hm]
    exact TRes.Agrees.of_eq (by
      show Except.ok (σ.erase.withGlob (σ.copyStToM sv hm).1.erase.glob, _) = _
      rw [TState.copyStToM, TState.withGlob_adopt]
      rfl)
  | newArr n hn =>
    show TRes.Agrees _ _ (do
        let sv := newArrVal R (← (← n.eval σ.erase).asInt)
        let (τ, mv) ← Semantics.copyStToM σ.erase.glob sv
        pure (σ.erase.withGlob τ, ← mv.asRef))
    rw [Simple.evalT_erase σ n, ok_bind, PrimTy.asInt_erase_uint, ok_bind, ← newArrT_erase R _ hn]
    simp only []
    rw [TState.copyStToM_erase σ _ (RefTy.mapFree_of_newArrOk hn)]
    exact TRes.Agrees.of_eq (by
      show Except.ok (σ.erase.withGlob (σ.copyStToM _ _).1.erase.glob, _) = _
      rw [TState.copyStToM, TState.withGlob_adopt]
      rfl)

/-! ### Memory addresses -/

/-- The untyped address. -/
def MAddr.erase {H : HTy} {T : Ty} : MAddr H T → Semantics.Addr
  | .field (f := f) r _ => .memoryField r.id f
  | .index r _ i => .memoryIndex r.id i

theorem MAddr.erase_wk {H H' : HTy} (e : H <+: H') {T : Ty} (a : MAddr H T) :
    (a.wk e).erase = a.erase := by
  cases a <;> rfl

theorem MLoc.addrT_erase (σ : TState C Γ) {T : Ty} (l : MLoc C Γ T) :
    TRes.Agrees MAddr.erase (l.addrT σ) (l.addr σ.erase) := by
  cases l with
  | field b f _ =>
    exact TRes.Agrees.bind (b.mvalT_erase σ) fun _ => rfl
  | index a b i =>
    exact TRes.Agrees.bind (b.mvalT_erase σ) fun _ =>
      TRes.Agrees.bind (i.evalT_erase σ) fun _ => rfl

theorem writeAddr_erase (σ : TState C Γ) {T : Ty} (a : MAddr σ.H T) (v : MVal σ.H T) :
    writeAddr σ.erase.glob (MVal.erase T v) a.erase =
      toRes (fun hp : Heap σ.H => { σ.erase.glob with heap := hp.erase }) (σ.heap.writeAddr a v) := by
  cases a with
  | field r h => exact Heap.memWriteField_erase (σ := σ.erase.glob) rfl r h v
  | index r a i => exact Heap.memWriteIndex_erase (σ := σ.erase.glob) rfl r a i v

theorem readLoc_erase (σ : TState C Γ) {p : PrimTy} (a : MAddr σ.H (.prim p)) :
    Semantics.readLoc σ.erase.glob a.erase = toRes PrimTy.erase (σ.heap.readAddr a) := by
  cases a with
  | field r h =>
    simp only [Semantics.readLoc, MAddr.erase, Heap.getObj_erase (σ := σ.erase.glob) rfl r, bind,
      Except.bind]
    show (match lookupBy _ (MFields.erase _ (σ.heap.get r)) with
      | some v => v.asValue | none => .error .stuck) = _
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

theorem opStoreT_erase (σ : TState C Γ) {op : BinOp} (hop : op.hasCompoundAssign = true)
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

theorem opMemT_erase (σ : TState C Γ) {op : BinOp} (hop : op.hasCompoundAssign = true)
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

theorem bumpStoreT_erase (σ : TState C Γ) (op : IncDec) {p : PrimTy} (hp : p.isNumeric = true)
    (r : SRef C (.prim p)) {k' : Semantics.State × Value → State C Γ × Value}
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

theorem bumpMemT_erase (σ : TState C Γ) (op : IncDec) {p : PrimTy} (hp : p.isNumeric = true)
    (a : MAddr σ.H (.prim p)) {k' : Semantics.State × Value → State C Γ × Value}
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

theorem TState.erase_get (σ : TState C Γ) {t : LTy} (i : Idx Γ t) :
    Env.get i σ.erase.env = LTy.TDenote.erase t (TEnv.get i σ.env) :=
  TEnv.get_erase i σ.env

theorem OpLoc.storeT_erase (σ : TState C Γ) {op : BinOp} (hop : op.hasCompoundAssign = true)
    {p : PrimTy} (hp : p.isNumeric = true) (l : OpLoc C Γ p)
    (v : p.Denote) :
    TRes.Agrees (fun o : Out C σ.H Γ => o.st.erase) (l.storeT σ op v)
      (l.store σ.erase op (PrimTy.erase v)) := by
  cases l with
  | «local» i =>
    simp only [OpLoc.storeT, OpLoc.store, opLocal, TState.erase_get, LTy.TDenote.erase_val]
    rw [bind_bind_eq (compound_erase' hop hp _ _)]
    cases compoundT op p (PrimTy.key (TEnv.get i σ.env)) (PrimTy.key v) with
    | none => rfl
    | some new => exact TRes.Agrees.of_eq (congrArg Except.ok (TState.setLocal_erase σ i new).symm)
  | root r hr => exact opStoreT_erase σ hop hp (SRef.ofRoot r hr) v
  | field b f hf =>
    exact TRes.Agrees.bind (Loc.resolveT_erase σ (Loc.field b f hf)) fun r =>
      opStoreT_erase σ hop hp r v
  | index it b i =>
    exact TRes.Agrees.bind (Loc.resolveT_erase σ (Loc.index it b (.simple i))) fun r =>
      opStoreT_erase σ hop hp r v
  | mfield b f hf =>
    show TRes.Agrees _ (do opMemT σ op (← (MLoc.field b f hf).addrT σ) v)
      (do
        let id ← (← b.mval σ.erase).asRef
        σ.erase.withGlob <$> opMem σ.erase.glob op p (.memoryField id f) (PrimTy.erase v))
    have e : (do
        let id ← (← b.mval σ.erase).asRef
        σ.erase.withGlob <$> opMem σ.erase.glob op p (.memoryField id f) (PrimTy.erase v)) =
        ((MLoc.field b f hf).addr σ.erase >>= fun a =>
          σ.erase.withGlob <$> opMem σ.erase.glob op p a (PrimTy.erase v)) := by
      simp only [MLoc.addr, bind_assoc, pure_bind]
    rw [e]
    exact TRes.Agrees.bind (MLoc.addrT_erase σ (MLoc.field b f hf)) fun a =>
      opMemT_erase σ hop hp a v
  | mindex a b i =>
    show TRes.Agrees _ (do opMemT σ op (← (MLoc.index a b (.simple i)).addrT σ) v)
      (do
        let id ← (← b.mval σ.erase).asRef
        let iv ← (← i.eval σ.erase).asInt
        σ.erase.withGlob <$> opMem σ.erase.glob op p (.memoryIndex id iv) (PrimTy.erase v))
    have e : (do
        let id ← (← b.mval σ.erase).asRef
        let iv ← (← i.eval σ.erase).asInt
        σ.erase.withGlob <$> opMem σ.erase.glob op p (.memoryIndex id iv) (PrimTy.erase v)) =
        ((MLoc.index a b (.simple i)).addr σ.erase >>= fun a =>
          σ.erase.withGlob <$> opMem σ.erase.glob op p a (PrimTy.erase v)) := by
      simp only [MLoc.addr, Val.eval, bind_assoc, pure_bind]
    rw [e]
    exact TRes.Agrees.bind (MLoc.addrT_erase σ (MLoc.index a b (.simple i))) fun a =>
      opMemT_erase σ hop hp a v

theorem OpLoc.bumpT_erase (σ : TState C Γ) (op : IncDec) {p : PrimTy} (hp : p.isNumeric = true)
    (l : OpLoc C Γ p) :
    TRes.Agrees (fun x : Out C σ.H Γ × p.Denote => (x.1.st.erase, PrimTy.erase x.2))
      (l.bumpT σ op) (l.bump σ.erase op) := by
  cases l with
  | «local» i =>
    simp only [OpLoc.bumpT, OpLoc.bump, bumpLocal, TState.erase_get, LTy.TDenote.erase_val,
      asInt_erase_numeric hp, ok_bind, bump_erase hp]
    cases Core.bumpT op p (PrimTy.key (TEnv.get i σ.env)) with
    | none => rfl
    | some new =>
      refine TRes.Agrees.of_eq ?_
      rw [TState.setLocal_erase]
      cases op.isPre <;> rfl
  | root r hr => exact bumpStoreT_erase σ op hp (SRef.ofRoot r hr) fun _ _ => rfl
  | field b f hf =>
    exact TRes.Agrees.bind (Loc.resolveT_erase σ (Loc.field b f hf)) fun r =>
      bumpStoreT_erase σ op hp r fun _ _ => rfl
  | index it b i =>
    exact TRes.Agrees.bind (Loc.resolveT_erase σ (Loc.index it b (.simple i))) fun r =>
      bumpStoreT_erase σ op hp r fun _ _ => rfl
  | mfield b f hf =>
    simp only [OpLoc.bumpT, MLoc.addrT, bind_assoc, pure_bind]
    refine TRes.Agrees.bind (b.mvalT_erase σ) fun r => ?_
    exact bumpMemT_erase σ op hp (.field r hf) fun _ _ => rfl
  | mindex a b i =>
    simp only [OpLoc.bumpT, MLoc.addrT, Val.evalT, bind_assoc, pure_bind, ok_bind]
    refine TRes.Agrees.bind (b.mvalT_erase σ) fun r => ?_
    show TRes.Agrees _ (bumpMemT σ op (.index r a (i.evalT σ).1)) (do
      let iv ← (← i.eval σ.erase).asInt
      _ <$> bumpMem σ.erase.glob op p (.memoryIndex r.id iv))
    rw [Simple.evalT_erase σ i, ok_bind, PrimTy.asInt_erase_uint, ok_bind]
    exact bumpMemT_erase σ op hp (.index r a (i.evalT σ).1) fun _ _ => rfl

/-! ### Calls and payments -/

theorem Args.evalT_erase (σ : TState C Γ) : {ps : Ctx} → (as : Args C Γ ps) →
    TRes.Agrees (TEnv.erase ps) (as.evalT σ) (as.eval σ.erase)
  | _, .nil => rfl
  | _, .snoc as _ _ e => by
    unfold Args.evalT Args.eval
    exact TRes.Agrees.bind (as.evalT_erase σ) fun _ =>
      TRes.Agrees.bind (e.evalT_erase σ) fun _ => rfl

theorem ExtCall.keyT_erase (σ : TState C Γ) (c : ExtCall C Γ) :
    c.key σ.erase = .ok (c.keyT σ) := by
  have hm : ∀ l : List (ExtArg C Γ), l.mapM (fun a => a.2.eval σ.erase) =
      .ok (l.map fun a => PrimTy.erase (a.2.evalT σ)) := by
    intro l
    induction l with
    | nil => rfl
    | cons a l ih => rw [List.mapM_cons, Simple.evalT_erase, ok_bind, ih, ok_bind]; rfl
  unfold ExtCall.key
  rw [Simple.evalT_erase, ok_bind, PrimTy.asInt_erase_uint, ok_bind, hm, ok_bind]
  rfl

theorem PrimTy.ofValue?_fits (p : PrimTy) (v : Value) :
    (match PrimTy.ofValue? p v with
      | some x => v.fits p = true ∧ PrimTy.erase x = v
      | none => v.fits p = false) := by
  cases p <;> cases v
  case bool.bool b => exact ⟨rfl, rfl⟩
  case uint.int n =>
    simp only [PrimTy.ofValue?, Semantics.PrimVal.fits, PrimTy.inRange, Semantics.uintBound]
    by_cases hb : 0 ≤ n ∧ n < ((2 ^ 256 : Nat) : Int)
    · rw [dif_pos (decide_eq_true hb)]
      exact ⟨decide_eq_true hb, rfl⟩
    · rw [dif_neg (fun h => hb (of_decide_eq_true h))]
      exact decide_eq_false hb
  case int.int n =>
    simp only [PrimTy.ofValue?, Semantics.PrimVal.fits, PrimTy.inRange, Semantics.intBound]
    by_cases hb : -((2 ^ 255 : Nat) : Int) ≤ n ∧ n < ((2 ^ 255 : Nat) : Int)
    · rw [dif_pos (decide_eq_true hb)]
      exact ⟨decide_eq_true hb, rfl⟩
    · rw [dif_neg (fun h => hb (of_decide_eq_true h))]
      exact decide_eq_false hb
  all_goals rfl

theorem Binders.decodeT_erase {H : HTy} : {ρ : Ctx} → (bs : Binders ρ) → (vs : List Value) →
    TRes.Agrees (fun x : TEnv C H ρ × List Value => (TEnv.erase ρ x.1, x.2))
      (bs.decodeT vs) (bs.decode vs)
  | _, .nil, _ => rfl
  | _, .snoc bs p _, vs => by
    unfold Binders.decodeT Binders.decode
    refine TRes.Agrees.bind (bs.decodeT_erase vs) fun x => ?_
    rcases x with ⟨e, rest⟩
    cases rest with
    | nil => rfl
    | cons v rest =>
      have hf := PrimTy.ofValue?_fits p v
      cases h : PrimTy.ofValue? p v with
      | none =>
        rw [h] at hf
        simp only [h, hf, Bool.false_eq_true, ↓reduceIte]
        rfl
      | some x =>
        rw [h] at hf
        simp only [h, hf.1, ↓reduceIte]
        exact TRes.Agrees.of_eq (by rw [← hf.2]; rfl)

theorem CodeBinder.decodeT_erase {H : HTy} {κ : Ctx} (code : CodeBinder κ) (c : Value) :
    TRes.Agrees (TEnv.erase κ) (code.decodeT (C := C) (H := H) c) (code.decode c) := by
  cases code with
  | none => rfl
  | some _ =>
    unfold CodeBinder.decodeT CodeBinder.decode
    have hf := PrimTy.ofValue?_fits .uint c
    cases h : PrimTy.ofValue? .uint c with
    | none =>
      rw [h] at hf
      simp only [hf, Bool.false_eq_true, ↓reduceIte]
      rfl
    | some x =>
      rw [h] at hf
      simp only [hf.1, ↓reduceIte]
      exact TRes.Agrees.of_eq (by rw [← hf.2]; rfl)

theorem TEnv.append_erase {H : HTy} {Γ : Ctx} : (ρ : Ctx) → (r : TEnv C H ρ) → (e : TEnv C H Γ) →
    TEnv.erase (ρ ++ Γ) (TEnv.append ρ r e) = Env.append ρ (TEnv.erase ρ r) (TEnv.erase Γ e)
  | [], _, _ => rfl
  | _ :: ρ, r, e => congrArg (Prod.mk _) (TEnv.append_erase ρ r.2 e)

theorem TEnv.take_erase {H : HTy} {Γ : Ctx} : (ρ : Ctx) → (e : TEnv C H (ρ ++ Γ)) →
    Env.take ρ (TEnv.erase (ρ ++ Γ) e) = TEnv.erase ρ (TEnv.take ρ e)
  | [], _ => rfl
  | _ :: ρ, e => congrArg (Prod.mk _) (TEnv.take_erase ρ e.2)

theorem Binders.defaultsT_erase {H : HTy} : {ρ : Ctx} → (bs : Binders ρ) →
    TEnv.erase ρ (Binders.defaultsT (C := C) (H := H) bs) = Binders.defaults bs
  | _, .nil => rfl
  | _, .snoc bs p _ => by
    show ((PrimTy.erase (PrimTy.dflt p), TEnv.erase _ (Binders.defaultsT bs)) : Env C (.val p :: _)) =
      (PrimTy.default p, Binders.defaults bs)
    rw [PrimTy.erase_dflt, Binders.defaultsT_erase bs]

theorem TState.withEnv_erase {Δ : Ctx} (σ : TState C Γ) (e : TEnv C σ.H Δ) :
    (σ.withEnv e).erase = σ.erase.withEnv (TEnv.erase Δ e) := rfl

/-- Entering a call: the frame the untyped run builds on the erased caller is
the erasure of the typed one. -/
theorem CallRet.enterT_erase {rs Γ' ps : Ctx} (ret : CallRet Γ rs Γ') (σ : TState C Γ)
    (a : TEnv C σ.H ps) {β : Type} (K : State C (rs ++ ps) → Res β) :
    (do
      let (τ, r) ← ret.enter σ.erase.glob
      K (State.ofGlob τ (Env.append rs r (TEnv.erase ps a)))) =
      K (ret.enterT (σ.withEnv a)).st.erase := by
  cases ret with
  | none => rfl
  | val p r res =>
    show K (State.ofGlob (Γ := .val p :: ps) σ.erase.glob
      (PrimTy.default p, TEnv.erase ps a)) = _
    rw [← PrimTy.erase_dflt]
    rfl
  | rets bs =>
    show K (State.ofGlob σ.erase.glob (Env.append rs (Binders.defaults bs) (TEnv.erase ps a))) = _
    rw [← Binders.defaultsT_erase (H := σ.H) bs, ← TEnv.append_erase]
    rfl
  | mem R r hd hm =>
    show (do
      let (τ, r) ← (do
        let (τ', id) ← Semantics.allocDefault (σ.withEnv a).erase.glob R
        pure (τ', ((id, ()) : Env C [.mem R])))
      K (State.ofGlob τ (Env.append [.mem R] r (TEnv.erase ps a)))) = _
    rw [TState.allocDefault_erase (σ.withEnv a) R hm]
    refine congrArg K ?_
    simp only [CallRet.enterT, TState.allocDefaultG, TState.grow, TState.allocDefault,
      TState.adopt, TState.push, TState.withEnv, TState.erase, State.ofGlob, State.glob,
      Env.append, TEnv.erase_wk]
    congr 1
    show (_, TEnv.erase ps a) = (_, TEnv.erase ps (TEnv.wk _ ps a))
    rw [TEnv.erase_wk]
    rfl

theorem CallRet.leaveT_erase {H : HTy} {rs Γ' : Ctx} (ret : CallRet Γ rs Γ') (e : TEnv C H Γ)
    (r : TEnv C H rs) :
    TEnv.erase Γ' (ret.leaveT e r) = ret.leave (TEnv.erase Γ e) (TEnv.erase rs r) := by
  cases ret with
  | none => rfl
  | val p x res =>
    cases res with
    | none => rfl
    | some i => exact (TEnv.set_erase i r.1 e).symm
  | rets bs => exact TEnv.append_erase _ r e
  | mem R x hd hm => rfl

theorem TState.pay_erase (σ : TState C Γ) (addr amt : Int) :
    (σ.pay addr amt).erase = σ.erase.withGlob (σ.erase.glob.pay addr amt) := rfl

end Eval

/-! ## Statements -/

/-- A typed step against an untyped one: from every typed state, the results
agree on the erased one. -/
def StepAgrees {Γ Γ' : Ctx} (t : TStep C Γ Γ') (u : State C Γ → Res (State C Γ')) : Prop :=
  ∀ σ : TState C Γ, TRes.Agrees (fun o : Out C σ.H Γ' => o.st.erase) (t σ) (u σ.erase)

theorem TRes.Agrees.emap {α β γ δ : Type} {f : α → β} {g : γ → δ} {t : TRes α} {u : Res β}
    (h : TRes.Agrees f t u) {k : α → γ} {k' : β → δ} (hk : ∀ a, k' (f a) = g (k a)) :
    TRes.Agrees g (t.map k) (u.map k') :=
  TRes.Agrees.map h hk

theorem TRes.Agrees.mapLeft {α β γ : Type} {f : α → β} {g : γ → β} {t : TRes α} {u : Res β}
    (h : TRes.Agrees f t u) {k : α → γ} (hk : ∀ a, f a = g (k a)) :
    TRes.Agrees g (t.map k) u := by
  match t, h with
  | .ok a, h => subst h; exact congrArg Except.ok (hk a)
  | .error .revert, h => subst h; rfl
  | .error .panic, h => subst h; rfl
  | .error .diverge, _ => trivial
  | .error .exhausted, _ => trivial

theorem PrimTy.uint_nonneg (x : PrimTy.uint.Denote) : 0 ≤ x.1 := by
  have h := x.2
  simp only [PrimTy.inRange, decide_eq_true_eq] at h
  exact h.1

namespace TRun

variable {Γ : Ctx}

theorem assign_erase {T : Ty} (l : Loc C Γ T) (r : Src C Γ T) :
    StepAgrees (TRun.assign l r) (Run.assign l r) := fun σ => by
  refine TRes.Agrees.bind (r.valueT_erase σ) fun sv => ?_
  refine TRes.Agrees.bind (l.resolveT_erase σ) fun ref => ?_
  show TRes.Agrees _ (do
      let st ← TRes.ofOpt (σ.storage.write ref sv)
      pure (⟨σ.withStorage st, List.prefix_refl _⟩ : Out C σ.H Γ))
    (σ.erase.withGlob <$> σ.erase.glob.writeStorage ref.root ref.path.erase sv.erase)
  rw [Storage.writeStorage_erase (σ := σ.erase.glob) rfl ref sv]
  cases σ.storage.write ref sv <;> rfl

theorem rebind_erase {R : RefTy} (i : Idx Γ (.alias R)) (r : ARhs C Γ R) :
    StepAgrees (TRun.rebind i r) (Run.rebind i r) := fun σ =>
  TRes.Agrees.bind (r.evalT_erase σ) fun x =>
    TRes.Agrees.of_eq (congrArg Except.ok (TState.setLocal_erase (σ.withStorage x.1) i (some x.2)).symm)

theorem assignLocal_erase {p : PrimTy} (i : Idx Γ (.val p)) (r : Val C Γ p) :
    StepAgrees (TRun.assignLocal i r) (Run.assignLocal i r) := fun σ =>
  TRes.Agrees.bind (r.evalT_erase σ) fun x =>
    TRes.Agrees.of_eq (congrArg Except.ok (TState.setLocal_erase σ i x).symm)

theorem declLocal_erase (p : PrimTy) (init : Option (Val C Γ p)) :
    StepAgrees (TRun.declLocal p init) (Run.declLocal p init) :=
  fun σ => by
  cases init with
  | none =>
    refine TRes.Agrees.of_eq ?_
    show Except.ok (σ.erase.push (t := .val p) (PrimTy.default p)) = _
    rw [← PrimTy.erase_dflt]
    rfl
  | some e =>
    exact TRes.Agrees.bind (e.evalT_erase σ) fun _ => rfl

theorem declStorage_erase (R : RefTy) (init : Option (ARhs C Γ R)) :
    StepAgrees (TRun.declStorage R init) (Run.declStorage R init) := fun σ => by
  cases init with
  | none => rfl
  | some r =>
    exact TRes.Agrees.bind (r.evalT_erase σ) fun _ => rfl

theorem opAssign_erase {p : PrimTy} (op : BinOp) (hop : op.hasCompoundAssign = true)
    (hp : p.isNumeric = true) (l : OpLoc C Γ p) (r : Val C Γ p) :
    StepAgrees (TRun.opAssign op l r) (Run.opAssign op l r) := fun σ =>
  TRes.Agrees.bind (r.evalT_erase σ) fun v => l.storeT_erase σ hop hp v

theorem incDec_erase {p : PrimTy} (op : IncDec) (hp : p.isNumeric = true) (l : OpLoc C Γ p) :
    StepAgrees (TRun.incDec op l) (Run.incDec op l) := fun σ =>
  TRes.Agrees.bind (l.bumpT_erase σ op hp) fun _ => rfl

theorem assignIncDec_erase {p : PrimTy} (i : Idx Γ (.val p)) (op : IncDec)
    (hp : p.isNumeric = true) (l : OpLoc C Γ p) :
    StepAgrees (TRun.assignIncDec i op l) (Run.assignIncDec i op l) := fun σ =>
  TRes.Agrees.bind (l.bumpT_erase σ op hp) fun x =>
    TRes.Agrees.of_eq (congrArg Except.ok (TState.setLocal_erase x.1.st i x.2).symm)

theorem pop_erase {E : Ty} (b : SPath C Γ (.array E)) :
    StepAgrees (TRun.pop b) (Run.pop b) := fun σ => by
  refine TRes.Agrees.bind (b.resolveT_erase σ) fun ref => ?_
  show TRes.Agrees _ (do
      let st ← TRes.ofOpt (σ.storage.pop E.isMapping ref)
      pure (⟨σ.withStorage st, List.prefix_refl _⟩ : Out C σ.H Γ))
    (σ.erase.withGlob <$> popAt σ.erase.glob E.isMapping ref.root ref.path.erase)
  rw [Storage.popAt_erase (σ := σ.erase.glob) rfl E.isMapping ref]
  cases σ.storage.pop E.isMapping ref <;> rfl

theorem transfer_erase (r a : Val C Γ .uint) :
    StepAgrees (TRun.transfer r a) (Run.transfer r a) := fun σ => by
  refine TRes.Agrees.bind (r.evalT_erase σ) fun addr => ?_
  rw [PrimTy.asInt_erase_uint, ok_bind]
  refine TRes.Agrees.bind (a.evalT_erase σ) fun amt => ?_
  rw [PrimTy.asInt_erase_uint, ok_bind]
  show TRes.Agrees _ (.ok _) (σ.erase.withGlob <$> transferAt σ.erase.glob addr.1 amt.1)
  rw [transferAt, if_neg (Int.not_lt.mpr (PrimTy.uint_nonneg amt))]
  rfl

theorem push_erase {E : Ty} (b : SPath C Γ (.array E)) (v : Option (Src C Γ E)) :
    StepAgrees (TRun.push b v) (Run.push b v) := fun σ => by
  refine TRes.Agrees.bind (b.resolveT_erase σ) fun ref => ?_
  cases v with
  | none =>
    show TRes.Agrees _ (if σ.storage.full ref then .error .exhausted else do
        let st ← TRes.ofOpt (σ.storage.push ref fun slot => some slot)
        pure (⟨σ.withStorage st, List.prefix_refl _⟩ : Out C σ.H Γ))
      (σ.erase.withGlob <$> pushAt σ.erase.glob E ref.root ref.path.erase
        (Src.pushVal σ.erase none))
    cases hfull : σ.storage.full ref
    · rw [if_neg Bool.false_ne_true]
      rw [Storage.pushAt_erase (σ := σ.erase.glob) rfl ref (Src.pushVal σ.erase none)
        (fun slot => some slot) (fun _ => rfl) (.inl hfull)]
      cases σ.storage.push ref (fun slot => some slot) <;> rfl
    · trivial
  | some r =>
    show TRes.Agrees _ (do
        let sv ← r.valueT σ
        if σ.storage.full ref then .error .exhausted else do
        let st ← TRes.ofOpt (σ.storage.push ref fun _ => some sv.strip)
        pure (⟨σ.withStorage st, List.prefix_refl _⟩ : Out C σ.H Γ))
      (σ.erase.withGlob <$> pushAt σ.erase.glob E ref.root ref.path.erase
        (Src.pushVal σ.erase (some r)))
    have ha := r.valueT_erase σ
    have hn := r.valueT_noPanic σ
    revert ha hn
    cases r.valueT σ with
    | ok sv =>
      intro ha _
      have hval : ∀ x : SVal E, Src.pushVal σ.erase (some r) x.erase =
          toRes SVal.erase ((fun _ => some sv.strip) x) := fun _ => by
        show (do pure (← r.value σ.erase).strip) = _
        rw [show r.value σ.erase = .ok sv.erase from ha, ok_bind, ← SVal.strip_erase]
        rfl
      show TRes.Agrees _ (if σ.storage.full ref then .error .exhausted else do
          let st ← TRes.ofOpt (σ.storage.push ref fun _ => some sv.strip)
          pure (⟨σ.withStorage st, List.prefix_refl _⟩ : Out C σ.H Γ)) _
      cases hfull : σ.storage.full ref
      · rw [if_neg Bool.false_ne_true]
        rw [Storage.pushAt_erase (σ := σ.erase.glob) rfl ref _ _ hval (.inl hfull)]
        cases σ.storage.push ref (fun _ => some sv.strip) <;> rfl
      · trivial
    | error e =>
      intro ha hn
      cases e with
      | diverge => trivial
      | exhausted => trivial
      | panic => exact absurd rfl hn
      | revert =>
        have hval : ∀ x : SVal E, Src.pushVal σ.erase (some r) x.erase =
            toRes SVal.erase ((fun _ => (none : Option (SVal E))) x) := fun _ => by
          show (do pure (← r.value σ.erase).strip) = _
          rw [show r.value σ.erase = .error .revert from ha]
          rfl
        rw [Storage.pushAt_erase (σ := σ.erase.glob) rfl ref _ _ hval (.inr fun _ => rfl)]
        have hnone : σ.storage.push ref (fun _ => (none : Option (SVal E))) = none := by
          simp only [Storage.push]
          cases σ.storage.find ref <;> rfl
        rw [hnone]
        rfl

theorem send_erase (pv : Idx Γ (.val .bool)) (r a : Val C Γ .uint) :
    StepAgrees (TRun.send pv r a) (Run.send pv r a) := fun σ => by
  refine TRes.Agrees.bind (r.evalT_erase σ) fun addr => ?_
  rw [PrimTy.asInt_erase_uint, ok_bind]
  refine TRes.Agrees.bind (a.evalT_erase σ) fun amt => ?_
  rw [PrimTy.asInt_erase_uint, ok_bind]
  show TRes.Agrees _ (.ok (sendT σ pv addr.1 amt.1)) (sendAt σ.erase pv addr.1 amt.1)
  rw [sendAt, if_neg (Int.not_lt.mpr (PrimTy.uint_nonneg amt))]
  show TRes.Agrees _ _ (match lookupBy (sendKey addr.1 amt.1) σ.tx.ext with
    | none | some (.ok _) => .ok ((σ.erase.withGlob (σ.erase.glob.pay addr.1 amt.1)).setLocal pv
      (.bool true))
    | some _ => .ok (σ.erase.setLocal pv (.bool false)))
  unfold sendT
  have ht := TState.setLocal_erase (σ.pay addr.1 amt.1) pv (true : Bool)
  have hf := TState.setLocal_erase σ pv (false : Bool)
  cases lookupBy (sendKey addr.1 amt.1) σ.tx.ext with
  | none => exact TRes.Agrees.of_eq (congrArg Except.ok ht.symm)
  | some x =>
    cases x with
    | ok _ => exact TRes.Agrees.of_eq (congrArg Except.ok ht.symm)
    | error | panic _ | other => exact TRes.Agrees.of_eq (congrArg Except.ok hf.symm)

theorem TState.allocDefault_glob (σ : TState C Γ) (R : RefTy) (hm : (Ty.ref R).mapFree = true) :
    σ.erase.withGlob (σ.allocDefault R hm).1.erase.glob = (σ.allocDefault R hm).1.erase :=
  TState.withGlob_adopt σ _

theorem declMem_erase (R : RefTy) (init : Option (MRhs C Γ R)) (hm : (Ty.ref R).mapFree = true) :
    StepAgrees (TRun.declMem R init hm) (Run.declMem R init) := fun σ => by
  cases init with
  | none =>
    show TRes.Agrees _ _ (do
      let (τ, id) ← Semantics.allocDefault σ.erase.glob R
      pure ((σ.erase.withGlob τ).push (t := .mem R) id))
    rw [TState.allocDefault_erase σ R hm, ok_bind]
    refine TRes.Agrees.of_eq (congrArg Except.ok ?_)
    show _ = ((σ.allocDefault R hm).1.push (t := .mem R) (σ.allocDefault R hm).2).erase
    rw [TState.push_erase, ← TState.allocDefault_glob]
    rfl
  | some r =>
    exact TRes.Agrees.bind (r.evalT_erase σ) fun _ => rfl

theorem rebindMem_erase {R : RefTy} (i : Idx Γ (.mem R)) (r : MRhs C Γ R) :
    StepAgrees (TRun.rebindMem i r) (Run.rebindMem i r) := fun σ =>
  TRes.Agrees.bind (r.evalT_erase σ) fun g =>
    TRes.Agrees.of_eq (congrArg Except.ok (TState.setLocal_erase g.st i g.val).symm)

theorem assignFromMem_erase {R : RefTy} (l : Loc C Γ (.ref R)) (p : MPath C Γ (.ref R)) :
    StepAgrees (TRun.assignFromMem l p) (Run.assignFromMem l p) := fun σ => by
  refine TRes.Agrees.bind (p.mvalT_erase σ) fun m => ?_
  show TRes.Agrees _ _ (do
    let sv ← Semantics.copyMem σ.erase.glob (MVal.erase (.ref R) m)
    let (root, segs) ← l.resolve σ.erase
    σ.erase.withGlob <$> σ.erase.glob.writeStorage root segs sv)
  rw [TState.copyMem_erase σ m, ok_bind]
  refine TRes.Agrees.bind (l.resolveT_erase σ) fun ref => ?_
  show TRes.Agrees _ (do
      let st ← TRes.ofOpt (σ.storage.write ref (σ.copyMToSt m))
      pure (⟨σ.withStorage st, List.prefix_refl _⟩ : Out C σ.H Γ))
    (σ.erase.withGlob <$> σ.erase.glob.writeStorage ref.root ref.path.erase
      (σ.copyMToSt m).erase)
  rw [Storage.writeStorage_erase (σ := σ.erase.glob) rfl ref]
  cases σ.storage.write ref (σ.copyMToSt m) <;> rfl

theorem assignMem_erase {T : Ty} (l : MLoc C Γ T) (r : MSrc C Γ T) :
    StepAgrees (TRun.assignMem l r) (Run.assignMem l r) := fun σ => by
  refine TRes.Agrees.bind (r.mvalT_erase σ) fun mv => ?_
  show TRes.Agrees _ _ (l.write σ.erase (MVal.erase T mv))
  rw [MLoc.write_eq]
  refine TRes.Agrees.bind (l.addrT_erase σ) fun a => ?_
  show TRes.Agrees _ (do
      let hp ← TRes.ofOpt (σ.heap.writeAddr a mv)
      pure (⟨σ.withHeap hp, List.prefix_refl _⟩ : Out C σ.H Γ))
    (σ.erase.withGlob <$> writeAddr σ.erase.glob (MVal.erase T mv) a.erase)
  rw [writeAddr_erase σ a mv]
  cases σ.heap.writeAddr a mv <;> rfl

theorem delete_erase {T : Ty} (l : Loc C Γ T) :
    StepAgrees (TRun.delete l) (Run.delete l) := fun σ => by
  refine TRes.Agrees.bind (l.resolveT_erase σ) fun ref => ?_
  show TRes.Agrees _ (do
      let st ← TRes.ofOpt (σ.storage.delete ref)
      pure (⟨σ.withStorage st, List.prefix_refl _⟩ : Out C σ.H Γ))
    (do
      let cur ← σ.erase.glob.findStorage ref.root ref.path.erase
      σ.erase.withGlob <$> σ.erase.glob.saveStorage ref.root ref.path.erase cur.defaultOf)
  rw [← map_bind, Storage.delete_erase (σ := σ.erase.glob) rfl ref]
  cases σ.storage.delete ref <;> rfl

theorem TState.erase_env_adopt {α : HTy → Type} (σ : TState C Γ) (g : Grown σ.H α) :
    (σ.adopt g).1.erase.env = σ.erase.env := TEnv.erase_wk g.ext Γ σ.env

theorem clearT_erase (σ : TState C Γ) {T : Ty} (a : MAddr σ.H T) (hm : T.mapFree = true) :
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
    rw [TState.allocDefault_erase σ R hm, ok_bind]
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
      rw [TState.withHeap_erase]
      simp only [State.withGlob]
      rw [show (σ.allocDefaultG R hm).st.erase.env = σ.erase.env from TState.erase_env_adopt σ _]

theorem deleteMem_erase {T : Ty} (p : MPath C Γ T) :
    StepAgrees (TRun.deleteMem p) (Run.deleteMem p) := fun σ => by
  cases p with
  | var i hm =>
    show TRes.Agrees _ _ (do
      let (τ, id) ← Semantics.allocDefault σ.erase.glob _
      pure ((σ.erase.withGlob τ).setLocal i id))
    rw [TState.allocDefault_erase σ _ hm, ok_bind]
    refine TRes.Agrees.of_eq (congrArg Except.ok ?_)
    show _ = ((σ.allocDefault _ hm).1.setLocal i (σ.allocDefault _ hm).2).erase
    rw [TState.setLocal_erase, ← TState.allocDefault_glob]
    rfl
  | loc l =>
    exact TRes.Agrees.bind (l.addrT_erase σ) fun a => clearT_erase σ a l.mapFree

theorem TState.withGlob_copyStToMG {T : Ty} (σ : TState C Γ) (v : SVal T)
    (hm : T.mapFree = true) :
    σ.erase.withGlob (σ.copyStToMG v hm).st.erase.glob = (σ.copyStToMG v hm).st.erase :=
  TState.withGlob_adopt σ _

theorem assignNew_erase {R : RefTy} (l : NewLhs C Γ R) (n : Simple C Γ .uint)
    (h : R.newArrOk = true) :
    StepAgrees (TRun.assignNew l n h) (Run.assignNew l n) := fun σ => by
  have key : ∀ {β : Type} (K : Semantics.State → Nat → Res β),
      (do
        let sv := newArrVal R (← (← n.eval σ.erase).asInt)
        let (τ, mv) ← Semantics.copyStToM σ.erase.glob sv
        let id ← mv.asRef
        K τ id) =
      K (σ.copyStToMG (newArrT R (n.evalT σ) h) (RefTy.mapFree_of_newArrOk h)).st.erase.glob
        ((σ.copyStToMG (newArrT R (n.evalT σ) h) (RefTy.mapFree_of_newArrOk h)).val : HRef _ R).id := fun K => by
    rw [Simple.evalT_erase σ n, ok_bind, PrimTy.asInt_erase_uint, ok_bind, ← newArrT_erase R _ h]
    simp only []
    rw [TState.copyStToM_erase σ _ (RefTy.mapFree_of_newArrOk h), ok_bind]
    rfl
  cases l with
  | store l =>
    have e := key (β := State C Γ) fun τ id => do
      let σ' := σ.erase.withGlob τ
      let sv' ← Semantics.copyMem τ (.ref id)
      let (root, segs) ← l.resolve σ'
      σ'.withGlob <$> τ.writeStorage root segs sv'
    show TRes.Agrees _ _ (do
      let sv := newArrVal R (← (← n.eval σ.erase).asInt)
      let (τ, mv) ← Semantics.copyStToM σ.erase.glob sv
      let id ← mv.asRef
      let σ' := σ.erase.withGlob τ
      let sv' ← Semantics.copyMem τ (.ref id)
      let (root, segs) ← l.resolve σ'
      σ'.withGlob <$> τ.writeStorage root segs sv')
    rw [e]
    simp only [TRun.assignNew]
    rw [TState.withGlob_copyStToMG]
    have gen : ∀ G : Grew C Γ σ.H (MVal · (.ref R)), TRes.Agrees (fun o : Out C σ.H Γ => o.st.erase)
        (do
          let ref ← l.resolveT G.st
          let st ← TRes.ofOpt (G.st.storage.write ref (MVal.copyMToSt G.st.heap G.val))
          pure (⟨G.st.withStorage st, G.ext⟩ : Out C σ.H Γ))
        (do
          let sv' ← Semantics.copyMem G.st.erase.glob (.ref (G.val : HRef _ R).id)
          let (root, segs) ← l.resolve G.st.erase
          G.st.erase.withGlob <$> G.st.erase.glob.writeStorage root segs sv') := fun G => by
      rw [show Semantics.copyMem G.st.erase.glob (.ref (G.val : HRef _ R).id) = _ from
        TState.copyMem_erase G.st G.val, ok_bind]
      refine TRes.Agrees.bind (l.resolveT_erase G.st) fun ref => ?_
      show TRes.Agrees _ (do
          let st ← TRes.ofOpt (G.st.storage.write ref (G.st.copyMToSt G.val))
          pure (⟨G.st.withStorage st, G.ext⟩ : Out C σ.H Γ))
        (G.st.erase.withGlob <$> G.st.erase.glob.writeStorage ref.root ref.path.erase
          (G.st.copyMToSt G.val).erase)
      rw [Storage.writeStorage_erase (σ := G.st.erase.glob) rfl ref]
      cases G.st.storage.write ref (G.st.copyMToSt G.val) <;> rfl
    exact gen _
  | mem l =>
    have e := key (β := State C Γ) fun τ id => l.write (σ.erase.withGlob τ) (.ref id)
    show TRes.Agrees _ _ (do
      let sv := newArrVal R (← (← n.eval σ.erase).asInt)
      let (τ, mv) ← Semantics.copyStToM σ.erase.glob sv
      let id ← mv.asRef
      l.write (σ.erase.withGlob τ) (.ref id))
    rw [e]
    simp only [TRun.assignNew]
    rw [TState.withGlob_copyStToMG]
    have gen : ∀ G : Grew C Γ σ.H (MVal · (.ref R)), TRes.Agrees (fun o : Out C σ.H Γ => o.st.erase)
        (do
          let a ← l.addrT G.st
          let hp ← TRes.ofOpt (G.st.heap.writeAddr a G.val)
          pure (⟨G.st.withHeap hp, G.ext⟩ : Out C σ.H Γ))
        (l.write G.st.erase (.ref (G.val : HRef _ R).id)) := fun G => by
      rw [MLoc.write_eq]
      refine TRes.Agrees.bind (l.addrT_erase G.st) fun a => ?_
      show TRes.Agrees _ (do
          let hp ← TRes.ofOpt (G.st.heap.writeAddr a G.val)
          pure (⟨G.st.withHeap hp, G.ext⟩ : Out C σ.H Γ))
        (G.st.erase.withGlob <$> writeAddr G.st.erase.glob (MVal.erase (.ref R) G.val) a.erase)
      rw [writeAddr_erase G.st a G.val]
      cases G.st.heap.writeAddr a G.val <;> rfl
    exact gen _

theorem ite_erase {Γ₁ Γ₂ : Ctx} (c : Val C Γ .bool) (h₁ : Ext Γ Γ₁) (thn : TStep C Γ Γ₁)
    (thnU : State C Γ → Res (State C Γ₁)) (h₂ : Ext Γ Γ₂) (els : TStep C Γ Γ₂)
    (elsU : State C Γ → Res (State C Γ₂)) (hthn : StepAgrees thn thnU)
    (hels : StepAgrees els elsU) :
    StepAgrees (TRun.ite c h₁ thn h₂ els) (Run.ite c h₁ thnU h₂ elsU) := fun σ => by
  refine TRes.Agrees.bind (c.evalT_erase σ) fun v => ?_
  cases v
  · exact (hels σ).emap fun o => (TState.drop_erase h₂ o.st).symm
  · exact (hthn σ).emap fun o => (TState.drop_erase h₁ o.st).symm

theorem require_erase (c : Val C Γ .bool) :
    StepAgrees (TRun.require c) (fun σ => do guardOk (← c.eval σ) σ) := fun σ =>
  TRes.Agrees.bind (c.evalT_erase σ) fun v => by cases v <;> rfl

theorem assert_erase (c : Val C Γ .bool) :
    StepAgrees (TRun.assert c) (fun σ => do assertOk (← c.eval σ) σ) := fun σ =>
  TRes.Agrees.bind (c.evalT_erase σ) fun v => by cases v <;> rfl

theorem block_erase {Γ₁ : Ctx} (h : Ext Γ Γ₁) (body : TStep C Γ Γ₁)
    (bodyU : State C Γ → Res (State C Γ₁)) (hb : StepAgrees body bodyU) :
    StepAgrees (TRun.block h body) (Run.block h bodyU) := fun σ =>
  (hb σ).emap fun o => (TState.drop_erase h o.st).symm

theorem seq_erase {Γ₁ Γ₂ : Ctx} (s : TStep C Γ Γ₁) (sU : State C Γ → Res (State C Γ₁))
    (P : TStep C Γ₁ Γ₂) (PU : State C Γ₁ → Res (State C Γ₂)) (hs : StepAgrees s sU)
    (hP : StepAgrees P PU) : StepAgrees (TRun.seq s P) (Run.seq sU PU) := fun σ => by
  have h := hs σ
  unfold TRun.seq Run.seq
  revert h
  cases s σ with
  | ok o =>
    intro h
    rw [show sU σ.erase = .ok o.st.erase from h]
    exact (hP o.st).mapLeft fun _ => rfl
  | error e =>
    intro h
    cases e with
    | revert => rw [show sU σ.erase = .error .revert from h]; rfl
    | panic => rw [show sU σ.erase = .error .panic from h]; rfl
    | diverge => trivial
    | exhausted => trivial

theorem call_erase {Γ' ps rs Γf : Ctx} (args : Args C Γ ps) (ret : CallRet Γ rs Γ')
    (hb : Ext (rs ++ ps) Γf) (body : TStep C (rs ++ ps) Γf)
    (bodyU : State C (rs ++ ps) → Res (State C Γf))
    (hbody : StepAgrees body bodyU) :
    StepAgrees (TRun.call args ret hb body) (Run.call args ret hb bodyU) := fun σ => by
  refine TRes.Agrees.bind (args.evalT_erase σ) fun a => ?_
  show TRes.Agrees _ _ (do
    let (τ, r) ← ret.enter σ.erase.glob
    let υ ← bodyU (State.ofGlob τ (Env.append rs r (TEnv.erase ps a)))
    pure (υ.withEnv (ret.leave σ.erase.env (Env.take rs (Env.drop hb υ.env)))))
  have key := CallRet.enterT_erase ret σ a (fun s => do
    let υ ← bodyU s
    pure (υ.withEnv (ret.leave σ.erase.env (Env.take rs (Env.drop hb υ.env)))))
  refine (congrArg (TRes.Agrees _ _) key).mpr ?_
  refine TRes.Agrees.bind (hbody _) fun o => TRes.Agrees.of_eq (congrArg Except.ok ?_)
  rw [TState.withEnv_erase, CallRet.leaveT_erase, TEnv.erase_wk, ← TEnv.take_erase,
    ← TEnv.drop_erase]
  rfl

theorem tryCall_erase {ρ κ Γ₁ Γ₂ Γ₃ Γ₄ : Ctx} (call : ExtCall C Γ) (rets : Binders ρ)
    (h₁ : Ext (ρ ++ Γ) Γ₁) (ok : TStep C (ρ ++ Γ) Γ₁) (okU : State C (ρ ++ Γ) → Res (State C Γ₁))
    (h₂ : Ext Γ Γ₂) (err : TStep C Γ Γ₂) (errU : State C Γ → Res (State C Γ₂))
    (code : CodeBinder κ) (h₃ : Ext (κ ++ Γ) Γ₃) (pnc : TStep C (κ ++ Γ) Γ₃)
    (pncU : State C (κ ++ Γ) → Res (State C Γ₃)) (h₄ : Ext Γ Γ₄) (other : TStep C Γ Γ₄)
    (otherU : State C Γ → Res (State C Γ₄)) (hok : StepAgrees ok okU) (herr : StepAgrees err errU)
    (hpnc : StepAgrees pnc pncU) (hother : StepAgrees other otherU) :
    StepAgrees (TRun.tryCall call rets h₁ ok h₂ err code h₃ pnc h₄ other)
      (Run.tryCall call rets h₁ okU h₂ errU code h₃ pncU h₄ otherU) := fun σ => by
  unfold TRun.tryCall Run.tryCall
  rw [ExtCall.keyT_erase, ok_bind, show σ.erase.tx.ext = σ.tx.ext from rfl]
  cases lookupBy (call.keyT σ) σ.tx.ext with
  | none => rfl
  | some x =>
    cases x with
    | ok vs =>
      refine TRes.Agrees.bind (rets.decodeT_erase (H := σ.H) vs) fun x => ?_
      rcases x with ⟨r, rest⟩
      show TRes.Agrees _ ((ok (σ.withEnv (TEnv.append ρ r σ.env))).map _)
        ((okU (σ.erase.withEnv (Env.append ρ (TEnv.erase ρ r) σ.erase.env))).map _)
      rw [show σ.erase.withEnv (Env.append ρ (TEnv.erase ρ r) σ.erase.env) =
        (σ.withEnv (TEnv.append ρ r σ.env)).erase by
          rw [TState.withEnv_erase, TEnv.append_erase]; rfl]
      exact (hok _).emap fun o => (TState.drop_erase _ o.st).symm
    | error => exact (herr σ).emap fun o => (TState.drop_erase _ o.st).symm
    | panic c =>
      refine TRes.Agrees.bind (code.decodeT_erase (H := σ.H) c) fun r => ?_
      show TRes.Agrees _ ((pnc (σ.withEnv (TEnv.append κ r σ.env))).map _)
        ((pncU (σ.erase.withEnv (Env.append κ (TEnv.erase κ r) σ.erase.env))).map _)
      rw [show σ.erase.withEnv (Env.append κ (TEnv.erase κ r) σ.erase.env) =
        (σ.withEnv (TEnv.append κ r σ.env)).erase by
          rw [TState.withEnv_erase, TEnv.append_erase]; rfl]
      exact (hpnc _).emap fun o => (TState.drop_erase _ o.st).symm
    | other => exact (hother σ).emap fun o => (TState.drop_erase _ o.st).symm

end TRun

/-! ### Loops -/

/-- One unwinding step's outcome against the untyped one: the same state to
go on from, or results that agree (a typed `diverge` or `exhausted` against
anything). -/
def SumAgrees {α β : Type} (f : α → β) (x : α ⊕ TRes α) (y : β ⊕ Res β) : Prop :=
  match x with
  | .inl a => y = .inl (f a)
  | .inr t => (t = .error .diverge ∨ t = .error .exhausted) ∨ ∃ u, y = .inr u ∧ TRes.Agrees f t u

theorem SumAgrees.inr {α β : Type} {f : α → β} {t : TRes α} {u : Res β}
    (h : TRes.Agrees f t u) : SumAgrees f (.inr t) (.inr u) := Or.inr ⟨u, rfl, h⟩

theorem loop_step_erase {α β : Type} {f : α → β} {body : α → TRes α} {bodyU : β → Res β}
    {c : α → TRes Bool} {cU : β → Res Value}
    (hbody : ∀ a, TRes.Agrees f (body a) (bodyU (f a)))
    (hc : ∀ a, TRes.Agrees (fun b : Bool => PrimTy.erase (p := .bool) b) (c a) (cU (f a))) (a : α) :
    SumAgrees f (TLoop.step body c a) (Loop.step bodyU cU (f a)) := by
  unfold TLoop.step Loop.step
  have h := hc a
  revert h
  cases c a with
  | ok b =>
    intro h
    rw [show cU (f a) = .ok (.bool b) from h]
    cases b with
    | false => exact SumAgrees.inr rfl
    | true =>
      show SumAgrees f (match body a with
          | .error h => .inr (.error h)
          | .ok τ => .inl τ)
        (match bodyU (f a) with
          | .error h => .inr (.error h)
          | .ok τ => .inl τ)
      have hb := hbody a
      revert hb
      cases body a with
      | ok a' => intro hb; rw [show bodyU (f a) = .ok (f a') from hb]; rfl
      | error e =>
        intro hb
        cases e with
        | revert => rw [show bodyU (f a) = .error .revert from hb]; exact SumAgrees.inr rfl
        | panic => rw [show bodyU (f a) = .error .panic from hb]; exact SumAgrees.inr rfl
        | diverge => exact Or.inl (Or.inl rfl)
        | exhausted => exact Or.inl (Or.inr rfl)
  | error e =>
    intro h
    cases e with
    | revert => rw [show cU (f a) = .error .revert from h]; exact SumAgrees.inr rfl
    | panic => rw [show cU (f a) = .error .panic from h]; exact SumAgrees.inr rfl
    | diverge => exact Or.inl (Or.inl rfl)
    | exhausted => exact Or.inl (Or.inr rfl)

theorem loop_iterN_erase {α β : Type} {f : α → β} {body : α → TRes α} {bodyU : β → Res β}
    {c : α → TRes Bool} {cU : β → Res Value}
    (hbody : ∀ a, TRes.Agrees f (body a) (bodyU (f a)))
    (hc : ∀ a, TRes.Agrees (fun b : Bool => PrimTy.erase (p := .bool) b) (c a) (cU (f a))) :
    (n : Nat) → (a : α) → SumAgrees f (TLoop.iterN body c n a) (Loop.iterN bodyU cU n (f a))
  | 0, _ => rfl
  | n + 1, a => by
    have hs := loop_step_erase hbody hc a
    simp only [TLoop.iterN, Loop.iterN]
    revert hs
    cases TLoop.step body c a with
    | inl a' =>
      intro hs
      rw [show Loop.step bodyU cU (f a) = .inl (f a') from hs]
      exact loop_iterN_erase hbody hc n a'
    | inr t =>
      intro hs
      rcases hs with hd | ⟨u, hu, ht⟩
      · exact Or.inl hd
      · rw [hu]
        exact Or.inr ⟨u, rfl, ht⟩

theorem loop_run_erase {α β : Type} {f : α → β} {body : α → TRes α} {bodyU : β → Res β}
    {c : α → TRes Bool} {cU : β → Res Value}
    (hbody : ∀ a, TRes.Agrees f (body a) (bodyU (f a)))
    (hc : ∀ a, TRes.Agrees (fun b : Bool => PrimTy.erase (p := .bool) b) (c a) (cU (f a)))
    (a : α) : TRes.Agrees f (TLoop.run body c a) (Loop.run bodyU cU (f a)) := by
  by_cases hex : ∃ r n, TLoop.iterN body c n a = .inr r
  · obtain ⟨r, n, hn⟩ := hex
    rw [TLoop.run_of_iterN hn]
    have hs := loop_iterN_erase hbody hc n a
    rw [hn] at hs
    rcases hs with hd | ⟨u, hu, hr⟩
    · rcases hd with rfl | rfl <;> trivial
    · rw [Loop.run_of_iterN hu]
      exact hr
  · rw [TLoop.run_of_not_done fun n => ?_]
    · trivial
    · cases h : TLoop.iterN body c n a with
      | inl a' => exact ⟨a', rfl⟩
      | inr r => exact absurd ⟨r, n, h⟩ hex

namespace TRun

variable {Γ : Ctx}

theorem loop_erase {Γ₁ : Ctx} (c : Val C Γ .bool) (h : Ext Γ Γ₁) (body : TStep C Γ Γ₁)
    (bodyU : State C Γ → Res (State C Γ₁))
    (hbody : StepAgrees body bodyU) : StepAgrees (TRun.loop c h body) (Run.loop c h bodyU) :=
  fun σ => loop_run_erase (f := fun o : Out C σ.H Γ => o.st.erase)
    (fun o => TRes.Agrees.emap (g := fun o' : Out C σ.H Γ => o'.st.erase) (hbody o.st)
      fun o' => (TState.drop_erase h o'.st).symm)
    (fun o => c.evalT_erase o.st) ⟨σ, List.prefix_refl _⟩

end TRun

/-! ## The run -/

mutual

theorem Stmt.trunR_erase : {Γ Γ' : Ctx} → (s : Stmt C Γ Γ') →
    StepAgrees s.trunR s.runR
  | _, _, .assign l r => TRun.assign_erase l r
  | _, _, .rebind i r => TRun.rebind_erase i r
  | _, _, .assignLocal i r => TRun.assignLocal_erase i r
  | _, _, .declLocal p _ init => TRun.declLocal_erase p init
  | _, _, .declStorage R _ init => TRun.declStorage_erase R init
  | _, _, .opAssign op hop hp l r => TRun.opAssign_erase op hop hp l r
  | _, _, .incDec op hp l => TRun.incDec_erase op hp l
  | _, _, .assignIncDec i op hp l _ => TRun.assignIncDec_erase i op hp l
  | _, _, .push b v _ => TRun.push_erase b v
  | _, _, .pop b => TRun.pop_erase b
  | _, _, .transfer r a => TRun.transfer_erase r a
  | _, _, .send pv r a => TRun.send_erase pv r a
  | _, _, .declMem R _ init _ hm => TRun.declMem_erase R init hm
  | _, _, .rebindMem i r => TRun.rebindMem_erase i r
  | _, _, .assignFromMem l p => TRun.assignFromMem_erase l p
  | _, _, .assignMem l r => TRun.assignMem_erase l r
  | _, _, .delete l => TRun.delete_erase l
  | _, _, .deleteMem p _ => TRun.deleteMem_erase p
  | _, _, .assignNew l n hn => TRun.assignNew_erase l n hn
  | _, _, .ite c thn els =>
    TRun.ite_erase c thn.ext thn.trunR thn.runR els.ext els.trunR els.runR
      (Prog.trunR_erase thn) (Prog.trunR_erase els)
  | _, _, .require c => TRun.require_erase c
  | _, _, .assert c => TRun.assert_erase c
  | _, _, .revert => fun _ => rfl
  | _, _, .call _ args ret body =>
    TRun.call_erase args ret body.ext body.trunR body.runR (Prog.trunR_erase body)
  | _, _, .tryCall call rets ok err code pnc other =>
    TRun.tryCall_erase call rets ok.ext ok.trunR ok.runR err.ext err.trunR err.runR code
      pnc.ext pnc.trunR pnc.runR other.ext other.trunR other.runR
      (Prog.trunR_erase ok) (Prog.trunR_erase err)
      (Prog.trunR_erase pnc) (Prog.trunR_erase other)
  | _, _, .loop _ c body =>
    TRun.loop_erase c body.ext body.trunR body.runR (Prog.trunR_erase body)
  | _, _, .block body =>
    TRun.block_erase body.ext body.trunR body.runR (Prog.trunR_erase body)

theorem Prog.trunR_erase : {Γ Γ' : Ctx} → (P : Prog C Γ Γ') →
    StepAgrees P.trunR P.runR
  | _, _, .nil => fun _ => rfl
  | _, _, .cons s P =>
    TRun.seq_erase s.trunR s.runR P.trunR P.runR (Stmt.trunR_erase s)
      (Prog.trunR_erase P)

end

/-- **The typed run erases to the scoped run**: from a typed state, the state
a statement leaves erases to the one `Stmt.run` leaves from the erased state,
and it reverts or panics where that one does. -/
theorem Stmt.trun_erase {Γ Γ' : Ctx} (σ : TState C Γ) (s : Stmt C Γ Γ') :
    TRes.Agrees (fun o : Out C σ.H Γ' => o.st.erase) (s.trun σ) (s.run σ.erase) :=
  Stmt.trunR_erase s σ

/-- **The typed run erases to the scoped run**, for a sequence. -/
theorem Prog.trun_erase {Γ Γ' : Ctx} (σ : TState C Γ) (P : Prog C Γ Γ') :
    TRes.Agrees (fun o : Out C σ.H Γ' => o.st.erase) (P.trun σ) (P.run σ.erase) :=
  Prog.trunR_erase P σ

/-- A typed run that ends, ends the untyped run in its erasure. -/
theorem Prog.run_of_trun {Γ Γ' : Ctx} {σ : TState C Γ} {P : Prog C Γ Γ'}
    {o : Out C σ.H Γ'} (ho : P.trun σ = .ok o) : P.run σ.erase = .ok o.st.erase := by
  have := Prog.trun_erase σ P
  rw [ho] at this
  exact this

/-- A typed run that reverts or panics halts the untyped run the same way:
the untyped run is never stuck where the typed one is neither diverging nor
exhausted. -/
theorem Prog.run_halt_of_trun {Γ Γ' : Ctx} {σ : TState C Γ} {P : Prog C Γ Γ'}
    {e : THalt} (he : e ≠ .diverge) (hx : e ≠ .exhausted) (ho : P.trun σ = .error e) :
    P.run σ.erase = .error e.erase := by
  have := Prog.trun_erase σ P
  rw [ho] at this
  cases e with
  | revert => exact this
  | panic => exact this
  | diverge => exact absurd rfl he
  | exhausted => exact absurd rfl hx

/-- From a contract's deployed storage. -/
theorem Prog.trun_init_erase {Γ' : Ctx} (P : Prog C [] Γ') :
    TRes.Agrees (fun o : Out C (TState.init C).H Γ' => o.st.erase) (P.trun (TState.init C))
      (P.run (State.ofSem { storage := C.initStorage })) := by
  rw [← TState.init_erase]
  exact Prog.trun_erase _ P

/-! ## Examples -/

/-- `solc`'s order of `++` holds of the scoped run too: the typed run ends
(`Semantics/Core/TypedRun.lean`), and the scoped run ends in its erasure. -/
example : ∃ τ, Prog.run (TState.ofStorage Storage.testSuite).erase incOrderCore = .ok τ := by
  cases h : Prog.trun (TState.ofStorage Storage.testSuite) incOrderCore with
  | ok o => exact ⟨_, Prog.run_of_trun h⟩
  | error e =>
    have : (Prog.trun (TState.ofStorage Storage.testSuite) incOrderCore).halt? = none := by
      decide +kernel
    rw [h] at this
    cases this

end Solidity.Core
