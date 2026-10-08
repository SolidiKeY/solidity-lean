import Solidity.Calculus.Core.SoundKit
import Solidity.Calculus.SoundUpdate

/-!
# Soundness of the update arms

The rules of `Calculus/Core/Arms.lean` and `Step.lean` whose premise is an
update (`Premise.Sound`, `Calculus/Core/ProvesSound.lean`).  An update is a
term of `Update.lean`, read on the erasure, so each arm is an equation
between the update and M3's run of the statement (`*_run`, stated over any
untyped state), carried to the typed run by the bridge
(`Premise.sound_update_run`, `Calculus/Core/SoundKit.lean`).  Before them,
M3's run with a local pushed (`pushed`, `MLoc.Agree`, `OpLoc.Agree`) and
the global operations' frame lemmas (`Calculus/SoundUpdate.lean`'s, on
`σ.glob`).

The bridge asks of the typed run that it does not diverge under the
diamond: an expression, a location and every write but a push neither
diverge nor are exhausted (`Val.evalT_ends` and its kin,
`Typing/StraightRun.lean`), and a push onto `2^256 - 1` elements is
exhausted (`TRun.push_nd`, decision 15), which both modalities accept.  Every
statement is on the bridge: no struct repeats a member name (decision 16).
-/

namespace Solidity.Core
open Solidity (Modality Srt Op0 Op1 Op2 Op3 NoPanic)
open Semantics (Value SVal MVal Seg Halt Res)
open Solidity (readAddr)

variable {C : Contract}


/-! ## A statement read with a local pushed runs as before

A capture's statement is the one it replaces with the captured part read
from the fresh local, and the rest shifted under it (`Val.up` and its kin):
from the state with the local pushed, it runs as the statement it replaces,
the local kept on top.  One lemma per kind of statement, given that its parts
read as the replaced statement's do. -/

section Push

variable {Γ : Ctx} {t : LTy} (σ : State C Γ) (w : t.Denote C)

/-- The outcome of a run from `σ`, the local `w` pushed on its state. -/
abbrev pushed (w : t.Denote C) (r : Res (State C Γ)) : Res (State C (t :: Γ)) :=
  r.map (State.push · w)

theorem pushed_bind {α : Type} (x : Res α) (f : α → Res (State C Γ)) :
    pushed w (x >>= f) = x >>= fun a => pushed w (f a) := by
  cases x <;> rfl

theorem pushed_pure (τ : State C Γ) : pushed w (pure τ) = pure (τ.push w) := rfl

theorem withGlob_map_push (x : Res Semantics.State) :
    (σ.push w).withGlob <$> x = pushed w (σ.withGlob <$> x) := by
  cases x <;> rfl

/-- What the push lemmas rewrite with. -/
macro "push_run" "[" ls:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| simp only [State.glob_push, withGlob_map_push, pushed_bind, pushed_pure,
    State.push_setLocal, State.push_withGlob, $ls,*])

/-- The outcome of a step that also gives a value, the local pushed. -/
abbrev pushed₂ (w : t.Denote C) (r : Res (State C Γ × Value)) : Res (State C (t :: Γ) × Value) :=
  r.map fun x => (x.1.push w, x.2)

/-! ### Parts that read as before -/

/-- A compound target read with a local pushed as `l` reads: the same local
one down, or a receiver and index that read as `l`'s. -/
inductive OpLoc.Agree (σ : State C Γ) (w : t.Denote C) :
    {p : PrimTy} → OpLoc C (t :: Γ) p → OpLoc C Γ p → Prop
  | «local» {p : PrimTy} (i : Idx Γ (.val p)) : OpLoc.Agree σ w (.local i.there) (.local i)
  | root {p : PrimTy} (r : Name) (h : C.rootType r = some (.prim p)) :
      OpLoc.Agree σ w (.root r h) (.root r h)
  | field {s : Name} {p : PrimTy} {b' : SPath C (t :: Γ) (.struct s)} {b : SPath C Γ (.struct s)}
      (f : Name) (h : C.fieldType s f = some (.prim p)) (hb : b'.resolve (σ.push w) = b.resolve σ) :
      OpLoc.Agree σ w (.field b' f h) (.field b f h)
  | index {R : RefTy} {k p : PrimTy} (it : IndexTy R k (.prim p)) {b' : SPath C (t :: Γ) (.ref R)}
      {b : SPath C Γ (.ref R)} {i' : Simple C (t :: Γ) k} {i : Simple C Γ k}
      (hb : b'.resolve (σ.push w) = b.resolve σ) (hi : i'.eval (σ.push w) = i.eval σ) :
      OpLoc.Agree σ w (.index it b' i') (.index it b i)
  | mfield {s : Name} {p : PrimTy} {b' : MPath C (t :: Γ) (.struct s)} {b : MPath C Γ (.struct s)}
      (f : Name) (h : C.fieldType s f = some (.prim p)) (hb : b'.mval (σ.push w) = b.mval σ) :
      OpLoc.Agree σ w (.mfield b' f h) (.mfield b f h)
  | mindex {R : RefTy} {p : PrimTy} (a : ArrTy R (.prim p)) {b' : MPath C (t :: Γ) (.ref R)}
      {b : MPath C Γ (.ref R)} {i' : Simple C (t :: Γ) .uint} {i : Simple C Γ .uint}
      (hb : b'.mval (σ.push w) = b.mval σ) (hi : i'.eval (σ.push w) = i.eval σ) :
      OpLoc.Agree σ w (.mindex a b' i') (.mindex a b i)

/-- A memory location read with a local pushed as `l` reads. -/
inductive MLoc.Agree (σ : State C Γ) (w : t.Denote C) :
    {T : Ty} → MLoc C (t :: Γ) T → MLoc C Γ T → Prop
  | field {s : Name} {T : Ty} {b' : MPath C (t :: Γ) (.struct s)} {b : MPath C Γ (.struct s)}
      (f : Name) (h : C.fieldType s f = some T) (hb : b'.mval (σ.push w) = b.mval σ) :
      MLoc.Agree σ w (.field b' f h) (.field b f h)
  | index {R : RefTy} {E : Ty} (a : ArrTy R E) {b' : MPath C (t :: Γ) (.ref R)}
      {b : MPath C Γ (.ref R)} {i' : Val C (t :: Γ) .uint} {i : Val C Γ .uint}
      (hb : b'.mval (σ.push w) = b.mval σ) (hi : i'.eval (σ.push w) = i.eval σ) :
      MLoc.Agree σ w (.index a b' i') (.index a b i)

variable {σ w} in
theorem MLoc.Agree.read {T : Ty} {l' : MLoc C (t :: Γ) T} {l : MLoc C Γ T}
    (h : MLoc.Agree σ w l' l) : l'.read (σ.push w) = l.read σ := by
  cases h with
  | field f h hb => simp only [MLoc.read, hb, State.glob_push]
  | index a hb hi => simp only [MLoc.read, hb, hi, State.glob_push]

variable {σ w} in
theorem MLoc.Agree.addr {T : Ty} {l' : MLoc C (t :: Γ) T} {l : MLoc C Γ T}
    (h : MLoc.Agree σ w l' l) : l'.addr (σ.push w) = l.addr σ := by
  cases h with
  | field f h hb => simp only [MLoc.addr, hb]
  | index a hb hi => simp only [MLoc.addr, hb, hi]

variable {σ w} in
theorem MLoc.Agree.write {T : Ty} {l' : MLoc C (t :: Γ) T} {l : MLoc C Γ T}
    (h : MLoc.Agree σ w l' l) (mv : Semantics.MVal) : l'.write (σ.push w) mv = pushed w (l.write σ mv) := by
  cases h with
  | field f h hb => push_run [MLoc.write, hb]
  | index a hb hi => push_run [MLoc.write, hb, hi]

theorem MLoc.Agree.of_up {T : Ty} (l : MLoc C Γ T) : MLoc.Agree σ w l.up l := by
  cases l with
  | field b f h => exact .field f h (MPath.mval_up σ w b)
  | index a b i => exact .index a (MPath.mval_up σ w b) (Val.eval_up σ w i)

theorem OpLoc.Agree.of_up {p : PrimTy} (l : OpLoc C Γ p) : OpLoc.Agree σ w l.up l := by
  cases l with
  | «local» i => exact .local i
  | root r h => exact .root r h
  | field b f h => exact .field f h (SPath.resolve_up σ w b)
  | index it b i => exact .index it (SPath.resolve_up σ w b) (Simple.eval_up i σ w)
  | mfield b f h => exact .mfield f h (MPath.mval_up σ w b)
  | mindex a b i => exact .mindex a (MPath.mval_up σ w b) (Simple.eval_up i σ w)

variable {σ w} in
theorem OpLoc.Agree.store {p : PrimTy} {l' : OpLoc C (t :: Γ) p} {l : OpLoc C Γ p}
    (h : OpLoc.Agree σ w l' l) (op : BinOp) (v : Value) :
    l'.store (σ.push w) op v = pushed w (l.store σ op v) := by
  cases h with
  | «local» i => push_run [OpLoc.store, opLocal, State.get_push_there]
  | root r h => push_run [OpLoc.store]
  | field f h hb => push_run [OpLoc.store, Loc.resolve, hb]
  | index it hb hi => push_run [OpLoc.store, Loc.resolve, Val.eval, hb, hi]
  | mfield f h hb => push_run [OpLoc.store, hb]
  | mindex a hb hi => push_run [OpLoc.store, hb, hi]

theorem pushed₂_bind {α : Type} (x : Res α) (f : α → Res (State C Γ × Value)) :
    pushed₂ w (x >>= f) = x >>= fun a => pushed₂ w (f a) := by
  cases x <;> rfl

variable {σ w} in
theorem OpLoc.Agree.bump {p : PrimTy} {l' : OpLoc C (t :: Γ) p} {l : OpLoc C Γ p}
    (h : OpLoc.Agree σ w l' l) (op : IncDec) :
    l'.bump (σ.push w) op = pushed₂ w (l.bump σ op) := by
  cases h with
  | «local» i => push_run [OpLoc.bump, bumpLocal, State.get_push_there, pushed₂_bind]; rfl
  | root r h =>
    simp only [OpLoc.bump, State.glob_push]
    cases bumpStore σ.glob op _ r [] with
    | error => rfl
    | ok x => rfl
  | field f h hb =>
    push_run [OpLoc.bump, Loc.resolve, hb, pushed₂_bind]
    congr 1; funext q; cases bumpStore σ.glob op p q.1 q.2 <;> rfl
  | index it hb hi =>
    push_run [OpLoc.bump, Loc.resolve, Val.eval, hb, hi, pushed₂_bind]
    congr 1; funext q; cases bumpStore σ.glob op p q.1 q.2 <;> rfl
  | mfield f h hb =>
    push_run [OpLoc.bump, hb, pushed₂_bind]
    congr 1; funext q; congr 1; funext id; cases bumpMem σ.glob op p _ <;> rfl
  | mindex a hb hi =>
    push_run [OpLoc.bump, hb, hi, pushed₂_bind]
    congr 1; funext q; congr 1; funext id; congr 1; funext iv; congr 1; funext n
    cases bumpMem σ.glob op p _ <;> rfl

/-! ### Right-hand sides that read as before -/

/-- An alias's right-hand side, its state pushed. -/
abbrev pushedA {R : RefTy} (w : t.Denote C) (r : Res (State C Γ × (Name × List Seg))) :
    Res (State C (t :: Γ) × (Name × List Seg)) :=
  r.map fun x => (x.1.push w, x.2)

/-- A memory right-hand side, its state pushed. -/
abbrev pushedM (w : t.Denote C) (r : Res (State C Γ × Nat)) : Res (State C (t :: Γ) × Nat) :=
  r.map fun x => (x.1.push w, x.2)

theorem pushedA_bind {R : RefTy} {α : Type} (x : Res α)
    (f : α → Res (State C Γ × (Name × List Seg))) :
    pushedA (R := R) w (x >>= f) = x >>= fun a => pushedA (R := R) w (f a) := by
  cases x <;> rfl

theorem pushedA_pure {R : RefTy} (τ : State C Γ) (q : Name × List Seg) :
    pushedA (R := R) w (pure (τ, q)) = pure (τ.push w, q) := rfl

theorem pushedM_bind {α : Type} (x : Res α) (f : α → Res (State C Γ × Nat)) :
    pushedM w (x >>= f) = x >>= fun a => pushedM w (f a) := by
  cases x <;> rfl

theorem pushedM_pure (τ : State C Γ) (n : Nat) : pushedM w (pure (τ, n)) = pure (τ.push w, n) := rfl

theorem ARhs.eval_path_push {R : RefTy} (p' : SPath C (t :: Γ) (.ref R)) (p : SPath C Γ (.ref R))
    (h : p'.resolve (σ.push w) = p.resolve σ) :
    (ARhs.path p').eval (σ.push w) = pushedA (R := R) w ((ARhs.path p).eval σ) := by
  simp only [ARhs.eval, h]
  cases p.resolve σ <;> rfl

theorem ARhs.eval_push_push {R : RefTy} (b' : SPath C (t :: Γ) (.array (.ref R)))
    (b : SPath C Γ (.array (.ref R))) (hd : (Ty.ref R).defaultOkS = true)
    (h : b'.resolve (σ.push w) = b.resolve σ) :
    (ARhs.push b' hd).eval (σ.push w) = pushedA (R := R) w ((ARhs.push b hd).eval σ) := by
  push_run [ARhs.eval, h, pushedA_bind, pushedA_pure]

theorem ARhs.eval_up {R : RefTy} (r : ARhs C Γ R) :
    r.up.eval (σ.push w) = pushedA (R := R) w (r.eval σ) := by
  cases r with
  | path p => exact ARhs.eval_path_push σ w p.up p (SPath.resolve_up σ w p)
  | push b hd => exact ARhs.eval_push_push σ w b.up b hd (SPath.resolve_up σ w b)

theorem MRhs.eval_alias_push {R : RefTy} (p' : MPath C (t :: Γ) (.ref R)) (p : MPath C Γ (.ref R))
    (h : p'.mval (σ.push w) = p.mval σ) :
    (MRhs.alias p').eval (σ.push w) = pushedM w ((MRhs.alias p).eval σ) := by
  push_run [MRhs.eval, h, pushedM_bind, pushedM_pure]

theorem MRhs.eval_copy_push {R : RefTy} (p' : SPath C (t :: Γ) (.ref R)) (p : SPath C Γ (.ref R))
    (hm : (Ty.ref R).mapFree = true) (h : p'.resolve (σ.push w) = p.resolve σ) :
    (MRhs.copy p' hm).eval (σ.push w) = pushedM w ((MRhs.copy p hm).eval σ) := by
  push_run [MRhs.eval, h, pushedM_bind, pushedM_pure]

theorem MRhs.eval_newArr_push {R : RefTy} (n' : Simple C (t :: Γ) .uint) (n : Simple C Γ .uint)
    (hn : R.newArrOk = true) (h : n'.eval (σ.push w) = n.eval σ) :
    (MRhs.newArr n' hn).eval (σ.push w) = pushedM w ((MRhs.newArr (R := R) n hn).eval σ) := by
  push_run [MRhs.eval, h, pushedM_bind, pushedM_pure]

theorem MRhs.eval_up {R : RefTy} (r : MRhs C Γ R) :
    r.up.eval (σ.push w) = pushedM w (r.eval σ) := by
  cases r with
  | alias p => exact MRhs.eval_alias_push σ w p.up p (MPath.mval_up σ w p)
  | copy p hm => exact MRhs.eval_copy_push σ w p.up p hm (SPath.resolve_up σ w p)
  | newArr n hn => exact MRhs.eval_newArr_push σ w n.up n hn (Simple.eval_up n σ w)

theorem MSrc.mval_up {T : Ty} (r : MSrc C Γ T) : r.up.mval (σ.push w) = r.mval σ := by
  cases r with
  | val v => simp only [MSrc.up, MSrc.mval, Val.eval_up]
  | ref p => simp only [MSrc.up, MSrc.mval, MPath.mval_up]

end Push

/-! ## Updates: the update ends as the statement does

Step 3 of every family.  The update reads its right-hand sides in the state
it is applied in, the statement left to right; both reach the same writes
through the same reads, and a write of the storage (the heap) changes
nothing else (`Calculus/SoundUpdate.lean`'s `*_with`). -/

section Updates

variable {Γ : Ctx} {m : Modality} (σ : State C Γ)

theorem Src.eval_lower {T : Ty} (r : Src C Γ T) : r.lower.eval σ = r.value σ := by
  cases r with
  | val v => simp only [Src.lower, Tm.eval, Op1.eval, Src.value, Val.eval_lower]
  | copy p hm => simp only [Src.lower, Tm.eval, Op2.eval, Op0.eval, Src.value, SPath.eval_lower,
      pure_bind]

theorem MSrc.eval_lower {T : Ty} (r : MSrc C Γ T) : r.lower.eval σ = r.mval σ := by
  cases r with
  | val v => simp only [MSrc.lower, Tm.eval, Op1.eval, MSrc.mval, Val.eval_lower]
  | ref p => simp only [MSrc.lower, Tm.eval, Op1.eval, MSrc.mval, MPath.eval_lower, bind_assoc]

theorem MLoc.eval_lower_addr {T : Ty} (l : MLoc C Γ T) : l.lower.eval σ = l.addr σ := by
  cases l with
  | field b f h => simp only [MLoc.lower, Tm.eval, Op1.eval, MLoc.addr, MPath.eval_lower, bind_assoc]
  | index a b i => simp only [MLoc.lower, Tm.eval, Op2.eval, MLoc.addr, MPath.eval_lower,
      Val.eval_lower, bind_assoc]

/-- A storage write through the term: the global part with the storage it
leaves. -/
theorem storage_glob (x : Res Semantics.State)
    (hx : (x >>= fun τ => pure { σ.glob with storage := τ.storage }) = x) :
    (x >>= fun st => pure (σ.withGlob { σ.glob with storage := st.storage })) = σ.withGlob <$> x := by
  conv => rhs; rw [← hx]
  cases x <;> rfl

/-- A heap write through the term. -/
theorem memory_glob (x : Res Semantics.State)
    (hx : (x >>= fun μ => pure { σ.glob with heap := μ.heap, nextId := μ.nextId }) = x) :
    (x >>= fun μ => pure (σ.withGlob { σ.glob with heap := μ.heap, nextId := μ.nextId })) =
      σ.withGlob <$> x := by
  conv => rhs; rw [← hx]
  cases x <;> rfl

theorem upd1_apply (e : UpdElem C Γ Γ) : (Upd.nil.snoc e).apply σ = e.write σ σ := rfl

theorem Simple.eval_ok {p : PrimTy} (s : Simple C Γ p) : ∃ v, s.eval σ = .ok v := by
  cases s <;> exact ⟨_, rfl⟩

theorem Res.bind_ok {α β : Type} (a : α) (f : α → Res β) : ((Except.ok a : Res α) >>= f) = f a :=
  rfl

theorem writeStorage_toSVal (s : Semantics.State) (r : Name) (segs : List Seg) (v : Value) :
    s.writeStorage r segs v.toSVal = s.saveStorage r segs v.toSVal := by
  cases v <;> rfl

/-- A storage save through the term, as the statement's write. -/
theorem saveStorage_glob (r : Name) (segs : List Seg) (v : Semantics.SVal) :
    (σ.glob.saveStorage r segs v >>= fun d =>
      pure (σ.withGlob { σ.glob with storage := d.storage })) =
      σ.withGlob <$> σ.glob.saveStorage r segs v :=
  storage_glob σ _ (Solidity.State.saveStorage_with _ _ _ _)

/-- A heap write through the term, as the statement's write. -/
theorem writeAddr_glob (mv : Semantics.MVal) (a : Semantics.Addr) :
    (writeAddr σ.glob mv a >>= fun μ =>
      pure (σ.withGlob { σ.glob with heap := μ.heap, nextId := μ.nextId })) =
      σ.withGlob <$> writeAddr σ.glob mv a :=
  memory_glob σ _ (Solidity.writeAddr_with _ _ _)

/-- A global step's state and value, with the locals (`Semantics/Core.lean`'s
private `withGlob₂`). -/
def glob₂ (x : Semantics.State × Value) : State C Γ × Value := (σ.withGlob x.1, x.2)

@[simp] theorem glob₂_fst (x : Semantics.State × Value) : (glob₂ σ x).1 = σ.withGlob x.1 := rfl
@[simp] theorem glob₂_snd (x : Semantics.State × Value) : (glob₂ σ x).2 = x.2 := rfl

theorem bind_withGlob (x : Res Semantics.State) :
    (x >>= fun τ => pure (σ.withGlob τ)) = σ.withGlob <$> x := by
  cases x <;> rfl

theorem OpLoc.bump_root {p : PrimTy} (op : IncDec) (r : Name) (h : C.rootType r = some (.prim p)) :
    (OpLoc.root (Γ := Γ) r h).bump σ op = glob₂ σ <$> bumpStore σ.glob op p r [] := rfl

theorem OpLoc.bump_field {p : PrimTy} (op : IncDec) {s : Name} (b : SPath C Γ (.struct s)) (f : Name)
    (h : C.fieldType s f = some (.prim p)) :
    (OpLoc.field b f h).bump σ op = (do
      let (rt, segs) ← (Loc.field b f h).resolve σ
      glob₂ σ <$> bumpStore σ.glob op p rt segs) := rfl

theorem OpLoc.bump_index {p : PrimTy} (op : IncDec) {R : RefTy} {k : PrimTy}
    (it : IndexTy R k (.prim p)) (b : SPath C Γ (.ref R)) (i : Simple C Γ k) :
    (OpLoc.index it b i).bump σ op = (do
      let (rt, segs) ← (Loc.index it b (.simple i)).resolve σ
      glob₂ σ <$> bumpStore σ.glob op p rt segs) := rfl

theorem OpLoc.bump_mfield {p : PrimTy} (op : IncDec) {s : Name} (b : MPath C Γ (.struct s)) (f : Name)
    (h : C.fieldType s f = some (.prim p)) :
    (OpLoc.mfield b f h).bump σ op = (do
      let id ← (← b.mval σ).asRef
      glob₂ σ <$> bumpMem σ.glob op p (.memoryField id f)) := rfl

theorem OpLoc.bump_mindex {p : PrimTy} (op : IncDec) {R : RefTy} (a : ArrTy R (.prim p))
    (b : MPath C Γ (.ref R)) (i : Simple C Γ .uint) :
    (OpLoc.mindex a b i).bump σ op = (do
      let id ← (← b.mval σ).asRef
      let iv ← (← i.eval σ).asInt
      glob₂ σ <$> bumpMem σ.glob op p (.memoryIndex id iv)) := rfl

/-- `localIncrement`, `storageRootIncrement`, `storageFieldIncrement`,
`storageIndexIncrement`, `memoryFieldIncrement`, `memoryIndexArrayIncrement`:
`{l := l ± 1}`. -/
theorem incDec_write {p : PrimTy} (op : IncDec) (l : OpLoc C Γ p) :
    (l.set (l.op op.binOp .one)).write σ σ = Run.incDec op l σ := by
  cases l with
  | «local» i =>
    simp only [Rhs.eval, OpLoc.bump, bumpLocal, OpLoc.set, OpLoc.op, OpLoc.cur, UpdElem.write,
      Tm.eval, Op2.eval, Op0.eval, evalBinop_bump, Solidity.applyBinOp_bump, Run.incDec,
      bind_assoc, pure_bind]
  | root r h =>
    simp only [Loc.lower, OpLoc.bump_root, bumpStore, writeStorage_toSVal, saveStorage_glob,
      OpLoc.set, OpLoc.op, OpLoc.cur, UpdElem.write, Tm.eval, Op3.eval, Op2.eval,
      Op1.eval, Op0.eval, Val.lower, evalBinop_bump, Solidity.applyBinOp_bump, Run.incDec,
      bind_assoc, pure_bind, map_bind, map_pure, glob₂_fst, bind_withGlob]
  | field b f h =>
    simp only [Loc.eval_lower, OpLoc.bump_field, bumpStore, writeStorage_toSVal,
      saveStorage_glob, OpLoc.set, OpLoc.op, OpLoc.cur, UpdElem.write, Tm.eval, Op3.eval, Op2.eval,
      Op1.eval, Op0.eval, Val.lower, evalBinop_bump, Solidity.applyBinOp_bump, Run.incDec,
      bind_assoc, pure_bind, map_bind, map_pure, glob₂_fst, bind_withGlob]
    cases Loc.resolve σ (Loc.field b f h) <;> rfl
  | index it b ie =>
    simp only [Loc.eval_lower, OpLoc.bump_index, bumpStore, writeStorage_toSVal,
      saveStorage_glob, OpLoc.set, OpLoc.op, OpLoc.cur, UpdElem.write, Tm.eval, Op3.eval, Op2.eval,
      Op1.eval, Op0.eval, Val.lower, evalBinop_bump, Solidity.applyBinOp_bump, Run.incDec,
      bind_assoc, pure_bind, map_bind, map_pure, glob₂_fst, bind_withGlob]
    cases Loc.resolve σ (Loc.index it b (.simple ie)) <;> rfl
  | mfield b f h =>
    simp only [MLoc.lower, MPath.eval_lower, OpLoc.bump_mfield, bumpMem, writeAddr_glob,
      Solidity.readLoc_eq, Solidity.writeLoc_eq, OpLoc.set, OpLoc.op, OpLoc.cur, UpdElem.write, Tm.eval, Op3.eval, Op2.eval,
      Op1.eval, Op0.eval, Val.lower, evalBinop_bump, Solidity.applyBinOp_bump, Run.incDec,
      bind_assoc, pure_bind, map_bind, map_pure, glob₂_fst, bind_withGlob]
    cases MPath.mval σ b with
    | error => rfl
    | ok mv => cases hr : mv.asRef <;> simp only [Res.bind_ok, hr] <;> rfl
  | mindex a b ie =>
    obtain ⟨iv, hi⟩ := Simple.eval_ok σ ie
    have hi' : ie.eval σ = pure iv := hi
    simp only [MLoc.lower, MPath.eval_lower, Simple.eval_lower, hi', OpLoc.bump_mindex, bumpMem,
      writeAddr_glob, Solidity.readLoc_eq, Solidity.writeLoc_eq, OpLoc.set, OpLoc.op, OpLoc.cur, UpdElem.write, Tm.eval, Op3.eval, Op2.eval,
      Op1.eval, Op0.eval, Val.lower, evalBinop_bump, Solidity.applyBinOp_bump, Run.incDec,
      bind_assoc, pure_bind, map_bind, map_pure, glob₂_fst, bind_withGlob]
    cases MPath.mval σ b with
    | error => rfl
    | ok mv =>
      cases hr : mv.asRef <;> cases hn : iv.asInt <;> simp only [Res.bind_ok, hr] <;> rfl

theorem writeAddr_ok_with {s x : Semantics.State} {mv : Semantics.MVal} {a : Semantics.Addr}
    (h : writeAddr s mv a = .ok x) : { s with heap := x.heap, nextId := x.nextId } = x := by
  have e := Solidity.writeAddr_with s mv a
  rw [h] at e
  exact Except.ok.inj e

theorem upd2_apply (e₁ e₂ : UpdElem C Γ Γ) :
    ((Upd.nil.snoc e₁).snoc e₂).apply σ = (do e₂.write σ (← e₁.write σ σ)) := rfl

theorem Res.bind_eq_ok {α β : Type} {x : Res α} {f : α → Res β} {b : β} :
    (x >>= f) = .ok b ↔ ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error e => exact ⟨fun h => (nomatch h), fun ⟨_, h, _⟩ => (nomatch h)⟩
  | ok a => exact ⟨fun h => ⟨a, rfl, h⟩, fun ⟨_, h, h'⟩ => by cases h; exact h'⟩

theorem Res.map_eq_ok {α β : Type} {x : Res α} {f : α → β} {b : β} :
    (f <$> x) = .ok b ↔ ∃ a, x = .ok a ∧ f a = b := by
  cases x with
  | error e => exact ⟨fun h => (nomatch h), fun ⟨_, h, _⟩ => (nomatch h)⟩
  | ok a => exact ⟨fun h => ⟨a, rfl, Except.ok.inj h⟩, fun ⟨_, h, h'⟩ => by cases h; rw [← h']; rfl⟩

/-- The value `l++` gives is what the term `bumped(l)` reads in the state before. -/
theorem bump_bumped {p : PrimTy} (op : IncDec) (l : OpLoc C Γ p) {σ' : State C Γ} {v : Value}
    (hb : l.bump σ op = .ok (σ', v)) : (Tm.bumped op p l.cur).eval σ = .ok v := by
  unfold Tm.bumped
  cases l with
  | «local» j =>
    simp only [OpLoc.bump, bumpLocal, Res.bind_eq_ok] at hb
    obtain ⟨n, hn, new, hnew, he⟩ := hb
    cases Except.ok.inj he
    split <;> simp only [OpLoc.cur, Tm.eval, Op2.eval, Op0.eval, evalBinop_bump,
      Solidity.applyBinOp_bump, Res.bind_ok, pure_bind, *]
    all_goals rfl
  | root r h =>
    simp only [OpLoc.bump_root, bumpStore, Res.map_eq_ok, Res.bind_eq_ok] at hb
    obtain ⟨⟨τ, w⟩, ⟨sv, hsv, old, hold, n, hn, new, hnew, τ', hτ', he⟩, hg⟩ := hb
    cases Except.ok.inj he; cases hg
    split <;> simp only [Loc.lower, OpLoc.cur, Tm.eval, Op2.eval, Op0.eval, Val.lower, evalBinop_bump, Solidity.applyBinOp_bump, Res.bind_ok, pure_bind, bind_assoc, hsv, hold, hn, hnew] <;> rfl
  | field b f h =>
    simp only [OpLoc.bump_field, bumpStore, Res.map_eq_ok, Res.bind_eq_ok] at hb
    obtain ⟨⟨rt, segs⟩, hr, ⟨τ, w⟩, ⟨sv, hsv, old, hold, n, hn, new, hnew, τ', hτ', he⟩, hg⟩ := hb
    cases Except.ok.inj he; cases hg
    split <;> simp only [Loc.eval_lower, OpLoc.cur, Tm.eval, Op2.eval, Op0.eval, Val.lower, evalBinop_bump, Solidity.applyBinOp_bump, Res.bind_ok, pure_bind, bind_assoc, hr, hsv, hold, hn, hnew] <;> rfl
  | index it b ie =>
    simp only [OpLoc.bump_index, bumpStore, Res.map_eq_ok, Res.bind_eq_ok] at hb
    obtain ⟨⟨rt, segs⟩, hr, ⟨τ, w⟩, ⟨sv, hsv, old, hold, n, hn, new, hnew, τ', hτ', he⟩, hg⟩ := hb
    cases Except.ok.inj he; cases hg
    split <;> simp only [Loc.eval_lower, OpLoc.cur, Tm.eval, Op2.eval, Op0.eval, Val.lower, evalBinop_bump, Solidity.applyBinOp_bump, Res.bind_ok, pure_bind, bind_assoc, hr, hsv, hold, hn, hnew] <;> rfl
  | mfield b f h =>
    simp only [OpLoc.bump_mfield, bumpMem, Res.map_eq_ok, Res.bind_eq_ok] at hb
    obtain ⟨mv, hmv, id, hid, ⟨τ, w⟩, ⟨old, hold, n, hn, new, hnew, τ', hτ', he⟩, hg⟩ := hb
    cases Except.ok.inj he; cases hg
    simp only [Solidity.readLoc_eq, Res.bind_eq_ok] at hold
    obtain ⟨r, hr, hro⟩ := hold
    split <;> simp only [MLoc.lower, MPath.eval_lower, OpLoc.cur, Tm.eval, Op2.eval, Op1.eval, Op0.eval, Val.lower, evalBinop_bump, Solidity.applyBinOp_bump, Res.bind_ok, pure_bind, bind_assoc, hmv, hid, hr, hro, hn, hnew] <;> rfl
  | mindex a b ie =>
    simp only [OpLoc.bump_mindex, bumpMem, Res.map_eq_ok, Res.bind_eq_ok] at hb
    obtain ⟨mv, hmv, id, hid, iv, hiv, k, hk, ⟨τ, w⟩, ⟨old, hold, n, hn, new, hnew, τ', hτ', he⟩, hg⟩ := hb
    cases Except.ok.inj he; cases hg
    simp only [Solidity.readLoc_eq, Res.bind_eq_ok] at hold
    obtain ⟨r, hr, hro⟩ := hold
    split <;> simp only [MLoc.lower, MPath.eval_lower, Simple.eval_lower, OpLoc.cur, Tm.eval, Op2.eval, Op0.eval, Val.lower, evalBinop_bump, Solidity.applyBinOp_bump, Res.bind_ok, pure_bind, bind_assoc, hmv, hid, hiv, hk,
      hr, hro, hn, hnew] <;> rfl

end Updates

open Solidity (Modality Srt Op0 Op1 Op2 Op3 NoPanic)
open Semantics (Value SVal MVal Seg Halt Res)

/-! ## The equations, over M3's state

Each update arm's equation between its update and M3's run of the
statement, over any M3 state, as `Premise.sound_update_run` asks. -/

section Runs

variable {Γ : Ctx} (σ : State C Γ)

theorem setLocal_run {p : PrimTy} (i : Idx Γ (.val p)) (v : Val C Γ p) :
    (Upd.nil.snoc (.local i (.val v.lower))).apply σ = Stmt.run σ (.assignLocal i v) := by
  show (do pure (σ.setLocal i (← v.lower.eval σ))) = Run.assignLocal i v σ
  rw [Val.eval_lower]; rfl

theorem save_run {T : Ty} (l : Loc C Γ T) (r : Src C Γ T) :
    (Upd.nil.snoc (.storage (.app3 .save .storage l.lower r.lower))).apply σ =
      Stmt.run σ (.assign l r) := by
  show (do
    let st ← Op3.eval σ.glob .save (pure σ.glob) (l.lower.eval σ) (r.lower.eval σ)
    pure (σ.withGlob { σ.glob with storage := st.storage })) = Run.assign l r σ
  simp only [Op3.eval, Loc.eval_lower, Src.eval_lower, Run.assign, bind_assoc, pure_bind]
  congr 1; funext sv; congr 1; funext q
  exact storage_glob σ _ (Solidity.State.writeStorage_with _ _ _ _)

theorem saveMem_run {R : RefTy} (l : Loc C Γ (.ref R)) (p : MPath C Γ (.ref R)) :
    (Upd.nil.snoc (.storage (.app3 .save .storage l.lower
      (.app2 .copyMem .memory p.lower)))).apply σ = Stmt.run σ (.assignFromMem l p) := by
  show (do
    let st ← Op3.eval σ.glob .save (pure σ.glob) (l.lower.eval σ)
      (Op2.eval σ.glob .copyMem (pure σ.glob) (p.lower.eval σ))
    pure (σ.withGlob { σ.glob with storage := st.storage })) = Run.assignFromMem l p σ
  simp only [Op3.eval, Op2.eval, Loc.eval_lower, MPath.eval_lower, Run.assignFromMem, bind_assoc,
    pure_bind]
  congr 1; funext mv; congr 1; funext id; congr 1; funext sv; congr 1; funext q
  exact storage_glob σ _ (Solidity.State.writeStorage_with _ _ _ _)

theorem delAt_run {T : Ty} (l : Loc C Γ T) :
    (Upd.nil.snoc (.storage (.app2 .delAt .storage l.lower))).apply σ =
      Stmt.run σ (.delete l) := by
  show (do
    let st ← Op2.eval σ.glob .delAt (pure σ.glob) (l.lower.eval σ)
    pure (σ.withGlob { σ.glob with storage := st.storage })) = Run.delete l σ
  simp only [Op2.eval, Loc.eval_lower, Run.delete, bind_assoc, pure_bind]
  congr 1; funext q; congr 1; funext cur
  exact storage_glob σ _ (Solidity.State.saveStorage_with _ _ _ _)

theorem writeMem_run {T : Ty} (l : MLoc C Γ T) (r : MSrc C Γ T) :
    (Upd.nil.snoc (.memory (.app3 .write .memory l.lower r.lower))).apply σ =
      Stmt.run σ (.assignMem l r) := by
  show (do
    let μ ← Op3.eval σ.glob .write (pure σ.glob) (l.lower.eval σ) (r.lower.eval σ)
    pure (σ.withGlob { σ.glob with heap := μ.heap, nextId := μ.nextId })) = Run.assignMem l r σ
  simp only [Op3.eval, MLoc.eval_lower_addr, MSrc.eval_lower, Run.assignMem, MLoc.write_eq,
    bind_assoc, pure_bind]
  congr 1; funext mv; congr 1; funext a
  exact memory_glob σ _ (Solidity.writeAddr_with _ _ _)

theorem rebindPath_run {R : RefTy} (i : Idx Γ (.alias R)) (p : SPath C Γ (.ref R)) :
    (Upd.nil.snoc (.local i (.path p.lower))).apply σ = Stmt.run σ (.rebind i (.path p)) := by
  show (do pure (σ.setLocal i (← do pure (some (← p.lower.eval σ))))) = Run.rebind i (.path p) σ
  simp only [SPath.eval_lower, Run.rebind, ARhs.eval, bind_assoc, pure_bind]

theorem rebindMemAlias_run {R : RefTy} (i : Idx Γ (.mem R)) (p : MPath C Γ (.ref R)) :
    (Upd.nil.snoc (.local i (.mref p.lower))).apply σ = Stmt.run σ (.rebindMem i (.alias p)) := by
  show (do pure (σ.setLocal i (← do pure (some (← p.lower.eval σ))))) =
    Run.rebindMem i (.alias p) σ
  simp only [MPath.eval_lower, Run.rebindMem, MRhs.eval, bind_assoc, pure_bind]

theorem opAssign_run {p : PrimTy} (op : BinOp) (hop : op.hasCompoundAssign = true)
    (hp : p.isNumeric = true) (l : OpLoc C Γ p) (se : Simple C Γ p) :
    (Upd.nil.snoc (l.set (l.op op se.lower))).apply σ =
      Stmt.run σ (.opAssign op hop hp l (.simple se)) := by
  obtain ⟨v, hv⟩ := Simple.eval_ok σ se
  rw [upd1_apply]
  show _ = Run.opAssign op l (.simple se) σ
  cases l with
  | «local» i =>
    simp only [OpLoc.set, OpLoc.op, OpLoc.cur, UpdElem.write, Rhs.eval, Tm.eval, Op2.eval,
      Simple.eval_lower, hv, evalBinop_compound hop, Run.opAssign, Val.eval, OpLoc.store, opLocal,
      bind_assoc, pure_bind]
  | root r h =>
    have hv' : se.eval σ = pure v := hv
    simp only [OpLoc.set, OpLoc.op, OpLoc.cur, UpdElem.write, Tm.eval, Op3.eval, Op2.eval,
      Op1.eval, Op0.eval, Val.lower, Loc.lower, Simple.eval_lower, hv', evalBinop_compound hop,
      Run.opAssign, Val.eval, OpLoc.store, opStore, bind_assoc, pure_bind, writeStorage_toSVal,
      saveStorage_glob, map_bind]
  | field b f h =>
    have hv' : se.eval σ = pure v := hv
    simp only [OpLoc.set, OpLoc.op, OpLoc.cur, UpdElem.write, Tm.eval, Op3.eval, Op2.eval,
      Op1.eval, Op0.eval, Val.lower, Loc.eval_lower, Simple.eval_lower, hv', evalBinop_compound hop,
      Run.opAssign, Val.eval, OpLoc.store, opStore, bind_assoc, pure_bind, writeStorage_toSVal,
      saveStorage_glob, map_bind]
    cases Loc.resolve σ (Loc.field b f h) <;> rfl
  | index it b ie =>
    have hv' : se.eval σ = pure v := hv
    simp only [OpLoc.set, OpLoc.op, OpLoc.cur, UpdElem.write, Tm.eval, Op3.eval, Op2.eval,
      Op1.eval, Op0.eval, Val.lower, Loc.eval_lower, Simple.eval_lower, hv', evalBinop_compound hop,
      Run.opAssign, Val.eval, OpLoc.store, opStore, bind_assoc, pure_bind, writeStorage_toSVal,
      saveStorage_glob, map_bind]
    cases Loc.resolve σ (Loc.index it b (.simple ie)) <;> rfl
  | mfield b f h =>
    have hv' : se.eval σ = pure v := hv
    simp only [OpLoc.set, OpLoc.op, OpLoc.cur, UpdElem.write, Tm.eval, Op3.eval, Op2.eval,
      Op1.eval, Op0.eval, Val.lower, MLoc.lower, MPath.eval_lower, Simple.eval_lower, hv',
      evalBinop_compound hop, Run.opAssign, Val.eval, OpLoc.store, opMem, bind_assoc, pure_bind,
      writeAddr_glob, map_bind, Solidity.readLoc_eq, Solidity.writeLoc_eq]
    cases MPath.mval σ b with
    | error => rfl
    | ok mv => cases hr : mv.asRef <;> simp only [Res.bind_ok, hr] <;> rfl
  | mindex a b ie =>
    have hv' : se.eval σ = pure v := hv
    obtain ⟨iv, hi⟩ := Simple.eval_ok σ ie
    have hi' : ie.eval σ = pure iv := hi
    simp only [OpLoc.set, OpLoc.op, OpLoc.cur, UpdElem.write, Tm.eval, Op3.eval, Op2.eval,
      Op1.eval, Op0.eval, Val.lower, MLoc.lower, MPath.eval_lower, Simple.eval_lower, hv', hi',
      evalBinop_compound hop, Run.opAssign, Val.eval, OpLoc.store, opMem, bind_assoc, pure_bind,
      writeAddr_glob, map_bind, Solidity.readLoc_eq, Solidity.writeLoc_eq]
    cases MPath.mval σ b with
    | error => rfl
    | ok mv =>
      cases hr : mv.asRef <;> cases hn : iv.asInt <;> simp only [Res.bind_ok, hr] <;> rfl

theorem incDec_run {p : PrimTy} (op : IncDec) (hp : p.isNumeric = true) (l : OpLoc C Γ p) :
    (Upd.nil.snoc (l.set (l.op op.binOp .one))).apply σ = Stmt.run σ (.incDec op hp l) := by
  rw [upd1_apply]; exact incDec_write σ op l

theorem assignIncDec_run {p : PrimTy} (i : Idx Γ (.val p)) (op : IncDec)
    (hp : p.isNumeric = true) (l : OpLoc C Γ p) (hs : l.recvSimple = true) :
    ((Upd.nil.snoc (l.set (l.op op.binOp .one))).snoc
      (.local i (.val (Tm.bumped op p l.cur)))).apply σ =
      Stmt.run σ (.assignIncDec i op hp l hs) := by
  rw [upd2_apply, incDec_write]
  show _ = Run.assignIncDec i op l σ
  simp only [Run.incDec, Run.assignIncDec, bind_assoc, pure_bind]
  cases hb : l.bump σ op with
  | error => rfl
  | ok x =>
    obtain ⟨σ', v⟩ := x
    show (do pure (σ'.setLocal i (← (Tm.bumped op p l.cur).eval σ))) = _
    rw [bump_bumped σ op l hb]; rfl

end Runs

/-! ## The update arms -/

section Arms

variable {Γ : Ctx} {m : Modality} (σ : TState C Γ)

/-- `localValueAssign`, the reads, `binopAssignment`, `unopAssignment`, the
length reads: `{v := e}` for `v = e;`. -/
theorem sound_setLocal {p : PrimTy} (i : Idx Γ (.val p)) (v : Val C Γ p) :
    Premise.Sound m (.assignLocal i v) (.setLocal i v) σ :=
  Premise.sound_update_run σ (setLocal_run σ.erase i v) fun _ =>
    ((Val.evalT_ends σ v).bind fun _ => TRes.Ends.ok _).1

/-- `storageRootWriteStore`, `storageFieldWriteSave`, `storageIndexWrite*Save`,
`…CopySource`: `{storage := save(storage, l, src)}`. -/
theorem sound_save {T : Ty} (l : Loc C Γ T) (r : Src C Γ T) :
    Premise.Sound m (.assign l r) (.save l r) σ :=
  Premise.sound_update_run (s := .assign l r) σ (save_run σ.erase l r) fun _ =>
    ((Src.valueT_ends σ r).bind fun _ => (Loc.resolveT_ends σ l).bind fun _ =>
      (TRes.Ends.ofOpt _).bind fun _ => TRes.Ends.ok _).1

/-- `memoryToStorage*CopyRoot`: `{storage := save(storage, l, copyMem(memory, p))}`. -/
theorem sound_saveMem {R : RefTy} (l : Loc C Γ (.ref R)) (p : MPath C Γ (.ref R)) :
    Premise.Sound m (.assignFromMem l p) (.saveMem l p) σ :=
  Premise.sound_update_run (s := .assignFromMem l p) σ (saveMem_run σ.erase l p) fun _ =>
    ((MPath.mvalT_ends σ p).bind fun _ => (Loc.resolveT_ends σ l).bind fun _ =>
      (TRes.Ends.ofOpt _).bind fun _ => TRes.Ends.ok _).1

/-- `storageRootDelete`, `storageFieldDelete`, `storageIndexDelete`,
`storageIndexArrayDelete`: `{storage := delAt(storage, l)}`. -/
theorem sound_delAt {T : Ty} (l : Loc C Γ T) : Premise.Sound m (.delete l) (.delAt l) σ :=
  Premise.sound_update_run σ (delAt_run σ.erase l) fun _ =>
    ((Loc.resolveT_ends σ l).bind fun _ => (TRes.Ends.ofOpt _).bind fun _ => TRes.Ends.ok _).1

/-- `memoryFieldWrite`, `memoryIndexWriteArray`, `memoryFieldWriteCopy`,
`memoryIndexWriteCopy`: `{memory := write(memory, l, src)}`. -/
theorem sound_writeMem {T : Ty} (l : MLoc C Γ T) (r : MSrc C Γ T) :
    Premise.Sound m (.assignMem l r) (.writeMem l r) σ :=
  Premise.sound_update_run σ (writeMem_run σ.erase l r) fun _ =>
    ((MSrc.mvalT_ends σ r).bind fun _ => (MLoc.addrT_ends σ l).bind fun _ =>
      (TRes.Ends.ofOpt _).bind fun _ => TRes.Ends.ok _).1

/-- `storageLocalRootRebind`, `…BindLocalRoot`: `{lsv := p}`. -/
theorem sound_rebindPath {R : RefTy} (i : Idx Γ (.alias R)) (p : SPath C Γ (.ref R)) :
    Premise.Sound m (.rebind i (.path p)) (.upd1 (.local i (.path p.lower))) σ :=
  Premise.sound_update_run σ (rebindPath_run σ.erase i p) fun _ =>
    (((SPath.resolveT_ends σ p).bind fun _ => TRes.Ends.ok _).bind fun _ => TRes.Ends.ok _).1

/-- `memoryRootRebind`, `memoryFieldReadAliasRoot`, `memoryIndexReadArrayMemory`:
`{mv := p}`. -/
theorem sound_rebindMemAlias {R : RefTy} (i : Idx Γ (.mem R)) (p : MPath C Γ (.ref R)) :
    Premise.Sound m (.rebindMem i (.alias p)) (.upd1 (.local i (.mref p.lower))) σ :=
  Premise.sound_update_run σ (rebindMemAlias_run σ.erase i p) fun _ =>
    ((MRhs.evalT_ends σ (.alias p)).bind fun _ => TRes.Ends.ok _).1

/-- `localOpAssign`, `storage*OpAssign`, `memory*OpAssign`: `{l := l ⊕ se}`. -/
theorem sound_opAssign {p : PrimTy} (op : BinOp) (hop : op.hasCompoundAssign = true)
    (hp : p.isNumeric = true) (l : OpLoc C Γ p) (se : Simple C Γ p) :
    Premise.Sound m (.opAssign op hop hp l (.simple se)) (.upd1 (l.set (l.op op se.lower))) σ :=
  Premise.sound_update_run σ (opAssign_run σ.erase op hop hp l se) fun _ =>
    (TRes.Ends.bind (TRes.Ends.ok _) fun _ => OpLoc.storeT_ends σ op l _).1

/-- `localIncrement`, `storage*Increment`, `memory*Increment`: `{l := l ± 1}`. -/
theorem sound_incDec {p : PrimTy} (op : IncDec) (hp : p.isNumeric = true) (l : OpLoc C Γ p) :
    Premise.Sound m (.incDec op hp l) (.upd1 (l.set (l.op op.binOp .one))) σ :=
  Premise.sound_update_run σ (incDec_run σ.erase op hp l) fun _ =>
    ((OpLoc.bumpT_ends σ op l).bind fun _ => TRes.Ends.ok _).1

/-- `localAssignIncrement`, `…IncrementAssignment`:
`{l := l ± 1 ‖ v := bumped(l)}`. -/
theorem sound_assignIncDec {p : PrimTy} (i : Idx Γ (.val p)) (op : IncDec)
    (hp : p.isNumeric = true) (l : OpLoc C Γ p) (hs : l.recvSimple = true) :
    Premise.Sound m (.assignIncDec i op hp l hs) (.update ((Upd.nil.snoc
      (l.set (l.op op.binOp .one))).snoc (.local i (.val (Tm.bumped op p l.cur))))) σ :=
  Premise.sound_update_run σ (assignIncDec_run σ.erase i op hp l hs) fun _ =>
    ((OpLoc.bumpT_ends σ op l).bind fun _ => TRes.Ends.ok _).1

end Arms

/-! ## The other update arms (`Step.lean`): the equations -/

section Runs2

variable {Γ : Ctx} (σ : State C Γ)

theorem pushSlot_run {E : Ty} (b : SPath C Γ (.array E)) (hd : (none.isSome || E.defaultOkS) = true) :
    (Upd.nil.snoc (.storage (.app2 (.pushSlot E) .storage b.lower))).apply σ =
      Stmt.run σ (.push b none hd) := by
  rw [upd1_apply]
  show (do
    let st ← Op2.eval σ.glob (.pushSlot E) (pure σ.glob) (b.lower.eval σ)
    pure (σ.withGlob { σ.glob with storage := st.storage })) = Run.push b none σ
  simp only [Op2.eval, SPath.eval_lower, Run.push, bind_assoc, pure_bind]
  congr 1; funext q
  exact storage_glob σ _ (Solidity.pushAt_with _ _ _ _ _)

theorem extend_run {E : Ty} (b : SPath C Γ (.array E)) (hd : (none.isSome || E.defaultOkS) = true) :
    (Upd.nil.snoc (.storage (.app2 (.extend E) .storage b.lower))).apply σ =
      Stmt.run σ (.push b none hd) := by
  rw [upd1_apply]
  show (do
    let st ← Op2.eval σ.glob (.extend E) (pure σ.glob) (b.lower.eval σ)
    pure (σ.withGlob { σ.glob with storage := st.storage })) = Run.push b none σ
  simp only [Op2.eval, SPath.eval_lower, Run.push, pushPlaceAt, pushAt, Src.pushVal,
    SemanticsProperties.State.saveStorage_eq, bind_assoc, pure_bind]
  simp only [bind, Except.bind, pure, Except.pure, Functor.map, Except.map]
  cases b.resolve σ with
  | error => rfl
  | ok q =>
    simp only
    cases σ.glob.findStorage q.1 q.2 with
    | error => rfl
    | ok v =>
      cases v with
      | array elems shadow fx =>
        simp only
        cases σ.glob.storeRes q.1 q.2 _ <;> rfl
      | _ => rfl

theorem pushSome_run {E : Ty} (b : SPath C Γ (.array E)) (r : Src C Γ E)
    (hd : ((some r).isSome || E.defaultOkS) = true) :
    (Upd.nil.snoc (.storage (.app3 .push .storage b.lower r.lower))).apply σ =
      Stmt.run σ (.push b (some r) hd) := by
  rw [upd1_apply]
  show (do
    let st ← Op3.eval σ.glob .push (pure σ.glob) (b.lower.eval σ) (r.lower.eval σ)
    pure (σ.withGlob { σ.glob with storage := st.storage })) = Run.push b (some r) σ
  simp only [Op3.eval, SPath.eval_lower, Src.eval_lower, Run.push, bind_assoc, pure_bind]
  congr 1; funext q
  rw [show Src.pushVal σ (some r) = fun _ => (do pure (← r.value σ).strip) from rfl,
    Solidity.pushAt_const σ.glob E .uint]
  exact storage_glob σ _ (Solidity.pushAt_with _ _ _ _ _)

theorem pop_run {E : Ty} (b : SPath C Γ (.array E)) :
    (Upd.nil.snoc (.storage (.app2 (if E.isMapping then .shrink else .pop)
      .storage b.lower))).apply σ = Stmt.run σ (.pop b) := by
  rw [upd1_apply]
  cases hE : E.isMapping with
  | false =>
    show (do
      let st ← Op2.eval σ.glob .pop (pure σ.glob) (b.lower.eval σ)
      pure (σ.withGlob { σ.glob with storage := st.storage })) = Run.pop b σ
    simp only [Op2.eval, SPath.eval_lower, Run.pop, hE, bind_assoc, pure_bind]
    congr 1; funext q
    exact storage_glob σ _ (Solidity.popAt_with _ _ _ _)
  | true =>
    show (do
      let st ← Op2.eval σ.glob .shrink (pure σ.glob) (b.lower.eval σ)
      pure (σ.withGlob { σ.glob with storage := st.storage })) = Run.pop b σ
    simp only [Op2.eval, SPath.eval_lower, Run.pop, hE, bind_assoc, pure_bind]
    congr 1; funext q
    exact storage_glob σ _ (Solidity.popAt_with _ _ _ _)

theorem rebindPush_run {R : RefTy} (i : Idx Γ (.alias R)) (b : SPath C Γ (.array (.ref R)))
    (hd : (Ty.ref R).defaultOkS = true) :
    ((Upd.nil.snoc (.storage (.app2 (.extend (.ref R)) .storage b.lower))).snoc
      (.local i (.path (.app1 .next rfl b.lower)))).apply σ = Stmt.run σ (.rebind i (.push b hd)) := by
  rw [upd2_apply]
  show _ = Run.rebind i (.push b hd) σ
  simp only [UpdElem.write, Rhs.eval, Tm.eval, Op2.eval, Op1.eval, Op0.eval, SPath.eval_lower,
    Run.rebind, ARhs.eval, pushPlaceAt, SemanticsProperties.State.saveStorage_eq, bind_assoc,
    pure_bind]
  simp only [bind, Except.bind, pure, Except.pure]
  cases b.resolve σ with
  | error => rfl
  | ok q =>
    simp only
    cases σ.glob.findStorage q.1 q.2 with
    | error => rfl
    | ok v =>
      cases v with
      | array elems shadow fx =>
        simp only
        cases σ.glob.storeRes q.1 q.2 _ <;> rfl
      | _ => rfl

theorem transferBox_run (sadr se : Simple C Γ .uint) :
    (Upd.nil.snoc (.payTo sadr se)).apply σ = Stmt.run σ (.transfer (.simple sadr) (.simple se)) := by
  rw [upd1_apply]
  obtain ⟨a, ha⟩ := Simple.eval_ok σ sadr
  obtain ⟨v, hv⟩ := Simple.eval_ok σ se
  show _ = Run.transfer (.simple sadr) (.simple se) σ
  simp only [UpdElem.write, Simple.eval_lower, ha, hv, Run.transfer, Val.eval, transferAt,
    Semantics.State.pay, Res.bind_ok]
  cases a.asInt with
  | error => rfl
  | ok n =>
    cases v.asInt with
    | error => rfl
    | ok k =>
      simp only [Res.bind_ok]
      by_cases hk : k < 0 <;> simp only [hk, ↓reduceIte] <;> rfl

theorem send_run (pv : Idx Γ (.val .bool)) (sadr se : Simple C Γ .uint) :
    ∃ U ∈ [(Upd.nil.snoc (.payTo sadr se)).snoc (.local pv (.val (Tm.lit (.bool true)))),
        Upd.nil.snoc (.local pv (.val (Tm.lit (.bool false))))],
      Res.Sim (U.apply σ) (Stmt.run σ (.send pv (.simple sadr) (.simple se))) := by
  obtain ⟨a, ha⟩ := Simple.eval_ok σ sadr
  obtain ⟨v, hv⟩ := Simple.eval_ok σ se
  have e₁ : ((Upd.nil.snoc (.payTo sadr se)).snoc
      (.local pv (.val (Tm.lit (.bool true))))).apply σ = (do
        let addr ← a.asInt
        let amt ← v.asInt
        if amt < 0 then .error .revert
        else pure ((σ.withGlob (σ.glob.pay addr amt)).setLocal pv (.bool true))) := by
    rw [upd2_apply]
    simp only [UpdElem.write, Rhs.eval, Tm.eval, Op0.eval, Simple.eval_lower, ha, hv, Res.bind_ok,
      bind_assoc]
    cases a.asInt with
    | error => rfl
    | ok n =>
      cases v.asInt with
      | error => rfl
      | ok k => by_cases hk : k < 0 <;> simp only [Res.bind_ok, hk, ↓reduceIte] <;> rfl
  have e₂ : (Upd.nil.snoc (.local pv (.val (Tm.lit (C := C) (Γ := Γ) (.bool false))))).apply σ =
      .ok (σ.setLocal pv (.bool false)) := rfl
  have hr : Stmt.run σ (.send pv (.simple sadr) (.simple se)) = (do
      let addr ← a.asInt
      let amt ← v.asInt
      sendAt σ pv addr amt) := by
    show Run.send pv _ _ σ = _
    simp only [Run.send, Val.eval, ha, hv, Res.bind_ok]
  rw [hr]
  cases ha' : a.asInt with
  | error e => exact ⟨_, List.mem_cons_self .., by rw [e₁, ha']; exact Res.Sim.refl _⟩
  | ok n =>
    cases hv' : v.asInt with
    | error e => exact ⟨_, List.mem_cons_self .., by rw [e₁, ha', hv']; exact Res.Sim.refl _⟩
    | ok k =>
      rw [ha', hv'] at e₁
      simp only [Res.bind_ok, sendAt] at e₁ ⊢
      by_cases hk : k < 0
      · exact ⟨_, List.mem_cons_self .., by rw [e₁]; simp only [hk, ↓reduceIte]; exact Res.Sim.refl _⟩
      · simp only [hk, ↓reduceIte] at e₁ ⊢
        cases hl : Semantics.lookupBy (sendKey n k) σ.tx.ext with
        | none => exact ⟨_, List.mem_cons_self .., by rw [e₁]; exact Res.Sim.refl _⟩
        | some r =>
          cases r with
          | ok => exact ⟨_, List.mem_cons_self .., by rw [e₁]; exact Res.Sim.refl _⟩
          | _ =>
            exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), by rw [e₂]; exact Res.Sim.refl _⟩

theorem declMemFresh_run (R : RefTy) (x : Var) (hd : (none.isSome || (Ty.ref R).defaultOkS) = true)
    (hm : (Ty.ref R).mapFree = true) :
    ((Upd.nil.decl x (.mref (.app1 (.alloc R) rfl .memory))).snoc
      (.memory (.app1 (.addM R) rfl .memory))).apply σ = Stmt.run σ (.declMem R x none hd hm) := by
  show (do
    let τ ← (Upd.nil.decl x (.mref (.app1 (.alloc R) rfl .memory))).apply σ
    UpdElem.write σ (.memory (.app1 (.addM R) rfl .memory)) τ) = Run.declMem R none σ
  simp only [Upd.apply, UpdElem.write, Rhs.eval, Tm.eval, Op1.eval, Op0.eval, Run.declMem,
    Solidity.allocDefault_eq, bind_assoc, pure_bind]
  simp only [bind, Except.bind, pure, Except.pure]
  cases Solidity.allocHN σ.glob R <;> rfl

theorem deleteMemVar_run {R : RefTy} (i : Idx Γ (.mem R)) (hm : (Ty.ref R).mapFree = true)
    (hd : (Ty.ref R).defaultOkS = true) :
    ((Upd.nil.snoc (.local i (.mref (.app1 (.alloc R) rfl .memory)))).snoc
      (.memory (.app1 (.addM R) rfl .memory))).apply σ = Stmt.run σ (.deleteMem (.var i hm) hd) := by
  rw [upd2_apply]
  show _ = Run.deleteMem (.var i hm) σ
  simp only [UpdElem.write, Rhs.eval, Tm.eval, Op1.eval, Op0.eval, Run.deleteMem,
    Solidity.allocDefault_eq, bind_assoc, pure_bind]
  simp only [bind, Except.bind, pure, Except.pure]
  cases Solidity.allocHN σ.glob R <;> rfl

theorem allocCopy_run {R : RefTy} (i : Idx Γ (.mem R)) (r : MRhs C Γ R) (v : Tm C Γ .sv)
    (hr : r.eval σ = (do
      let (τ, mv) ← Semantics.copyStToM σ.glob (← v.eval σ)
      pure (σ.withGlob τ, ← mv.asRef))) :
    ((Upd.nil.snoc (.local i (.mref (.app2 .copy .memory v)))).snoc
      (.memory (.app2 .copySt .memory v))).apply σ = Stmt.run σ (.rebindMem i r) := by
  rw [upd2_apply]
  show _ = Run.rebindMem i r σ
  simp only [Run.rebindMem, hr, UpdElem.write, Rhs.eval, Tm.eval, Op2.eval, Op0.eval,
    Solidity.copyStToM_eq, bind_assoc, pure_bind]
  simp only [bind, Except.bind, pure, Except.pure]
  cases v.eval σ with
  | error => rfl
  | ok sv =>
    simp only
    cases Solidity.copyHN σ.glob sv with
    | error => rfl
    | ok q =>
      simp only
      cases q.2.2.asRef <;> rfl

theorem clearMem_run {T : Ty} (l : MLoc C Γ T) (hd : T.defaultOkS = true) :
    ∃ U, Premise.clearMem l.lower T = .update U ∧
      Res.Sim (U.apply σ) (Stmt.run σ (.deleteMem (.loc l) hd)) := by
  cases T with
  | prim p =>
    refine ⟨_, rfl, Res.Sim.of_eq ?_⟩
    rw [upd1_apply]
    show _ = Run.deleteMem (.loc l) σ
    simp only [UpdElem.write, Tm.eval, Op3.eval, Op1.eval, Op0.eval, MLoc.eval_lower_addr,
      Run.deleteMem, memClear, bind_assoc, pure_bind, writeAddr_glob]
  | ref R =>
    refine ⟨_, rfl, ?_⟩
    rw [upd1_apply]
    show Res.Sim _ (Run.deleteMem (.loc l) σ)
    simp only [UpdElem.write, Tm.eval, Op3.eval, Op1.eval, Op0.eval, MLoc.eval_lower_addr,
      Run.deleteMem, memClear, Solidity.allocDefault_eq, bind_assoc, pure_bind]
    simp only [bind, Except.bind, pure, Except.pure, Functor.map, Except.map]
    have ha : NoPanic (l.addr σ) := by
      have h := Tm.eval_noPanic σ l.lower
      rw [MLoc.eval_lower_addr] at h
      exact h
    have hal : NoPanic (Solidity.allocHN σ.glob R) := Solidity.allocHN_noPanic σ.glob R
    revert ha hal
    cases l.addr σ with
    | error e =>
      cases Solidity.allocHN σ.glob R with
      | error e' => exact fun ha hal => ⟨fun h => absurd (congrArg Except.error h) hal,
          fun h => absurd (congrArg Except.error h) ha⟩
      | ok q => intro _ _; exact Res.Sim.refl _
    | ok a =>
      cases Solidity.allocHN σ.glob R with
      | error e' => intro _ _; exact Res.Sim.refl _
      | ok q =>
        intro _ _
        simp only
        cases hw : writeAddr _ _ a with
        | error => exact Res.Sim.refl _
        | ok μ =>
          simp only [writeAddr_ok_with hw]
          exact Res.Sim.refl _

end Runs2

/-! ## The other update arms (`Step.lean`) -/

section Arms2

variable {Γ : Ctx} {m : Modality} (σ : TState C Γ)

/-- `storagePushLengthSave`: `{storage := pushSlot(storage, b)}`. -/
theorem sound_pushSlot {E : Ty} (b : SPath C Γ (.array E))
    (hd : (none.isSome || E.defaultOkS) = true) :
    Premise.Sound m (.push b none hd) (.upd1 (.storage (.app2 (.pushSlot E) .storage b.lower))) σ :=
  Premise.sound_update_run σ (pushSlot_run σ.erase b hd) fun _ => TRun.push_nd σ b none

/-- `storagePushLengthSaveReferenceElement`: `{storage := extend(storage, b)}`. -/
theorem sound_extend {E : Ty} (b : SPath C Γ (.array E))
    (hd : (none.isSome || E.defaultOkS) = true) :
    Premise.Sound m (.push b none hd) (.upd1 (.storage (.app2 (.extend E) .storage b.lower))) σ :=
  Premise.sound_update_run σ (extend_run σ.erase b hd) fun _ => TRun.push_nd σ b none

/-- `storagePushValueSave`, `storagePushValueCopySource`:
`{storage := push(storage, b, src)}`. -/
theorem sound_pushSome {E : Ty} (b : SPath C Γ (.array E)) (r : Src C Γ E)
    (hd : ((some r).isSome || E.defaultOkS) = true) :
    Premise.Sound m (.push b (some r) hd)
      (.upd1 (.storage (.app3 .push .storage b.lower r.lower))) σ :=
  Premise.sound_update_run σ (pushSome_run σ.erase b r hd) fun _ => TRun.push_nd σ b (some r)

/-- `storagePopSave`, `storagePopSaveMappingElement`. -/
theorem sound_pop {E : Ty} (b : SPath C Γ (.array E)) :
    Premise.Sound m (.pop b) (.upd1 (.storage (.app2 (if E.isMapping then .shrink else .pop)
      .storage b.lower))) σ :=
  Premise.sound_update_run σ (pop_run σ.erase b) fun _ =>
    ((SPath.resolveT_ends σ b).bind fun _ => (TRes.Ends.ofOpt _).bind fun _ => TRes.Ends.ok _).1

/-- `storageLocalRootPushBind`, `storageLocalRootPushBindMappingElement`:
`{storage := extend(storage, b) ‖ lsv := next(b)}`. -/
theorem sound_rebindPush {R : RefTy} (i : Idx Γ (.alias R)) (b : SPath C Γ (.array (.ref R)))
    (hd : (Ty.ref R).defaultOkS = true) :
    Premise.Sound m (.rebind i (.push b hd)) (.update ((Upd.nil.snoc
      (.storage (.app2 (.extend (.ref R)) .storage b.lower))).snoc
      (.local i (.path (.app1 .next rfl b.lower))))) σ :=
  Premise.sound_update_run σ (rebindPush_run σ.erase i b hd) fun _ =>
    TRes.NoDiv.bind (ARhs.evalT_nd σ (.push b hd)) fun _ => TRes.NoDiv.ok _

/-- `transferNoCallbackBox`: `{net := …}`. -/
theorem sound_transferBox (sadr se : Simple C Γ .uint) :
    Premise.Sound m (.transfer (.simple sadr) (.simple se)) (.upd1 (.payTo sadr se)) σ :=
  Premise.sound_update_run σ (transferBox_run σ.erase sadr se) fun _ => TRes.NoDiv.ok _

/-- `transferDiamond` (Lean): the goal fails. -/
theorem sound_done_false {Γ' : Ctx} (s : Stmt C Γ Γ') : Premise.Sound m s (.done false) σ :=
  Premise.sound_done σ false fun h => nomatch h

/-- `sendNoCallbackBox`, `sendNoCallbackDiamond`: the payment with `pv` true,
or `pv` false. -/
theorem sound_send (pv : Idx Γ (.val .bool)) (sadr se : Simple C Γ .uint) (fs : List (Fml C Γ)) :
    Premise.Sound m (.send pv (.simple sadr) (.simple se)) (.cases fs
      [(Upd.nil.snoc (.payTo sadr se)).snoc (.local pv (.val (Tm.lit (.bool true)))),
        Upd.nil.snoc (.local pv (.val (Tm.lit (.bool false))))]) σ :=
  Premise.sound_cases_run σ (fun _ => send_run σ.erase pv sadr se) fun _ => TRes.NoDiv.ok _

/-- `memoryReferenceDeclFreshAlloc`. -/
theorem sound_declMemFresh (R : RefTy) (x : Var)
    (hd : (none.isSome || (Ty.ref R).defaultOkS) = true) (hm : (Ty.ref R).mapFree = true) :
    Premise.Sound m (.declMem R x none hd hm) (.update ((Upd.nil.decl x
      (.mref (.app1 (.alloc R) rfl .memory))).snoc (.memory (.app1 (.addM R) rfl .memory)))) σ :=
  Premise.sound_update_run σ (declMemFresh_run σ.erase R x hd hm) fun _ => TRes.NoDiv.ok _

/-- `memoryRootDeleteFreshRebind`. -/
theorem sound_deleteMemVar {R : RefTy} (i : Idx Γ (.mem R)) (hm : (Ty.ref R).mapFree = true)
    (hd : (Ty.ref R).defaultOkS = true) :
    Premise.Sound m (.deleteMem (.var i hm) hd) (.update ((Upd.nil.snoc
      (.local i (.mref (.app1 (.alloc R) rfl .memory)))).snoc
      (.memory (.app1 (.addM R) rfl .memory)))) σ :=
  Premise.sound_update_run σ (deleteMemVar_run σ.erase i hm hd) fun _ => TRes.NoDiv.ok _

/-- `memoryStorageCopy`, `memoryArrayFreshAlloc`, given M3's reading of the
right-hand side on the erasure. -/
theorem sound_allocCopy {R : RefTy} (i : Idx Γ (.mem R)) (r : MRhs C Γ R) (v : Tm C Γ .sv)
    (hr : r.eval σ.erase = (do
      let (τ, mv) ← Semantics.copyStToM σ.erase.glob (← v.eval σ.erase)
      pure (σ.erase.withGlob τ, ← mv.asRef))) :
    Premise.Sound m (.rebindMem i r) (.allocCopy i v) σ :=
  Premise.sound_update_run σ (allocCopy_run σ.erase i r v hr) fun _ =>
    ((MRhs.evalT_ends σ r).bind fun _ => TRes.Ends.ok _).1

theorem clearT_ends : {T : Ty} → (a : MAddr σ.H T) → (hm : T.mapFree = true) →
    (TRun.clearT σ a hm).Ends
  | .prim _, _, _ => (TRes.Ends.ofOpt _).bind fun _ => TRes.Ends.ok _
  | .ref R, a, hm => by
    simp only [TRun.clearT]
    split <;> exact ⟨(fun h => nomatch h), fun h => nomatch h⟩

/-- `memoryFieldDelete*`, `memoryIndexDelete*`: a slot reset to its default,
or written a fresh default object. -/
theorem sound_clearMem {T : Ty} (l : MLoc C Γ T) (hd : T.defaultOkS = true) :
    Premise.Sound m (.deleteMem (.loc l) hd) (.clearMem l.lower T) σ := by
  obtain ⟨U, hU, hs⟩ := clearMem_run σ.erase l hd
  rw [hU]
  exact Premise.sound_updateSim_run σ hs fun _ =>
    ((MLoc.addrT_ends σ l).bind fun a => clearT_ends σ a _).1

/-- `valueDeclSkip`: `{v := defVal(T)}`. -/
theorem sound_valueDeclSkip (p : PrimTy) (x : Var) :
    Premise.Sound m (.declLocal p x none)
      (.update (Upd.nil.decl x (.val (p := p) (.app0 (.lit p.default))))) σ :=
  Premise.sound_update_run (s := .declLocal p x none) σ rfl fun _ => TRes.NoDiv.ok _

/-- `storageLocalDeclSkip`: `{lsv := unset}`. -/
theorem sound_storageLocalDeclSkip (R : RefTy) (x : Var) :
    Premise.Sound m (.declStorage R x none) (.update (Upd.nil.decl (t := .alias R) x .unset)) σ :=
  Premise.sound_update_run (s := .declStorage R x none) σ rfl fun _ => TRes.NoDiv.ok _

/-- `revertBox`, `revertDiamond`. -/
theorem sound_revert :
    Premise.Sound m (.revert : Stmt C Γ Γ) (.done (m == .box)) σ :=
  Premise.sound_done σ _ fun h =>
    ⟨by cases m <;> first | rfl | exact absurd h (by decide), .revert, rfl, by decide⟩

end Arms2

end Solidity.Core
