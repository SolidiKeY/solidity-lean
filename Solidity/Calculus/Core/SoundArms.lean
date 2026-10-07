import Solidity.Calculus.Core.SoundKit

/-!
# Soundness of the arms of `Calculus/Core/Arms.lean` and `Step.lean`

Every arm of `Stmt.step` but the calls, `try` and loops of
`Calculus/Core/Blocks.lean` is sound against M3's interpreter
(`Core.Stmt.run`), in the shape `Calculus/Core/SoundKit.lean` states
(`Stmt.StepSound`).  The proofs follow today's (`Calculus/SoundUpdate.lean`,
`Calculus/SoundUnfold.lean`): a term reads what the expression it lowers
evaluates to (`Val.eval_lower` and its kin, as `Update.lean`'s
`Val.lower_eval`), so an update rule's update ends as its statement does;
a capture's statement, read with the fresh local on top, runs as the
statement it replaces (`Val.eval_up` and its kin, `Calculus/Core/Logic.lean`).
No freshness premise: a rule's fresh local is a position its premise pushes
and pops.
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

theorem pushed_drop (r : Res (State C Γ)) :
    (pushed w r).map (State.drop (.push .refl)) = r := by
  cases r <;> rfl

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
    (h : MLoc.Agree σ w l' l) (mv : MVal) : l'.write (σ.push w) mv = pushed w (l.write σ mv) := by
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

theorem Run.assignLocal_push {p : PrimTy} (i : Idx Γ (.val p)) (v' : Val C (t :: Γ) p)
    (v : Val C Γ p) (hv : v'.eval (σ.push w) = v.eval σ) :
    Run.assignLocal i.there v' (σ.push w) = pushed w (Run.assignLocal i v σ) := by
  push_run [Run.assignLocal, hv]

theorem Run.assign_push {T : Ty} (l' : Loc C (t :: Γ) T) (r' : Src C (t :: Γ) T) (l : Loc C Γ T)
    (r : Src C Γ T) (hr : r'.value (σ.push w) = r.value σ)
    (hl : l'.resolve (σ.push w) = l.resolve σ) :
    Run.assign l' r' (σ.push w) = pushed w (Run.assign l r σ) := by
  push_run [Run.assign, hr, hl]

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

theorem Src.value_up {T : Ty} (r : Src C Γ T) : r.up.value (σ.push w) = r.value σ := by
  cases r with
  | val v => simp only [Src.up, Src.value, Val.eval_up]
  | copy p hm => simp only [Src.up, Src.value, SPath.resolve_up, State.glob_push]

theorem MSrc.mval_up {T : Ty} (r : MSrc C Γ T) : r.up.mval (σ.push w) = r.mval σ := by
  cases r with
  | val v => simp only [MSrc.up, MSrc.mval, Val.eval_up]
  | ref p => simp only [MSrc.up, MSrc.mval, MPath.mval_up]

theorem Src.pushVal_up {T : Ty} (v : Option (Src C Γ T)) :
    Src.pushVal (σ.push w) (v.map Src.up) = Src.pushVal σ v := by
  cases v with
  | none => rfl
  | some r => funext slot; simp only [Option.map, Src.pushVal, Src.value_up]

/-! ### Statements -/

theorem Run.rebind_push {R : RefTy} (i : Idx Γ (.alias R)) (r' : ARhs C (t :: Γ) R) (r : ARhs C Γ R)
    (hr : r'.eval (σ.push w) = pushedA (R := R) w (r.eval σ)) :
    Run.rebind i.there r' (σ.push w) = pushed w (Run.rebind i r σ) := by
  simp only [Run.rebind, hr]
  cases r.eval σ <;> rfl

theorem Run.opAssign_push {p : PrimTy} (op : BinOp) {l' : OpLoc C (t :: Γ) p} {l : OpLoc C Γ p}
    (hl : OpLoc.Agree σ w l' l) (v' : Val C (t :: Γ) p) (v : Val C Γ p)
    (hv : v'.eval (σ.push w) = v.eval σ) :
    Run.opAssign op l' v' (σ.push w) = pushed w (Run.opAssign op l v σ) := by
  push_run [Run.opAssign, hv, hl.store]

theorem Run.incDec_push {p : PrimTy} (op : IncDec) {l' : OpLoc C (t :: Γ) p} {l : OpLoc C Γ p}
    (hl : OpLoc.Agree σ w l' l) :
    Run.incDec op l' (σ.push w) = pushed w (Run.incDec op l σ) := by
  simp only [Run.incDec, hl.bump]
  cases l.bump σ op <;> rfl

theorem Run.assignIncDec_push {p : PrimTy} (i : Idx Γ (.val p)) (op : IncDec)
    {l' : OpLoc C (t :: Γ) p} {l : OpLoc C Γ p} (hl : OpLoc.Agree σ w l' l) :
    Run.assignIncDec i.there op l' (σ.push w) = pushed w (Run.assignIncDec i op l σ) := by
  simp only [Run.assignIncDec, hl.bump]
  cases l.bump σ op <;> rfl

theorem Run.push_push {E : Ty} (b' : SPath C (t :: Γ) (.array E)) (b : SPath C Γ (.array E))
    (v' : Option (Src C (t :: Γ) E)) (v : Option (Src C Γ E))
    (hb : b'.resolve (σ.push w) = b.resolve σ) (hv : Src.pushVal (σ.push w) v' = Src.pushVal σ v) :
    Run.push b' v' (σ.push w) = pushed w (Run.push b v σ) := by
  push_run [Run.push, hb, hv]

theorem Run.pop_push {E : Ty} (b' : SPath C (t :: Γ) (.array E)) (b : SPath C Γ (.array E))
    (hb : b'.resolve (σ.push w) = b.resolve σ) :
    Run.pop b' (σ.push w) = pushed w (Run.pop b σ) := by
  push_run [Run.pop, hb]

theorem Run.transfer_push (r' a' : Val C (t :: Γ) .uint) (r a : Val C Γ .uint)
    (hr : r'.eval (σ.push w) = r.eval σ) (ha : a'.eval (σ.push w) = a.eval σ) :
    Run.transfer r' a' (σ.push w) = pushed w (Run.transfer r a σ) := by
  push_run [Run.transfer, hr, ha]

theorem sendAt_push (pv : Idx Γ (.val .bool)) (addr amt : Int) :
    sendAt (σ.push w) pv.there addr amt = pushed w (sendAt σ pv addr amt) := by
  unfold sendAt
  split
  · rfl
  · rw [show (σ.push w).tx = σ.tx from rfl]
    cases Semantics.lookupBy (sendKey addr amt) σ.tx.ext with
    | none => rfl
    | some r => cases r <;> rfl

theorem Run.send_push (pv : Idx Γ (.val .bool)) (r' a' : Val C (t :: Γ) .uint) (r a : Val C Γ .uint)
    (hr : r'.eval (σ.push w) = r.eval σ) (ha : a'.eval (σ.push w) = a.eval σ) :
    Run.send pv.there r' a' (σ.push w) = pushed w (Run.send pv r a σ) := by
  push_run [Run.send, hr, ha, sendAt_push]

theorem Run.rebindMem_push {R : RefTy} (i : Idx Γ (.mem R)) (r' : MRhs C (t :: Γ) R) (r : MRhs C Γ R)
    (hr : r'.eval (σ.push w) = pushedM w (r.eval σ)) :
    Run.rebindMem i.there r' (σ.push w) = pushed w (Run.rebindMem i r σ) := by
  simp only [Run.rebindMem, hr]
  cases r.eval σ <;> rfl

theorem Run.assignFromMem_push {R : RefTy} (l' : Loc C (t :: Γ) (.ref R)) (l : Loc C Γ (.ref R))
    (p' : MPath C (t :: Γ) (.ref R)) (p : MPath C Γ (.ref R))
    (hp : p'.mval (σ.push w) = p.mval σ) (hl : l'.resolve (σ.push w) = l.resolve σ) :
    Run.assignFromMem l' p' (σ.push w) = pushed w (Run.assignFromMem l p σ) := by
  push_run [Run.assignFromMem, hp, hl]

theorem Run.assignMem_push {T : Ty} {l' : MLoc C (t :: Γ) T} {l : MLoc C Γ T}
    (hl : MLoc.Agree σ w l' l) (r' : MSrc C (t :: Γ) T) (r : MSrc C Γ T)
    (hr : r'.mval (σ.push w) = r.mval σ) :
    Run.assignMem l' r' (σ.push w) = pushed w (Run.assignMem l r σ) := by
  push_run [Run.assignMem, hr, hl.write]

theorem Run.delete_push {T : Ty} (l' : Loc C (t :: Γ) T) (l : Loc C Γ T)
    (hl : l'.resolve (σ.push w) = l.resolve σ) :
    Run.delete l' (σ.push w) = pushed w (Run.delete l σ) := by
  push_run [Run.delete, hl]

theorem Run.deleteMem_push {T : Ty} {l' : MLoc C (t :: Γ) T} {l : MLoc C Γ T}
    (hl : MLoc.Agree σ w l' l) :
    Run.deleteMem (.loc l') (σ.push w) = pushed w (Run.deleteMem (.loc l) σ) := by
  push_run [Run.deleteMem, hl.addr]

theorem guardOk_push (c' : Val C (t :: Γ) .bool) (c : Val C Γ .bool)
    (hc : c'.eval (σ.push w) = c.eval σ) :
    (do guardOk (← c'.eval (σ.push w)) (σ.push w)) = pushed w (do guardOk (← c.eval σ) σ) := by
  rw [hc]
  cases c.eval σ with
  | error => rfl
  | ok v => rcases v with _ | (_ | _) <;> rfl

theorem assertOk_push (c' : Val C (t :: Γ) .bool) (c : Val C Γ .bool)
    (hc : c'.eval (σ.push w) = c.eval σ) :
    (do assertOk (← c'.eval (σ.push w)) (σ.push w)) = pushed w (do assertOk (← c.eval σ) σ) := by
  rw [hc]
  cases c.eval σ with
  | error => rfl
  | ok v => rcases v with _ | (_ | _) <;> rfl

end Push

end Solidity.Core
