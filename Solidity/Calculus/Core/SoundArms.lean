import Solidity.Calculus.Core.SoundKit
import Solidity.Calculus.SoundUpdate

/-!
# Soundness of the arms of `Calculus/Core/Arms.lean` and `Step.lean`

The premises of the update arms of `Stmt.step` are sound against M3's
interpreter (`Core.Stmt.run`), as `Premise.Sound`
(`Calculus/Core/SoundKit.lean`): an assignment to a local (`sound_setLocal`),
a storage write (`sound_save`, `sound_saveMem`), a `delete` (`sound_delAt`),
a memory write (`sound_writeMem`), a rebinding (`sound_rebindPath`,
`sound_rebindMemAlias`) and a compound assignment (`sound_opAssign`).  No arm
is proved as `Stmt.StepSound` yet (the other arms, and the calls, `try` and
loops of `Calculus/Core/Blocks.lean`, are not proved).  The proofs follow
today's (`Calculus/SoundUpdate.lean`, `Calculus/SoundUnfold.lean`): a term reads what the expression it lowers
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

theorem MLoc.write_eq {T : Ty} (l : MLoc C Γ T) (mv : MVal) :
    l.write σ mv = (do σ.withGlob <$> writeAddr σ.glob mv (← l.addr σ)) := by
  cases l with
  | field b f h => simp only [MLoc.write, MLoc.addr, bind_assoc, pure_bind]; rfl
  | index a b i => simp only [MLoc.write, MLoc.addr, bind_assoc, pure_bind]; rfl

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

/-- `localValueAssign`, `storageRootReadSelect`, `storageFieldReadFind`,
`storageIndexReadMappingFind`, `storageIndexReadArrayFind`, `binopAssignment`,
`unopAssignment`, `memoryFieldRead`, `memoryIndexReadArrayValue`,
`storageLengthRead`, `memoryLengthRead`: `{v := e}` for `v = e;`. -/
theorem sound_setLocal {p : PrimTy} (i : Idx Γ (.val p)) (v : Val C Γ p) :
    Premise.Sound m (.assignLocal i v) (.setLocal i v) σ :=
  Premise.Sound.update (by
    show (do pure (σ.setLocal i (← v.lower.eval σ))) = Run.assignLocal i v σ
    rw [Val.eval_lower]; rfl)

/-- `storageRootWriteStore`, `storageFieldWriteSave`, `storageIndexWrite*Save`,
`…CopySource`: `{storage := save(storage, l, src)}` for `l = src;`. -/
theorem sound_save {T : Ty} (l : Loc C Γ T) (r : Src C Γ T) :
    Premise.Sound m (.assign l r) (.save l r) σ :=
  Premise.Sound.update (by
    show (do
      let st ← Op3.eval σ.glob .save (pure σ.glob) (l.lower.eval σ) (r.lower.eval σ)
      pure (σ.withGlob { σ.glob with storage := st.storage })) = Run.assign l r σ
    simp only [Op3.eval, Loc.eval_lower, Src.eval_lower, Run.assign, bind_assoc, pure_bind]
    congr 1; funext sv; congr 1; funext q
    exact storage_glob σ _ (Solidity.State.writeStorage_with _ _ _ _))

/-- `memoryToStorageStoreRoot`, `…FieldCopyRoot`, `…IndexMappingCopyRoot`,
`…IndexArrayCopyRoot`: `{storage := save(storage, l, copyMem(memory, p))}`. -/
theorem sound_saveMem {R : RefTy} (l : Loc C Γ (.ref R)) (p : MPath C Γ (.ref R)) :
    Premise.Sound m (.assignFromMem l p) (.saveMem l p) σ :=
  Premise.Sound.update (by
    show (do
      let st ← Op3.eval σ.glob .save (pure σ.glob) (l.lower.eval σ)
        (Op2.eval σ.glob .copyMem (pure σ.glob) (p.lower.eval σ))
      pure (σ.withGlob { σ.glob with storage := st.storage })) = Run.assignFromMem l p σ
    simp only [Op3.eval, Op2.eval, Loc.eval_lower, MPath.eval_lower, Run.assignFromMem, bind_assoc,
      pure_bind]
    congr 1; funext mv; congr 1; funext id; congr 1; funext sv; congr 1; funext q
    exact storage_glob σ _ (Solidity.State.writeStorage_with _ _ _ _))

/-- `storageRootDelete`, `storageFieldDelete`, `storageIndexDelete`,
`storageIndexArrayDelete`: `{storage := delAt(storage, l)}`. -/
theorem sound_delAt {T : Ty} (l : Loc C Γ T) : Premise.Sound m (.delete l) (.delAt l) σ :=
  Premise.Sound.update (by
    show (do
      let st ← Op2.eval σ.glob .delAt (pure σ.glob) (l.lower.eval σ)
      pure (σ.withGlob { σ.glob with storage := st.storage })) = Run.delete l σ
    simp only [Op2.eval, Loc.eval_lower, Run.delete, bind_assoc, pure_bind]
    congr 1; funext q; congr 1; funext cur
    exact storage_glob σ _ (Solidity.State.saveStorage_with _ _ _ _))

/-- `memoryFieldWrite`, `memoryIndexWriteArray`, `memoryFieldWriteCopy`,
`memoryIndexWriteCopy`: `{memory := write(memory, l, src)}`. -/
theorem sound_writeMem {T : Ty} (l : MLoc C Γ T) (r : MSrc C Γ T) :
    Premise.Sound m (.assignMem l r) (.writeMem l r) σ :=
  Premise.Sound.update (by
    show (do
      let μ ← Op3.eval σ.glob .write (pure σ.glob) (l.lower.eval σ) (r.lower.eval σ)
      pure (σ.withGlob { σ.glob with heap := μ.heap, nextId := μ.nextId })) = Run.assignMem l r σ
    simp only [Op3.eval, MLoc.eval_lower_addr, MSrc.eval_lower, Run.assignMem, MLoc.write_eq,
      bind_assoc, pure_bind]
    congr 1; funext mv; congr 1; funext a
    exact memory_glob σ _ (Solidity.writeAddr_with _ _ _))

/-- `storageLocalRootRebind`, `storageFieldReadBindLocalRoot`,
`storageIndexReadMappingBindLocalRoot`, `storageIndexReadArrayBindLocalRoot`:
`{lsv := p}`. -/
theorem sound_rebindPath {R : RefTy} (i : Idx Γ (.alias R)) (p : SPath C Γ (.ref R)) :
    Premise.Sound m (.rebind i (.path p)) (.upd1 (.local i (.path p.lower))) σ :=
  Premise.Sound.update (by
    show (do pure (σ.setLocal i (← do pure (some (← p.lower.eval σ))))) = Run.rebind i (.path p) σ
    simp only [SPath.eval_lower, Run.rebind, ARhs.eval, bind_assoc, pure_bind])

/-- `memoryRootRebind`, `memoryFieldReadAliasRoot`, `memoryIndexReadArrayMemory`:
`{mv := p}`. -/
theorem sound_rebindMemAlias {R : RefTy} (i : Idx Γ (.mem R)) (p : MPath C Γ (.ref R)) :
    Premise.Sound m (.rebindMem i (.alias p)) (.upd1 (.local i (.mref p.lower))) σ :=
  Premise.Sound.update (by
    show (do pure (σ.setLocal i (← p.lower.eval σ))) = Run.rebindMem i (.alias p) σ
    simp only [MPath.eval_lower, Run.rebindMem, MRhs.eval, bind_assoc, pure_bind])

/-- A compound assignment at a resolved storage location, as the update
writes it: read, apply, write back at the root. -/
theorem opStore_write (op : BinOp) (p : PrimTy) (rt : Name) (segs : List Seg) (v : Value) :
    (do
      let x ← σ.glob.findStorage rt segs
      let x ← x.asValue
      let x ← Semantics.applyBinOp op x v
      let x ← Semantics.checkArith (.prim p) x
      let w ← σ.glob.writeStorage rt segs x.toSVal
      pure (σ.withGlob { σ.glob with storage := w.storage })) =
      σ.withGlob <$> Solidity.opStore σ.glob op p rt segs v := by
  simp only [Solidity.opStore, map_bind]
  congr 1; funext sv; congr 1; funext a; congr 1; funext b; congr 1; funext c
  cases c <;> exact storage_glob σ _ (Solidity.State.writeStorage_with _ _ _ _)

/-- The same at a storage location, resolved once by the statement and
twice by the update (its read and its write). -/
theorem opStore_loc {T : Ty} (op : BinOp) (p : PrimTy) (L : Loc C Γ T) (v : Value) :
    (do
      let x ← L.resolve σ
      let x ← σ.glob.findStorage x.fst x.snd
      let x ← x.asValue
      let x ← Semantics.applyBinOp op x v
      let x ← Semantics.checkArith (.prim p) x
      let q ← L.resolve σ
      let w ← σ.glob.writeStorage q.fst q.snd x.toSVal
      pure (σ.withGlob { σ.glob with storage := w.storage })) =
      (do let q ← L.resolve σ; σ.withGlob <$> Solidity.opStore σ.glob op p q.fst q.snd v) := by
  cases L.resolve σ with
  | error e => rfl
  | ok q => exact opStore_write σ op p q.fst q.snd v

/-- A compound assignment at a memory address, from the old value read:
apply, check, write back. -/
theorem opMem_tail (op : BinOp) (p : PrimTy) (a : Semantics.Addr) (v : Value) (r : Res Value) :
    (do
      let x ← r
      let x ← Semantics.applyBinOp op x v
      let x ← Semantics.checkArith (.prim p) x
      let μ ← writeAddr σ.glob x.toMVal a
      pure (σ.withGlob { σ.glob with heap := μ.heap, nextId := μ.nextId })) =
      σ.withGlob <$> (do
        let old ← r
        let new ← Semantics.applyBinOp op old v
        let new ← Semantics.checkArith (.prim p) new
        Semantics.writeLoc σ.glob a new) := by
  simp only [map_bind]
  congr 1; funext x; congr 1; funext y; congr 1; funext c
  cases a <;> exact memory_glob σ _ (Solidity.writeAddr_with _ _ _)

/-- A compound assignment at a memory location, as the update writes it:
read, apply, write back at the address. -/
theorem opMem_loc {T : Ty} (op : BinOp) (p : PrimTy) (L : MLoc C Γ T) (v : Value) :
    (do
      let x ← L.read σ
      let x ← x.asValue
      let x ← Semantics.applyBinOp op x v
      let x ← Semantics.checkArith (.prim p) x
      let a ← L.addr σ
      let μ ← writeAddr σ.glob x.toMVal a
      pure (σ.withGlob { σ.glob with heap := μ.heap, nextId := μ.nextId })) =
      (do let a ← L.addr σ; σ.withGlob <$> Solidity.opMem σ.glob op p a v) := by
  cases L with
  | field b f h =>
    simp only [MLoc.read, MLoc.addr, bind_assoc, pure_bind]
    cases MPath.mval σ b with
    | error e => rfl
    | ok mv =>
      simp only [Solidity.SemanticsProperties.Res.ok_bind]
      cases mv.asRef with
      | error e => rfl
      | ok id =>
        simp only [Solidity.SemanticsProperties.Res.ok_bind, Solidity.opMem, Semantics.readLoc, bind_assoc]
        cases σ.glob.getObj id with
        | error e => rfl
        | ok o =>
          simp only [Solidity.SemanticsProperties.Res.ok_bind]
          cases o with
          | array _ _ => rfl
          | struct fields =>
            dsimp only
            cases Semantics.lookupBy f fields with
            | none => rfl
            | some w => exact opMem_tail σ op p _ v w.asValue
  | index a b i =>
    simp only [MLoc.read, MLoc.addr, bind_assoc, pure_bind]
    cases MPath.mval σ b with
    | error e => rfl
    | ok mv =>
      simp only [Solidity.SemanticsProperties.Res.ok_bind]
      cases mv.asRef with
      | error e => rfl
      | ok id =>
        simp only [Solidity.SemanticsProperties.Res.ok_bind]
        cases Val.eval σ i with
        | error e => rfl
        | ok iv =>
          simp only [Solidity.SemanticsProperties.Res.ok_bind]
          cases iv.asInt with
          | error e => rfl
          | ok n =>
            simp only [Solidity.SemanticsProperties.Res.ok_bind, Solidity.opMem, Semantics.readLoc, bind_assoc]
            cases σ.glob.getObj id with
            | error e => rfl
            | ok o =>
              simp only [Solidity.SemanticsProperties.Res.ok_bind]
              cases o with
              | struct _ => rfl
              | array elems fx =>
                by_cases hn : 0 ≤ n ∧ n.toNat < elems.length
                · simp only [dif_pos hn]
                  exact opMem_tail σ op p _ v _
                · simp only [dif_neg hn]
                  rfl

theorem Simple.eval_ok {p : PrimTy} (s : Simple C Γ p) : ∃ v, s.eval σ = .ok v := by
  cases s <;> exact ⟨_, rfl⟩

/-- `localOpAssign`, `storageRootOpAssign`, `storageFieldOpAssign`,
`storageIndexMappingOpAssign`, `storageIndexArrayOpAssign`,
`memoryFieldOpAssign`, `memoryIndexArrayOpAssign`: `{l := l ⊕ se}`. -/
theorem sound_opAssign {p : PrimTy} (op : BinOp) (hop : op.hasCompoundAssign = true)
    (hp : p.isNumeric = true) (l : OpLoc C Γ p) (se : Simple C Γ p) :
    Premise.Sound m (.opAssign op hop hp l (.simple se)) (.upd1 (l.set (l.op op se.lower))) σ := by
  refine Premise.Sound.update ?_
  obtain ⟨v, hv⟩ := Simple.eval_ok σ se
  have hv' : se.eval σ = pure v := hv
  rw [upd1_apply]
  show _ = Run.opAssign op l (.simple se) σ
  cases l with
  | «local» i =>
    simp only [OpLoc.set, OpLoc.op, OpLoc.cur, UpdElem.write, Rhs.eval, Tm.eval, Op2.eval,
      Simple.eval_lower, hv, evalBinop_compound hop, Run.opAssign, Val.eval, OpLoc.store, opLocal,
      bind_assoc, pure_bind]
  | root r h =>
    simp only [OpLoc.set, OpLoc.op, OpLoc.cur, UpdElem.write, Tm.eval, Op3.eval, Op2.eval, Op1.eval,
      Op0.eval, Simple.eval_lower, hv', evalBinop_compound hop, Run.opAssign, Val.eval, OpLoc.store,
      Loc.eval_lower, Val.eval_lower, bind_assoc, pure_bind]
    exact opStore_loc σ op p _ v
  | field b f h =>
    simp only [OpLoc.set, OpLoc.op, OpLoc.cur, UpdElem.write, Tm.eval, Op3.eval, Op2.eval, Op1.eval,
      Op0.eval, Simple.eval_lower, hv', evalBinop_compound hop, Run.opAssign, Val.eval, OpLoc.store,
      Loc.eval_lower, Val.eval_lower, bind_assoc, pure_bind]
    exact opStore_loc σ op p _ v
  | index it b ie =>
    simp only [OpLoc.set, OpLoc.op, OpLoc.cur, UpdElem.write, Tm.eval, Op3.eval, Op2.eval, Op1.eval,
      Op0.eval, Simple.eval_lower, hv', evalBinop_compound hop, Run.opAssign, Val.eval, OpLoc.store,
      Loc.eval_lower, Val.eval_lower, bind_assoc, pure_bind]
    exact opStore_loc σ op p _ v
  | mfield b f h =>
    simp only [OpLoc.set, OpLoc.op, OpLoc.cur, UpdElem.write, Tm.eval, Op3.eval, Op2.eval, Op1.eval,
      Op0.eval, Simple.eval_lower, hv', evalBinop_compound hop, Run.opAssign, Val.eval, OpLoc.store,
      MLoc.eval_lower_addr, Val.eval_lower, bind_assoc, pure_bind]
    refine (opMem_loc σ op p _ v).trans ?_
    simp only [MLoc.addr, bind_assoc, pure_bind]
  | mindex a b ie =>
    simp only [OpLoc.set, OpLoc.op, OpLoc.cur, UpdElem.write, Tm.eval, Op3.eval, Op2.eval, Op1.eval,
      Op0.eval, Simple.eval_lower, hv', evalBinop_compound hop, Run.opAssign, Val.eval, OpLoc.store,
      MLoc.eval_lower_addr, Val.eval_lower, bind_assoc, pure_bind]
    refine (opMem_loc σ op p _ v).trans ?_
    simp only [MLoc.addr, Val.eval, bind_assoc, pure_bind]

end Updates

end Solidity.Core
