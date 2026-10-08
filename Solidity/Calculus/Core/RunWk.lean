import Solidity.Calculus.Core.Logic
import Solidity.Calculus.Core.WkOver

/-!
# A weakened program runs as the program

`Stmt.wk h` reads a statement of `Γ` in a context `Δ` that `Γ` thins into
(`Syntax/Core.lean`).  Run from a state of `Δ`, it does what the statement
does from that state's locals of `Γ` (`State.thin h`), and leaves the other
locals of `Δ` as they were: `Stmt.run_wk`, `Prog.run_wk`.  A call's body is
read under its caller once (`Prog.wk (Thin.atop …)`, `Calculus/Core/Blocks.lean`)
and the diamond's invariant rule reads a loop body under its variant
(`Prog.wk up`): their soundness is this.

The state of `Δ` is written `τ.lift h d`: `τ`'s locals at the positions `h`
keeps, `d`'s at the others (`Env.put`).  `Env.off h d` is what the others
hold; a weakened run keeps it (`WkRel`).  A statement that writes no scope
runs, lifted, as lifted (`lifted`, as `Calculus/Core/SoundArms.lean`'s
`pushed`); a scope's end pops the same locals on both sides
(`Thin.Over`).
-/

namespace Solidity.Core

open Semantics (Value SVal MVal Seg Halt Res)

variable {C : Contract}

/-! ## The locals a thinning drops -/

namespace Env

/-- `e` at the positions `h` keeps, `d` at the others. -/
def put : {Γ Δ : Ctx} → Thin Γ Δ → Env C Γ → Env C Δ → Env C Δ
  | _, _, .refl, e, _ => e
  | _, _, .keep h, e, d => (e.1, Env.put h e.2 d.2)
  | _, _, .drop h, e, d => (d.1, Env.put h e d.2)

/-- What the positions `h` drops hold. -/
def off : {Γ Δ : Ctx} → Thin Γ Δ → Env C Δ → List ((t : LTy) × t.Denote C)
  | _, _, .refl, _ => []
  | _, _, .keep h, d => Env.off h d.2
  | _, _, .drop h, d => ⟨_, d.1⟩ :: Env.off h d.2

theorem get_put {t : LTy} : {Γ Δ : Ctx} → (h : Thin Γ Δ) → (i : Idx Γ t) → (e : Env C Γ) → (d : Env C Δ) →
    Env.get (i.wk h) (Env.put h e d) = Env.get i e
  | _, _, .refl, _, _, _ => rfl
  | _, _, .keep _, .here, _, _ => rfl
  | _, _, .keep h, .there i, e, d => get_put h i e.2 d.2
  | _, _, .drop h, i, e, d => get_put h i e d.2

theorem set_put {t : LTy} : {Γ Δ : Ctx} → (h : Thin Γ Δ) → (i : Idx Γ t) → (v : t.Denote C) → (e : Env C Γ) →
    (d : Env C Δ) → Env.set (i.wk h) v (Env.put h e d) = Env.put h (Env.set i v e) d
  | _, _, .refl, _, _, _, _ => rfl
  | _, _, .keep _, .here, _, _, _ => rfl
  | _, _, .keep h, .there i, v, e, d => by
    show (e.1, Env.set (i.wk h) v (Env.put h e.2 d.2)) = (e.1, Env.put h (Env.set i v e.2) d.2)
    rw [set_put h i v e.2 d.2]
  | _, _, .drop h, i, v, e, d => by
    show (d.1, Env.set (i.wk h) v (Env.put h e d.2)) = (d.1, Env.put h (Env.set i v e) d.2)
    rw [set_put h i v e d.2]

theorem thin_put : {Γ Δ : Ctx} → (h : Thin Γ Δ) → (e : Env C Γ) → (d : Env C Δ) → Env.thin h (Env.put h e d) = e
  | _, _, .refl, _, _ => rfl
  | _, _, .keep h, e, d => by
    show (e.1, Env.thin h (Env.put h e.2 d.2)) = e
    rw [thin_put h e.2 d.2]; rfl
  | _, _, .drop h, e, d => thin_put h e d.2

theorem off_put : {Γ Δ : Ctx} → (h : Thin Γ Δ) → (e : Env C Γ) → (d : Env C Δ) → Env.off h (Env.put h e d) = Env.off h d
  | _, _, .refl, _, _ => rfl
  | _, _, .keep h, e, d => off_put h e.2 d.2
  | _, _, .drop h, e, d => by
    show ⟨_, d.1⟩ :: Env.off h (Env.put h e d.2) = ⟨_, d.1⟩ :: Env.off h d.2
    rw [off_put h e d.2]

theorem put_thin : {Γ Δ : Ctx} → (h : Thin Γ Δ) → (d : Env C Δ) → Env.put h (Env.thin h d) d = d
  | _, _, .refl, _ => rfl
  | _, _, .keep h, d => by
    show (d.1, Env.put h (Env.thin h d.2) d.2) = d
    rw [put_thin h d.2]; rfl
  | _, _, .drop h, d => by
    show (d.1, Env.put h (Env.thin h d.2) d.2) = d
    rw [put_thin h d.2]; rfl

/-- Only what `h` drops of the background matters. -/
theorem put_congr : {Γ Δ : Ctx} → (h : Thin Γ Δ) → (e : Env C Γ) → {d d' : Env C Δ} →
    Env.off h d = Env.off h d' → Env.put h e d = Env.put h e d'
  | _, _, .refl, _, _, _, _ => rfl
  | _, _, .keep h, e, d, d', hd => by
    show (e.1, Env.put h e.2 d.2) = (e.1, Env.put h e.2 d'.2)
    rw [put_congr h e.2 hd]
  | _, _, .drop h, e, d, d', hd => by
    have h' : (⟨_, d.1⟩ : (t : LTy) × t.Denote C) = ⟨_, d'.1⟩ ∧ Env.off h d.2 = Env.off h d'.2 :=
      List.cons.inj hd
    have h1 : d.1 = d'.1 := eq_of_heq (Sigma.mk.inj h'.1).2
    show (d.1, Env.put h e d.2) = (d'.1, Env.put h e d'.2)
    rw [h1, put_congr h e h'.2]

variable {Γ Δ : Ctx}

theorem put_keepAll (h : Thin Γ Δ) : (ρ : Ctx) → (r r' : Env C ρ) → (e : Env C Γ) → (d : Env C Δ) →
    Env.put (Thin.keepAll ρ h) (Env.append ρ r e) (Env.append ρ r' d) = Env.append ρ r (Env.put h e d)
  | [], _, _, _, _ => rfl
  | _ :: ρ, r, r', e, d => by
    show (r.1, Env.put (Thin.keepAll ρ h) (Env.append ρ r.2 e) (Env.append ρ r'.2 d)) = _
    rw [put_keepAll h ρ r.2 r'.2 e d]; rfl

theorem off_keepAll (h : Thin Γ Δ) : (ρ : Ctx) → (r : Env C ρ) → (d : Env C Δ) →
    Env.off (Thin.keepAll ρ h) (Env.append ρ r d) = Env.off h d
  | [], _, _ => rfl
  | _ :: ρ, r, d => off_keepAll h ρ r.2 d

end Env

/-! ## A state of `Δ` from one of `Γ` -/

section Lift

variable {Γ Δ : Ctx}

/-- `τ`'s locals at the positions `h` keeps, `d`'s at the others. -/
def State.lift (h : Thin Γ Δ) (d : Env C Δ) (τ : State C Γ) : State C Δ :=
  τ.withEnv (Env.put h τ.env d)

theorem State.lift_thin (h : Thin Γ Δ) (σ : State C Δ) : (σ.thin h).lift h σ.env = σ := by
  cases σ
  simp only [State.lift, State.thin, State.withEnv, Env.put_thin]

theorem State.glob_lift (h : Thin Γ Δ) (d : Env C Δ) (τ : State C Γ) :
    (τ.lift h d).glob = τ.glob := rfl

theorem State.lift_setLocal (h : Thin Γ Δ) (d : Env C Δ) (τ : State C Γ) {t : LTy} (i : Idx Γ t)
    (v : t.Denote C) : (τ.lift h d).setLocal (i.wk h) v = (τ.setLocal i v).lift h d := by
  simp only [State.lift, State.setLocal, State.withEnv, Env.set_put]

theorem State.lift_withGlob (h : Thin Γ Δ) (d : Env C Δ) (τ : State C Γ) (g : Semantics.State) :
    (τ.lift h d).withGlob g = (τ.withGlob g).lift h d := rfl

theorem State.lift_push (h : Thin Γ Δ) (d : Env C Δ) (τ : State C Γ) {t : LTy} (v w : t.Denote C) :
    (τ.lift h d).push v = (τ.push v).lift (.keep h) (w, d) := rfl

theorem State.get_lift (h : Thin Γ Δ) (d : Env C Δ) (τ : State C Γ) {t : LTy} (i : Idx Γ t) :
    Env.get (i.wk h) (τ.lift h d).env = Env.get i τ.env :=
  Env.get_put h i τ.env d

theorem State.lift_congr (h : Thin Γ Δ) {d d' : Env C Δ} (hd : Env.off h d = Env.off h d')
    (τ : State C Γ) : τ.lift h d = τ.lift h d' := by
  simp only [State.lift, Env.put_congr h τ.env hd]

/-- An outcome, its state lifted. -/
abbrev lifted (h : Thin Γ Δ) (d : Env C Δ) (r : Res (State C Γ)) : Res (State C Δ) :=
  r.map (State.lift h d)

theorem lifted_bind (h : Thin Γ Δ) (d : Env C Δ) {α : Type} (x : Res α) (f : α → Res (State C Γ)) :
    lifted h d (x >>= f) = x >>= fun a => lifted h d (f a) := by
  cases x <;> rfl

theorem lifted_pure (h : Thin Γ Δ) (d : Env C Δ) (τ : State C Γ) :
    lifted h d (pure τ) = pure (τ.lift h d) := rfl

theorem withGlob_map_lift (h : Thin Γ Δ) (d : Env C Δ) (τ : State C Γ) (x : Res Semantics.State) :
    (τ.lift h d).withGlob <$> x = lifted h d (τ.withGlob <$> x) := by
  cases x <;> rfl

/-- An outcome with a value, its state lifted. -/
abbrev lifted₂ {α : Type} (h : Thin Γ Δ) (d : Env C Δ) (r : Res (State C Γ × α)) :
    Res (State C Δ × α) :=
  r.map fun x => (x.1.lift h d, x.2)

theorem lifted₂_bind {α β : Type} (h : Thin Γ Δ) (d : Env C Δ) (x : Res β)
    (f : β → Res (State C Γ × α)) :
    lifted₂ h d (x >>= f) = x >>= fun a => lifted₂ h d (f a) := by
  cases x <;> rfl

theorem lifted₂_pure {α : Type} (h : Thin Γ Δ) (d : Env C Δ) (τ : State C Γ) (a : α) :
    lifted₂ h d (pure (τ, a)) = pure (τ.lift h d, a) := rfl

/-- What the lift lemmas rewrite with. -/
macro "lift_run" "[" ls:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| simp only [State.glob_lift, withGlob_map_lift, lifted_bind, lifted_pure, lifted₂_bind,
    lifted₂_pure, State.lift_setLocal, State.lift_withGlob, State.get_lift, $ls,*])

end Lift

/-! ## Parts read in a weakened context -/

section Parts

variable {Γ Δ : Ctx} (h : Thin Γ Δ) (d : Env C Δ) (τ : State C Γ)

theorem Simple.eval_wk {p : PrimTy} (s : Simple C Γ p) : (s.wk h).eval (τ.lift h d) = s.eval τ := by
  cases s with
  | «local» i => simp only [Simple.wk, Simple.eval, State.get_lift]
  | _ => rfl

theorem aliasPath_wk {R : RefTy} (i : Idx Γ (.alias R)) :
    aliasPath (τ.lift h d) (i.wk h) = aliasPath τ i := by
  simp only [aliasPath, State.get_lift]

theorem memRef_wk {R : RefTy} (i : Idx Γ (.mem R)) :
    memRef (τ.lift h d) (i.wk h) = memRef τ i := by
  simp only [memRef, State.get_lift]

mutual

theorem SPath.resolve_wk : {T : Ty} → (b : SPath C Γ T) → (b.wk h).resolve (τ.lift h d) = b.resolve τ
  | _, .alias i => aliasPath_wk h d τ i
  | _, .loc l => Loc.resolve_wk l

theorem Loc.resolve_wk : {T : Ty} → (l : Loc C Γ T) → (l.wk h).resolve (τ.lift h d) = l.resolve τ
  | _, .root .. => rfl
  | _, .field b f _ => by simp only [Loc.wk, Loc.resolve, SPath.resolve_wk b]
  | _, .index _ b i => by
    simp only [Loc.wk, Loc.resolve, SPath.resolve_wk b, Val.eval_wk i, State.glob_lift]

theorem MPath.mval_wk : {T : Ty} → (b : MPath C Γ T) → (b.wk h).mval (τ.lift h d) = b.mval τ
  | _, .var i _ => by simp only [MPath.wk, MPath.mval, memRef_wk h d τ i]
  | _, .loc l => MLoc.read_wk l

theorem MLoc.read_wk : {T : Ty} → (l : MLoc C Γ T) → (l.wk h).read (τ.lift h d) = l.read τ
  | _, .field b f _ => by simp only [MLoc.wk, MLoc.read, MPath.mval_wk b, State.glob_lift]
  | _, .index _ b i => by
    simp only [MLoc.wk, MLoc.read, MPath.mval_wk b, Val.eval_wk i, State.glob_lift]

theorem Val.eval_wk : {p : PrimTy} → (v : Val C Γ p) → (v.wk h).eval (τ.lift h d) = v.eval τ
  | _, .simple s => Simple.eval_wk h d τ s
  | _, .read l => by simp only [Val.wk, Val.eval, Loc.resolve_wk l, State.glob_lift]
  | _, .binop .. => by simp only [Val.wk, Val.eval, Val.eval_wk]
  | _, .unop .. => by simp only [Val.wk, Val.eval, Val.eval_wk]
  | _, .ternary .. => by simp only [Val.wk, Val.eval, Val.eval_wk]
  | _, .readMem l => by simp only [Val.wk, Val.eval, MLoc.read_wk l]
  | _, .len b _ => by simp only [Val.wk, Val.eval, SPath.resolve_wk b, State.glob_lift]
  | _, .mlen b _ => by simp only [Val.wk, Val.eval, MPath.mval_wk b, State.glob_lift]

end

theorem Src.value_wk {T : Ty} (r : Src C Γ T) : (r.wk h).value (τ.lift h d) = r.value τ := by
  cases r with
  | val v => simp only [Src.wk, Src.value, Val.eval_wk]
  | copy p _ => simp only [Src.wk, Src.value, SPath.resolve_wk, State.glob_lift]

theorem Src.pushVal_wk {T : Ty} (v : Option (Src C Γ T)) :
    Src.pushVal (τ.lift h d) (v.map (·.wk h)) = Src.pushVal τ v := by
  cases v with
  | none => rfl
  | some r => funext slot; simp only [Option.map, Src.pushVal, Src.value_wk]

theorem MSrc.mval_wk {T : Ty} (r : MSrc C Γ T) : (r.wk h).mval (τ.lift h d) = r.mval τ := by
  cases r with
  | val v => simp only [MSrc.wk, MSrc.mval, Val.eval_wk]
  | ref p => simp only [MSrc.wk, MSrc.mval, MPath.mval_wk]

theorem MLoc.addr_wk {T : Ty} (l : MLoc C Γ T) : (l.wk h).addr (τ.lift h d) = l.addr τ := by
  cases l with
  | field b f _ => simp only [MLoc.wk, MLoc.addr, MPath.mval_wk]
  | index _ b i => simp only [MLoc.wk, MLoc.addr, MPath.mval_wk, Val.eval_wk]

theorem MLoc.write_wk {T : Ty} (l : MLoc C Γ T) (mv : MVal) :
    (l.wk h).write (τ.lift h d) mv = lifted h d (l.write τ mv) := by
  cases l with
  | field b f _ => lift_run [MLoc.wk, MLoc.write, MPath.mval_wk]
  | index _ b i => lift_run [MLoc.wk, MLoc.write, MPath.mval_wk, Val.eval_wk]

theorem ARhs.eval_wk {R : RefTy} (r : ARhs C Γ R) :
    (r.wk h).eval (τ.lift h d) = lifted₂ h d (r.eval τ) := by
  cases r with
  | path p => lift_run [ARhs.wk, ARhs.eval, SPath.resolve_wk]
  | push b _ => lift_run [ARhs.wk, ARhs.eval, SPath.resolve_wk]

theorem MRhs.eval_wk {R : RefTy} (r : MRhs C Γ R) :
    (r.wk h).eval (τ.lift h d) = lifted₂ h d (r.eval τ) := by
  cases r with
  | «alias» p => lift_run [MRhs.wk, MRhs.eval, MPath.mval_wk]
  | copy p _ => lift_run [MRhs.wk, MRhs.eval, SPath.resolve_wk]
  | newArr n _ => lift_run [MRhs.wk, MRhs.eval, Simple.eval_wk]

end Parts

/-! ## Statements that open no scope -/

section Stmts

variable {Γ Δ : Ctx} (h : Thin Γ Δ) (d : Env C Δ) (τ : State C Γ)

theorem OpLoc.store_wk (op : BinOp) {p : PrimTy} (l : OpLoc C Γ p) (v : Value) :
    (l.wk h).store (τ.lift h d) op v = lifted h d (l.store τ op v) := by
  cases l with
  | «local» i => lift_run [OpLoc.wk, OpLoc.store, opLocal]
  | root r _ => lift_run [OpLoc.wk, OpLoc.store]
  | field b f _ => lift_run [OpLoc.wk, OpLoc.store, Loc.resolve, SPath.resolve_wk]
  | index _ b i => lift_run [OpLoc.wk, OpLoc.store, Loc.resolve, Val.eval, SPath.resolve_wk,
      Simple.eval_wk]
  | mfield b f _ => lift_run [OpLoc.wk, OpLoc.store, MPath.mval_wk]
  | mindex _ b i => lift_run [OpLoc.wk, OpLoc.store, MPath.mval_wk, Simple.eval_wk]

theorem OpLoc.bump_wk (op : IncDec) {p : PrimTy} (l : OpLoc C Γ p) :
    (l.wk h).bump (τ.lift h d) op = lifted₂ h d (l.bump τ op) := by
  cases l with
  | «local» i => lift_run [OpLoc.wk, OpLoc.bump, bumpLocal]
  | root r _ =>
    simp only [OpLoc.wk, OpLoc.bump, State.glob_lift]
    cases bumpStore τ.glob op _ r [] <;> rfl
  | field b f _ =>
    lift_run [OpLoc.wk, OpLoc.bump, Loc.resolve, SPath.resolve_wk]
    congr 1; funext q; cases bumpStore τ.glob op p q.1 q.2 <;> rfl
  | index _ b i =>
    lift_run [OpLoc.wk, OpLoc.bump, Loc.resolve, Val.eval, SPath.resolve_wk, Simple.eval_wk]
    congr 1; funext q; cases bumpStore τ.glob op p q.1 q.2 <;> rfl
  | mfield b f _ =>
    lift_run [OpLoc.wk, OpLoc.bump, MPath.mval_wk]
    congr 1; funext q; congr 1; funext id; cases bumpMem τ.glob op p _ <;> rfl
  | mindex _ b i =>
    lift_run [OpLoc.wk, OpLoc.bump, MPath.mval_wk, Simple.eval_wk]
    congr 1; funext q; congr 1; funext id; congr 1; funext iv; congr 1; funext n
    cases bumpMem τ.glob op p _ <;> rfl

theorem sendAt_wk (pv : Idx Γ (.val .bool)) (addr amt : Int) :
    sendAt (τ.lift h d) (pv.wk h) addr amt = lifted h d (sendAt τ pv addr amt) := by
  unfold sendAt
  split
  · rfl
  · rw [show (τ.lift h d).tx = τ.tx from rfl]
    cases Semantics.lookupBy (sendKey addr amt) τ.tx.ext with
    | none => lift_run []; rfl
    | some r => cases r <;> (lift_run []; rfl)

theorem guardOk_wk (c : Val C Γ .bool) :
    (do guardOk (← (c.wk h).eval (τ.lift h d)) (τ.lift h d)) =
      lifted h d (do guardOk (← c.eval τ) τ) := by
  rw [Val.eval_wk]
  cases c.eval τ with
  | error => rfl
  | ok v => rcases v with _ | (_ | _) <;> rfl

theorem assertOk_wk (c : Val C Γ .bool) :
    (do assertOk (← (c.wk h).eval (τ.lift h d)) (τ.lift h d)) =
      lifted h d (do assertOk (← c.eval τ) τ) := by
  rw [Val.eval_wk]
  cases c.eval τ with
  | error => rfl
  | ok v => rcases v with _ | (_ | _) <;> rfl

theorem Run.deleteMem_wk {T : Ty} (p : MPath C Γ T) :
    Run.deleteMem (p.wk h) (τ.lift h d) = lifted h d (Run.deleteMem p τ) := by
  cases p with
  | var i _ =>
    lift_run [MPath.wk, Run.deleteMem]
  | loc l => lift_run [MPath.wk, Run.deleteMem, MLoc.addr_wk]

theorem Run.assignNew_wk {R : RefTy} (l : NewLhs C Γ R) (n : Simple C Γ .uint) :
    Run.assignNew (l.wk h) (n.wk h) (τ.lift h d) = lifted h d (Run.assignNew l n τ) := by
  cases l with
  | store l => lift_run [NewLhs.wk, Run.assignNew, Simple.eval_wk, Loc.resolve_wk]
  | mem l => lift_run [NewLhs.wk, Run.assignNew, Simple.eval_wk, MLoc.write_wk]

end Stmts

section Stmts2

variable {Γ Δ : Ctx} (h : Thin Γ Δ) (d : Env C Δ) (τ : State C Γ)

theorem Run.assign_wk {T : Ty} (l : Loc C Γ T) (r : Src C Γ T) :
    Run.assign (l.wk h) (r.wk h) (τ.lift h d) = lifted h d (Run.assign l r τ) := by
  lift_run [Run.assign, Src.value_wk, Loc.resolve_wk]

theorem Run.rebind_wk {R : RefTy} (i : Idx Γ (.alias R)) (r : ARhs C Γ R) :
    Run.rebind (i.wk h) (r.wk h) (τ.lift h d) = lifted h d (Run.rebind i r τ) := by
  simp only [Run.rebind, ARhs.eval_wk]
  cases r.eval τ with
  | error => rfl
  | ok x => exact congrArg Except.ok (State.lift_setLocal h d x.1 i _)

theorem Run.assignLocal_wk {p : PrimTy} (i : Idx Γ (.val p)) (r : Val C Γ p) :
    Run.assignLocal (i.wk h) (r.wk h) (τ.lift h d) = lifted h d (Run.assignLocal i r τ) := by
  lift_run [Run.assignLocal, Val.eval_wk]

theorem Run.opAssign_wk {p : PrimTy} (op : BinOp) (l : OpLoc C Γ p) (r : Val C Γ p) :
    Run.opAssign op (l.wk h) (r.wk h) (τ.lift h d) = lifted h d (Run.opAssign op l r τ) := by
  lift_run [Run.opAssign, Val.eval_wk, OpLoc.store_wk]

theorem Run.incDec_wk {p : PrimTy} (op : IncDec) (l : OpLoc C Γ p) :
    Run.incDec op (l.wk h) (τ.lift h d) = lifted h d (Run.incDec op l τ) := by
  simp only [Run.incDec, OpLoc.bump_wk]
  cases l.bump τ op <;> rfl

theorem Run.assignIncDec_wk {p : PrimTy} (i : Idx Γ (.val p)) (op : IncDec) (l : OpLoc C Γ p) :
    Run.assignIncDec (i.wk h) op (l.wk h) (τ.lift h d) = lifted h d (Run.assignIncDec i op l τ) := by
  simp only [Run.assignIncDec, OpLoc.bump_wk]
  cases l.bump τ op with
  | error => rfl
  | ok x => exact congrArg Except.ok (State.lift_setLocal h d x.1 i _)

theorem Run.push_wk {E : Ty} (b : SPath C Γ (.array E)) (v : Option (Src C Γ E)) :
    Run.push (b.wk h) (v.map (·.wk h)) (τ.lift h d) = lifted h d (Run.push b v τ) := by
  lift_run [Run.push, SPath.resolve_wk, Src.pushVal_wk]

theorem Run.pop_wk {E : Ty} (b : SPath C Γ (.array E)) :
    Run.pop (b.wk h) (τ.lift h d) = lifted h d (Run.pop b τ) := by
  lift_run [Run.pop, SPath.resolve_wk]

theorem Run.transfer_wk (r a : Val C Γ .uint) :
    Run.transfer (r.wk h) (a.wk h) (τ.lift h d) = lifted h d (Run.transfer r a τ) := by
  lift_run [Run.transfer, Val.eval_wk]

theorem Run.send_wk (pv : Idx Γ (.val .bool)) (r a : Val C Γ .uint) :
    Run.send (pv.wk h) (r.wk h) (a.wk h) (τ.lift h d) = lifted h d (Run.send pv r a τ) := by
  lift_run [Run.send, Val.eval_wk, sendAt_wk]

theorem Run.rebindMem_wk {R : RefTy} (i : Idx Γ (.mem R)) (r : MRhs C Γ R) :
    Run.rebindMem (i.wk h) (r.wk h) (τ.lift h d) = lifted h d (Run.rebindMem i r τ) := by
  simp only [Run.rebindMem, MRhs.eval_wk]
  cases r.eval τ with
  | error => rfl
  | ok x => exact congrArg Except.ok (State.lift_setLocal h d x.1 i _)

theorem Run.assignFromMem_wk {R : RefTy} (l : Loc C Γ (.ref R)) (q : MPath C Γ (.ref R)) :
    Run.assignFromMem (l.wk h) (q.wk h) (τ.lift h d) = lifted h d (Run.assignFromMem l q τ) := by
  lift_run [Run.assignFromMem, MPath.mval_wk, Loc.resolve_wk]

theorem Run.assignMem_wk {T : Ty} (l : MLoc C Γ T) (r : MSrc C Γ T) :
    Run.assignMem (l.wk h) (r.wk h) (τ.lift h d) = lifted h d (Run.assignMem l r τ) := by
  lift_run [Run.assignMem, MSrc.mval_wk, MLoc.write_wk]

theorem Run.delete_wk {T : Ty} (l : Loc C Γ T) :
    Run.delete (l.wk h) (τ.lift h d) = lifted h d (Run.delete l τ) := by
  lift_run [Run.delete, Loc.resolve_wk]

/-- A declaration, lifted: the declared local kept on top. -/
abbrev liftedTop {t : LTy} (r : Res (State C (t :: Γ))) : Res (State C (t :: Δ)) :=
  r.map fun τ' => τ'.lift (.keep h) (τ'.env.1, d)

theorem Run.declLocal_wk (p : PrimTy) (init : Option (Val C Γ p)) :
    Run.declLocal p (init.map (·.wk h)) (τ.lift h d) = liftedTop h d (Run.declLocal p init τ) := by
  cases init with
  | none => rfl
  | some e =>
    simp only [Option.map, Run.declLocal, Val.eval_wk]
    cases e.eval τ <;> rfl

theorem Run.declStorage_wk (R : RefTy) (init : Option (ARhs C Γ R)) :
    Run.declStorage R (init.map (·.wk h)) (τ.lift h d) =
      liftedTop h d (Run.declStorage R init τ) := by
  cases init with
  | none => rfl
  | some r =>
    simp only [Option.map, Run.declStorage, ARhs.eval_wk]
    cases r.eval τ <;> rfl

theorem Run.declMem_wk (R : RefTy) (init : Option (MRhs C Γ R)) :
    Run.declMem R (init.map (·.wk h)) (τ.lift h d) = liftedTop h d (Run.declMem R init τ) := by
  cases init with
  | none =>
    simp only [Option.map, Run.declMem, State.glob_lift]
    cases Semantics.allocDefault τ.glob R <;> rfl
  | some r =>
    simp only [Option.map, Run.declMem, MRhs.eval_wk]
    cases r.eval τ <;> rfl

theorem Args.eval_wk : {ps : Ctx} → (as : Args C Γ ps) → (as.wk h).eval (τ.lift h d) = as.eval τ
  | _, .nil => rfl
  | _, .snoc as p x e => by
    show (do
        let r ← Args.eval (τ.lift h d) (as.wk h)
        let v ← (e.wk h).eval (τ.lift h d)
        pure (v, r)) = (do
        let r ← Args.eval τ as
        let v ← e.eval τ
        pure (v, r))
    rw [Args.eval_wk as, Val.eval_wk]

theorem ExtCall.key_wk (c : ExtCall C Γ) : (c.wk h).key (τ.lift h d) = c.key τ := by
  have hm : ∀ as : List (ExtArg C Γ),
      (as.map fun a => (⟨a.1, a.2.wk h⟩ : ExtArg C Δ)).mapM (fun a => a.2.eval (τ.lift h d)) =
        as.mapM fun a => a.2.eval τ := by
    intro as
    induction as with
    | nil => rfl
    | cons a as ih => simp only [List.map_cons, List.mapM_cons, Simple.eval_wk, ih]
  simp only [ExtCall.key, ExtCall.wk, Simple.eval_wk, hm]

end Stmts2

/-! ## Outcomes related by a weakening -/

section Rel

variable {Γ Δ : Ctx}

/-- Two outcomes, the second the first's run weakened by `h`: the same halt,
or states the first's lifted over locals whose dropped ones hold `o`. -/
def WkRel (h : Thin Γ Δ) (o : List ((t : LTy) × t.Denote C)) :
    Res (State C Γ) → Res (State C Δ) → Prop
  | .ok τ, .ok ρ => ∃ d, Env.off h d = o ∧ ρ = τ.lift h d
  | .error e, .error e' => e = e'
  | _, _ => False

theorem WkRel.of_map {h : Thin Γ Δ} {o : List ((t : LTy) × t.Denote C)} (r : Res (State C Γ))
    {f : State C Γ → State C Δ} (hf : ∀ τ, ∃ d, Env.off h d = o ∧ f τ = τ.lift h d) :
    WkRel h o r (r.map f) := by
  cases r with
  | error => rfl
  | ok τ => exact hf τ

theorem WkRel.of_eq {h : Thin Γ Δ} {d : Env C Δ} {r₀ : Res (State C Γ)} {r : Res (State C Δ)}
    (he : r = lifted h d r₀) : WkRel h (Env.off h d) r₀ r :=
  he ▸ WkRel.of_map r₀ fun _ => ⟨d, rfl, rfl⟩

theorem WkRel.of_top {t : LTy} {h : Thin Γ Δ} {d : Env C Δ} {r₀ : Res (State C (t :: Γ))}
    {r : Res (State C (t :: Δ))} (he : r = liftedTop h d r₀) : WkRel (.keep h) (Env.off h d) r₀ r :=
  he ▸ WkRel.of_map r₀ fun τ' => ⟨(τ'.env.1, d), rfl, rfl⟩

/-- The run lifted, when the background is fixed. -/
theorem WkRel.eq_lifted {h : Thin Γ Δ} {d : Env C Δ} {r₀ : Res (State C Γ)} {r : Res (State C Δ)}
    (hr : WkRel h (Env.off h d) r₀ r) : r = lifted h d r₀ := by
  cases r₀ with
  | error e => cases r with
    | error e' => cases hr; rfl
    | ok => cases hr
  | ok τ => cases r with
    | error => cases hr
    | ok ρ =>
      obtain ⟨d', hd, rfl⟩ := hr
      exact congrArg Except.ok (State.lift_congr h hd τ)

theorem WkRel.bind_same {α : Type} {h : Thin Γ Δ} {o : List ((t : LTy) × t.Denote C)} (x : Res α)
    {f : α → Res (State C Γ)} {g : α → Res (State C Δ)} (hfg : ∀ a, WkRel h o (f a) (g a)) :
    WkRel h o (x >>= f) (x >>= g) := by
  cases x with
  | error => rfl
  | ok a => exact hfg a

theorem WkRel.bind {Γ₁ Δ₁ : Ctx} {h₁ : Thin Γ Δ} {h₂ : Thin Γ₁ Δ₁}
    {o : List ((t : LTy) × t.Denote C)} {r₀ : Res (State C Γ)} {r : Res (State C Δ)}
    (hr : WkRel h₁ o r₀ r) {f : State C Γ → Res (State C Γ₁)} {g : State C Δ → Res (State C Δ₁)}
    (hfg : ∀ τ d, Env.off h₁ d = o → WkRel h₂ o (f τ) (g (τ.lift h₁ d))) :
    WkRel h₂ o (r₀.bind f) (r.bind g) := by
  cases r₀ with
  | error e => cases r with
    | error e' => cases hr; rfl
    | ok => cases hr
  | ok τ => cases r with
    | error => cases hr
    | ok ρ =>
      obtain ⟨d', hd, rfl⟩ := hr
      exact hfg τ d' hd

end Rel

/-! ## A scope's end on both sides -/

namespace Thin.Over

theorem env {Γ Γ' Δ Δ' : Ctx} {e : Ext Γ Γ'} {h : Thin Γ Δ} {e' : Ext Δ Δ'} {h' : Thin Γ' Δ'}
    (ho : Thin.Over e h e' h') (x : Env C Γ') (d' : Env C Δ') :
    Env.drop e' (Env.put h' x d') = Env.put h (Env.drop e x) (Env.drop e' d') ∧
      Env.off h (Env.drop e' d') = Env.off h' d' := by
  induction ho with
  | refl => exact ⟨rfl, rfl⟩
  | push _ ih => exact ih x.2 d'.2

end Thin.Over

theorem WkRel.drop {Γ Γ' Δ Δ' : Ctx} {e : Ext Γ Γ'} {h : Thin Γ Δ} {e' : Ext Δ Δ'}
    {h' : Thin Γ' Δ'} (ho : Thin.Over e h e' h') {o : List ((t : LTy) × t.Denote C)}
    {r₀ : Res (State C Γ')} {r : Res (State C Δ')} (hr : WkRel h' o r₀ r) :
    WkRel h o (r₀.map (State.drop e)) (r.map (State.drop e')) := by
  cases r₀ with
  | error e => cases r with
    | error e' => cases hr; rfl
    | ok => cases hr
  | ok τ => cases r with
    | error => cases hr
    | ok ρ =>
      obtain ⟨d', hd, rfl⟩ := hr
      obtain ⟨h1, h2⟩ := ho.env τ.env d'
      exact ⟨Env.drop e' d', h2.trans hd, by
        simp only [State.drop, State.lift, State.withEnv, h1]⟩

/-! ## A loop whose every turn is lifted -/

namespace Loop

variable {α β : Type} {body : α → Res α} {c : α → Res Value} {body' : β → Res β}
  {c' : β → Res Value} (f : α → β)

theorem iterN_map (hc : ∀ a, c' (f a) = c a) (hb : ∀ a, body' (f a) = (body a).map f) :
    (n : Nat) → (σ : α) → iterN body' c' n (f σ) = Sum.map f (Except.map f) (iterN body c n σ)
  | 0, _ => rfl
  | n + 1, σ => by
    simp only [iterN, step, hc, hb]
    cases c σ with
    | error => rfl
    | ok v =>
      rcases v with _ | (_ | _)
      · rfl
      · rfl
      · simp only
        cases body σ with
        | error => rfl
        | ok τ => exact iterN_map hc hb n τ

/-- **A loop every turn of which is lifted by `f` runs lifted.** -/
theorem run_map (hc : ∀ a, c' (f a) = c a) (hb : ∀ a, body' (f a) = (body a).map f) (σ : α) :
    run body' c' (f σ) = (run body c σ).map f := by
  by_cases hex : ∃ r n, iterN body c n σ = .inr r
  · obtain ⟨r, n, hn⟩ := hex
    rw [run_of_iterN hn]
    apply run_of_iterN (n := n)
    rw [iterN_map f hc hb n σ, hn]; rfl
  · have hex' : ¬ ∃ r n, iterN body' c' n (f σ) = .inr r := by
      rintro ⟨r, n, hn⟩
      rw [iterN_map f hc hb n σ] at hn
      cases hi : iterN body c n σ with
      | inl => rw [hi] at hn; cases hn
      | inr r₀ => exact hex ⟨r₀, n, hi⟩
    simp only [run, hex, hex', dite_false]
    rfl

end Loop

/-! ## A weakened statement runs as the statement -/

theorem CallRet.enter_wk {Γ Δ : Ctx} (h : Thin Γ Δ) (g : Semantics.State) {rs Γ' : Ctx}
    (ret : CallRet Γ rs Γ') : (ret.wk h).2.2.enter (C := C) g = ret.enter g := by
  cases ret <;> rfl

theorem CallRet.leave_wk {Γ Δ : Ctx} (h : Thin Γ Δ) (e : Env C Γ) (d : Env C Δ) {rs Γ' : Ctx}
    (ret : CallRet Γ rs Γ') (x : Env C rs) :
    ∃ d', Env.off (ret.wk h).2.1 d' = Env.off h d ∧
      (ret.wk h).2.2.leave (Env.put h e d) x = Env.put (ret.wk h).2.1 (ret.leave e x) d' := by
  cases ret with
  | none => exact ⟨d, rfl, rfl⟩
  | val p r res =>
    cases res with
    | none => exact ⟨d, rfl, rfl⟩
    | some i => exact ⟨d, rfl, Env.set_put h i x.1 e d⟩
  | rets bs => exact ⟨Env.append _ x d, Env.off_keepAll h _ x d, (Env.put_keepAll h _ x x e d).symm⟩
  | mem R r hd hm => exact ⟨(x.1, d), rfl, rfl⟩

mutual

/-- **A weakened statement runs as the statement**: from a state of `Δ`, it
does what the statement does from that state's locals of `Γ`, and keeps the
others. -/
theorem Stmt.run_wk : {Γ Γ' : Ctx} → (s : Stmt C Γ Γ') → ∀ {Δ : Ctx} (h : Thin Γ Δ)
    (d : Env C Δ) (τ : State C Γ),
    WkRel (s.wk h).2.1 (Env.off h d) (s.run τ) ((s.wk h).2.2.run (τ.lift h d))
  | _, _, .assign l r, _, h, d, τ => WkRel.of_eq (Run.assign_wk h d τ l r)
  | _, _, .rebind i r, _, h, d, τ => WkRel.of_eq (Run.rebind_wk h d τ i r)
  | _, _, .assignLocal i r, _, h, d, τ => WkRel.of_eq (Run.assignLocal_wk h d τ i r)
  | _, _, .declLocal p _ init, _, h, d, τ => WkRel.of_top (Run.declLocal_wk h d τ p init)
  | _, _, .declStorage R _ init, _, h, d, τ => WkRel.of_top (Run.declStorage_wk h d τ R init)
  | _, _, .opAssign op _ _ l r, _, h, d, τ => WkRel.of_eq (Run.opAssign_wk h d τ op l r)
  | _, _, .incDec op _ l, _, h, d, τ => WkRel.of_eq (Run.incDec_wk h d τ op l)
  | _, _, .assignIncDec i op _ l _, _, h, d, τ => WkRel.of_eq (Run.assignIncDec_wk h d τ i op l)
  | _, _, .push b v _, _, h, d, τ => WkRel.of_eq (Run.push_wk h d τ b v)
  | _, _, .pop b, _, h, d, τ => WkRel.of_eq (Run.pop_wk h d τ b)
  | _, _, .transfer r a, _, h, d, τ => WkRel.of_eq (Run.transfer_wk h d τ r a)
  | _, _, .send pv r a, _, h, d, τ => WkRel.of_eq (Run.send_wk h d τ pv r a)
  | _, _, .declMem R _ init _ _, _, h, d, τ => WkRel.of_top (Run.declMem_wk h d τ R init)
  | _, _, .rebindMem i r, _, h, d, τ => WkRel.of_eq (Run.rebindMem_wk h d τ i r)
  | _, _, .assignFromMem l q, _, h, d, τ => WkRel.of_eq (Run.assignFromMem_wk h d τ l q)
  | _, _, .assignMem l r, _, h, d, τ => WkRel.of_eq (Run.assignMem_wk h d τ l r)
  | _, _, .delete l, _, h, d, τ => WkRel.of_eq (Run.delete_wk h d τ l)
  | _, _, .deleteMem q hq, _, h, d, τ => WkRel.of_eq (Run.deleteMem_wk h d τ q)
  | _, _, .assignNew l n _, _, h, d, τ => WkRel.of_eq (Run.assignNew_wk h d τ l n)
  | _, _, .require c, _, h, d, τ => WkRel.of_eq (guardOk_wk h d τ c)
  | _, _, .assert c, _, h, d, τ => WkRel.of_eq (assertOk_wk h d τ c)
  | _, _, .revert, _, h, d, τ => rfl
  | _, _, .ite c thn els, _, h, d, τ => by
    show WkRel h _ (Run.ite c thn.ext thn.runR els.ext els.runR τ)
      (Run.ite (c.wk h) (thn.wk h).2.2.ext (thn.wk h).2.2.runR (els.wk h).2.2.ext
        (els.wk h).2.2.runR (τ.lift h d))
    unfold Run.ite
    rw [Val.eval_wk]
    refine WkRel.bind_same _ fun v => ?_
    rcases v with _ | (_ | _)
    · rfl
    · exact WkRel.drop (Prog.wk_over els h) (Prog.run_wk els h d τ)
    · exact WkRel.drop (Prog.wk_over thn h) (Prog.run_wk thn h d τ)
  | _, _, .call f args ret body, _, h, d, τ => by
    show WkRel (ret.wk h).2.1 (Env.off h d) (Run.call args ret body.ext body.runR τ)
      (Run.call (args.wk h) (ret.wk h).2.2 body.ext body.runR (τ.lift h d))
    unfold Run.call
    rw [Args.eval_wk, State.glob_lift, CallRet.enter_wk]
    refine WkRel.bind_same _ fun a => WkRel.bind_same _ fun ⟨g, r⟩ => WkRel.bind_same _ fun υ => ?_
    obtain ⟨d', hd', he⟩ := CallRet.leave_wk h τ.env d ret (Env.take _ (Env.drop body.ext υ.env))
    refine ⟨d', hd', ?_⟩
    show υ.withEnv ((ret.wk h).2.2.leave (Env.put h τ.env d) _) = _
    rw [he]; rfl
  | _, _, .tryCall call rets ok err code pnc other, _, h, d, τ => by
    show WkRel h (Env.off h d)
      (Run.tryCall call rets ok.ext ok.runR err.ext err.runR code pnc.ext pnc.runR other.ext
        other.runR τ)
      (Run.tryCall (call.wk h) rets (ok.wk (Thin.keepAll _ h)).2.2.ext
        (ok.wk (Thin.keepAll _ h)).2.2.runR (err.wk h).2.2.ext (err.wk h).2.2.runR code
        (pnc.wk (Thin.keepAll _ h)).2.2.ext (pnc.wk (Thin.keepAll _ h)).2.2.runR
        (other.wk h).2.2.ext (other.wk h).2.2.runR (τ.lift h d))
    unfold Run.tryCall
    rw [ExtCall.key_wk]
    refine WkRel.bind_same _ fun k => ?_
    rw [show (τ.lift h d).tx = τ.tx from rfl]
    cases Semantics.lookupBy k τ.tx.ext with
    | none => rfl
    | some o =>
      cases o with
      | ok vs =>
        refine WkRel.bind_same _ fun ⟨r, _⟩ => ?_
        have e : (τ.lift h d).withEnv (Env.append _ r (τ.lift h d).env) =
            (τ.withEnv (Env.append _ r τ.env)).lift (Thin.keepAll _ h) (Env.append _ r d) := by
          simp only [State.lift, State.withEnv, Env.put_keepAll]
        dsimp only
        rw [e]
        have := WkRel.drop (Thin.Over.trans (Thin.Over.append h _) (Prog.wk_over ok _))
          (Prog.run_wk ok (Thin.keepAll _ h) (Env.append _ r d) (τ.withEnv (Env.append _ r τ.env)))
        rwa [Env.off_keepAll] at this
      | error => exact WkRel.drop (Prog.wk_over err h) (Prog.run_wk err h d τ)
      | panic c =>
        refine WkRel.bind_same _ fun r => ?_
        have e : (τ.lift h d).withEnv (Env.append _ r (τ.lift h d).env) =
            (τ.withEnv (Env.append _ r τ.env)).lift (Thin.keepAll _ h) (Env.append _ r d) := by
          simp only [State.lift, State.withEnv, Env.put_keepAll]
        rw [e]
        have := WkRel.drop (Thin.Over.trans (Thin.Over.append h _) (Prog.wk_over pnc _))
          (Prog.run_wk pnc (Thin.keepAll _ h) (Env.append _ r d) (τ.withEnv (Env.append _ r τ.env)))
        rwa [Env.off_keepAll] at this
      | other => exact WkRel.drop (Prog.wk_over other h) (Prog.run_wk other h d τ)
  | _, _, .loop a c body, _, h, d, τ => by
    apply WkRel.of_eq
    show Loop.run (fun τ' => (Prog.run τ' (body.wk h).2.2).map (State.drop (body.wk h).2.2.ext))
        (fun τ' => (c.wk h).eval τ') (τ.lift h d) =
      lifted h d (Loop.run (fun τ' => (Prog.run τ' body).map (State.drop body.ext))
        (fun τ' => c.eval τ') τ)
    exact Loop.run_map (State.lift h d) (fun a => Val.eval_wk h d a c)
      (fun a => WkRel.eq_lifted (WkRel.drop (Prog.wk_over body h) (Prog.run_wk body h d a))) τ
  | _, _, .block body, _, h, d, τ => WkRel.drop (Prog.wk_over body h) (Prog.run_wk body h d τ)

/-- **A weakened sequence runs as the sequence.** -/
theorem Prog.run_wk : {Γ Γ' : Ctx} → (P : Prog C Γ Γ') → ∀ {Δ : Ctx} (h : Thin Γ Δ)
    (d : Env C Δ) (τ : State C Γ),
    WkRel (P.wk h).2.1 (Env.off h d) (P.run τ) ((P.wk h).2.2.run (τ.lift h d))
  | _, _, .nil, _, h, d, τ => ⟨d, rfl, rfl⟩
  | _, _, .cons s P, _, h, d, τ => by
    show WkRel (P.wk (s.wk h).2.1).2.1 _ (Prog.run τ (.cons s P))
      (Prog.run (τ.lift h d) (.cons (s.wk h).2.2 (P.wk (s.wk h).2.1).2.2))
    rw [Prog.run_cons, Prog.run_cons]
    exact WkRel.bind (Stmt.run_wk s h d τ) fun τ' d' hd' => hd' ▸ Prog.run_wk P _ d' τ'

end

end Solidity.Core
