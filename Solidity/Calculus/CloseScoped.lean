import Solidity.Calculus.NFmlClose
import Solidity.Calculus.SeqRewrite

/-!
# `sol_close` on a scoped leaf

`sol_symex` on a scoped goal (`⊨ dl!{ … }` under `open scoped Solidity.Scoped`)
leaves leaves `Valid ψ`, `ψ : Fml C []` with no modality.  `sol_close`,
`sol_close_mt` and `sol_spec_close` close them here, on the scoped formula,
by the elaborators below, which read it with `close_rw_s`
(`Calculus/NFmlClose.lean` declares the syntax and the simp sets).

**The leaf as the closer reads it.**  `holds` asks an update's rest of every
typed state that erases to where the update ends, with a heap typing that
extends the one before (`Calculus/Logic.lean`).  Read as it stands, each
update leaves a quantifier over typed states and an equation on their
erasure, which `simp` can only use in context: three times the work of the
erased leaf.  `sol_close_unwrap` therefore first takes the leaf to
`holdsE`, what it says of the erased state (`valid_of_holdsE`,
`holds_of_holdsE`): an update's rest is read where the update ends, a
hidden binder over the erased values of its type, a negation and a
precondition only of a first-order formula (`fo`, where the two readings
agree, `holds_iff_holdsE`).  This is one way, as the erased leaf was
(`Fml.posB`), and as strong: the binders still range over the values of
their types where the type is primitive (decision 82): a parameter
(`∀ uint a`) and a hidden binder of a value type (`LTy.forallE`) range over
`PrimTy.Denote`, a `uint` over `[0, 2²⁵⁶)` (`forall_uint`).

**The set** states lemmas about `Calculus/Logic.lean`'s readings only
(`Tm.eval`, `Tm.denote`, `Upd.apply`, `UpdElem.write`, `Rhs.eval`) and the
erased state's operations (`EState.get`, `push`, `setLocal`, `withGlob`,
`glob`, `drop`, `thin`, `anon`), never its fields, so that the state can
change underneath (W9.6) without touching the tactic.  A term is read
constructor by constructor, as `close_rw` reads the closer's term (each
equation follows from the symbol's, `Calculus/CloseLemmas.lean`); the
locals sit in a stack of `push`es, which `setLocal`, `drop` and `thin`
reach by position.  What the interpreter knows is `close_rw`'s, shared.
-/

namespace Solidity

open Semantics SemanticsProperties

variable {C : Contract}

/-- A local of the erased state, by its position. -/
def EState.get {Γ : Ctx} {t : LTy} (σ : EState C Γ) (i : Idx Γ t) : t.Denote C := Env.get i σ.env

/-- A `Res` of an optional value: an unset local reverts. -/
def Close.optRes {α : Type} : Option α → Res α
  | some a => .ok a
  | none => .error .revert

namespace CloseS

/-! ## The erased state's operations

A leaf's state is the typed state's erasure with what its updates did: a
stack of `push`es over `withGlob`, which `setLocal`, `drop` and `thin`
reach by position. -/

section EStateAPI

variable {Γ : Ctx} {t t' : LTy}

theorem get_push_here (σ : EState C Γ) (v : t.Denote C) : (σ.push v).get .here = v := rfl
theorem get_push_there (σ : EState C Γ) (v : t.Denote C) (i : Idx Γ t') :
    (σ.push v).get (.there i) = σ.get i := rfl
theorem glob_push (σ : EState C Γ) (v : t.Denote C) : (σ.push v).glob = σ.glob := rfl
theorem glob_withGlob (σ : EState C Γ) (g : Semantics.State) :
    (σ.withGlob g).glob = { g with env := [] } := rfl
theorem glob_env (σ : EState C Γ) : σ.glob.env = [] := rfl
theorem withGlob_push (σ : EState C Γ) (v : t.Denote C) (g : Semantics.State) :
    (σ.push v).withGlob g = (σ.withGlob g).push v := rfl
theorem withGlob_withGlob (σ : EState C Γ) (g g' : Semantics.State) :
    (σ.withGlob g).withGlob g' = σ.withGlob g' := rfl
theorem setLocal_push_here (σ : EState C Γ) (w v : t.Denote C) :
    (σ.push w).setLocal .here v = σ.push v := rfl
theorem setLocal_push_there (σ : EState C Γ) (w : t.Denote C) (i : Idx Γ t') (v : t'.Denote C) :
    (σ.push w).setLocal (.there i) v = (σ.setLocal i v).push w := rfl
theorem drop_refl (σ : EState C Γ) : σ.drop .refl = σ := rfl
theorem drop_push {Δ : Ctx} (h : Ext Γ Δ) (σ : EState C Δ) (v : t.Denote C) :
    (σ.push v).drop (.push h) = σ.drop h := rfl
theorem thin_refl (σ : EState C Γ) : σ.thin .refl = σ := rfl
theorem thin_keep {Δ : Ctx} (h : Thin Γ Δ) (σ : EState C Δ) (v : t.Denote C) :
    (σ.push v).thin (.keep h) = (σ.thin h).push v := rfl
theorem thin_drop {Δ : Ctx} (h : Thin Γ Δ) (σ : EState C Δ) (v : t.Denote C) :
    (σ.push v).thin (.drop h) = σ.thin h := rfl
theorem anon_nil (σ : EState C Γ) (b : (x : (t : LTy) × Idx Γ t) → x.1.Denote C) :
    σ.anon [] b = σ := rfl
theorem anon_cons (σ : EState C Γ) (x : (t : LTy) × Idx Γ t) (xs : List ((t : LTy) × Idx Γ t))
    (b : (x : (t : LTy) × Idx Γ t) → x.1.Denote C) :
    σ.anon (x :: xs) b = (σ.setLocal x.2 (b x)).anon xs b := rfl

theorem optRes_some {α : Type} (a : α) : Close.optRes (some a) = .ok a := rfl
theorem optRes_none {α : Type} : Close.optRes (none : Option α) = .error .revert := rfl

/-- The typed state's erasure after a loop body's `{anon(xs)}`. -/
theorem anon_erase (σ : State C Γ) (xs : List ((t : LTy) × Idx Γ t))
    (b : (x : (t : LTy) × Idx Γ t) → x.1.TDenote C σ.H) :
    (σ.anon xs b).erase = σ.erase.anon xs fun x => LTy.TDenote.erase x.1 (b x) := by
  have key : ∀ (ys : List ((t : LTy) × Idx Γ t)) (e : TEnv C σ.H Γ),
      (σ.withEnv (ys.foldl (fun e x => TEnv.set x.2 (b x) e) e)).erase =
        ys.foldl (fun τ x => τ.setLocal x.2 (LTy.TDenote.erase x.1 (b x))) (σ.withEnv e).erase := by
    intro ys
    induction ys with
    | nil => intro e; rfl
    | cons x ys ih =>
      intro e
      rw [List.foldl_cons, List.foldl_cons, ih]
      exact congrArg (fun τ => List.foldl _ τ ys) (State.setLocal_erase (σ.withEnv e) x.2 (b x))
  exact key xs σ.env

end EStateAPI

/-! ## Terms, one constructor at a time

Each as `close_rw`'s equation for the closer's term (`Calculus/NFmlClose.lean`),
a local read by its position, a symbol on the global part (`EState.glob`). -/

section Terms

variable {Γ : Ctx} (σ : EState C Γ)

theorem eval_pvV {p : PrimTy} (i : Idx Γ (.val p)) :
    (Tm.pvV i : Tm C Γ .val).eval σ = .ok (σ.get i) :=
  rfl
theorem eval_pvP {R : RefTy} (i : Idx Γ (.alias R)) :
    (Tm.pvP i : Tm C Γ .path).eval σ = Close.optRes (σ.get i) := by
  simp only [Tm.eval, aliasPath, EState.get]
  split <;> rename_i h <;> simp only [h] <;> rfl
theorem eval_pvS (i : Idx Γ .old) :
    (Tm.pvS i : Tm C Γ .st).eval σ = .ok { σ.glob with storage := σ.get i } := rfl
theorem eval_pvI {R : RefTy} (i : Idx Γ (.mem R)) :
    (Tm.pvI i : Tm C Γ .ident).eval σ = Close.optRes (σ.get i) := by
  simp only [Tm.eval, memRef, EState.get]
  split <;> rename_i h <;> simp only [h] <;> rfl
theorem eval_netOf (i : Idx Γ .oldNet) (a : Tm C Γ .val) : (Tm.netOf i a).eval σ =
    a.eval σ >>= Value.asInt >>= fun n => .ok (.int ((lookupBy n (σ.get i)).getD 0)) := by
  simp only [Tm.eval, bind, Except.bind, EState.get]
  cases a.eval σ <;> rfl

theorem eval_lit (v : Value) : (Tm.app0 (.lit v) : Tm C Γ .val).eval σ = .ok v := rfl
theorem eval_env (k : EnvKey) :
    (Tm.app0 (.env k) : Tm C Γ .val).eval σ = .ok (.int (σ.glob.envVal k)) := rfl
theorem eval_root (r : Name) : (Tm.app0 (.root r) : Tm C Γ .path).eval σ = .ok (r, []) := rfl
theorem eval_storage : (Tm.app0 .storage : Tm C Γ .st).eval σ = .ok σ.glob := rfl
theorem eval_memory : (Tm.app0 .memory : Tm C Γ .mem).eval σ = .ok σ.glob := rfl
theorem eval_mtSt (vs : List (Name × Ty)) : (Tm.app0 (.mtSt vs) : Tm C Γ .st).eval σ =
    .ok { σ.glob with storage := vs.map fun (n, T) => (n, defaultForTy T) } := rfl

theorem eval_unop (op : UnOp) (p : PrimTy) (h : (Op1.unop op p).named = false) (a : Tm C Γ .val) :
    (Tm.app1 (.unop op p) h a).eval σ = a.eval σ >>= fun x => applyUnOp op x >>= unopCheck op p :=
  rfl
theorem eval_net (h : Op1.net.named = false) (a : Tm C Γ .val) : (Tm.app1 .net h a).eval σ =
    a.eval σ >>= Value.asInt >>= fun n => .ok (.int (σ.glob.getNet n)) :=
  Close.Op1.eval_net _ _
theorem eval_field (f : Name) (h : (Op1.field f).named = false) (p : Tm C Γ .path) :
    (Tm.app1 (.field f) h p).eval σ = p.eval σ >>= fun rs => .ok (rs.1, rs.2 ++ [.field f]) := rfl
theorem eval_next (h : Op1.next.named = false) (p : Tm C Γ .path) : (Tm.app1 .next h p).eval σ =
    p.eval σ >>= fun rs => σ.glob.findStorage rs.1 rs.2 >>= Close.pastEnd rs :=
  Close.Op1.eval_next _ _
theorem eval_sval (h : Op1.sval.named = false) (t : Tm C Γ .val) :
    (Tm.app1 .sval h t).eval σ = t.eval σ >>= fun v => .ok v.toSVal := rfl
theorem eval_alloc (R : RefTy) (h : (Op1.alloc R).named = false) (m : Tm C Γ .mem) :
    (Tm.app1 (.alloc R) h m).eval σ = m.eval σ >>= fun τ => allocDefault τ R >>= fun r => .ok r.2 :=
  rfl
theorem eval_mfield (f : Name) (h : (Op1.mfield f).named = false) (i : Tm C Γ .ident) :
    (Tm.app1 (.mfield f) h i).eval σ = i.eval σ >>= fun id => .ok (.memoryField id f) := rfl
theorem eval_addM (R : RefTy) (h : (Op1.addM R).named = false) (m : Tm C Γ .mem) :
    (Tm.app1 (.addM R) h m).eval σ = m.eval σ >>= fun τ => allocDefault τ R >>= fun r => .ok r.1 :=
  rfl
theorem eval_mval (h : Op1.mval.named = false) (t : Tm C Γ .val) :
    (Tm.app1 .mval h t).eval σ = t.eval σ >>= fun v => .ok v.toMVal := rfl
theorem eval_ref (h : Op1.ref.named = false) (i : Tm C Γ .ident) :
    (Tm.app1 .ref h i).eval σ = i.eval σ >>= fun id => .ok (.ref id) := rfl

theorem eval_binop (op : BinOp) (p : PrimTy) (a b : Tm C Γ .val) :
    (Tm.app2 (.binop op p) a b).eval σ = a.eval σ >>= fun x => evalBinop op p x (b.eval σ) := rfl
theorem eval_find (s : Tm C Γ .st) (p : Tm C Γ .path) : (Tm.app2 .find s p).eval σ =
    s.eval σ >>= fun τ => p.eval σ >>= fun rs => τ.findStorage rs.1 rs.2 >>= SVal.asValue := rfl
theorem eval_len (s : Tm C Γ .st) (p : Tm C Γ .path) : (Tm.app2 .len s p).eval σ =
    s.eval σ >>= fun τ => p.eval σ >>= fun rs => τ.findStorage rs.1 rs.2 >>= Close.arrLen :=
  Close.Op2.eval_len _ _ _
theorem eval_read (m : Tm C Γ .mem) (a : Tm C Γ .addr) : (Tm.app2 .read m a).eval σ =
    m.eval σ >>= fun τ => a.eval σ >>= fun addr => Close.readVal τ addr := rfl
theorem eval_at (p : Tm C Γ .path) (i : Tm C Γ .val) : (Tm.app2 .at p i).eval σ =
    p.eval σ >>= fun rs => i.eval σ >>= Value.asInt >>= fun k =>
      σ.glob.checkIndex rs.1 rs.2 k >>= fun _ => .ok (rs.1, rs.2 ++ [.at k]) :=
  Close.Op2.eval_at _ _ _
theorem eval_delAt (s : Tm C Γ .st) (p : Tm C Γ .path) : (Tm.app2 .delAt s p).eval σ =
    s.eval σ >>= fun τ => p.eval σ >>= fun rs => τ.findStorage rs.1 rs.2 >>= fun cur =>
      τ.saveStorage rs.1 rs.2 cur.defaultOf := rfl
theorem eval_pushSlot (E : Ty) (s : Tm C Γ .st) (p : Tm C Γ .path) :
    (Tm.app2 (.pushSlot E) s p).eval σ = s.eval σ >>= fun τ => p.eval σ >>= fun rs =>
      τ.findStorage rs.1 rs.2 >>= Close.pushOn τ E rs.1 rs.2 pure :=
  Close.Op2.eval_pushSlot _ _ _ _
theorem eval_pop (s : Tm C Γ .st) (p : Tm C Γ .path) : (Tm.app2 .pop s p).eval σ =
    s.eval σ >>= fun τ => p.eval σ >>= fun rs =>
      τ.findStorage rs.1 rs.2 >>= Close.popOn τ false rs.1 rs.2 :=
  Close.Op2.eval_pop _ _ _
theorem eval_shrink (s : Tm C Γ .st) (p : Tm C Γ .path) : (Tm.app2 .shrink s p).eval σ =
    s.eval σ >>= fun τ => p.eval σ >>= fun rs =>
      τ.findStorage rs.1 rs.2 >>= Close.popOn τ true rs.1 rs.2 :=
  Close.Op2.eval_shrink _ _ _
theorem eval_sfind (s : Tm C Γ .st) (p : Tm C Γ .path) : (Tm.app2 .sfind s p).eval σ =
    s.eval σ >>= fun τ => p.eval σ >>= fun rs => τ.findStorage rs.1 rs.2 := rfl
theorem eval_copyMem (m : Tm C Γ .mem) (i : Tm C Γ .ident) : (Tm.app2 .copyMem m i).eval σ =
    m.eval σ >>= fun τ => i.eval σ >>= fun id => copyMem τ (.ref id) := rfl
theorem eval_iread (m : Tm C Γ .mem) (a : Tm C Γ .addr) : (Tm.app2 .iread m a).eval σ =
    m.eval σ >>= fun τ => a.eval σ >>= fun addr => readAddr τ addr >>= MVal.asRef := rfl
theorem eval_copy (m : Tm C Γ .mem) (v : Tm C Γ .sv) : (Tm.app2 .copy m v).eval σ =
    v.eval σ >>= fun sv => m.eval σ >>= fun τ => copyStToM τ sv >>= fun r => r.2.asRef := rfl
theorem eval_mat (i : Tm C Γ .ident) (k : Tm C Γ .val) : (Tm.app2 .mat i k).eval σ =
    i.eval σ >>= fun id => k.eval σ >>= Value.asInt >>= fun j => .ok (.memoryIndex id j) :=
  Close.Op2.eval_mat _ _ _
theorem eval_copySt (m : Tm C Γ .mem) (v : Tm C Γ .sv) : (Tm.app2 .copySt m v).eval σ =
    v.eval σ >>= fun sv => m.eval σ >>= fun τ => copyStToM τ sv >>= fun r => .ok r.1 := rfl

theorem eval_ite (c a b : Tm C Γ .val) : (Tm.app3 .ite c a b).eval σ =
    c.eval σ >>= fun cv => pickBranch cv (a.eval σ) (b.eval σ) := rfl
theorem eval_save (s : Tm C Γ .st) (p : Tm C Γ .path) (h : Op1.sval.named = false)
    (t : Tm C Γ .val) : (Tm.app3 .save s p (.app1 .sval h t)).eval σ =
    t.eval σ >>= fun x => s.eval σ >>= fun τ => p.eval σ >>= fun rs =>
      τ.saveStorage rs.1 rs.2 x.toSVal :=
  Close.Op3.eval_save_val _ _ _ _
theorem eval_save_find (s s' : Tm C Γ .st) (p p' : Tm C Γ .path) :
    (Tm.app3 .save s p (.app2 .sfind s' p')).eval σ =
    (Tm.app2 .sfind s' p').eval σ >>= fun sv => s.eval σ >>= fun τ => p.eval σ >>= fun rs =>
      τ.findStorage rs.1 rs.2 >>= fun cur => τ.saveStorage rs.1 rs.2 (cur.overlay sv) :=
  Close.Op3.eval_save_find _ _ _ _ _
theorem eval_save_copyMem (s : Tm C Γ .st) (p : Tm C Γ .path) (m : Tm C Γ .mem)
    (i : Tm C Γ .ident) : (Tm.app3 .save s p (.app2 .copyMem m i)).eval σ =
    (Tm.app2 .copyMem m i).eval σ >>= fun sv => s.eval σ >>= fun τ => p.eval σ >>= fun rs =>
      τ.findStorage rs.1 rs.2 >>= fun cur => τ.saveStorage rs.1 rs.2 (cur.overlay sv) :=
  Close.Op3.eval_save_copyMem _ _ _ _ _
theorem eval_push (s : Tm C Γ .st) (p : Tm C Γ .path) (v : Tm C Γ .sv) :
    (Tm.app3 .push s p v).eval σ = s.eval σ >>= fun τ => p.eval σ >>= fun rs =>
      τ.findStorage rs.1 rs.2 >>=
        Close.pushOn τ .uint rs.1 rs.2 (fun _ => v.eval σ >>= fun sv => pure sv.strip) :=
  Close.Op3.eval_push _ _ _ _
theorem eval_write (m : Tm C Γ .mem) (a : Tm C Γ .addr) (v : Tm C Γ .mv) :
    (Tm.app3 .write m a v).eval σ =
    v.eval σ >>= fun mv => m.eval σ >>= fun τ => a.eval σ >>= fun addr => writeAddr τ mv addr :=
  rfl

theorem denote_lit (v : Value) : (Tm.app0 (.lit v) : Tm C Γ .val).denote σ = .prim v := rfl
theorem denote_env (k : EnvKey) :
    (Tm.app0 (.env k) : Tm C Γ .val).denote σ = .prim (.int (σ.glob.envVal k)) := rfl
theorem denote_pvV {p : PrimTy} (i : Idx Γ (.val p)) :
    (Tm.pvV i : Tm C Γ .val).denote σ = .prim (σ.get i) := rfl

end Terms

/-! ## Updates: right-hand sides read in the state before, written into the
state so far -/

section Updates

variable {Γ Δ : Ctx} (σ₀ : EState C Γ)

theorem rhs_val {p : PrimTy} (t : Tm C Γ .val) : (Rhs.val (p := p) t).eval σ₀ = t.eval σ₀ := rfl
theorem rhs_path {R : RefTy} (p : Tm C Γ .path) :
    (Rhs.path (R := R) p).eval σ₀ = p.eval σ₀ >>= fun r => .ok (some r) := rfl
theorem rhs_unset {R : RefTy} : (Rhs.unset (R := R) : Rhs C Γ _).eval σ₀ = .ok none := rfl
theorem rhs_mref {R : RefTy} (i : Tm C Γ .ident) :
    (Rhs.mref (R := R) i).eval σ₀ = i.eval σ₀ >>= fun id => .ok (some id) := rfl
theorem rhs_store (s : Tm C Γ .st) : (Rhs.store s).eval σ₀ = s.eval σ₀ >>= fun g => .ok g.storage :=
  rfl
theorem rhs_saveNet : (Rhs.saveNet : Rhs C Γ _).eval σ₀ = .ok σ₀.glob.net := rfl
theorem rhs_saveNetMt : (Rhs.saveNetMt : Rhs C Γ _).eval σ₀ = .ok [] := rfl

theorem write_local {t : LTy} (i : Idx Δ t) (r : Rhs C Γ t) (τ : EState C Δ) :
    (UpdElem.local i r).write σ₀ τ = r.eval σ₀ >>= fun v => .ok (τ.setLocal i v) := rfl
theorem write_storage (s : Tm C Γ .st) (τ : EState C Δ) :
    (UpdElem.storage s : UpdElem C Γ Δ).write σ₀ τ =
      s.eval σ₀ >>= fun g => .ok (τ.withGlob { τ.glob with storage := g.storage }) := rfl
theorem write_memory (m : Tm C Γ .mem) (τ : EState C Δ) :
    (UpdElem.memory m : UpdElem C Γ Δ).write σ₀ τ =
      m.eval σ₀ >>= fun μ => .ok (τ.withGlob { τ.glob with heap := μ.heap, nextId := μ.nextId }) :=
  rfl
theorem write_selfBalance (op : IntOp) (a : Tm C Γ .val) (τ : EState C Δ) :
    (UpdElem.selfBalance op a : UpdElem C Γ Δ).write σ₀ τ = a.eval σ₀ >>= Value.asInt >>= fun amt =>
      .ok (τ.withGlob { τ.glob with selfBalance := op.apply σ₀.glob.selfBalance amt }) := by
  simp only [UpdElem.write, bind, Except.bind]
  cases a.eval σ₀ <;> rfl
theorem write_net (r : Tm C Γ .val) (op : IntOp) (a : Tm C Γ .val) (τ : EState C Δ) :
    (UpdElem.net r op a : UpdElem C Γ Δ).write σ₀ τ =
      r.eval σ₀ >>= Value.asInt >>= fun addr => a.eval σ₀ >>= Value.asInt >>= fun amt =>
        .ok (τ.withGlob { τ.glob with
          net := setBy addr (op.apply (τ.glob.getNet addr) amt) τ.glob.net }) := by
  simp only [UpdElem.write, bind, Except.bind]
  cases r.eval σ₀ with
  | error => rfl
  | ok v =>
    cases v with
    | bool b => rfl
    | int addr =>
      cases a.eval σ₀ with
      | error => rfl
      | ok w => cases w <;> rfl
theorem write_pay (r a : Tm C Γ .val) (τ : EState C Δ) :
    (UpdElem.pay r a : UpdElem C Γ Δ).write σ₀ τ =
      r.eval σ₀ >>= Value.asInt >>= fun addr => a.eval σ₀ >>= Value.asInt >>= fun amt =>
        if amt < 0 then .error .revert
        else .ok (τ.withGlob { τ.glob with
          net := if addr = σ₀.glob.tx.selfAddress then τ.glob.net
            else setBy addr (τ.glob.getNet addr - amt) τ.glob.net }) := by
  simp only [UpdElem.write, bind, Except.bind]
  cases r.eval σ₀ with
  | error => rfl
  | ok v =>
    cases v with
    | bool b => rfl
    | int addr =>
      cases a.eval σ₀ with
      | error => rfl
      | ok w => cases w <;> rfl
theorem write_netMt (r a : Tm C Γ .val) (τ : EState C Δ) :
    (UpdElem.netMt r a : UpdElem C Γ Δ).write σ₀ τ =
      r.eval σ₀ >>= Value.asInt >>= fun addr => a.eval σ₀ >>= Value.asInt >>= fun amt =>
        .ok (τ.withGlob { τ.glob with net := [(addr, amt)] }) := by
  simp only [UpdElem.write, bind, Except.bind]
  cases r.eval σ₀ with
  | error => rfl
  | ok v =>
    cases v with
    | bool b => rfl
    | int addr =>
      cases a.eval σ₀ with
      | error => rfl
      | ok w => cases w <;> rfl
theorem write_setBalance (a : Tm C Γ .val) (τ : EState C Δ) :
    (UpdElem.setBalance a : UpdElem C Γ Δ).write σ₀ τ = a.eval σ₀ >>= Value.asInt >>= fun amt =>
      .ok (τ.withGlob { τ.glob with selfBalance := amt }) := by
  simp only [UpdElem.write, bind, Except.bind]
  cases a.eval σ₀ <;> rfl

theorem apply_nil : (Upd.nil : Upd C Γ Γ).apply σ₀ = .ok σ₀ := rfl
theorem apply_snoc (U : Upd C Γ Δ) (e : UpdElem C Γ Δ) :
    (U.snoc e).apply σ₀ = U.apply σ₀ >>= fun τ => e.write σ₀ τ := rfl
theorem apply_decl {t : LTy} (U : Upd C Γ Δ) (x : Var) (r : Rhs C Γ t) :
    (U.decl x r).apply σ₀ = U.apply σ₀ >>= fun τ => r.eval σ₀ >>= fun v => .ok (τ.push v) := rfl
theorem apply_pop {Δ' : Ctx} (U : Upd C Γ Δ) (h : Ext Δ' Δ) :
    (U.pop h).apply σ₀ = U.apply σ₀ >>= fun τ => .ok (τ.drop h) := by
  simp only [Upd.apply, bind, Except.bind]
  cases U.apply σ₀ <;> rfl
theorem apply_drop {Δ' : Ctx} (U : Upd C Γ Δ) (h : Thin Δ' Δ) :
    (U.drop h).apply σ₀ = U.apply σ₀ >>= fun τ => .ok (τ.thin h) := by
  simp only [Upd.apply, bind, Except.bind]
  cases U.apply σ₀ <;> rfl

end Updates

/-- A `uint` binder: an integer in range. -/
theorem forall_uint (P : PrimTy.uint.Denote → Prop) :
    (∀ v, P v) ↔ ∀ n : Int, (h₀ : 0 ≤ n) → (h₁ : n < uintBound) →
      P ⟨n, by simp only [PrimTy.inRange, decide_eq_true_eq]; exact ⟨h₀, h₁⟩⟩ :=
  ⟨fun h n _ _ => h _, fun h ⟨n, hn⟩ => by
    simp only [PrimTy.inRange, decide_eq_true_eq] at hn
    exact h n hn.1 hn.2⟩
theorem forall_int (P : PrimTy.int.Denote → Prop) :
    (∀ v, P v) ↔ ∀ n : Int, (h₀ : -intBound ≤ n) → (h₁ : n < intBound) →
      P ⟨n, by simp only [PrimTy.inRange, decide_eq_true_eq]; exact ⟨h₀, h₁⟩⟩ :=
  ⟨fun h n _ _ => h _, fun h ⟨n, hn⟩ => by
    simp only [PrimTy.inRange, decide_eq_true_eq] at hn
    exact h n hn.1 hn.2⟩
theorem erase_uint (n : Int) (h : PrimTy.uint.inRange n = true) :
    PrimTy.erase (p := .uint) ⟨n, h⟩ = .int n := rfl
theorem erase_int (n : Int) (h : PrimTy.int.inRange n = true) :
    PrimTy.erase (p := .int) ⟨n, h⟩ = .int n := rfl
theorem erase_bool (b : Bool) : PrimTy.erase (p := .bool) b = .bool b := rfl




/-! ## The leaf on the erased state -/

section Leaf

variable {Γ : Ctx}

/-- A formula with no update, hidden binder or modality (a `∀` allowed): it
reads the erasure only, so its two readings agree (`holds_iff_holdsE`). -/
def fo : {Γ : Ctx} → Fml C Γ → Bool
  | _, .tt | _, .eq .. | _, .defined _ => true
  | _, .not φ | _, .all _ _ φ => fo φ
  | _, .and φ ψ | _, .imp φ ψ => fo φ && fo ψ
  | _, _ => false

/-- A binder over the values of `t`: a primitive type's typed values, the
erased values of any other. -/
def _root_.Solidity.LTy.forallE (t : LTy) (P : t.Denote C → Prop) : Prop :=
  match t, P with
  | .val p, P => ∀ v : p.Denote, P (PrimTy.erase v)
  | .alias _, P | .mem _, P | .old, P | .oldNet, P => ∀ u, P u

/-- What `φ` says of the erased state `τ`, as `sol_close` reads a leaf. -/
def holdsE : {Γ : Ctx} → EState C Γ → Fml C Γ → Prop
  | _, _, .tt => True
  | _, τ, .eq a b => Theory.StValue.Equiv (a.denote τ) (b.denote τ)
  | _, τ, .defined t => ∃ x, t.eval τ = .ok x
  | _, τ, .not φ => fo φ = true ∧ ¬ holdsE τ φ
  | _, τ, .and φ ψ => holdsE τ φ ∧ holdsE τ ψ
  | _, τ, .imp φ ψ => fo φ = true ∧ (holdsE τ φ → holdsE τ ψ)
  | _, τ, .upd m U φ => m.wp (U.apply τ) (holdsE · φ)
  | _, _, .modal .. => False
  | _, τ, .havoc φ => ∀ (st : Storage C) nt, holdsE (τ.withGlob (τ.glob.havoc st.erase nt)) φ
  | _, τ, .all _ p φ => ∀ v : p.Denote, holdsE (τ.push (t := .val p) (PrimTy.erase v)) φ
  | _, τ, .bind _ _ t φ => t.forallE fun u => holdsE (τ.push u) φ
  | _, τ, .anon xs φ => ∀ b, holdsE (τ.anon xs b) φ

/-- A first-order formula reads as much on the erasure as on the typed state:
what a negation or a precondition may hold. -/
theorem holds_iff_holdsE : {Γ : Ctx} → {φ : Fml C Γ} → fo φ = true → (σ : State C Γ) →
    (holds σ φ ↔ holdsE σ.erase φ)
  | _, .tt, _, _ => Iff.rfl
  | _, .eq _ _, _, _ => Iff.rfl
  | _, .defined _, _, _ => Iff.rfl
  | _, .not φ, h, σ => by
    have h' : fo φ = true := h
    exact (not_congr (holds_iff_holdsE h' σ)).trans ⟨fun hn => ⟨h', hn⟩, fun hn => hn.2⟩
  | _, .and _ _, h, σ => by
    simp only [fo, Bool.and_eq_true] at h
    exact and_congr (holds_iff_holdsE h.1 σ) (holds_iff_holdsE h.2 σ)
  | _, .imp _ _, h, σ => by
    simp only [fo, Bool.and_eq_true] at h
    exact (imp_congr (holds_iff_holdsE h.1 σ) (holds_iff_holdsE h.2 σ)).trans
      ⟨fun hi => ⟨h.1, hi⟩, fun hi => hi.2⟩
  | _, .all _ p φ, h, σ => by
    have h' : fo φ = true := h
    exact forall_congr' fun v => holds_iff_holdsE h' (σ.push (t := .val p) v)
  | _, .upd .., h, _ | _, .modal .., h, _ | _, .havoc _, h, _ | _, .bind .., h, _
  | _, .anon .., h, _ => by cases h

/-- **The leaf read on the erasure is sound**: what `holdsE` says of a
typed state's erasure holds there. -/
theorem holds_of_holdsE : {Γ : Ctx} → (φ : Fml C Γ) → (σ : State C Γ) →
    holdsE σ.erase φ → holds σ φ
  | _, .tt, _, h | _, .eq _ _, _, h | _, .defined _, _, h => h
  | _, .not φ, σ, h => fun hp => h.2 ((holds_iff_holdsE h.1 σ).1 hp)
  | _, .and φ ψ, σ, h => ⟨holds_of_holdsE φ σ h.1, holds_of_holdsE ψ σ h.2⟩
  | _, .imp φ ψ, σ, h => fun hp => holds_of_holdsE ψ σ (h.2 ((holds_iff_holdsE h.1 σ).1 hp))
  | _, .upd m U φ, σ, h => by
    simp only [holds]
    simp only [holdsE] at h
    cases hU : U.apply σ.erase with
    | error e => rw [hU] at h; exact h
    | ok τ =>
      rw [hU] at h
      exact fun σ' he _ => holds_of_holdsE φ σ' (he ▸ h)
  | _, .modal .., _, h => h.elim
  | _, .havoc φ, σ, h => fun st nt => holds_of_holdsE φ (σ.havoc st nt) (h st nt)
  | _, .all _ p φ, σ, h => fun v => holds_of_holdsE φ (σ.push (t := .val p) v) (h v)
  | _, .bind m _ t φ, σ, h => by
    show m.forallB _
    intro v
    refine holds_of_holdsE φ (σ.push v) ?_
    rw [State.push_erase]
    cases t with
    | val p => exact h v
    | «alias» _ | mem _ | old | oldNet => exact h _
  | _, .anon xs φ, σ, h => fun b => holds_of_holdsE φ (σ.anon xs b) (by
      rw [anon_erase]; exact h _)

/-- A scoped leaf is valid where it holds of every typed state's erasure. -/
theorem valid_of_holdsE {φ : Fml C []} (h : ∀ σ : State C [], holdsE σ.erase φ) : Valid φ :=
  fun σ => holds_of_holdsE φ σ (h σ)

theorem holdsE_tt (τ : EState C Γ) : holdsE τ (.tt : Fml C Γ) ↔ True := Iff.rfl
theorem holdsE_not (τ : EState C Γ) (φ : Fml C Γ) :
    holdsE τ (.not φ) ↔ fo φ = true ∧ ¬ holdsE τ φ := Iff.rfl
theorem holdsE_and (τ : EState C Γ) (φ ψ : Fml C Γ) :
    holdsE τ (.and φ ψ) ↔ holdsE τ φ ∧ holdsE τ ψ := Iff.rfl
theorem holdsE_imp (τ : EState C Γ) (φ ψ : Fml C Γ) :
    holdsE τ (.imp φ ψ) ↔ fo φ = true ∧ (holdsE τ φ → holdsE τ ψ) := Iff.rfl
theorem holdsE_eq (τ : EState C Γ) (a b : Tm C Γ .val) :
    holdsE τ (.eq a b) ↔ Theory.StValue.Equiv (a.denote τ) (b.denote τ) := Iff.rfl
theorem holdsE_defined (τ : EState C Γ) (t : Tm C Γ .val) : holdsE τ (.defined t) ↔
    Modality.diamond.wp (t.eval τ) fun _ => True := by
  simp only [holdsE]
  cases t.eval τ <;> simp [Modality.wp, Modality.onHalt]
theorem holdsE_eqD (τ : EState C Γ) (a b : Tm C Γ .val) : holdsE τ (Fml.eqD a b) ↔
    Modality.diamond.wp (a.eval τ) fun x => Modality.diamond.wp (b.eval τ) fun y => x = y := by
  have key : holdsE τ (Fml.eqD a b) ↔ ∃ x, a.eval τ = .ok x ∧ b.eval τ = .ok x := by
    constructor
    · rintro ⟨⟨x, hx⟩, ⟨y, hy⟩, he⟩
      have he' : Theory.StValue.Equiv (.prim x) (.prim y) := by
        rw [← Tm.denote_eval τ a x hx, ← Tm.denote_eval τ b y hy]; exact he
      rw [Theory.StValue.Equiv.prim_iff] at he'
      cases he'
      exact ⟨x, hx, hy⟩
    · rintro ⟨x, hx, hy⟩
      refine ⟨⟨x, hx⟩, ⟨x, hy⟩, ?_⟩
      show Theory.StValue.Equiv (a.denote τ) (b.denote τ)
      rw [Tm.denote_eval τ a x hx, Tm.denote_eval τ b x hy]
      exact Theory.StValue.Equiv.refl _
  rw [key]
  cases a.eval τ <;> cases b.eval τ <;>
    simp only [Modality.wp, Modality.onHalt, Except.ok.injEq, reduceCtorEq, false_and, and_false,
      and_self, exists_false, exists_eq_left', eq_comm]
theorem holdsE_upd {Δ : Ctx} (τ : EState C Γ) (m : Modality) (U : Upd C Γ Δ) (φ : Fml C Δ) :
    holdsE τ (.upd m U φ) ↔ m.wp (U.apply τ) (holdsE · φ) := Iff.rfl
theorem holdsE_havoc (τ : EState C Γ) (φ : Fml C Γ) : holdsE τ (.havoc φ) ↔
    ∀ (st : Storage C) nt, holdsE (τ.withGlob (τ.glob.havoc st.erase nt)) φ := Iff.rfl
theorem holdsE_all (τ : EState C Γ) (x : Var) (p : PrimTy) (φ : Fml C (.val p :: Γ)) :
    holdsE τ (.all x p φ) ↔ ∀ v : p.Denote, holdsE (τ.push (t := .val p) (PrimTy.erase v)) φ :=
  Iff.rfl
theorem holdsE_bind (τ : EState C Γ) (m : Modality) (x : Var) (t : LTy) (φ : Fml C (t :: Γ)) :
    holdsE τ (.bind m x t φ) ↔ t.forallE fun u => holdsE (τ.push u) φ := Iff.rfl
theorem holdsE_anon (τ : EState C Γ) (xs : List ((t : LTy) × Idx Γ t)) (φ : Fml C Γ) :
    holdsE τ (.anon xs φ) ↔ ∀ b, holdsE (τ.anon xs b) φ := Iff.rfl

theorem forallE_val (p : PrimTy) (P : Value → Prop) :
    LTy.forallE (C := C) (.val p) P ↔ ∀ v : p.Denote, P (PrimTy.erase v) := Iff.rfl
theorem forallE_alias (R : RefTy) (P : Option (Name × List Seg) → Prop) :
    LTy.forallE (C := C) (.alias R) P ↔ ∀ u, P u := Iff.rfl
theorem forallE_mem (R : RefTy) (P : Option Nat → Prop) :
    LTy.forallE (C := C) (.mem R) P ↔ ∀ u, P u := Iff.rfl
theorem forallE_old (P : List (Name × Semantics.SVal) → Prop) :
    LTy.forallE (C := C) .old P ↔ ∀ u, P u := Iff.rfl
theorem forallE_oldNet (P : List (Int × Int) → Prop) :
    LTy.forallE (C := C) .oldNet P ↔ ∀ u, P u := Iff.rfl

theorem fo_tt : fo (.tt : Fml C Γ) = true := rfl
theorem fo_eq (a b : Tm C Γ .val) : fo (.eq a b) = true := rfl
theorem fo_defined (t : Tm C Γ .val) : fo (.defined t) = true := rfl
theorem fo_not (φ : Fml C Γ) : fo (.not φ) = fo φ := rfl
theorem fo_and (φ ψ : Fml C Γ) : fo (.and φ ψ) = (fo φ && fo ψ) := rfl
theorem fo_imp (φ ψ : Fml C Γ) : fo (.imp φ ψ) = (fo φ && fo ψ) := rfl
theorem fo_all (x : Var) (p : PrimTy) (φ : Fml C (.val p :: Γ)) : fo (.all x p φ) = fo φ := rfl

end Leaf

end CloseS


/-! ## The set -/

attribute [close_rw_s high] CloseS.holdsE_eqD

attribute [close_rw_s]
  -- formulas
  CloseS.holdsE_tt CloseS.holdsE_not CloseS.holdsE_and CloseS.holdsE_imp CloseS.holdsE_eq
  CloseS.holdsE_defined CloseS.holdsE_upd CloseS.holdsE_havoc CloseS.holdsE_all
  CloseS.holdsE_bind CloseS.holdsE_anon CloseS.forallE_val CloseS.forallE_alias
  CloseS.forallE_mem CloseS.forallE_old CloseS.forallE_oldNet
  CloseS.fo_tt CloseS.fo_eq CloseS.fo_defined CloseS.fo_not CloseS.fo_and CloseS.fo_imp
  CloseS.fo_all
  CloseS.forall_uint CloseS.forall_int CloseS.erase_uint CloseS.erase_int CloseS.erase_bool
  CloseS.denote_lit CloseS.denote_pvV CloseS.denote_env Close.equiv_prim_left_iff
  Theory.StValue.Equiv.prim_iff Theory.StValue.prim.injEq
  -- the erased state
  CloseS.get_push_here CloseS.get_push_there CloseS.glob_push CloseS.glob_withGlob CloseS.glob_env
  CloseS.withGlob_push CloseS.withGlob_withGlob CloseS.setLocal_push_here CloseS.setLocal_push_there
  CloseS.drop_refl CloseS.drop_push CloseS.thin_refl CloseS.thin_keep CloseS.thin_drop
  CloseS.anon_nil CloseS.anon_cons CloseS.optRes_some CloseS.optRes_none
  -- updates
  CloseS.apply_nil CloseS.apply_snoc CloseS.apply_decl CloseS.apply_pop CloseS.apply_drop
  CloseS.write_local CloseS.write_storage CloseS.write_memory CloseS.write_selfBalance
  CloseS.write_net CloseS.write_pay CloseS.write_netMt CloseS.write_setBalance
  CloseS.rhs_val CloseS.rhs_path CloseS.rhs_unset CloseS.rhs_mref CloseS.rhs_store
  CloseS.rhs_saveNet CloseS.rhs_saveNetMt IntOp.apply
  -- terms
  CloseS.eval_pvV CloseS.eval_pvP CloseS.eval_pvS CloseS.eval_pvI CloseS.eval_netOf
  CloseS.eval_lit CloseS.eval_env CloseS.eval_root CloseS.eval_storage CloseS.eval_memory
  CloseS.eval_mtSt CloseS.eval_unop CloseS.eval_net CloseS.eval_field CloseS.eval_next
  CloseS.eval_sval CloseS.eval_alloc CloseS.eval_mfield CloseS.eval_addM CloseS.eval_mval
  CloseS.eval_ref CloseS.eval_binop CloseS.eval_find CloseS.eval_len CloseS.eval_read
  CloseS.eval_at CloseS.eval_delAt CloseS.eval_pushSlot CloseS.eval_pop CloseS.eval_shrink
  CloseS.eval_sfind CloseS.eval_copyMem CloseS.eval_iread CloseS.eval_copy CloseS.eval_mat
  CloseS.eval_copySt CloseS.eval_ite CloseS.eval_save CloseS.eval_save_find
  CloseS.eval_save_copyMem CloseS.eval_push CloseS.eval_write
  Semantics.State.envVal Semantics.State.getNet
  Close.idxOk_array Close.idxOk_map Close.pastEnd_array
  Close.forall_unit Close.exists_unit
  Close.find_overlay_fields Close.layAt_prim Close.fieldPath_nil Close.fieldPath_field
  Close.fieldPath_at
  -- operators
  Close.evalBinop_strict Close.evalBinop_and Close.evalBinop_or applyBinOp applyUnOp unopCheck
  Close.pickBranch_eq BinOp.retTy BinOp.isArith checkArith uintBound intBound
  Close.uintBitwise_ofNat Close.uintBitwise_ofNat_cast Close.uintBitwise_cast_ofNat
  uintBitwise_natCast Nat.reduceAnd Nat.reduceOr Nat.reduceXor
  -- runs
  Modality.wp_ok Modality.wp_pure Modality.wp_error Modality.wp_bind Modality.wp_ite
  Modality.wp_diamond Modality.onHalt_box Modality.onHalt_diamond
  Close.pure_eq_ok Res.ok_bind Res.error_bind Close.bind_ok_right bind_assoc
  Close.saveStorage_bind_restore Close.writeAddr_bind_restore
  -- values
  Close.asInt_eq_ok Close.asBool_eq_ok Close.asRef_eq_ok Close.toMVal_eq
  Close.toSVal_int Close.toSVal_bool Close.asValue_toSVal Close.asValue_toMVal Close.asValue_int
  Close.asValue_bool Close.mval_asValue_prim Close.mval_asValue_ref Close.mval_asRef_ref
  Close.defaultOf_int Close.defaultOf_bool Close.asInt_int Close.asBool_bool
  -- states
  Close.checkIndex_mk Close.findStorage_mk Close.getEnv_mk Close.readAddr_mk Close.readVal_mk
  Close.lookupBy_ite Close.lookupBy_setBy_int Semantics.State.pay Semantics.State.setNet
  Close.State.havoc_eq_mk
  -- paths, arrays, copies
  Close.diverge_cons' Close.not_diverge_nil_left Close.not_diverge_nil_right Close.prefix_nil
  Close.prefix_cons Close.prefix_cons_nil Close.after_nil Close.after_cons
  SemanticsProperties.SVal.find_nil
  List.nil_append List.cons_append List.append_nil List.foldl_cons List.foldl_nil
  Close.arrLen_array Close.arrLen_eq_ok Close.pushOn_array Close.popOn_push Close.popOn_push_keep
  Close.find_push_last
  Close.copyLeaf_prim Close.apart_field Close.apart_index Close.apart_field_index
  Close.apart_index_field
  -- logic
  Except.ok.injEq Option.some.injEq Option.map_some Option.map_none
  PrimVal.int.injEq PrimVal.bool.injEq
  Semantics.MVal.prim.injEq Semantics.MVal.ref.injEq Semantics.SVal.prim.injEq Prod.mk.injEq
  Seg.field.injEq Seg.at.injEq
  Int.ofNat.injEq
  forall_eq' forall_eq exists_eq_left' exists_eq_left exists_eq' exists_eq forall_exists_index
  and_imp
  true_and and_true and_self implies_true forall_const ne_eq not_false_eq_true not_true_eq_false
  true_or or_true or_false false_or not_and not_exists Classical.not_not true_implies
  false_implies decide_eq_true_eq decide_eq_false_iff_not
  Bool.and_true Bool.and_false Bool.true_and Bool.false_and Bool.or_true Bool.or_false
  Bool.true_or Bool.false_or Bool.not_true Bool.not_false Bool.not_not
  Bool.not_eq_true' Bool.not_eq_false' Bool.and_eq_true Bool.or_eq_true Bool.and_eq_false_iff
  Bool.or_eq_false_iff
  -- computation
  reduceCtorEq reduceIte reduceDIte String.reduceEq Nat.reduceEqDiff Nat.reducePow Int.reduceEq
  Int.reduceAdd Int.reduceSub Int.reduceMul Int.reduceNeg Int.reduceLT Int.reduceLE

attribute [close_rw_s] Modality.wp_box_saveStorage Modality.wp_box_findStorage
  Modality.wp_box_writeAddr Modality.wp_box_copyStToM Modality.wp_box_allocDefault
  Modality.wp_box_copyMem Modality.wp_box_transferAt

attribute [close_rw_s_last] Modality.wp_box



/-! ## The steps on a scoped goal -/

open Lean Elab Tactic Meta

/-- `sol_close_unwrap` on a scoped leaf `Valid ψ`: the leaf as `holdsE`
reads it (`CloseS.valid_of_holdsE`). -/
@[tactic Solidity.tacticSol_close_unwrap]
def evalSolCloseUnwrapS : Tactic := fun _ => withMainContext do
  let g ← getMainGoal
  let ty ← instantiateMVars (← g.getType)
  unless ty.isAppOf ``Solidity.Valid do throwUnsupportedSyntax
  let tag ← g.getTag
  let gs ← g.apply (← mkConstWithFreshMVarLevels ``CloseS.valid_of_holdsE)
  for g' in gs do g'.setTag tag
  replaceMainGoal gs

/-- Run `tac` where the goal is a scoped leaf's, else step aside. -/
def onScoped (tac : TacticM Syntax) : Tactic := fun _ => do
  unless ← Close.scopedGoal do throwUnsupportedSyntax
  evalTactic (← tac)

@[tactic Solidity.tacticSol_close_eval]
def evalSolCloseEvalS : Tactic := onScoped `(tactic| simp only [close_rw_s])

@[tactic Solidity.tacticSol_close_facts]
def evalSolCloseFactsS : Tactic := onScoped `(tactic|
  simp (config := { contextual := true, maxSteps := 400000 }) only [close_rw_s])

@[tactic Solidity.tacticSol_close_reads]
def evalSolCloseReadsS : Tactic := onScoped `(tactic|
  simp (config := { contextual := true, maxSteps := 400000 }) only [close_rw_s, close_rw_s_last])

@[tactic Solidity.tacticSol_close_reads_all]
def evalSolCloseReadsAllS : Tactic := onScoped `(tactic|
  simp_all (config := { maxSteps := 400000 }) only [close_rw_s, close_rw_s_last])

@[tactic Solidity.tacticSol_close_mt_eval]
def evalSolCloseMtEvalS : Tactic := onScoped `(tactic|
  simp (config := { decide := true }) only [close_rw_s, List.map_cons, List.map_nil,
    defaultForTy, Semantics.State.saveStorage, Semantics.State.findStorage, lookupBy, setBy,
    Semantics.SVal.save, Semantics.SVal.find, Except.ok.injEq, exists_eq_left'])

end Solidity
