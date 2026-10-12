import Solidity.Calculus.Close
import Solidity.Calculus.SeqRewrite

/-!
# `sol_close` on a scoped leaf

`sol_symex` on a scoped goal (`⊨ dl!{ … }` under `open scoped Solidity.Scoped`)
leaves leaves `Valid ψ`, `ψ : Fml C []` with no modality.  `sol_close`,
`sol_close_mt` and `sol_spec_close` close them here, on the scoped formula,
by the elaborators below, which read it with `close_rw_s`
(`Calculus/Close.lean` declares the syntax and the simp sets).

**The leaf as the closer reads it**: `holds` itself, over the typed state
(W9.7.2; the erased reading `holdsE` is gone).  A term reads the state's
global part (`State.globE`) and its locals by position (`State.loc`, a
stack of `Locs.push`es over the root state's).  An update is computed on
the state it is applied in (`Upd.applyV`: its global part and its locals'
values), and its rest is read in every typed state it lands on
(`CloseS.holds_upd`, from `Upd.afterT_applyV`): `LandedAll H g ℓ`, the
states `Landed H g ℓ` whose type carries what they read, so a plain rewrite
reads them (`Landed.globE_eq`, `Landed.loc_eq`) with no contextual pass and
no hypothesis.  Three choices keep it as cheap as the erased reading was:
the rest is a constant until the update's result is known
(`LandedRest`, else `simp` reads it twice, first with the result
abstract); the binder is a constant, not a `∀`, so no binder lemma is
tried at it (`LandedAll`, opened at the end, `landedAll_def`); and a landed
state names the heap typing before, not the state, so a hidden binder
pushed before an update is not read after it (`H_push`).  A negation and a
precondition read as they stand (`holds` is exact).  The binders range
over the values of their types: a parameter (`∀ uint a`) and a hidden
binder of a value type over `PrimTy.Denote`, a `uint` over `[0, 2²⁵⁶)`
(`forall_uint`); a hidden binder of a reference type over the typed
references, read erased (`LTy.TDenote.erase`).

**The set** states lemmas about `Calculus/Lands.lean`'s typed readers
only (`Tm.evalT`, `Tm.denoteT`, `Rhs.evalT`, `Upd.applyV`, `UpdElem.globT`)
and the typed state's operations as `State.loc`/`State.globE` read them
(`push`, `setLocal`, `anon`, `havoc`, `drop`), never its fields.  A term is
read constructor by constructor (each equation follows from the symbol's,
`Calculus/CloseLemmas.lean`).  What the interpreter knows is `close_rw`'s,
shared; its write-naming lemmas are restated without the locals' fact
(`CloseS.wp_box_saveStorage`, …), which no typed leaf reads.
-/

namespace Solidity

open Semantics SemanticsProperties

variable {C : Contract}

/-- A `Res` of an optional value: an unset local reverts. -/
def Close.optRes {α : Type} : Option α → Res α
  | some a => .ok a
  | none => .error .revert

namespace CloseS

/-! ## The typed state's parts

A leaf's state is a typed state, read by its global part (`State.globE`)
and its locals by position (`State.getE`); after an update, a typed state
it lands on, of which those two are known (`Upd.Lands`).  The pushes, sets
and havocs are `Calculus/Lands.lean`'s (`State.getE_push_here`, …). -/

section StateAPI

variable {Γ : Ctx}

/-! A typed state's locals are read as one function (`State.loc`), which a
push, a set, a havoc and a pop rewrite to a `Locs` expression; a landed
state's is the update's (`holds_upd`): one equation, not one a local. -/

theorem loc_push {t : LTy} (σ : State C Γ) (v : t.TDenote C σ.H) :
    (σ.push v).loc = σ.loc.push (LTy.TDenote.erase t v) := State.loc_push σ v
theorem loc_setLocal {t : LTy} (σ : State C Γ) (i : Idx Γ t) (v : t.TDenote C σ.H) :
    (σ.setLocal i v).loc = σ.loc.set i (LTy.TDenote.erase t v) := by
  funext u j
  by_cases h : i.toNat = j.toNat
  · obtain rfl := Idx.ty_eq_of_toNat h
    obtain rfl := Idx.toNat_inj i j h
    rw [Locs.set_same]
    exact State.getE_setLocal_same σ i v
  · rw [Locs.set_ne _ _ _ h]
    exact State.getE_setLocal_ne σ i j h v
theorem loc_havoc (σ : State C Γ) (st : Storage C) (nt : List (Int × Int)) :
    (σ.havoc st nt).loc = σ.loc := rfl
theorem loc_drop {Δ : Ctx} (h : Ext Γ Δ) (σ : State C Δ) : (σ.drop h).loc = σ.loc.drop h :=
  State.loc_drop h σ

theorem globE_env (σ : State C Γ) : σ.globE.env = [] := rfl
theorem optRes_some {α : Type} (a : α) : Close.optRes (some a) = .ok a := rfl
theorem optRes_none {α : Type} : Close.optRes (none : Option α) = .error .revert := rfl
theorem optRes_map_some {α β : Type} (f : α → β) (a : α) :
    Close.optRes ((some a).map f) = .ok (f a) := rfl

theorem erase_val {H : HTy} (p : PrimTy) (v : (LTy.val p).TDenote C H) :
    LTy.TDenote.erase (.val p) v = PrimTy.erase (p := p) v := rfl
theorem erase_alias {H : HTy} (R : RefTy) (v : (LTy.alias R).TDenote C H) :
    LTy.TDenote.erase (C := C) (.alias R) v = v.map SRef.erase := rfl
theorem erase_mem {H : HTy} (R : RefTy) (v : (LTy.mem R).TDenote C H) :
    LTy.TDenote.erase (C := C) (.mem R) v = v.map (·.id) := rfl
theorem erase_old {H : HTy} (v : LTy.old.TDenote C H) :
    LTy.TDenote.erase (C := C) (H := H) .old v = Storage.erase (v : Storage C) := rfl
theorem erase_oldNet {H : HTy} (v : LTy.oldNet.TDenote C H) :
    LTy.TDenote.erase (C := C) (H := H) .oldNet v = v := rfl

end StateAPI

/-! ## Terms, one constructor at a time

Each as `close_rw`'s equation for the closer's term (`Calculus/Close.lean`),
a local read by its position, a symbol on the global part (`State.globE`). -/

section Terms

variable {Γ : Ctx} (σ : State C Γ)

theorem eval_pvV {p : PrimTy} (i : Idx Γ (.val p)) :
    (Tm.pvV i : Tm C Γ .val).evalT σ = .ok (σ.loc _ i) :=
  rfl
theorem eval_pvP {R : RefTy} (i : Idx Γ (.alias R)) :
    (Tm.pvP i : Tm C Γ .path).evalT σ = Close.optRes (σ.loc _ i) := by
  show σ.aliasPathT i = _
  unfold State.aliasPathT State.loc State.getE
  generalize (TEnv.get i σ.env : Option (SRef C (.ref R))) = x
  cases x <;> rfl
theorem eval_pvS (i : Idx Γ .old) :
    (Tm.pvS i : Tm C Γ .st).evalT σ = .ok { σ.globE with storage := σ.loc _ i } := rfl
theorem eval_pvI {R : RefTy} (i : Idx Γ (.mem R)) :
    (Tm.pvI i : Tm C Γ .ident).evalT σ = Close.optRes (σ.loc _ i) := by
  show σ.memRefT i = _
  unfold State.memRefT State.loc State.getE
  generalize (TEnv.get i σ.env : Option (HRef σ.H R)) = x
  cases x <;> rfl
theorem eval_netOf (i : Idx Γ .oldNet) (a : Tm C Γ .val) : (Tm.netOf i a).evalT σ =
    a.evalT σ >>= Value.asInt >>= fun n => .ok (.int ((lookupBy n (σ.loc _ i)).getD 0)) := by
  simp only [Tm.evalT, bind, Except.bind]
  cases a.evalT σ <;> rfl

theorem eval_lit (v : Value) : (Tm.app0 (.lit v) : Tm C Γ .val).evalT σ = .ok v := rfl
theorem eval_env (k : EnvKey) :
    (Tm.app0 (.env k) : Tm C Γ .val).evalT σ = .ok (.int (σ.globE.envVal k)) := rfl
theorem eval_root (r : Name) : (Tm.app0 (.root r) : Tm C Γ .path).evalT σ = .ok (r, []) := rfl
theorem eval_storage : (Tm.app0 .storage : Tm C Γ .st).evalT σ = .ok σ.globE := rfl
theorem eval_memory : (Tm.app0 .memory : Tm C Γ .mem).evalT σ = .ok σ.globE := rfl
theorem eval_mtSt (vs : List (Name × Ty)) : (Tm.app0 (.mtSt vs) : Tm C Γ .st).evalT σ =
    .ok { σ.globE with storage := vs.map fun (n, T) => (n, defaultForTy T) } := rfl

theorem eval_unop (op : UnOp) (p : PrimTy) (h : (Op1.unop op p).named = false) (a : Tm C Γ .val) :
    (Tm.app1 (.unop op p) h a).evalT σ =
      a.evalT σ >>= fun x => applyUnOp op x >>= unopCheck op p :=
  rfl
theorem eval_net (h : Op1.net.named = false) (a : Tm C Γ .val) : (Tm.app1 .net h a).evalT σ =
    a.evalT σ >>= Value.asInt >>= fun n => .ok (.int (σ.globE.getNet n)) :=
  Close.Op1.eval_net _ _
theorem eval_field (f : Name) (h : (Op1.field f).named = false) (p : Tm C Γ .path) :
    (Tm.app1 (.field f) h p).evalT σ = p.evalT σ >>= fun rs => .ok (rs.1, rs.2 ++ [.field f]) :=
  rfl
theorem eval_next (h : Op1.next.named = false) (p : Tm C Γ .path) : (Tm.app1 .next h p).evalT σ =
    p.evalT σ >>= fun rs => σ.globE.findStorage rs.1 rs.2 >>= Close.pastEnd rs :=
  Close.Op1.eval_next _ _
theorem eval_sval (h : Op1.sval.named = false) (t : Tm C Γ .val) :
    (Tm.app1 .sval h t).evalT σ = t.evalT σ >>= fun v => .ok v.toSVal := rfl
theorem eval_alloc (R : RefTy) (h : (Op1.alloc R).named = false) (m : Tm C Γ .mem) :
    (Tm.app1 (.alloc R) h m).evalT σ =
      m.evalT σ >>= fun τ => allocDefault τ R >>= fun r => .ok r.2 :=
  rfl
theorem eval_mfield (f : Name) (h : (Op1.mfield f).named = false) (i : Tm C Γ .ident) :
    (Tm.app1 (.mfield f) h i).evalT σ = i.evalT σ >>= fun id => .ok (.memoryField id f) := rfl
theorem eval_addM (R : RefTy) (h : (Op1.addM R).named = false) (m : Tm C Γ .mem) :
    (Tm.app1 (.addM R) h m).evalT σ =
      m.evalT σ >>= fun τ => allocDefault τ R >>= fun r => .ok r.1 :=
  rfl
theorem eval_mval (h : Op1.mval.named = false) (t : Tm C Γ .val) :
    (Tm.app1 .mval h t).evalT σ = t.evalT σ >>= fun v => .ok v.toMVal := rfl
theorem eval_ref (h : Op1.ref.named = false) (i : Tm C Γ .ident) :
    (Tm.app1 .ref h i).evalT σ = i.evalT σ >>= fun id => .ok (.ref id) := rfl

theorem eval_binop (op : BinOp) (p : PrimTy) (a b : Tm C Γ .val) :
    (Tm.app2 (.binop op p) a b).evalT σ = a.evalT σ >>= fun x => evalBinop op p x (b.evalT σ) :=
  rfl
theorem eval_find (s : Tm C Γ .st) (p : Tm C Γ .path) : (Tm.app2 .find s p).evalT σ =
    s.evalT σ >>= fun τ => p.evalT σ >>= fun rs => τ.findStorage rs.1 rs.2 >>= SVal.asValue := rfl
theorem eval_len (s : Tm C Γ .st) (p : Tm C Γ .path) : (Tm.app2 .len s p).evalT σ =
    s.evalT σ >>= fun τ => p.evalT σ >>= fun rs => τ.findStorage rs.1 rs.2 >>= Close.arrLen :=
  Close.Op2.eval_len _ _ _
theorem eval_read (m : Tm C Γ .mem) (a : Tm C Γ .addr) : (Tm.app2 .read m a).evalT σ =
    m.evalT σ >>= fun τ => a.evalT σ >>= fun addr => Close.readVal τ addr := rfl
theorem eval_at (p : Tm C Γ .path) (i : Tm C Γ .val) : (Tm.app2 .at p i).evalT σ =
    p.evalT σ >>= fun rs => i.evalT σ >>= Value.asInt >>= fun k =>
      σ.globE.checkIndex rs.1 rs.2 k >>= fun _ => .ok (rs.1, rs.2 ++ [.at k]) :=
  Close.Op2.eval_at _ _ _
theorem eval_delAt (s : Tm C Γ .st) (p : Tm C Γ .path) : (Tm.app2 .delAt s p).evalT σ =
    s.evalT σ >>= fun τ => p.evalT σ >>= fun rs => τ.findStorage rs.1 rs.2 >>= fun cur =>
      τ.saveStorage rs.1 rs.2 cur.defaultOf := rfl
theorem eval_pushSlot (E : Ty) (s : Tm C Γ .st) (p : Tm C Γ .path) :
    (Tm.app2 (.pushSlot E) s p).evalT σ = s.evalT σ >>= fun τ => p.evalT σ >>= fun rs =>
      τ.findStorage rs.1 rs.2 >>= Close.pushOn τ E rs.1 rs.2 pure :=
  Close.Op2.eval_pushSlot _ _ _ _
theorem eval_pop (s : Tm C Γ .st) (p : Tm C Γ .path) : (Tm.app2 .pop s p).evalT σ =
    s.evalT σ >>= fun τ => p.evalT σ >>= fun rs =>
      τ.findStorage rs.1 rs.2 >>= Close.popOn τ false rs.1 rs.2 :=
  Close.Op2.eval_pop _ _ _
theorem eval_shrink (s : Tm C Γ .st) (p : Tm C Γ .path) : (Tm.app2 .shrink s p).evalT σ =
    s.evalT σ >>= fun τ => p.evalT σ >>= fun rs =>
      τ.findStorage rs.1 rs.2 >>= Close.popOn τ true rs.1 rs.2 :=
  Close.Op2.eval_shrink _ _ _
theorem eval_sfind (s : Tm C Γ .st) (p : Tm C Γ .path) : (Tm.app2 .sfind s p).evalT σ =
    s.evalT σ >>= fun τ => p.evalT σ >>= fun rs => τ.findStorage rs.1 rs.2 := rfl
theorem eval_copyMem (m : Tm C Γ .mem) (i : Tm C Γ .ident) : (Tm.app2 .copyMem m i).evalT σ =
    m.evalT σ >>= fun τ => i.evalT σ >>= fun id => copyMem τ (.ref id) := rfl
theorem eval_iread (m : Tm C Γ .mem) (a : Tm C Γ .addr) : (Tm.app2 .iread m a).evalT σ =
    m.evalT σ >>= fun τ => a.evalT σ >>= fun addr => readAddr τ addr >>= MVal.asRef := rfl
theorem eval_copy (m : Tm C Γ .mem) (v : Tm C Γ .sv) : (Tm.app2 .copy m v).evalT σ =
    v.evalT σ >>= fun sv => m.evalT σ >>= fun τ => copyStToM τ sv >>= fun r => r.2.asRef := rfl
theorem eval_mat (i : Tm C Γ .ident) (k : Tm C Γ .val) : (Tm.app2 .mat i k).evalT σ =
    i.evalT σ >>= fun id => k.evalT σ >>= Value.asInt >>= fun j => .ok (.memoryIndex id j) :=
  Close.Op2.eval_mat _ _ _
theorem eval_copySt (m : Tm C Γ .mem) (v : Tm C Γ .sv) : (Tm.app2 .copySt m v).evalT σ =
    v.evalT σ >>= fun sv => m.evalT σ >>= fun τ => copyStToM τ sv >>= fun r => .ok r.1 := rfl

theorem eval_ite (c a b : Tm C Γ .val) : (Tm.app3 .ite c a b).evalT σ =
    c.evalT σ >>= fun cv => pickBranch cv (a.evalT σ) (b.evalT σ) := rfl
theorem eval_save (s : Tm C Γ .st) (p : Tm C Γ .path) (h : Op1.sval.named = false)
    (t : Tm C Γ .val) : (Tm.app3 .save s p (.app1 .sval h t)).evalT σ =
    t.evalT σ >>= fun x => s.evalT σ >>= fun τ => p.evalT σ >>= fun rs =>
      τ.saveStorage rs.1 rs.2 x.toSVal :=
  Close.Op3.eval_save_val _ _ _ _
theorem eval_save_find (s s' : Tm C Γ .st) (p p' : Tm C Γ .path) :
    (Tm.app3 .save s p (.app2 .sfind s' p')).evalT σ =
    (Tm.app2 .sfind s' p').evalT σ >>= fun sv => s.evalT σ >>= fun τ => p.evalT σ >>= fun rs =>
      τ.findStorage rs.1 rs.2 >>= fun cur => τ.saveStorage rs.1 rs.2 (cur.overlay sv) :=
  Close.Op3.eval_save_find _ _ _ _ _
theorem eval_save_copyMem (s : Tm C Γ .st) (p : Tm C Γ .path) (m : Tm C Γ .mem)
    (i : Tm C Γ .ident) : (Tm.app3 .save s p (.app2 .copyMem m i)).evalT σ =
    (Tm.app2 .copyMem m i).evalT σ >>= fun sv => s.evalT σ >>= fun τ => p.evalT σ >>= fun rs =>
      τ.findStorage rs.1 rs.2 >>= fun cur => τ.saveStorage rs.1 rs.2 (cur.overlay sv) :=
  Close.Op3.eval_save_copyMem _ _ _ _ _
theorem eval_push (s : Tm C Γ .st) (p : Tm C Γ .path) (v : Tm C Γ .sv) :
    (Tm.app3 .push s p v).evalT σ = s.evalT σ >>= fun τ => p.evalT σ >>= fun rs =>
      τ.findStorage rs.1 rs.2 >>=
        Close.pushOn τ .uint rs.1 rs.2 (fun _ => v.evalT σ >>= fun sv => pure sv.strip) :=
  Close.Op3.eval_push _ _ _ _
theorem eval_write (m : Tm C Γ .mem) (a : Tm C Γ .addr) (v : Tm C Γ .mv) :
    (Tm.app3 .write m a v).evalT σ =
    v.evalT σ >>= fun mv => m.evalT σ >>= fun τ => a.evalT σ >>= fun addr => writeAddr τ mv addr :=
  rfl

theorem denote_lit (v : Value) : (Tm.app0 (.lit v) : Tm C Γ .val).denoteT σ = .prim v := rfl
theorem denote_env (k : EnvKey) :
    (Tm.app0 (.env k) : Tm C Γ .val).denoteT σ = .prim (.int (σ.globE.envVal k)) := rfl
theorem denote_pvV {p : PrimTy} (i : Idx Γ (.val p)) :
    (Tm.pvV i : Tm C Γ .val).denoteT σ = .prim (σ.loc _ i) := rfl

end Terms

/-! ## Updates: the global part and the locals' values

An update is computed on the state it is applied in (`Upd.applyV`, below
element by element, every right-hand side read in the state before): its
global part and the values it leaves in the locals, a `Locs` stack. -/

section Updates

variable {Γ Δ : Ctx} (σ₀ : State C Γ)

theorem rhs_val {p : PrimTy} (t : Tm C Γ .val) : (Rhs.val (p := p) t).evalT σ₀ = t.evalT σ₀ := rfl
theorem rhs_path {R : RefTy} (p : Tm C Γ .path) :
    (Rhs.path (R := R) p).evalT σ₀ = p.evalT σ₀ >>= fun r => .ok (some r) := rfl
theorem rhs_unset {R : RefTy} : (Rhs.unset (R := R) : Rhs C Γ _).evalT σ₀ = .ok none := rfl
theorem rhs_mref {R : RefTy} (i : Tm C Γ .ident) :
    (Rhs.mref (R := R) i).evalT σ₀ = i.evalT σ₀ >>= fun id => .ok (some id) := rfl
theorem rhs_store (s : Tm C Γ .st) :
    (Rhs.store s).evalT σ₀ = s.evalT σ₀ >>= fun g => .ok g.storage := rfl
theorem rhs_saveNet : (Rhs.saveNet : Rhs C Γ _).evalT σ₀ = .ok σ₀.globE.net := rfl
theorem rhs_saveNetMt : (Rhs.saveNetMt : Rhs C Γ _).evalT σ₀ = .ok [] := rfl

theorem glob_storage (s : Tm C Γ .st) (g : Semantics.State) :
    (UpdElem.storage s : UpdElem C Γ Δ).globT σ₀ g =
      s.evalT σ₀ >>= fun g' => .ok { g with storage := g'.storage } := rfl
theorem glob_memory (m : Tm C Γ .mem) (g : Semantics.State) :
    (UpdElem.memory m : UpdElem C Γ Δ).globT σ₀ g =
      m.evalT σ₀ >>= fun μ => .ok { g with heap := μ.heap, nextId := μ.nextId } := rfl
theorem glob_selfBalance (op : IntOp) (a : Tm C Γ .val) (g : Semantics.State) :
    (UpdElem.selfBalance op a : UpdElem C Γ Δ).globT σ₀ g = a.evalT σ₀ >>= Value.asInt >>=
      fun amt => .ok { g with selfBalance := op.apply σ₀.globE.selfBalance amt } := by
  simp only [UpdElem.globT, bind, Except.bind]
  cases a.evalT σ₀ <;> rfl
theorem glob_net (r : Tm C Γ .val) (op : IntOp) (a : Tm C Γ .val) (g : Semantics.State) :
    (UpdElem.net r op a : UpdElem C Γ Δ).globT σ₀ g =
      r.evalT σ₀ >>= Value.asInt >>= fun addr => a.evalT σ₀ >>= Value.asInt >>= fun amt =>
        .ok { g with net := setBy addr (op.apply (g.getNet addr) amt) g.net } := by
  simp only [UpdElem.globT, bind, Except.bind]
  cases r.evalT σ₀ with
  | error => rfl
  | ok v =>
    cases v with
    | bool b => rfl
    | int addr =>
      cases a.evalT σ₀ with
      | error => rfl
      | ok w => cases w <;> rfl
theorem glob_pay (r a : Tm C Γ .val) (g : Semantics.State) :
    (UpdElem.pay r a : UpdElem C Γ Δ).globT σ₀ g =
      r.evalT σ₀ >>= Value.asInt >>= fun addr => a.evalT σ₀ >>= Value.asInt >>= fun amt =>
        if amt < 0 then .error .revert
        else .ok { g with
          net := if addr = σ₀.globE.tx.selfAddress then g.net
            else setBy addr (g.getNet addr - amt) g.net } := by
  simp only [UpdElem.globT, bind, Except.bind]
  cases r.evalT σ₀ with
  | error => rfl
  | ok v =>
    cases v with
    | bool b => rfl
    | int addr =>
      cases a.evalT σ₀ with
      | error => rfl
      | ok w => cases w <;> rfl
theorem glob_netMt (r a : Tm C Γ .val) (g : Semantics.State) :
    (UpdElem.netMt r a : UpdElem C Γ Δ).globT σ₀ g =
      r.evalT σ₀ >>= Value.asInt >>= fun addr => a.evalT σ₀ >>= Value.asInt >>= fun amt =>
        .ok { g with net := [(addr, amt)] } := by
  simp only [UpdElem.globT, bind, Except.bind]
  cases r.evalT σ₀ with
  | error => rfl
  | ok v =>
    cases v with
    | bool b => rfl
    | int addr =>
      cases a.evalT σ₀ with
      | error => rfl
      | ok w => cases w <;> rfl
theorem glob_setBalance (a : Tm C Γ .val) (g : Semantics.State) :
    (UpdElem.setBalance a : UpdElem C Γ Δ).globT σ₀ g = a.evalT σ₀ >>= Value.asInt >>= fun amt =>
      .ok { g with selfBalance := amt } := by
  simp only [UpdElem.globT, bind, Except.bind]
  cases a.evalT σ₀ <;> rfl

theorem applyV_nil : (Upd.nil : Upd C Γ Γ).applyV σ₀ = .ok (σ₀.globE, σ₀.loc) := rfl
theorem applyV_snoc (U : Upd C Γ Δ) (e : UpdElem C Γ Δ) :
    (U.snoc e).applyV σ₀ = U.applyV σ₀ >>= fun p => e.applyV σ₀ p.1 p.2 := rfl
theorem applyV_decl {t : LTy} (U : Upd C Γ Δ) (x : Var) (r : Rhs C Γ t) :
    (U.decl x r).applyV σ₀ = U.applyV σ₀ >>= fun p => r.evalT σ₀ >>= fun v => .ok (p.1, p.2.push v) :=
  rfl
theorem applyV_pop {Δ' : Ctx} (U : Upd C Γ Δ) (h : Ext Δ' Δ) :
    (U.pop h).applyV σ₀ = U.applyV σ₀ >>= fun p => .ok (p.1, p.2.drop h) := rfl
theorem applyV_drop {Δ' : Ctx} (U : Upd C Γ Δ) (h : Thin Δ' Δ) :
    (U.drop h).applyV σ₀ = U.applyV σ₀ >>= fun p => .ok (p.1, p.2.thin h) := rfl

theorem elem_local {t : LTy} (i : Idx Δ t) (r : Rhs C Γ t) (g : Semantics.State) (ℓ : Locs C Δ) :
    (UpdElem.local i r).applyV σ₀ g ℓ = r.evalT σ₀ >>= fun v => .ok (g, ℓ.set i v) := rfl
theorem elem_storage (s : Tm C Γ .st) (g : Semantics.State) (ℓ : Locs C Δ) :
    (UpdElem.storage s : UpdElem C Γ Δ).applyV σ₀ g ℓ =
      (UpdElem.storage s : UpdElem C Γ Δ).globT σ₀ g >>= fun g' => .ok (g', ℓ) := rfl
theorem elem_memory (m : Tm C Γ .mem) (g : Semantics.State) (ℓ : Locs C Δ) :
    (UpdElem.memory m : UpdElem C Γ Δ).applyV σ₀ g ℓ =
      (UpdElem.memory m : UpdElem C Γ Δ).globT σ₀ g >>= fun g' => .ok (g', ℓ) := rfl
theorem elem_selfBalance (op : IntOp) (a : Tm C Γ .val) (g : Semantics.State) (ℓ : Locs C Δ) :
    (UpdElem.selfBalance op a : UpdElem C Γ Δ).applyV σ₀ g ℓ =
      (UpdElem.selfBalance op a : UpdElem C Γ Δ).globT σ₀ g >>= fun g' => .ok (g', ℓ) := rfl
theorem elem_net (r : Tm C Γ .val) (op : IntOp) (a : Tm C Γ .val) (g : Semantics.State)
    (ℓ : Locs C Δ) : (UpdElem.net r op a : UpdElem C Γ Δ).applyV σ₀ g ℓ =
      (UpdElem.net r op a : UpdElem C Γ Δ).globT σ₀ g >>= fun g' => .ok (g', ℓ) := rfl
theorem elem_pay (r a : Tm C Γ .val) (g : Semantics.State) (ℓ : Locs C Δ) :
    (UpdElem.pay r a : UpdElem C Γ Δ).applyV σ₀ g ℓ =
      (UpdElem.pay r a : UpdElem C Γ Δ).globT σ₀ g >>= fun g' => .ok (g', ℓ) := rfl
theorem elem_netMt (r a : Tm C Γ .val) (g : Semantics.State) (ℓ : Locs C Δ) :
    (UpdElem.netMt r a : UpdElem C Γ Δ).applyV σ₀ g ℓ =
      (UpdElem.netMt r a : UpdElem C Γ Δ).globT σ₀ g >>= fun g' => .ok (g', ℓ) := rfl
theorem elem_setBalance (a : Tm C Γ .val) (g : Semantics.State) (ℓ : Locs C Δ) :
    (UpdElem.setBalance a : UpdElem C Γ Δ).applyV σ₀ g ℓ =
      (UpdElem.setBalance a : UpdElem C Γ Δ).globT σ₀ g >>= fun g' => .ok (g', ℓ) := rfl

/-! The locals an update leaves, by position. -/

theorem push_here {t : LTy} (ℓ : Locs C Δ) (v : t.Denote C) : ℓ.push v t .here = v := rfl
theorem push_there {t u : LTy} (ℓ : Locs C Δ) (v : t.Denote C) (i : Idx Δ u) :
    ℓ.push v u (.there i) = ℓ u i := rfl
theorem set_here_here {t : LTy} (ℓ : Locs C (t :: Δ)) (v : t.Denote C) :
    ℓ.set .here v t .here = v := Locs.set_same ℓ .here v
theorem set_here_there {t u : LTy} (ℓ : Locs C (t :: Δ)) (v : t.Denote C) (j : Idx Δ u) :
    ℓ.set .here v u (.there j) = ℓ u (.there j) :=
  Locs.set_ne ℓ .here (.there j) (fun h => nomatch h) v
theorem set_there_here {t u : LTy} (ℓ : Locs C (u :: Δ)) (i : Idx Δ t) (v : t.Denote C) :
    ℓ.set (.there i) v u .here = ℓ u .here :=
  Locs.set_ne ℓ (.there i) .here (fun h => nomatch h) v
theorem set_there_there {t u w : LTy} (ℓ : Locs C (w :: Δ)) (i : Idx Δ t) (v : t.Denote C)
    (j : Idx Δ u) :
    ℓ.set (.there i) v u (.there j) = Locs.set (fun _ k => ℓ _ (.there k)) i v u j := by
  by_cases h : i.toNat = j.toNat
  · obtain rfl := Idx.ty_eq_of_toNat h
    obtain rfl := Idx.toNat_inj i j h
    rw [Locs.set_same, Locs.set_same]
  · rw [Locs.set_ne _ _ _ h, Locs.set_ne _ (.there i) (.there j) (fun h' => h (Nat.add_right_cancel h'))]
/-! The locals an update leaves kept as a stack of pushes over the state's
own (`set` and `drop` absorbed), as the erased state's were: a read is then
a walk down the stack. -/

theorem set_push_here {t : LTy} (ℓ : Locs C Δ) (w v : t.Denote C) :
    (ℓ.push w).set .here v = ℓ.push v := by
  funext u j
  cases j with
  | here => exact Locs.set_same _ _ _
  | there j => exact Locs.set_ne _ .here (.there j) (by simp only [Idx.toNat]; omega) v
theorem set_push_there {t u : LTy} (ℓ : Locs C Δ) (w : u.Denote C) (i : Idx Δ t) (v : t.Denote C) :
    (ℓ.push w).set (.there i) v = (ℓ.set i v).push w := by
  funext u' j
  cases j with
  | here => exact Locs.set_ne _ (.there i) .here (by simp only [Idx.toNat]; omega) v
  | there j =>
    by_cases h : i.toNat = j.toNat
    · obtain rfl := Idx.ty_eq_of_toNat h
      obtain rfl := Idx.toNat_inj i j h
      rw [Locs.set_same]
      exact (Locs.set_same _ _ _).symm
    · rw [Locs.set_ne _ (.there i) (.there j) (fun h' => h (Nat.add_right_cancel h'))]
      exact (Locs.set_ne ℓ i j h v).symm
theorem drop_refl' (ℓ : Locs C Δ) : ℓ.drop .refl = ℓ := rfl
theorem drop_push' {Δ' : Ctx} {t : LTy} (h : Ext Δ' Δ) (ℓ : Locs C Δ) (w : t.Denote C) :
    (ℓ.push w).drop (.push h) = ℓ.drop h := rfl
theorem thin_refl' (ℓ : Locs C Δ) : ℓ.thin .refl = ℓ := rfl
theorem thin_keep' {Δ' : Ctx} {t : LTy} (h : Thin Δ' Δ) (ℓ : Locs C Δ) (w : t.Denote C) :
    (ℓ.push w).thin (.keep h) = (ℓ.thin h).push w := by
  funext u j
  cases j <;> rfl
theorem thin_drop' {Δ' : Ctx} {t : LTy} (h : Thin Δ' Δ) (ℓ : Locs C Δ) (w : t.Denote C) :
    (ℓ.push w).thin (.drop h) = ℓ.thin h := rfl

theorem drop_apply {Δ' : Ctx} {t : LTy} (h : Ext Δ' Δ) (ℓ : Locs C Δ) (i : Idx Δ' t) :
    ℓ.drop h t i = ℓ t (i.ext h) := rfl
theorem thin_apply {Δ' : Ctx} {t : LTy} (h : Thin Δ' Δ) (ℓ : Locs C Δ) (i : Idx Δ' t) :
    ℓ.thin h t i = ℓ t (i.wk h) := rfl
theorem ext_refl {t : LTy} (i : Idx Δ t) : i.ext .refl = i := rfl
theorem ext_push {Δ' : Ctx} {t u : LTy} (i : Idx Δ' t) (h : Ext Δ' Δ) :
    i.ext (Ext.push (t := u) h) = .there (i.ext h) := rfl
theorem wk_refl {t : LTy} (i : Idx Δ t) : i.wk .refl = i := rfl
theorem wk_keep_here {Δ' : Ctx} {t : LTy} (h : Thin Δ' Δ) :
    (Idx.here : Idx (t :: Δ') t).wk (.keep h) = .here := rfl
theorem wk_keep_there {Δ' : Ctx} {t u : LTy} (h : Thin Δ' Δ) (i : Idx Δ' t) :
    (Idx.there (u := u) i).wk (.keep h) = .there (i.wk h) := rfl
theorem wk_drop {Δ' : Ctx} {t u : LTy} (h : Thin Δ' Δ) (i : Idx Δ' t) :
    i.wk (Thin.drop (t := u) h) = .there (i.wk h) := rfl

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
/-- A natural literal cast to an integer is the integer literal: the bounds
`uintBound`, `intBound` and the bitwise results then compare by the
literal simprocs (`Int.reduceLT`), not by unfolding the cast. -/
theorem natCast_ofNat (n : Nat) : ((no_index (OfNat.ofNat n) : Nat) : Int) = OfNat.ofNat n := rfl

/-! ## The leaf, as `holds` reads it -/

section Leaf

variable {Γ : Ctx}

/-- A scoped leaf is valid where it holds in every typed state. -/
theorem valid_of_holds {φ : Fml C []} (h : ∀ σ : State C [], holds σ φ) : Valid φ := h

theorem holds_tt (σ : State C Γ) : holds σ (.tt : Fml C Γ) ↔ True := Iff.rfl
theorem holds_not (σ : State C Γ) (φ : Fml C Γ) : holds σ (.not φ) ↔ ¬ holds σ φ := Iff.rfl
theorem holds_and (σ : State C Γ) (φ ψ : Fml C Γ) :
    holds σ (.and φ ψ) ↔ holds σ φ ∧ holds σ ψ := Iff.rfl
theorem holds_imp (σ : State C Γ) (φ ψ : Fml C Γ) :
    holds σ (.imp φ ψ) ↔ (holds σ φ → holds σ ψ) := Iff.rfl
theorem holds_eq (σ : State C Γ) (a b : Tm C Γ .val) :
    holds σ (.eq a b) ↔ Theory.StValue.Equiv (a.denoteT σ) (b.denoteT σ) := Iff.rfl
theorem holds_defined (σ : State C Γ) (t : Tm C Γ .val) : holds σ (.defined t) ↔
    Modality.diamond.wp (t.evalT σ) fun _ => True := by
  show (∃ x, t.evalT σ = .ok x) ↔ _
  cases t.evalT σ <;> simp [Modality.wp, Modality.onHalt]
theorem holds_eqD (σ : State C Γ) (a b : Tm C Γ .val) : holds σ (Fml.eqD a b) ↔
    Modality.diamond.wp (a.evalT σ) fun x => Modality.diamond.wp (b.evalT σ) fun y => x = y := by
  have key : holds σ (Fml.eqD a b) ↔ ∃ x, a.evalT σ = .ok x ∧ b.evalT σ = .ok x := by
    constructor
    · rintro ⟨⟨x, hx⟩, ⟨y, hy⟩, he⟩
      have he' : Theory.StValue.Equiv (.prim x) (.prim y) := by
        rw [← Tm.denoteT_evalT σ a x hx, ← Tm.denoteT_evalT σ b y hy]; exact he
      rw [Theory.StValue.Equiv.prim_iff] at he'
      cases he'
      exact ⟨x, hx, hy⟩
    · rintro ⟨x, hx, hy⟩
      refine ⟨⟨x, hx⟩, ⟨x, hy⟩, ?_⟩
      show Theory.StValue.Equiv (a.denoteT σ) (b.denoteT σ)
      rw [Tm.denoteT_evalT σ a x hx, Tm.denoteT_evalT σ b x hy]
      exact Theory.StValue.Equiv.refl _
  rw [key]
  cases a.evalT σ <;> cases b.evalT σ <;>
    simp only [Modality.wp, Modality.onHalt, Except.ok.injEq, reduceCtorEq, false_and, and_false,
      and_self, exists_false, exists_eq_left', eq_comm]
/-- A typed state an update lands on: the global part `g`, the locals `ℓ`,
a heap typing that extends `H`, the one of the state it is applied in
(`Upd.afterT_applyV`).  What it reads is in its type, so a plain rewrite
reads it (`Landed.globE_eq`, `Landed.loc_eq`): no contextual pass, no
hypothesis.  It names the heap typing before, not the state: a hidden
binder pushed before the update is then not read by the states after it. -/
structure Landed {Δ : Ctx} (H : HTy) (g : Semantics.State) (ℓ : Locs C Δ) : Type where
  /-- The state landed on. -/
  val : State C Δ
  globE_eq : val.globE = g
  loc_eq : val.loc = ℓ
  ext : H <+: val.H

/-- `p` of every typed state that lands on `g` and `ℓ`: a constant, not a
binder, so that `simp` tries no binder lemma at it (`forall_const` and its
kin, which ask an instance of every binder's type) and only enters its
body; unfolded at the end (`landedAll_def`). -/
def LandedAll {Δ : Ctx} (H : HTy) (g : Semantics.State) (ℓ : Locs C Δ)
    (p : Landed (C := C) H g ℓ → Prop) : Prop :=
  ∀ x, p x

theorem landedAll_def {Δ : Ctx} (H : HTy) (g : Semantics.State) (ℓ : Locs C Δ)
    (p : Landed (C := C) H g ℓ → Prop) : LandedAll H g ℓ p ↔ ∀ x, p x := Iff.rfl

/-- A landed state the rest no longer reads: only whether there is one. -/
theorem landedAll_const {Δ : Ctx} (H : HTy) (g : Semantics.State) (ℓ : Locs C Δ) (P : Prop) :
    LandedAll H g ℓ (fun _ => P) ↔ (Nonempty (Landed (C := C) H g ℓ) → P) :=
  ⟨fun h ⟨x⟩ => h x, fun h x => h ⟨x⟩⟩

/-- What follows an update applied over the heap typing `H`, read in every
typed state it lands on: a constant, so that `simp` reads it only once the
update's result is known (`landedRest_def`), not first with the result
abstract. -/
def LandedRest {Δ : Ctx} (H : HTy) (φ : Fml C Δ) (q : Semantics.State × Locs C Δ) : Prop :=
  LandedAll H q.1 q.2 fun x => holds x.val φ

theorem landedRest_def {Δ : Ctx} (H : HTy) (φ : Fml C Δ) (g : Semantics.State)
    (ℓ : Locs C Δ) : LandedRest H φ (g, ℓ) ↔ LandedAll H g ℓ fun x => holds x.val φ := Iff.rfl

/-- **An update's rest**, read in every typed state it lands on
(`Upd.afterT_applyV`): one with the global part and the locals the update
leaves. -/
theorem holds_upd {Δ : Ctx} (σ : State C Γ) (m : Modality) (U : Upd C Γ Δ) (φ : Fml C Δ) :
    holds σ (.upd m U φ) ↔ m.wp (U.applyV σ) (LandedRest σ.H φ) := by
  show U.afterT m σ (holds · φ) ↔ _
  rw [Upd.afterT_applyV]
  cases U.applyV σ with
  | error => rfl
  | ok q =>
    show (∀ σ' : State C Δ, _) ↔ LandedAll σ.H q.1 q.2 _
    rw [landedAll_def]
    refine ⟨fun h x => h x.val x.globE_eq (fun i => ?_) x.ext, fun h σ' hg hl hH =>
      h ⟨σ', hg, funext fun _ => funext fun i => hl i, hH⟩⟩
    exact congrFun (congrFun x.loc_eq _) i

/-! The heap typing of a pushed, set, havocked, anonymised or popped state:
the state's own. -/

theorem H_push {t : LTy} (σ : State C Γ) (v : t.TDenote C σ.H) : (σ.push v).H = σ.H := rfl
theorem H_setLocal {t : LTy} (σ : State C Γ) (i : Idx Γ t) (v : t.TDenote C σ.H) :
    (σ.setLocal i v).H = σ.H := rfl
theorem H_havoc (σ : State C Γ) (st : Storage C) (nt : List (Int × Int)) :
    (σ.havoc st nt).H = σ.H := rfl
theorem H_drop {Δ : Ctx} (h : Ext Γ Δ) (σ : State C Δ) : (σ.drop h).H = σ.H := rfl

theorem holds_havoc (σ : State C Γ) (φ : Fml C Γ) :
    holds σ (.havoc φ) ↔ ∀ (st : Storage C) nt, holds (σ.havoc st nt) φ := Iff.rfl
theorem holds_all (σ : State C Γ) (x : Var) (p : PrimTy) (φ : Fml C (.val p :: Γ)) :
    holds σ (.all x p φ) ↔ ∀ v : p.Denote, holds (σ.push (t := .val p) v) φ := Iff.rfl
theorem holds_bind (σ : State C Γ) (m : Modality) (x : Var) (t : LTy) (φ : Fml C (t :: Γ)) :
    holds σ (.bind m x t φ) ↔ ∀ v : t.TDenote C σ.H, holds (σ.push v) φ := Iff.rfl
/-! A hidden binder at each type, its domain written out (no `LTy.TDenote`
to reduce at every step). -/
theorem holds_bind_val (σ : State C Γ) (m : Modality) (x : Var) (p : PrimTy)
    (φ : Fml C (.val p :: Γ)) :
    holds σ (.bind m x (.val p) φ) ↔ ∀ v : p.Denote, holds (σ.push (t := .val p) v) φ := Iff.rfl
theorem holds_bind_alias (σ : State C Γ) (m : Modality) (x : Var) (R : RefTy)
    (φ : Fml C (.alias R :: Γ)) : holds σ (.bind m x (.alias R) φ) ↔
      ∀ v : Option (SRef C (.ref R)), holds (σ.push (t := .alias R) v) φ := Iff.rfl
theorem holds_bind_mem (σ : State C Γ) (m : Modality) (x : Var) (R : RefTy)
    (φ : Fml C (.mem R :: Γ)) : holds σ (.bind m x (.mem R) φ) ↔
      ∀ v : Option (HRef σ.H R), holds (σ.push (t := .mem R) v) φ := Iff.rfl
theorem holds_bind_old (σ : State C Γ) (m : Modality) (x : Var) (φ : Fml C (.old :: Γ)) :
    holds σ (.bind m x .old φ) ↔ ∀ v : Storage C, holds (σ.push (t := .old) v) φ := Iff.rfl
theorem holds_bind_oldNet (σ : State C Γ) (m : Modality) (x : Var) (φ : Fml C (.oldNet :: Γ)) :
    holds σ (.bind m x .oldNet φ) ↔ ∀ v : List (Int × Int), holds (σ.push (t := .oldNet) v) φ :=
  Iff.rfl
theorem holds_anon (σ : State C Γ) (xs : List ((t : LTy) × Idx Γ t)) (φ : Fml C Γ) :
    holds σ (.anon xs φ) ↔ ∀ b, holds (σ.anon xs b) φ := Iff.rfl

theorem forall_val {H : HTy} (p : PrimTy) (P : (LTy.val p).TDenote C H → Prop) :
    (∀ v : (LTy.val p).TDenote C H, P v) ↔ ∀ v : p.Denote, P v := Iff.rfl

end Leaf

end CloseS


/-! ## Writes under the box, for the typed state

`Calculus/CloseLemmas.lean`'s naming lemmas without the locals' fact
(`getEnv`): a typed state's locals are not in its global part (`State.globE`
has none), so the fact is never read, and each write is one hypothesis
lighter. -/

namespace CloseS

open Semantics in
theorem wp_box_saveStorage {σ : Semantics.State} {r : Name} {p : List Seg} {v : Semantics.SVal}
    {P : Semantics.State → Prop} :
    Modality.box.wp (σ.saveStorage r p v) P ↔
      ∀ τ, σ.saveStorage r p v = .ok τ → τ.findStorage r p = .ok v →
        (∀ q, Close.Prefix p q → τ.findStorage r q = v.find (Close.after p q)) →
        (∀ r' q, r' ≠ r ∨ Close.Diverge p q → τ.findStorage r' q = σ.findStorage r' q) →
        (∀ r' q k, r' ≠ r ∨ ¬ Close.Prefix p q → τ.checkIndex r' q k = σ.checkIndex r' q k) →
        (∀ q k, Close.Prefix p q → τ.checkIndex r q k = v.find (Close.after p q) >>= Close.idxOk k) →
        (∀ a, readAddr τ a = readAddr σ a) →
        (∀ a, Close.readVal τ a = Close.readVal σ a) →
        τ.tx = σ.tx → τ.selfBalance = σ.selfBalance → τ.net = σ.net → P τ := by
  rw [Modality.wp_box_saveStorage]
  exact ⟨fun h τ hs a b c d e f g i j k => h τ hs a b c d e (Close.getEnv_saveStorage hs) f g i j k,
    fun h τ hs a b c d e _ f g i j k => h τ hs a b c d e f g i j k⟩

open Semantics in
theorem wp_box_writeAddr {σ : Semantics.State} {mv : Semantics.MVal} {a : Addr}
    {P : Semantics.State → Prop} :
    Modality.box.wp (writeAddr σ mv a) P ↔
      ∀ τ, writeAddr σ mv a = .ok τ → readAddr τ a = .ok mv → Close.readVal τ a = mv.asValue →
        (∀ a', Close.Apart a a' → readAddr τ a' = readAddr σ a') →
        (∀ a', Close.Apart a a' → Close.readVal τ a' = Close.readVal σ a') →
        (∀ r q, τ.findStorage r q = σ.findStorage r q) →
        (∀ r q k, τ.checkIndex r q k = σ.checkIndex r q k) →
        τ.tx = σ.tx → τ.selfBalance = σ.selfBalance → P τ := by
  rw [Modality.wp_box_writeAddr]
  refine ⟨fun h τ hs a b c d e f g i => ?_, fun h τ hs a b c d e f _ g i => h τ hs a b c d e f g i⟩
  obtain ⟨id, obj, rfl, -⟩ := Close.writeAddr_setObj hs
  exact h _ hs a b c d e f (fun _ => rfl) g i

open Semantics in
theorem wp_box_copyStToM {σ : Semantics.State} {v : Semantics.SVal} {P : Semantics.State × Semantics.MVal → Prop} :
    Modality.box.wp (copyStToM σ v) P ↔
      ∀ τ mv, copyStToM σ v = .ok (τ, mv) →
        (∀ id f, mv = .ref id → f ≠ "length" →
          Close.readVal τ (.memoryField id f) = v.find [.field f] >>= SVal.asValue) →
        (∀ r q, τ.findStorage r q = σ.findStorage r q) →
        (∀ r q k, τ.checkIndex r q k = σ.checkIndex r q k) →
        τ.tx = σ.tx → τ.selfBalance = σ.selfBalance → P (τ, mv) := by
  rw [Modality.wp_box_copyStToM]
  exact ⟨fun h τ mv hs a b c d e => h τ mv hs a b c (Close.copyStToM_frame' hs).2 d e,
    fun h τ mv hs a b c _ d e => h τ mv hs a b c d e⟩

open Semantics in
theorem wp_box_allocDefault {σ : Semantics.State} {R : RefTy} {P : Semantics.State × Nat → Prop} :
    Modality.box.wp (allocDefault σ R) P ↔
      ∀ τ id, allocDefault σ R = .ok (τ, id) →
        (∀ f, f ≠ "length" →
          Close.readVal τ (.memoryField id f) =
            (defaultForRef R).find [.field f] >>= SVal.asValue) →
        (∀ r q, τ.findStorage r q = σ.findStorage r q) →
        (∀ r q k, τ.checkIndex r q k = σ.checkIndex r q k) →
        τ.tx = σ.tx → τ.selfBalance = σ.selfBalance → P (τ, id) := by
  rw [Modality.wp_box_allocDefault]
  exact ⟨fun h τ id hs a b c d e =>
      h τ id hs a b c (Close.copyStToM_frame' (Close.allocDefault_copy hs)).2 d e,
    fun h τ id hs a b c _ d e => h τ id hs a b c d e⟩

open Semantics in
theorem wp_box_transferAt {σ : Semantics.State} {addr amt : Int} {P : Semantics.State → Prop} :
    Modality.box.wp (transferAt σ addr amt) P ↔
      ∀ τ, transferAt σ addr amt = .ok τ →
        (∀ r q, τ.findStorage r q = σ.findStorage r q) →
        (∀ r q k, τ.checkIndex r q k = σ.checkIndex r q k) →
        (∀ a, readAddr τ a = readAddr σ a) → (∀ a, Close.readVal τ a = Close.readVal σ a) →
        τ.tx = σ.tx → τ.selfBalance = σ.selfBalance →
        τ.net = (σ.pay addr amt).net → P τ := by
  rw [Modality.wp_box_transferAt]
  exact ⟨fun h τ hs a b c d e f g => h τ hs a b (Close.transferAt_frame hs).2.1 c d e f g,
    fun h τ hs a b _ c d e f g => h τ hs a b c d e f g⟩

end CloseS

/-! ## The set -/

attribute [close_rw_s high] CloseS.holds_eqD

attribute [close_rw_s]
  -- formulas
  CloseS.holds_tt CloseS.holds_not CloseS.holds_and CloseS.holds_imp CloseS.holds_eq
  CloseS.holds_defined CloseS.holds_upd CloseS.holds_havoc CloseS.holds_all
  CloseS.holds_bind_val CloseS.holds_bind_alias CloseS.holds_bind_mem CloseS.holds_bind_old
  CloseS.holds_bind_oldNet CloseS.holds_anon
  CloseS.forall_uint CloseS.forall_int CloseS.erase_uint CloseS.erase_int CloseS.erase_bool
  CloseS.natCast_ofNat
  CloseS.denote_lit CloseS.denote_pvV CloseS.denote_env Close.equiv_prim_left_iff
  Theory.StValue.Equiv.prim_iff Theory.StValue.prim.injEq
  -- the typed state
  CloseS.loc_push CloseS.loc_setLocal CloseS.loc_havoc CloseS.loc_drop CloseS.Landed.globE_eq
  CloseS.set_push_here CloseS.set_push_there CloseS.drop_refl' CloseS.drop_push' CloseS.thin_refl'
  CloseS.thin_keep' CloseS.thin_drop'
  CloseS.Landed.loc_eq CloseS.landedAll_const CloseS.landedRest_def CloseS.H_push CloseS.H_setLocal
  CloseS.H_havoc CloseS.H_drop
  State.globE_push State.globE_setLocal State.anon_nil State.anon_cons
  State.globE_havoc State.globE_drop CloseS.globE_env
  CloseS.erase_val CloseS.erase_alias CloseS.erase_mem CloseS.erase_old CloseS.erase_oldNet
  CloseS.optRes_some CloseS.optRes_none CloseS.optRes_map_some
  -- updates
  CloseS.applyV_nil CloseS.applyV_snoc CloseS.applyV_decl CloseS.applyV_pop CloseS.applyV_drop
  CloseS.elem_local CloseS.elem_storage CloseS.elem_memory CloseS.elem_selfBalance
  CloseS.elem_net CloseS.elem_pay CloseS.elem_netMt CloseS.elem_setBalance
  CloseS.glob_storage CloseS.glob_memory CloseS.glob_selfBalance
  CloseS.glob_net CloseS.glob_pay CloseS.glob_netMt CloseS.glob_setBalance
  CloseS.push_here CloseS.push_there CloseS.set_here_here CloseS.set_here_there
  CloseS.set_there_here CloseS.set_there_there CloseS.drop_apply CloseS.thin_apply
  CloseS.ext_refl CloseS.ext_push CloseS.wk_refl CloseS.wk_keep_here
  CloseS.wk_keep_there CloseS.wk_drop
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

attribute [close_rw_s] CloseS.wp_box_saveStorage Modality.wp_box_findStorage
  CloseS.wp_box_writeAddr CloseS.wp_box_copyStToM CloseS.wp_box_allocDefault
  Modality.wp_box_copyMem CloseS.wp_box_transferAt

attribute [close_rw_s_last] Modality.wp_box



/-! ## The steps on a scoped goal -/

open Lean Elab Tactic Meta

/-- `sol_close_unwrap` on a scoped leaf `Valid ψ`: `holds` in every typed
state (`CloseS.valid_of_holds`). -/
@[tactic Solidity.tacticSol_close_unwrap]
def evalSolCloseUnwrapS : Tactic := fun _ => withMainContext do
  let g ← getMainGoal
  let ty ← instantiateMVars (← g.getType)
  unless ty.isAppOf ``Solidity.Valid do throwUnsupportedSyntax
  let tag ← g.getTag
  let gs ← g.apply (← mkConstWithFreshMVarLevels ``CloseS.valid_of_holds)
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
