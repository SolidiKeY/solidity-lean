import Solidity.Calculus.Close
import Solidity.Calculus.SeqRewrite
import Solidity.Theory.Typed.Mem
import Solidity.Calculus.EvalEqs
import Solidity.Calculus.TermAgree

/-!
# `sol_close` on a scoped leaf

`sol_symex` on a scoped goal (`⊨ᶠ dl!{ … }` under `open scoped Solidity.Scoped`)
leaves leaves `Fml.Valid ψ`, `ψ : Fml C []` with no modality.  `sol_close`,
`sol_close_mt` and `sol_spec_close` close them here, on the scoped formula,
by the elaborators below, which read it with `close_rw_s`
(`Calculus/Close.lean` declares the syntax and the simp sets).

**The leaf as the closer reads it**: `holds` itself, over the typed state.
A term reads the state's global part a field at a time (`State.glob`: the
storage, the ledger, the balance, the transaction) and its locals by
position (`State.locV`, a stack of `LocsV.push`es over the root state's),
every symbol by its typed equation (`Calculus/CloseLemmas.lean`'s
`Close.Op2.eval_find`, …, under `Tm.eval_app*`); a read is an `Option`,
`none` where it reverts, carried into the closer's weakest preconditions by
`Close.optRes`.  An update is computed on the state it is applied in
(`Upd.applyV`: its typed global part and its locals' values), and its rest
is read in every typed state it lands on (`CloseS.holds_upd`, from
`Upd.afterT_applyV`): `LandedAll g ℓ`, the states `Landed g ℓ` whose type
carries what they read, so a plain rewrite reads them (`Landed.storage_eq`,
`Landed.locV_eq`) with no contextual pass and no hypothesis.  The rest is a
constant until the update's result is known (`LandedRest`), and the binder
a constant, not a `∀` (`LandedAll`, opened at the end, `landedAll_def`).
The binders range over the values of their types: a `uint` over
`[0, 2²⁵⁶)` (`forall_uint`).

**The set** states lemmas about `Calculus/Lands.lean`'s typed readers
only (`Tm.eval`, `Tm.denote`, `Rhs.eval`, `Upd.applyV`, `UpdElem.globT`)
and the typed state's operations as `State.locV` and the global part's
fields read them.  A storage write under the box is named on the spot with
the typed laws in `Calculus/CloseFrame.lean` (above `TermLaws`, whose frame
laws it reads).
-/

namespace Solidity

open Semantics

variable {C : Contract}

/-- A result of an optional value: `none` reverts. -/
def Close.optRes {α : Type} : Option α → TRes α
  | some a => .ok a
  | none => .error .revert

namespace CloseS

/-! ## The typed state's parts

A leaf's state is a typed state, read by its global part (`State.glob`, a
field at a time) and its locals by position (`State.locV`); after an
update, a typed state it lands on, of which those two are known
(`Upd.afterT_applyV`).  The pushes, sets and pops are `Calculus/Lands.lean`'s
(`State.locV_push`, …). -/

section StateAPI

variable {Γ : Ctx}

theorem locV_havoc (σ : State C Γ) (st : Storage C) (nt : Ledger) (sb : PrimTy.uint.Denote) :
    (σ.havoc st nt sb).locV = σ.locV := rfl

/-! The global part a field at a time: the leaf reads fields, never the
global part whole, so no rewrite changes a type that depends on it. -/

theorem glob_storage (σ : State C Γ) : σ.glob.storage = σ.storage := rfl
theorem glob_net (σ : State C Γ) : σ.glob.net = σ.net := rfl
theorem glob_selfBalance (σ : State C Γ) : σ.glob.selfBalance = σ.selfBalance := rfl
theorem glob_tx (σ : State C Γ) : σ.glob.tx = σ.tx := rfl
theorem glob_envVal (σ : State C Γ) (k : EnvKey) : σ.glob.envVal k = σ.envVal k := rfl
theorem havoc_storage (σ : State C Γ) (st : Storage C) (nt : Ledger) (sb : PrimTy.uint.Denote) :
    (σ.havoc st nt sb).storage = st := rfl
theorem havoc_net (σ : State C Γ) (st : Storage C) (nt : Ledger) (sb : PrimTy.uint.Denote) :
    (σ.havoc st nt sb).net = nt := rfl
theorem havoc_selfBalance (σ : State C Γ) (st : Storage C) (nt : Ledger) (sb : PrimTy.uint.Denote) :
    (σ.havoc st nt sb).selfBalance = sb := rfl
theorem havoc_tx (σ : State C Γ) (st : Storage C) (nt : Ledger) (sb : PrimTy.uint.Denote) :
    (σ.havoc st nt sb).tx = σ.tx := rfl
theorem push_storage {t : LTy} (σ : State C Γ) (v : t.TDenote C σ.H) :
    (σ.push v).storage = σ.storage := rfl
/-- A memory array's length read through a pushed local is the state's: the
length is a number, so the rewrite changes no type that depends on the heap
typing (a premise read before a local and a goal read after it read one
length, `allLeftHide`'s instances among them). -/
theorem push_lenU {t : LTy} (σ : State C Γ) (v : t.TDenote C σ.H) {E : Ty}
    (r : HRef σ.H (.array E)) : (σ.push v).glob.memT.heap.lenU r = σ.glob.memT.heap.lenU r := rfl
theorem push_hashId {k : HashKind} {t : LTy} (σ : State C Γ) (v : t.TDenote C σ.H) (R : RefTy) (id : Nat) :
    (σ.push v).glob.memT.hashId k R id = σ.glob.memT.hashId k R id := rfl
theorem push_net {t : LTy} (σ : State C Γ) (v : t.TDenote C σ.H) : (σ.push v).net = σ.net := rfl
theorem push_selfBalance {t : LTy} (σ : State C Γ) (v : t.TDenote C σ.H) :
    (σ.push v).selfBalance = σ.selfBalance := rfl
theorem push_tx {t : LTy} (σ : State C Γ) (v : t.TDenote C σ.H) : (σ.push v).tx = σ.tx := rfl
theorem setLocal_storage {t : LTy} (σ : State C Γ) (i : Idx Γ t) (v : t.TDenote C σ.H) :
    (σ.setLocal i v).storage = σ.storage := rfl
theorem setLocal_hashId {k : HashKind} {t : LTy} (σ : State C Γ) (i : Idx Γ t) (v : t.TDenote C σ.H)
    (R : RefTy) (id : Nat) :
    (σ.setLocal i v).glob.memT.hashId k R id = σ.glob.memT.hashId k R id := rfl
theorem setLocal_net {t : LTy} (σ : State C Γ) (i : Idx Γ t) (v : t.TDenote C σ.H) :
    (σ.setLocal i v).net = σ.net := rfl
theorem setLocal_selfBalance {t : LTy} (σ : State C Γ) (i : Idx Γ t) (v : t.TDenote C σ.H) :
    (σ.setLocal i v).selfBalance = σ.selfBalance := rfl
theorem setLocal_tx {t : LTy} (σ : State C Γ) (i : Idx Γ t) (v : t.TDenote C σ.H) :
    (σ.setLocal i v).tx = σ.tx := rfl
theorem envVal_msgSender (σ : State C Γ) : σ.envVal .msgSender = σ.tx.msgSender := rfl
theorem envVal_msgValue (σ : State C Γ) : σ.envVal .msgValue = σ.tx.msgValue := rfl
theorem envVal_timestamp (σ : State C Γ) : σ.envVal .timestamp = σ.tx.timestamp := rfl
theorem envVal_selfBalance (σ : State C Γ) : σ.envVal .selfBalance = σ.selfBalance := rfl
theorem envVal_selfAddress (σ : State C Γ) : σ.envVal .selfAddress = σ.tx.selfAddress := rfl

theorem optRes_some {α : Type} (a : α) : Close.optRes (some a) = .ok a := rfl
theorem optRes_none {α : Type} : Close.optRes (none : Option α) = .error .revert := rfl
theorem optRes_bind {α β : Type} (x : Option α) (f : α → Option β) :
    Close.optRes (x.bind f) = Close.optRes x >>= fun a => Close.optRes (f a) := by
  cases x <;> rfl
theorem optRes_map {α β : Type} (x : Option α) (f : α → β) :
    Close.optRes (x.map f) = Close.optRes x >>= fun a => .ok (f a) := by
  cases x <;> rfl

theorem vden_val {p : PrimTy} {H : HTy} (v : (LTy.val p).TDenote C H) :
    LTy.VDen.ofT (C := C) (.val p) v = v := rfl
theorem vden_alias {R : RefTy} {H : HTy} (v : (LTy.alias R).TDenote C H) :
    LTy.VDen.ofT (C := C) (.alias R) v = v := rfl
theorem vden_mem {R : RefTy} {H : HTy} (v : (LTy.mem R).TDenote C H) :
    LTy.VDen.ofT (C := C) (.mem R) v = (v : Option (HRef H R)).map (·.id) := rfl
theorem vden_old {H : HTy} (v : LTy.old.TDenote C H) : LTy.VDen.ofT (C := C) .old v = v := rfl
theorem vden_oldNet {H : HTy} (v : LTy.oldNet.TDenote C H) :
    LTy.VDen.ofT (C := C) .oldNet v = v := rfl
theorem vden_kint {H : HTy} (v : LTy.kint.TDenote C H) :
    LTy.VDen.ofT (C := C) .kint v = v := rfl

end StateAPI

/-! ## Terms, one constructor at a time

Each a symbol's equation on the global part (`Calculus/CloseLemmas.lean`'s
`Close.Op2.eval_find`, …) under `Tm.eval_app*`, a local read by its
position.  An argument is an `Option`: `none` reverts.  Not stated: the
symbols under a `select` (`member`, `selectIn`, `fieldIn`, `findIn`,
`sfindIn`, `delAtIn`, `saveIn`, `atIn`), which no leaf of the strategy
reads. -/

section Terms

variable {Γ : Ctx} (σ : State C Γ)

theorem eval_pvV {p : PrimTy} (i : Idx Γ (.val p)) :
    (Tm.pvV i : Tm C Γ (.val p)).eval σ = some (σ.locV _ i) := rfl
theorem eval_pvP {R : RefTy} (i : Idx Γ (.alias R)) :
    (Tm.pvP i : Tm C Γ _).eval σ = σ.locV _ i := rfl
theorem eval_pvS (i : Idx Γ .old) : (Tm.pvS i : Tm C Γ .st).eval σ = some (σ.locV _ i) := rfl
theorem eval_pvI {R : RefTy} (i : Idx Γ (.mem R)) :
    (Tm.pvI i : Tm C Γ (.ident R)).eval σ = σ.locV _ i := rfl
theorem eval_netOf (i : Idx Γ .oldNet) (a : Tm C Γ (.val .uint)) :
    (Tm.netOf i a).eval σ = (a.eval σ).bind (Tm.netOfT (σ.locV _ i)) := rfl
theorem eval_pvZ (i : Idx Γ .kint) : (Tm.pvZ i : Tm C Γ .kint).eval σ = some (σ.locV _ i) := rfl
theorem eval_zlit (n : Int) : (Tm.app0 (.zlit n) : Tm C Γ .kint).eval σ = some n := rfl

theorem eval_lit {p : PrimTy} (v : p.Denote) :
    (Tm.app0 (.lit v) : Tm C Γ (.val p)).eval σ = some v := rfl
theorem eval_env (k : EnvKey) :
    (Tm.app0 (.env k) : Tm C Γ (.val .uint)).eval σ = some (σ.envVal k) := rfl
theorem eval_root (r : Name) {T : Ty} (h : C.rootType r = some T) :
    (Tm.app0 (.root r h) : Tm C Γ (.path T)).eval σ = some (SRef.ofRoot r h) := rfl
theorem eval_storage : (Tm.app0 .storage : Tm C Γ .st).eval σ = some σ.storage := rfl
theorem eval_mtSt : (Tm.app0 .mtSt : Tm C Γ .st).eval σ = some (Storage.init C) := rfl

theorem eval_unop (op : UnOp) {p : PrimTy} (h : op.accepts p = true) (a : Tm C Γ (.val p)) :
    (Tm.app1 (.unop op h) a).eval σ = (a.eval σ).bind (op.evalT h) := rfl
theorem eval_net (a : Tm C Γ (.val .uint)) : (Tm.app1 .net a).eval σ =
    (a.eval σ).map fun n => (lookupBy n σ.net).getD 0 := rfl
theorem eval_delValue {p : PrimTy} (a : Tm C Γ (.val p)) :
    (Tm.app1 .delValue a).eval σ = (a.eval σ).map fun _ => PrimTy.dflt p := rfl
theorem eval_field {s f : Name} {T : Ty} (h : C.fieldType s f = some T)
    (q : Tm C Γ (.path (.ref (.struct s)))) :
    (Tm.app1 (.field h) q).eval σ = (q.eval σ).map (·.field h) := rfl
theorem eval_next {E : Ty} (q : Tm C Γ (.path (.ref (.array E)))) :
    (Tm.app1 .next q).eval σ = (q.eval σ).bind σ.storage.nextT := rfl
theorem eval_sval {p : PrimTy} (t : Tm C Γ (.val p)) :
    (Tm.app1 .sval t).eval σ = (t.eval σ).map .prim := rfl
theorem eval_newArr {R : RefTy} (h : R.newArrOk = true) (t : Tm C Γ (.val .uint)) :
    (Tm.app1 (.newArr h) t).eval σ = (t.eval σ).map fun n => newArrT R n h := rfl
theorem eval_mfield {s f : Name} {T : Ty} (h : C.fieldType s f = some T)
    (i : Tm C Γ (.ident (.struct s))) :
    (Tm.app1 (.mfield h) i).eval σ = (i.eval σ).map fun id => .field id h := rfl
theorem eval_mval {p : PrimTy} (t : Tm C Γ (.val p)) :
    (Tm.app1 .mval t).eval σ = t.eval σ := rfl
theorem eval_ref {R : RefTy} (i : Tm C Γ (.ident R)) :
    (Tm.app1 (.ref (R := R)) i).eval σ = i.eval σ := rfl
theorem eval_wt (s : Tm C Γ .st) : (Tm.app1 .wt s).eval σ = (s.eval σ).bind Storage.wtT := rfl
theorem eval_cleanTail (s : Tm C Γ .st) :
    (Tm.app1 .cleanTail s).eval σ = (s.eval σ).bind Storage.cleanTailT := rfl
theorem eval_select {s : Name} (r : Name) (h : C.rootType r = some (.ref (.struct s)))
    (t : Tm C Γ .st) :
    (Tm.app1 (.select r h) t).eval σ = (t.eval σ).map fun st => Storage.selectT st h := rfl
theorem eval_toInt (a : Tm C Γ (.val .uint)) :
    (Tm.app1 .toInt a).eval σ = (a.eval σ).map fun n => n.1 := rfl
theorem eval_zbin (op : BinOp) (h : op.zArith = true) (a b : Tm C Γ .kint) :
    (Tm.app2 (.zbin op h) a b).eval σ =
      (a.eval σ).bind fun x => (b.eval σ).bind fun y => some (op.evalZ x y) := rfl
theorem eval_zcmp (op : BinOp) (h : op.zCmp = true) (a b : Tm C Γ .kint) :
    (Tm.app2 (.zcmp op h) a b).eval σ =
      (a.eval σ).bind fun x => (b.eval σ).bind fun y => some (op.cmpZ x y) := rfl

theorem eval_binop (op : BinOp) {p : PrimTy} (h : op.accepts p = true) (a b : Tm C Γ (.val p)) :
    (Tm.app2 (.binop op h) a b).eval σ = (a.eval σ).bind fun x => binopT op h x (b.eval σ) := rfl
theorem eval_find {p : PrimTy} (s : Tm C Γ .st) (q : Tm C Γ (.path (.prim p))) :
    (Tm.app2 .find s q).eval σ =
      (s.eval σ).bind fun st => (q.eval σ).bind fun r => (st.find r).bind fun v => some v.view :=
  rfl
theorem eval_sfind {T : Ty} (s : Tm C Γ .st) (q : Tm C Γ (.path T)) :
    (Tm.app2 .sfind s q).eval σ = (s.eval σ).bind fun st => (q.eval σ).bind fun r => st.find r :=
  rfl
theorem eval_delAt {T : Ty} (s : Tm C Γ .st) (q : Tm C Γ (.path T)) :
    (Tm.app2 .delAt s q).eval σ =
      (s.eval σ).bind fun st => (q.eval σ).bind fun r => st.delete r := rfl
theorem eval_at {R : RefTy} {k : PrimTy} {V : Ty} (it : IndexTy R k V)
    (q : Tm C Γ (.path (.ref R))) (i : Tm C Γ (.val k)) :
    (Tm.app2 (.at it) q i).eval σ =
      (q.eval σ).bind fun r => (i.eval σ).bind fun x => σ.storage.atT it r x := rfl
theorem eval_len {E : Ty} (s : Tm C Γ .st) (q : Tm C Γ (.path (.ref (.array E)))) :
    (Tm.app2 .len s q).eval σ = (s.eval σ).bind fun st => (q.eval σ).bind fun r => st.len r :=
  rfl
theorem eval_pushSlot {E : Ty} (s : Tm C Γ .st) (q : Tm C Γ (.path (.ref (.array E)))) :
    (Tm.app2 .pushSlot s q).eval σ =
      (s.eval σ).bind fun st => (q.eval σ).bind fun r => st.push r some := rfl
theorem eval_pop {E : Ty} (s : Tm C Γ .st) (q : Tm C Γ (.path (.ref (.array E)))) :
    (Tm.app2 .pop s q).eval σ =
      (s.eval σ).bind fun st => (q.eval σ).bind fun r => st.pop false r := rfl
theorem eval_shrink {E : Ty} (s : Tm C Γ .st) (q : Tm C Γ (.path (.ref (.array E)))) :
    (Tm.app2 .shrink s q).eval σ =
      (s.eval σ).bind fun st => (q.eval σ).bind fun r => st.pop true r := rfl
theorem eval_extend {E : Ty} (s : Tm C Γ .st) (q : Tm C Γ (.path (.ref (.array E)))) :
    (Tm.app2 .extend s q).eval σ = (s.eval σ).bind fun st => (q.eval σ).bind fun r =>
      (st.pushPlace r).bind fun x => some x.1 := rfl
theorem eval_nextIn {E : Ty} (s : Tm C Γ .st) (q : Tm C Γ (.path (.ref (.array E)))) :
    (Tm.app2 .nextIn s q).eval σ =
      (s.eval σ).bind fun st => (q.eval σ).bind fun r => st.nextT r := rfl
theorem eval_mat {R : RefTy} {E : Ty} (a : ArrTy R E) (i : Tm C Γ (.ident R))
    (k : Tm C Γ (.val .uint)) : (Tm.app2 (.mat a) i k).eval σ =
      (i.eval σ).bind fun id => (k.eval σ).bind fun j => some (.index id a j) := rfl

/-! The memory symbols, on the memory a term reads (`Grown σ.H`). -/

theorem eval_memory : (Tm.app0 .memory : Tm C Γ .mem).eval σ = some σ.glob.memT := rfl
theorem eval_alloc (R : RefTy) (h : (Ty.ref R).mapFree = true) (m : Tm C Γ .mem) :
    (Tm.app1 (.alloc R h) m).eval σ = (m.eval σ).map fun g => (g.heap.allocDefault R h).val.id :=
  rfl
theorem eval_addM (R : RefTy) (h : (Ty.ref R).mapFree = true) (m : Tm C Γ .mem) :
    (Tm.app1 (.addM R h) m).eval σ = (m.eval σ).map fun g => g.then (g.heap.allocDefault R h) :=
  rfl
theorem eval_read {p : PrimTy} (m : Tm C Γ .mem) (a : Tm C Γ (.addr (.prim p))) :
    (Tm.app2 .read m a).eval σ = (m.eval σ).bind fun g => (a.eval σ).bind fun ad => g.readT ad :=
  rfl
theorem eval_mlen {E : Ty} (m : Tm C Γ .mem) (i : Tm C Γ (.ident (.array E))) :
    (Tm.app2 .mlen m i).eval σ = (m.eval σ).bind fun g => (i.eval σ).bind fun id =>
      g.lenId E id := rfl
theorem eval_hash {k : HashKind} {R : RefTy} (m : Tm C Γ .mem) (i : Tm C Γ (.ident R)) :
    (Tm.app2 (.hash k) m i).eval σ = (m.eval σ).bind fun g => (i.eval σ).bind fun id =>
      some (g.hashId k R id) := rfl
theorem eval_copyMem {R : RefTy} (m : Tm C Γ .mem) (i : Tm C Γ (.ident R)) :
    (Tm.app2 .copyMem m i).eval σ = (m.eval σ).bind fun g => (i.eval σ).bind fun id =>
      (HRef.ofId? g.H' R id).bind fun r => some (MVal.copyMToSt g.heap (T := .ref R) r) := rfl
theorem eval_iread {R : RefTy} (m : Tm C Γ .mem) (a : Tm C Γ (.addr (.ref R))) :
    (Tm.app2 .iread m a).eval σ = (m.eval σ).bind fun g => (a.eval σ).bind fun ad =>
      (g.readT ad).bind fun (r : HRef _ R) => some r.id := rfl
theorem eval_copy {R : RefTy} (h : (Ty.ref R).mapFree = true) (m : Tm C Γ .mem)
    (v : Tm C Γ (.sv (.ref R))) : (Tm.app2 (.copy h) m v).eval σ =
      (m.eval σ).bind fun g => (v.eval σ).bind fun w => some (w.copyStToM g.heap h).val.id := rfl
theorem eval_copySt {T : Ty} (h : T.mapFree = true) (m : Tm C Γ .mem) (v : Tm C Γ (.sv T)) :
    (Tm.app2 (.copySt h) m v).eval σ =
      (m.eval σ).bind fun g => (v.eval σ).bind fun w => some (g.then (w.copyStToM g.heap h)) := rfl

theorem eval_ite {p : PrimTy} (c : Tm C Γ (.val .bool)) (a b : Tm C Γ (.val p)) :
    (Tm.app3 .ite c a b).eval σ = (c.eval σ).bind fun cv => cond cv (a.eval σ) (b.eval σ) := rfl
theorem eval_save {T : Ty} (s : Tm C Γ .st) (q : Tm C Γ (.path T)) (v : Tm C Γ (.sv T)) :
    (Tm.app3 .save s q v).eval σ = (s.eval σ).bind fun st => (q.eval σ).bind fun r =>
      (v.eval σ).bind fun w => st.write r w := rfl
theorem eval_push {E : Ty} (s : Tm C Γ .st) (q : Tm C Γ (.path (.ref (.array E))))
    (v : Tm C Γ (.sv E)) : (Tm.app3 .push s q v).eval σ = (s.eval σ).bind fun st =>
      (q.eval σ).bind fun r => st.push r fun _ => (v.eval σ).map SVal.strip := rfl
theorem eval_write {T : Ty} (m : Tm C Γ .mem) (a : Tm C Γ (.addr T)) (v : Tm C Γ (.mv T)) :
    (Tm.app3 .write m a v).eval σ = (m.eval σ).bind fun g => (a.eval σ).bind fun ad =>
      (v.eval σ).bind fun w => g.writeT ad w := rfl

theorem denote_lit {p : PrimTy} (v : p.Denote) :
    (Tm.app0 (.lit v) : Tm C Γ (.val p)).denote σ = some v := rfl
theorem denote_env (k : EnvKey) :
    (Tm.app0 (.env k) : Tm C Γ (.val .uint)).denote σ = some (σ.envVal k) := rfl
theorem denote_pvV {p : PrimTy} (i : Idx Γ (.val p)) :
    (Tm.pvV i : Tm C Γ (.val p)).denote σ = some (σ.locV _ i) := rfl
/-- An operator reads its operands' Theory values as the interpreter reads
their values (`Op2.denote`, `Op1.denote`, `Op3.denote`). -/
theorem denote_binop {p : PrimTy} (op : BinOp) (h : op.accepts p = true)
    (a b : Tm C Γ (.val p)) :
    (Tm.app2 (.binop op h) a b).denote σ =
      (a.denote σ).bind fun x => binopT op h x (b.denote σ) := rfl
theorem denote_unop {p : PrimTy} (op : UnOp) (h : op.accepts p = true) (a : Tm C Γ (.val p)) :
    (Tm.app1 (.unop op h) a).denote σ = (a.denote σ).bind (op.evalT h) := rfl
theorem denote_ite {p : PrimTy} (c : Tm C Γ (.val .bool)) (a b : Tm C Γ (.val p)) :
    (Tm.app3 .ite c a b).denote σ = (c.denote σ).bind fun x => cond x (a.denote σ) (b.denote σ) :=
  rfl

end Terms

/-! ## Updates: the global part and the locals' values

An update is computed on the state it is applied in (`Upd.applyV`, below
element by element, every right-hand side read in the state before): its
typed global part and the values it leaves in the locals (`LocsV`). -/

section Updates

variable {Γ Δ : Ctx} (σ₀ : State C Γ)

theorem rhs_val {p : PrimTy} (t : Tm C Γ (.val p)) : (Rhs.val t).eval σ₀ = t.eval σ₀ := rfl
theorem rhs_path {R : RefTy} (p : Tm C Γ (.path (.ref R))) :
    (Rhs.path p).eval σ₀ = (p.eval σ₀).map some := by
  show (p.eval σ₀).bind _ = _
  cases p.eval σ₀ <;> rfl
theorem rhs_unset {R : RefTy} : (Rhs.unset (R := R) : Rhs C Γ _).eval σ₀ = some none := rfl
theorem rhs_mref {R : RefTy} (i : Tm C Γ (.ident R)) :
    (Rhs.mref i).eval σ₀ = (i.eval σ₀).map some := by
  show (i.eval σ₀).bind _ = _
  cases i.eval σ₀ <;> rfl
theorem rhs_store (s : Tm C Γ .st) : (Rhs.store s).eval σ₀ = s.eval σ₀ := by
  show (s.eval σ₀).bind _ = _
  cases s.eval σ₀ <;> rfl
theorem rhs_saveNet : (Rhs.saveNet : Rhs C Γ _).eval σ₀ = some σ₀.net := rfl
theorem rhs_saveNetMt : (Rhs.saveNetMt : Rhs C Γ _).eval σ₀ = some [] := rfl
theorem rhs_zint (t : Tm C Γ .kint) : (Rhs.zint t).eval σ₀ = t.eval σ₀ := rfl

theorem glob_storageE (s : Tm C Γ .st) (g : GlobT C σ₀.H) :
    (UpdElem.storage s : UpdElem C Γ Δ).globT σ₀ g = (s.eval σ₀).map g.withStorage := by
  show (s.eval σ₀).bind _ = _
  cases s.eval σ₀ <;> rfl
theorem glob_memoryE (m : Tm C Γ .mem) (g : GlobT C σ₀.H) :
    (UpdElem.memory m : UpdElem C Γ Δ).globT σ₀ g = (m.eval σ₀).map g.withMem := by
  show (m.eval σ₀).bind _ = _
  cases m.eval σ₀ <;> rfl
theorem glob_selfBalanceE (op : IntOp) (a : Tm C Γ (.val .uint)) (g : GlobT C σ₀.H) :
    (UpdElem.selfBalance op a : UpdElem C Γ Δ).globT σ₀ g = (a.eval σ₀).bind fun amt =>
      (PrimTy.uint.ofInt? (op.apply σ₀.selfBalance.1 amt.1)).map g.withBalance := by
  show (a.eval σ₀).bind _ = _
  cases a.eval σ₀ with
  | none => rfl
  | some amt =>
    simp only [Option.bind_some]
    cases PrimTy.uint.ofInt? (op.apply σ₀.selfBalance.1 amt.1) <;> rfl
theorem glob_netE (r : Tm C Γ (.val .uint)) (op : IntOp) (a : Tm C Γ (.val .uint))
    (g : GlobT C σ₀.H) : (UpdElem.net r op a : UpdElem C Γ Δ).globT σ₀ g =
      (r.eval σ₀).bind fun addr => (a.eval σ₀).map fun amt =>
        g.withNet (setBy addr (op.apply ((lookupBy addr g.1.net).getD 0) amt.1) g.1.net) := by
  show (r.eval σ₀).bind _ = _
  cases r.eval σ₀ with
  | none => rfl
  | some _ => show Option.bind _ _ = _; cases a.eval σ₀ <;> rfl
theorem glob_payE (r a : Tm C Γ (.val .uint)) (g : GlobT C σ₀.H) :
    (UpdElem.pay r a : UpdElem C Γ Δ).globT σ₀ g =
      (r.eval σ₀).bind fun addr => (a.eval σ₀).bind fun amt =>
        some (g.paid σ₀ addr amt) := rfl
theorem glob_netMtE (r a : Tm C Γ (.val .uint)) (g : GlobT C σ₀.H) :
    (UpdElem.netMt r a : UpdElem C Γ Δ).globT σ₀ g =
      (r.eval σ₀).bind fun addr => (a.eval σ₀).map fun amt => g.withNet [(addr, amt.1)] := by
  show (r.eval σ₀).bind _ = _
  cases r.eval σ₀ with
  | none => rfl
  | some _ => show Option.bind _ _ = _; cases a.eval σ₀ <;> rfl
theorem glob_setBalanceE (a : Tm C Γ (.val .uint)) (g : GlobT C σ₀.H) :
    (UpdElem.setBalance a : UpdElem C Γ Δ).globT σ₀ g = (a.eval σ₀).map g.withBalance := by
  show (a.eval σ₀).bind _ = _
  cases a.eval σ₀ <;> rfl

/-! A typed global part replaced a field at a time. -/

theorem withStorage_storage {H : HTy} (g : GlobT C H) (st : Storage C) :
    (g.withStorage st).1.storage = st := rfl
theorem withStorage_net {H : HTy} (g : GlobT C H) (st : Storage C) :
    (g.withStorage st).1.net = g.1.net := rfl
theorem withStorage_selfBalance {H : HTy} (g : GlobT C H) (st : Storage C) :
    (g.withStorage st).1.selfBalance = g.1.selfBalance := rfl
theorem withStorage_tx {H : HTy} (g : GlobT C H) (st : Storage C) :
    (g.withStorage st).1.tx = g.1.tx := rfl
theorem withMem_storage {H : HTy} (g : GlobT C H) (μ : Grown H (fun _ => Unit)) :
    (g.withMem μ).1.storage = g.1.storage := rfl
theorem withMem_net {H : HTy} (g : GlobT C H) (μ : Grown H (fun _ => Unit)) :
    (g.withMem μ).1.net = g.1.net := rfl
theorem withMem_selfBalance {H : HTy} (g : GlobT C H) (μ : Grown H (fun _ => Unit)) :
    (g.withMem μ).1.selfBalance = g.1.selfBalance := rfl
theorem withMem_tx {H : HTy} (g : GlobT C H) (μ : Grown H (fun _ => Unit)) :
    (g.withMem μ).1.tx = g.1.tx := rfl
theorem withStorage_hashId {k : HashKind} {H : HTy} (g : GlobT C H) (st : Storage C) (R : RefTy) (id : Nat) :
    (g.withStorage st).1.memT.hashId k R id = g.1.memT.hashId k R id := rfl
theorem withNet_hashId {k : HashKind} {H : HTy} (g : GlobT C H) (nt : Ledger) (R : RefTy) (id : Nat) :
    (g.withNet nt).1.memT.hashId k R id = g.1.memT.hashId k R id := rfl
theorem withBalance_hashId {k : HashKind} {H : HTy} (g : GlobT C H) (b : PrimTy.uint.Denote) (R : RefTy)
    (id : Nat) : (g.withBalance b).1.memT.hashId k R id = g.1.memT.hashId k R id := rfl
theorem withNet_storage {H : HTy} (g : GlobT C H) (nt : Ledger) :
    (g.withNet nt).1.storage = g.1.storage := rfl
theorem withNet_net {H : HTy} (g : GlobT C H) (nt : Ledger) :
    (g.withNet nt).1.net = nt := rfl
theorem withNet_selfBalance {H : HTy} (g : GlobT C H) (nt : Ledger) :
    (g.withNet nt).1.selfBalance = g.1.selfBalance := rfl
theorem withNet_tx {H : HTy} (g : GlobT C H) (nt : Ledger) :
    (g.withNet nt).1.tx = g.1.tx := rfl
theorem withBalance_storage {H : HTy} (g : GlobT C H) (b : PrimTy.uint.Denote) :
    (g.withBalance b).1.storage = g.1.storage := rfl
theorem withBalance_net {H : HTy} (g : GlobT C H) (b : PrimTy.uint.Denote) :
    (g.withBalance b).1.net = g.1.net := rfl
theorem withBalance_selfBalance {H : HTy} (g : GlobT C H) (b : PrimTy.uint.Denote) :
    (g.withBalance b).1.selfBalance = b := rfl
theorem withBalance_tx {H : HTy} (g : GlobT C H) (b : PrimTy.uint.Denote) :
    (g.withBalance b).1.tx = g.1.tx := rfl
theorem globG_val {Γ : Ctx} (σ : State C Γ) : σ.globG.1 = σ.glob := rfl

theorem applyV_nil : (Upd.nil : Upd C Γ Γ).applyV σ₀ = some (σ₀.globG, σ₀.locV) := rfl
theorem applyV_snoc (U : Upd C Γ Δ) (e : UpdElem C Γ Δ) :
    (U.snoc e).applyV σ₀ = (U.applyV σ₀).bind fun p => e.applyV σ₀ p.1 p.2 := rfl
theorem applyV_decl {t : LTy} (U : Upd C Γ Δ) (x : Var) (r : Rhs C Γ t) :
    (U.decl x r).applyV σ₀ =
      (U.applyV σ₀).bind fun p => (r.eval σ₀).bind fun v => some (p.1, p.2.push v) := rfl
theorem applyV_pop {Δ' : Ctx} (U : Upd C Γ Δ) (h : Ext Δ' Δ) :
    (U.pop h).applyV σ₀ = (U.applyV σ₀).bind fun p => some (p.1, p.2.drop h) := rfl
theorem applyV_drop {Δ' : Ctx} (U : Upd C Γ Δ) (h : Thin Δ' Δ) :
    (U.drop h).applyV σ₀ = (U.applyV σ₀).bind fun p => some (p.1, p.2.thin h) := rfl

theorem elem_local {t : LTy} (i : Idx Δ t) (r : Rhs C Γ t) (g : GlobT C σ₀.H) (ℓ : LocsV C Δ) :
    (UpdElem.local i r).applyV σ₀ g ℓ = (r.eval σ₀).bind fun v => some (g, ℓ.set i v) := rfl
theorem elem_storage (s : Tm C Γ .st) (g : GlobT C σ₀.H) (ℓ : LocsV C Δ) :
    (UpdElem.storage s : UpdElem C Γ Δ).applyV σ₀ g ℓ =
      ((UpdElem.storage s : UpdElem C Γ Δ).globT σ₀ g).bind fun g' => some (g', ℓ) := rfl
theorem elem_memory (m : Tm C Γ .mem) (g : GlobT C σ₀.H) (ℓ : LocsV C Δ) :
    (UpdElem.memory m : UpdElem C Γ Δ).applyV σ₀ g ℓ =
      ((UpdElem.memory m : UpdElem C Γ Δ).globT σ₀ g).bind fun g' => some (g', ℓ) := rfl
theorem elem_selfBalance (op : IntOp) (a : Tm C Γ (.val .uint)) (g : GlobT C σ₀.H)
    (ℓ : LocsV C Δ) : (UpdElem.selfBalance op a : UpdElem C Γ Δ).applyV σ₀ g ℓ =
      ((UpdElem.selfBalance op a : UpdElem C Γ Δ).globT σ₀ g).bind fun g' => some (g', ℓ) := rfl
theorem elem_net (r : Tm C Γ (.val .uint)) (op : IntOp) (a : Tm C Γ (.val .uint))
    (g : GlobT C σ₀.H) (ℓ : LocsV C Δ) : (UpdElem.net r op a : UpdElem C Γ Δ).applyV σ₀ g ℓ =
      ((UpdElem.net r op a : UpdElem C Γ Δ).globT σ₀ g).bind fun g' => some (g', ℓ) := rfl
theorem elem_pay (r a : Tm C Γ (.val .uint)) (g : GlobT C σ₀.H) (ℓ : LocsV C Δ) :
    (UpdElem.pay r a : UpdElem C Γ Δ).applyV σ₀ g ℓ =
      ((UpdElem.pay r a : UpdElem C Γ Δ).globT σ₀ g).bind fun g' => some (g', ℓ) := rfl
theorem elem_netMt (r a : Tm C Γ (.val .uint)) (g : GlobT C σ₀.H) (ℓ : LocsV C Δ) :
    (UpdElem.netMt r a : UpdElem C Γ Δ).applyV σ₀ g ℓ =
      ((UpdElem.netMt r a : UpdElem C Γ Δ).globT σ₀ g).bind fun g' => some (g', ℓ) := rfl
theorem elem_setBalance (a : Tm C Γ (.val .uint)) (g : GlobT C σ₀.H) (ℓ : LocsV C Δ) :
    (UpdElem.setBalance a : UpdElem C Γ Δ).applyV σ₀ g ℓ =
      ((UpdElem.setBalance a : UpdElem C Γ Δ).globT σ₀ g).bind fun g' => some (g', ℓ) := rfl

/-! The locals an update leaves, by position. -/

theorem push_here {t : LTy} (ℓ : LocsV C Δ) (v : t.VDen C) : ℓ.push v t .here = v := rfl
theorem push_there {t u : LTy} (ℓ : LocsV C Δ) (v : t.VDen C) (i : Idx Δ u) :
    ℓ.push v u (.there i) = ℓ u i := rfl
theorem set_here_here {t : LTy} (ℓ : LocsV C (t :: Δ)) (v : t.VDen C) :
    ℓ.set .here v t .here = v := LocsV.set_same ℓ .here v
theorem set_here_there {t u : LTy} (ℓ : LocsV C (t :: Δ)) (v : t.VDen C) (j : Idx Δ u) :
    ℓ.set .here v u (.there j) = ℓ u (.there j) :=
  LocsV.set_ne ℓ .here (.there j) (fun h => nomatch h) v
theorem set_there_here {t u : LTy} (ℓ : LocsV C (u :: Δ)) (i : Idx Δ t) (v : t.VDen C) :
    ℓ.set (.there i) v u .here = ℓ u .here :=
  LocsV.set_ne ℓ (.there i) .here (fun h => nomatch h) v
theorem set_there_there {t u w : LTy} (ℓ : LocsV C (w :: Δ)) (i : Idx Δ t) (v : t.VDen C)
    (j : Idx Δ u) :
    ℓ.set (.there i) v u (.there j) = LocsV.set (fun _ k => ℓ _ (.there k)) i v u j := by
  by_cases h : i.toNat = j.toNat
  · obtain rfl := Idx.ty_eq_of_toNat h
    obtain rfl := Idx.toNat_inj i j h
    rw [LocsV.set_same, LocsV.set_same]
  · rw [LocsV.set_ne _ _ _ h,
      LocsV.set_ne _ (.there i) (.there j) (fun h' => h (Nat.add_right_cancel h'))]
/-! The locals an update leaves kept as a stack of pushes over the state's
own (`set` and `drop` absorbed): a read is then a walk down the stack. -/

theorem set_push_here {t : LTy} (ℓ : LocsV C Δ) (w v : t.VDen C) :
    (ℓ.push w).set .here v = ℓ.push v := by
  funext u j
  cases j with
  | here => exact LocsV.set_same _ _ _
  | there j => exact LocsV.set_ne _ .here (.there j) (by simp only [Idx.toNat]; omega) v
theorem set_push_there {t u : LTy} (ℓ : LocsV C Δ) (w : u.VDen C) (i : Idx Δ t) (v : t.VDen C) :
    (ℓ.push w).set (.there i) v = (ℓ.set i v).push w := by
  funext u' j
  cases j with
  | here => exact LocsV.set_ne _ (.there i) .here (by simp only [Idx.toNat]; omega) v
  | there j =>
    by_cases h : i.toNat = j.toNat
    · obtain rfl := Idx.ty_eq_of_toNat h
      obtain rfl := Idx.toNat_inj i j h
      rw [LocsV.set_same]
      exact (LocsV.set_same _ _ _).symm
    · rw [LocsV.set_ne _ (.there i) (.there j) (fun h' => h (Nat.add_right_cancel h'))]
      exact (LocsV.set_ne ℓ i j h v).symm
theorem drop_refl' (ℓ : LocsV C Δ) : ℓ.drop .refl = ℓ := rfl
theorem drop_push' {Δ' : Ctx} {t : LTy} (h : Ext Δ' Δ) (ℓ : LocsV C Δ) (w : t.VDen C) :
    (ℓ.push w).drop (.push h) = ℓ.drop h := rfl
theorem thin_refl' (ℓ : LocsV C Δ) : ℓ.thin .refl = ℓ := rfl
theorem thin_keep' {Δ' : Ctx} {t : LTy} (h : Thin Δ' Δ) (ℓ : LocsV C Δ) (w : t.VDen C) :
    (ℓ.push w).thin (.keep h) = (ℓ.thin h).push w := by
  funext u j
  cases j <;> rfl
theorem thin_drop' {Δ' : Ctx} {t : LTy} (h : Thin Δ' Δ) (ℓ : LocsV C Δ) (w : t.VDen C) :
    (ℓ.push w).thin (.drop h) = ℓ.thin h := rfl

theorem drop_apply {Δ' : Ctx} {t : LTy} (h : Ext Δ' Δ) (ℓ : LocsV C Δ) (i : Idx Δ' t) :
    ℓ.drop h t i = ℓ t (i.ext h) := rfl
theorem thin_apply {Δ' : Ctx} {t : LTy} (h : Thin Δ' Δ) (ℓ : LocsV C Δ) (i : Idx Δ' t) :
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

/-- A typed unsigned value, including an anonymous local, retains its range. -/
theorem uintRange (a : PrimTy.uint.Denote) : 0 ≤ a.val ∧
    a.val < 115792089237316195423570985008687907853269984665640564039457584007913129639936 := by
  have h : PrimTy.uint.inRange a.val = true := a.property
  simp only [PrimTy.inRange, decide_eq_true_eq] at h
  exact h

/-- A typed signed value retains its range when read through a dependent function. -/
theorem intRange (a : PrimTy.int.Denote) :
    -57896044618658097711785492504343953926634992332820282019728792003956564819968 ≤ a.val ∧
    a.val < 57896044618658097711785492504343953926634992332820282019728792003956564819968 := by
  have h : PrimTy.int.inRange a.val = true := a.property
  simp only [PrimTy.inRange, decide_eq_true_eq] at h
  exact h
theorem ofLit_uint (n : Int) (h : PrimTy.uint.inRange n = true) :
    PrimTy.ofLit .uint n h = (⟨n, h⟩ : {n : Int // PrimTy.uint.inRange n = true}) := rfl
theorem ofLit_int (n : Int) (h : PrimTy.int.inRange n = true) :
    PrimTy.ofLit .int n h = (⟨n, h⟩ : {n : Int // PrimTy.int.inRange n = true}) := rfl

/-! The typed operators at their operand types, so a closer leaf's
arithmetic is `Int` arithmetic under a range check.  A checked result is
`if inRange then some (uintOf n) else none`, with no proof inside: an
`uintOf n` the leaf meets under its range reads back as `n`
(`uintOf_val`), and nothing depends on the check's proof, so `simp`'s
`exists_eq_left'`/`forall_eq'` take it apart. -/

/-- `n` as a `uint`, `0` out of range: `ofInt?`'s value without the proof. -/
def uintOf (n : Int) : PrimTy.uint.Denote :=
  if h : PrimTy.uint.inRange n = true then ⟨n, h⟩ else ⟨0, by decide⟩
/-- `n` as an `int`, `0` out of range. -/
def intOf (n : Int) : PrimTy.int.Denote :=
  if h : PrimTy.int.inRange n = true then ⟨n, h⟩ else ⟨0, by decide⟩

theorem uintOf_val {n : Int} (h : 0 ≤ n ∧ n < uintBound) : (uintOf n).val = n := by
  have h' : PrimTy.uint.inRange n = true := by
    simp only [PrimTy.inRange, decide_eq_true_eq]; exact h
  simp only [uintOf, h', dite_true]
theorem intOf_val {n : Int} (h : -intBound ≤ n ∧ n < intBound) : (intOf n).val = n := by
  have h' : PrimTy.int.inRange n = true := by
    simp only [PrimTy.inRange, decide_eq_true_eq]; exact h
  simp only [intOf, h', dite_true]
/-- `uintOf_val` for every `n`: the closer's form, which `grind` splits. -/
theorem uintOf_val' (n : Int) :
    (uintOf n).val = if 0 ≤ n ∧ n < uintBound then n else 0 := by
  by_cases h : 0 ≤ n ∧ n < uintBound
  · rw [if_pos h, uintOf_val h]
  · have h' : ¬PrimTy.uint.inRange n = true := by
      simp only [PrimTy.inRange, decide_eq_true_eq]; exact h
    simp only [uintOf, h', Bool.false_eq_true, dite_false, if_neg h]
theorem intOf_val' (n : Int) :
    (intOf n).val = if -intBound ≤ n ∧ n < intBound then n else 0 := by
  by_cases h : -intBound ≤ n ∧ n < intBound
  · rw [if_pos h, intOf_val h]
  · have h' : ¬PrimTy.int.inRange n = true := by
      simp only [PrimTy.inRange, decide_eq_true_eq]; exact h
    simp only [intOf, h', Bool.false_eq_true, dite_false, if_neg h]
theorem eq_uintOf' (n : Int) (a : PrimTy.uint.Denote) :
    a = uintOf n ↔ a.val = if 0 ≤ n ∧ n < uintBound then n else 0 :=
  ⟨fun e => e ▸ uintOf_val' n, fun e => Subtype.ext (e.trans (uintOf_val' n).symm)⟩
theorem eq_intOf' (n : Int) (a : PrimTy.int.Denote) :
    a = intOf n ↔ a.val = if -intBound ≤ n ∧ n < intBound then n else 0 :=
  ⟨fun e => e ▸ intOf_val' n, fun e => Subtype.ext (e.trans (intOf_val' n).symm)⟩
theorem root_ofRoot {T : Ty} (r : Name) (h : C.rootType r = some T) :
    (SRef.ofRoot r h).root = r := rfl
/-- A key of a mapping at a root: always a slot (`inBounds` at `map`), so
two reads of `balances[0]` name the same reference, before a write and after. -/
theorem atT_map_root {k : PrimTy} {V : Ty} (st : Storage C) (r : Name)
    (h : C.rootType r = some (Ty.ref (RefTy.mapping k V))) (i : k.Denote) :
    st.atT IndexTy.map (SRef.ofRoot r h) i =
      some ((SRef.ofRoot r h).index IndexTy.map i) := rfl
theorem getD_ite {α : Type} {c : Prop} [Decidable c] (x y : Option α) (d : α) :
    (if c then x else y).getD d = if c then x.getD d else y.getD d := by
  split <;> rfl
theorem uint_eq_iff (a b : PrimTy.uint.Denote) : a = b ↔ a.val = b.val :=
  ⟨fun e => e ▸ rfl, Subtype.ext⟩
theorem int_eq_iff (a b : PrimTy.int.Denote) : a = b ↔ a.val = b.val :=
  ⟨fun e => e ▸ rfl, Subtype.ext⟩
/-- A `bool` word's equation at `Bool`, where the `Bool` lemmas
(`decide_eq_true_eq`, …) read it: an equation of denotations is at
`PrimTy.bool.Denote`, which they do not see through. -/
theorem bool_eq_iff (a b : PrimTy.bool.Denote) : @Eq PrimTy.bool.Denote a b ↔ @Eq Bool a b :=
  Iff.rfl
/-- A stored word against a value: their integers (`Shape (.prim p)` is the
value's type, which `uint_eq_iff` does not see through). -/
theorem view_eq_uint (x : SVal (.prim .uint)) (b : PrimTy.uint.Denote) :
    @Eq (Shape (.prim .uint)) x.view b ↔ (x.view : PrimTy.uint.Denote).val = b.val :=
  uint_eq_iff _ _
theorem view_eq_int (x : SVal (.prim .int)) (b : PrimTy.int.Denote) :
    @Eq (Shape (.prim .int)) x.view b ↔ (x.view : PrimTy.int.Denote).val = b.val :=
  int_eq_iff _ _
theorem root_field {s f : Name} {T : Ty} (r : SRef C (.ref (.struct s)))
    (h : C.fieldType s f = some T) : (r.field h).root = r.root := rfl
theorem root_index {R : RefTy} {k : PrimTy} {V : Ty} (r : SRef C (.ref R)) (it : IndexTy R k V)
    (i : k.Denote) : (r.index it i).root = r.root := rfl
/-- A checked index: the check, then the slot's reference, so two reads of
`values[1]` name the same reference whatever the storage they check in. -/
theorem atT_bind {R : RefTy} {k : PrimTy} {V : Ty} (st : Storage C) (it : IndexTy R k V)
    (r : SRef C (.ref R)) (i : k.Denote) :
    st.atT it r i = (st.checkIndex r it i).bind fun _ => some (r.index it i) :=
  rfl
theorem ofInt?_uint (n : Int) : PrimTy.uint.ofInt? n =
    if 0 ≤ n ∧ n < uintBound then some (uintOf n) else none := by
  by_cases h : 0 ≤ n ∧ n < uintBound
  · have h' : PrimTy.uint.inRange n = true := by
      simp only [PrimTy.inRange, decide_eq_true_eq]; exact h
    simp only [PrimTy.ofInt?, h', dite_true, if_pos h, uintOf]
  · have h' : ¬PrimTy.uint.inRange n = true := by
      simp only [PrimTy.inRange, decide_eq_true_eq]; exact h
    simp only [PrimTy.ofInt?, h', Bool.false_eq_true, dite_false, if_neg h]
theorem ofInt?_int (n : Int) : PrimTy.int.ofInt? n =
    if -intBound ≤ n ∧ n < intBound then some (intOf n) else none := by
  by_cases h : -intBound ≤ n ∧ n < intBound
  · have h' : PrimTy.int.inRange n = true := by
      simp only [PrimTy.inRange, decide_eq_true_eq]; exact h
    simp only [PrimTy.ofInt?, h', dite_true, if_pos h, intOf]
  · have h' : ¬PrimTy.int.inRange n = true := by
      simp only [PrimTy.inRange, decide_eq_true_eq]; exact h
    simp only [PrimTy.ofInt?, h', Bool.false_eq_true, dite_false, if_neg h]
theorem optRes_ite_ok {α : Type} {c : Prop} [Decidable c] (x a : α) :
    Close.optRes (if c then some x else none) = .ok a ↔ x = a ∧ c := by
  by_cases hc : c
  · simp only [hc, ite_true, optRes_some, Except.ok.injEq, and_true]
  · simp only [hc, ite_false, optRes_none, reduceCtorEq, and_false]
theorem optRes_ite {α : Type} {c : Prop} [Decidable c] (x y : Option α) :
    Close.optRes (if c then x else y) = if c then Close.optRes x else Close.optRes y :=
  apply_ite _ _ _ _

theorem binopT_uint (op : BinOp) (h : op.accepts .uint = true) (a : PrimTy.uint.Denote)
    (y : Option PrimTy.uint.Denote) :
    binopT op h a y = y.bind fun b => BinOp.evalNum .uint rfl a.1 b.1 op h := by
  cases op <;> rfl
theorem binopT_int (op : BinOp) (h : op.accepts .int = true) (a : PrimTy.int.Denote)
    (y : Option PrimTy.int.Denote) :
    binopT op h a y = y.bind fun b => BinOp.evalNum .int rfl a.1 b.1 op h := by
  cases op <;> rfl
theorem binopT_and (h : BinOp.and.accepts .bool = true) (a : PrimTy.bool.Denote)
    (y : Option PrimTy.bool.Denote) :
    binopT .and h a y = if a = true then y.bind (fun b => some (a && b)) else some false := by
  cases a <;> rfl
theorem binopT_or (h : BinOp.or.accepts .bool = true) (a : PrimTy.bool.Denote)
    (y : Option PrimTy.bool.Denote) :
    binopT .or h a y = if a = true then some true else y.bind (fun b => some (a || b)) := by
  cases a <;> rfl
theorem binopT_bool (op : BinOp) (h : op.accepts .bool = true) (h₁ : op ≠ .and) (h₂ : op ≠ .or)
    (a : PrimTy.bool.Denote) (y : Option PrimTy.bool.Denote) :
    binopT op h a y = y.bind fun b => BinOp.evalBool a b op h := by
  cases op <;> first | rfl | exact absurd rfl h₁ | exact absurd rfl h₂
theorem evalT_uint (op : BinOp) (h : op.accepts .uint = true) (a b : PrimTy.uint.Denote) :
    op.evalT h a b = BinOp.evalNum .uint rfl a.1 b.1 op h := rfl
theorem evalT_int (op : BinOp) (h : op.accepts .int = true) (a b : PrimTy.int.Denote) :
    op.evalT h a b = BinOp.evalNum .int rfl a.1 b.1 op h := rfl
theorem evalT_bool (op : BinOp) (h : op.accepts .bool = true) (a b : PrimTy.bool.Denote) :
    op.evalT h a b = BinOp.evalBool a b op h := rfl
theorem uint_eq_mk (a : PrimTy.uint.Denote) (n : Int) (h : PrimTy.uint.inRange n = true) :
    a = (⟨n, h⟩ : {n : Int // PrimTy.uint.inRange n = true}) ↔ a.val = n :=
  ⟨fun e => e ▸ rfl, fun e => Subtype.ext e⟩
theorem int_eq_mk (a : PrimTy.int.Denote) (n : Int) (h : PrimTy.int.inRange n = true) :
    a = (⟨n, h⟩ : {n : Int // PrimTy.int.inRange n = true}) ↔ a.val = n :=
  ⟨fun e => e ▸ rfl, fun e => Subtype.ext e⟩
theorem mk_eq_uint (a : PrimTy.uint.Denote) (n : Int) (h : PrimTy.uint.inRange n = true) :
    @Eq PrimTy.uint.Denote ⟨n, h⟩ a ↔ n = a.val :=
  ⟨fun e => e ▸ rfl, fun e => Subtype.ext e⟩
theorem mk_eq_int (a : PrimTy.int.Denote) (n : Int) (h : PrimTy.int.inRange n = true) :
    @Eq PrimTy.int.Denote ⟨n, h⟩ a ↔ n = a.val :=
  ⟨fun e => e ▸ rfl, fun e => Subtype.ext e⟩
/-- A natural literal cast to an integer is the integer literal: the bounds
`uintBound`, `intBound` and the bitwise results then compare by the
literal simprocs (`Int.reduceLT`), not by unfolding the cast. -/
theorem natCast_ofNat (n : Nat) : ((no_index (OfNat.ofNat n) : Nat) : Int) = OfNat.ofNat n := rfl

/-! ## The leaf, as `holds` reads it -/

section Leaf

variable {Γ : Ctx}

/-- A scoped leaf is valid where it holds in every typed state. -/
theorem valid_of_holds {φ : Fml C []} (h : ∀ σ : State C [], holds σ φ) : Fml.Valid φ := h

theorem holds_tt (σ : State C Γ) : holds σ (.tt : Fml C Γ) ↔ True := Iff.rfl
theorem holds_not (σ : State C Γ) (φ : Fml C Γ) : holds σ (.not φ) ↔ ¬ holds σ φ := Iff.rfl
theorem holds_and (σ : State C Γ) (φ ψ : Fml C Γ) :
    holds σ (.and φ ψ) ↔ holds σ φ ∧ holds σ ψ := Iff.rfl
theorem holds_imp (σ : State C Γ) (φ ψ : Fml C Γ) :
    holds σ (.imp φ ψ) ↔ (holds σ φ → holds σ ψ) := Iff.rfl
theorem holds_eq {p : PrimTy} (σ : State C Γ) (a b : Tm C Γ (.val p)) :
    holds σ (.eq a b) ↔ a.denote σ = b.denote σ := Iff.rfl
/-- An equation of two values the Theory reads as the interpreter does
(`Tm.agreeB`, `Calculus/TermAgree.lean`), marked so by `sol_close_unwrap`
(`Fml.eqA`, `Calculus/EvalEqs.lean`): both return one value, or both halt. -/
theorem holds_eqA {p : PrimTy} (σ : State C Γ) (a b : Tm C Γ (.val p))
    (h : (a.agreeB && b.agreeB) = true) :
    holds σ (Fml.eqA a b h) ↔ (Modality.diamond.wp (Close.optRes (a.eval σ)) fun x =>
      Modality.diamond.wp (Close.optRes (b.eval σ)) fun y => x = y) ∨
      (a.eval σ = none ∧ b.eval σ = none) := by
  simp only [Bool.and_eq_true] at h
  show holds σ (.eq a b) ↔ _
  rw [holds_eq_of_agree h.1 h.2 σ]
  cases a.eval σ <;> cases b.eval σ <;>
    simp only [Close.optRes, Modality.wp, Modality.onHalt, Option.some.injEq, reduceCtorEq,
      and_self, or_true, false_or, or_false, and_false, false_and]

/-- `CloseS.holds_eqA` where a side returns in every state (`Fml.eqT`): both
return, with one value. -/
theorem holds_eqT {p : PrimTy} (σ : State C Γ) (a b : Tm C Γ (.val p))
    (h : (a.agreeB && b.agreeB && (a.totB || b.totB)) = true) :
    holds σ (Fml.eqT a b h) ↔ Modality.diamond.wp (Close.optRes (a.eval σ)) fun x =>
      Modality.diamond.wp (Close.optRes (b.eval σ)) fun y => x = y := by
  have hab : (a.agreeB && b.agreeB) = true := by
    simp only [Bool.and_eq_true] at h ⊢; exact h.1
  have ht : (a.totB || b.totB) = true := by
    simp only [Bool.and_eq_true] at h; exact h.2
  show holds σ (Fml.eqA a b hab) ↔ _
  rw [holds_eqA]
  have hn : ¬ (a.eval σ = none ∧ b.eval σ = none) := by
    rintro ⟨h₁, h₂⟩
    rcases Bool.or_eq_true_iff.1 ht with h | h
    · obtain ⟨v, hv⟩ := Tm.totB_total h σ
      rw [h₁] at hv; cases hv
    · obtain ⟨v, hv⟩ := Tm.totB_total h σ
      rw [h₂] at hv; cases hv
  simp only [hn, or_false]

/-- An equation of atoms (`Fml.eqAtom`, marked by `sol_close_unwrap`): both
return, with one value. -/
theorem holds_eqAtom {p : PrimTy} (σ : State C Γ) (x y : Fml.Atom C Γ p) :
    holds σ (Fml.eqAtom x y) ↔ Modality.diamond.wp (Close.optRes (x.tm.eval σ)) fun u =>
      Modality.diamond.wp (Close.optRes (y.tm.eval σ)) fun w => u = w := by
  obtain ⟨u, hu⟩ := x.eval_some σ
  obtain ⟨w, hw⟩ := y.eval_some σ
  show holds σ (.eq x.tm y.tm) ↔ _
  rw [holds_eq_of_eval hu hw, hu, hw]
  simp only [Close.optRes, Modality.wp]

theorem holds_wellFormed (σ : State C Γ) (s : Tm C Γ .st) :
    holds σ (.wellFormed s) ↔
      Modality.diamond.wp (Close.optRes ((Tm.app1 .wt s).eval σ)) fun _ => True := by
  rw [Solidity.holds_wellFormed_eval]
  cases (Tm.app1 .wt s).eval σ <;> simp only [Close.optRes, ne_eq, not_true_eq_false, reduceCtorEq,
    not_false_eq_true, Modality.wp, Modality.onHalt]

/-- A typed state an update lands on: the global part `g`, the locals `ℓ`
(`Upd.afterT_applyV`).  What it reads is in its type, so a plain rewrite
reads it (`Landed.storage_eq`, `Landed.locV_eq`, …): no contextual pass, no
hypothesis. -/
structure Landed {Δ : Ctx} (g : State C []) (ℓ : LocsV C Δ) : Type where
  /-- The state landed on. -/
  val : State C Δ
  glob_eq : val.glob = g
  locV_eq : val.locV = ℓ

theorem Landed.storage_eq {Δ : Ctx} {g : State C []} {ℓ : LocsV C Δ} (x : Landed g ℓ) :
    x.val.storage = g.storage := congrArg State.storage x.glob_eq
theorem Landed.net_eq {Δ : Ctx} {g : State C []} {ℓ : LocsV C Δ} (x : Landed g ℓ) :
    x.val.net = g.net := congrArg State.net x.glob_eq
theorem Landed.selfBalance_eq {Δ : Ctx} {g : State C []} {ℓ : LocsV C Δ} (x : Landed g ℓ) :
    x.val.selfBalance = g.selfBalance := congrArg State.selfBalance x.glob_eq
theorem Landed.tx_eq {Δ : Ctx} {g : State C []} {ℓ : LocsV C Δ} (x : Landed g ℓ) :
    x.val.tx = g.tx := congrArg State.tx x.glob_eq
theorem Landed.hashId_eq {k : HashKind} {Δ : Ctx} {g : State C []} {ℓ : LocsV C Δ} (x : Landed g ℓ)
    (R : RefTy) (id : Nat) : x.val.glob.memT.hashId k R id = g.memT.hashId k R id := by
  rw [x.glob_eq]

/-- `p` of every typed state that lands on `g` and `ℓ`: a constant, not a
binder, so that `simp` tries no binder lemma at it (`forall_const` and its
kin, which ask an instance of every binder's type) and only enters its
body; unfolded at the end (`landedAll_def`). -/
def LandedAll {Δ : Ctx} (g : State C []) (ℓ : LocsV C Δ) (p : Landed g ℓ → Prop) : Prop :=
  ∀ x, p x

theorem landedAll_def {Δ : Ctx} (g : State C []) (ℓ : LocsV C Δ) (p : Landed g ℓ → Prop) :
    LandedAll g ℓ p ↔ ∀ x, p x := Iff.rfl

/-- A landed state the rest no longer reads: only whether there is one. -/
theorem landedAll_const {Δ : Ctx} (g : State C []) (ℓ : LocsV C Δ) (P : Prop) :
    LandedAll g ℓ (fun _ => P) ↔ (Nonempty (Landed g ℓ) → P) :=
  ⟨fun h ⟨x⟩ => h x, fun h x => h ⟨x⟩⟩

/-- The actual state witnesses its own global/local observations. -/
theorem landed_nonempty (σ : State C Δ) : Nonempty (Landed σ.glob σ.locV) :=
  ⟨⟨σ, rfl, rfl⟩⟩

/-- Capturing a primitive value cannot make representable locals unrealizable. -/
theorem landed_nonempty_push_val {Δ : Ctx} {g : State C []} {ℓ : LocsV C Δ}
    {p : PrimTy} (v : p.Denote) (h : Nonempty (Landed g ℓ)) :
    Nonempty (Landed g (ℓ.push (t := .val p) v)) := by
  obtain ⟨x⟩ := h
  refine ⟨⟨x.val.push v, x.glob_eq, ?_⟩⟩
  rw [State.locV_push, x.locV_eq]
  rfl

/-- A primitive capture is realizable exactly when the preceding locals are. -/
theorem landed_nonempty_push_val_iff {Δ : Ctx} {g : State C []} {ℓ : LocsV C Δ}
    {p : PrimTy} (v : p.Denote) :
    Nonempty (Landed g (ℓ.push (t := .val p) v)) ↔ Nonempty (Landed g ℓ) := by
  constructor
  · rintro ⟨x⟩
    refine ⟨⟨x.val.drop (.push .refl), x.glob_eq, ?_⟩⟩
    rw [State.locV_drop, x.locV_eq]
    rfl
  · exact landed_nonempty_push_val v

/-- Specialize the primitive type so the simplifier can recover its dependent value. -/
theorem landed_nonempty_push_uint {Δ : Ctx} {g : State C []} {ℓ : LocsV C Δ}
    (v : PrimTy.uint.Denote) :
    Nonempty (Landed g (ℓ.push (t := .val .uint) v)) ↔ Nonempty (Landed g ℓ) :=
  landed_nonempty_push_val_iff v

/-- Specialize the primitive type so the simplifier can recover its dependent value. -/
theorem landed_nonempty_push_int {Δ : Ctx} {g : State C []} {ℓ : LocsV C Δ}
    (v : PrimTy.int.Denote) :
    Nonempty (Landed g (ℓ.push (t := .val .int) v)) ↔ Nonempty (Landed g ℓ) :=
  landed_nonempty_push_val_iff v

/-- Specialize the primitive type so the simplifier can recover its dependent value. -/
theorem landed_nonempty_push_bool {Δ : Ctx} {g : State C []} {ℓ : LocsV C Δ}
    (v : PrimTy.bool.Denote) :
    Nonempty (Landed g (ℓ.push (t := .val .bool) v)) ↔ Nonempty (Landed g ℓ) :=
  landed_nonempty_push_val_iff v

/-- What follows an update, read in every typed state it lands on: a
constant, so that `simp` reads it only once the update's result is known
(`landedRest_def`), not first with the result abstract. -/
def LandedRest {H : HTy} {Δ : Ctx} (φ : Fml C Δ) (q : GlobT C H × LocsV C Δ) : Prop :=
  LandedAll q.1.1 q.2 fun x => holds x.val φ

theorem landedRest_def {H : HTy} {Δ : Ctx} (φ : Fml C Δ) (g : GlobT C H) (ℓ : LocsV C Δ) :
    LandedRest φ (g, ℓ) ↔ LandedAll g.1 ℓ fun x => holds x.val φ := Iff.rfl

/-- **An update's rest**, read in every typed state it lands on
(`Upd.afterT_applyV`): one with the global part and the locals the update
leaves. -/
theorem holds_upd {Δ : Ctx} (σ : State C Γ) (m : Modality) (U : Upd C Γ Δ) (φ : Fml C Δ) :
    holds σ (.upd m U φ) ↔
      m.wp (Close.optRes (U.applyV σ)) (LandedRest φ) ∨ (m = .diamond ∧ U.exh σ = true) := by
  show U.afterT m σ (holds · φ) ↔ _
  rw [Upd.afterT_applyV]
  cases ha : U.applyV σ with
  | none =>
    cases m with
    | box => exact ⟨fun _ => .inl trivial, fun _ => .inl trivial⟩
    | diamond =>
      show False ∨ _ ↔ False ∨ _
      simp only [false_or, true_and]
  | some q =>
    have hx : U.exh σ = false :=
      Upd.exh_of_globT (Upd.applyV_ok U ha).1
    simp only [hx, Bool.false_eq_true, and_false, or_false]
    show (∀ σ' : State C Δ, _) ↔ LandedAll q.1.1 q.2 _
    rw [landedAll_def]
    refine ⟨fun h x => h x.val x.glob_eq (fun i => ?_), fun h σ' hg hl =>
      h ⟨σ', hg, funext fun _ => funext fun i => hl i⟩⟩
    exact congrFun (congrFun x.locV_eq _) i

/-- An update with no push symbol is never out of gas (the closer's side
condition, read off the update by `Upd.pushFree`). -/
theorem exh_pushFree {Δ : Ctx} {σ : State C Γ} {U : Upd C Γ Δ} (h : U.pushFree = true) :
    U.exh σ = false :=
  Upd.exh_of_pushFree h

theorem holds_havoc (σ : State C Γ) (φ : Fml C Γ) :
    holds σ (.havoc φ) ↔ ∀ (st : Storage C) nt sb, holds (σ.havoc st nt sb) φ := Iff.rfl
theorem holds_all (σ : State C Γ) (x : Var) (p : PrimTy) (φ : Fml C (.val p :: Γ)) :
    holds σ (.all x p φ) ↔ ∀ v : p.Denote, holds (σ.push (t := .val p) v) φ := Iff.rfl
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
    holds σ (.bind m x .oldNet φ) ↔ ∀ v : Ledger, holds (σ.push (t := .oldNet) v) φ :=
  Iff.rfl
theorem holds_bind_kint (σ : State C Γ) (m : Modality) (x : Var) (φ : Fml C (.kint :: Γ)) :
    holds σ (.bind m x .kint φ) ↔ ∀ v : Int, holds (σ.push (t := .kint) v) φ := Iff.rfl
theorem holds_anon (σ : State C Γ) (xs : List ((t : LTy) × Idx Γ t)) (φ : Fml C Γ) :
    holds σ (.anon xs φ) ↔ ∀ b, holds (σ.anon xs b) φ := Iff.rfl
/-- A fresh object of any contents: one more object, its reference the new
local (`Fml.allocAll`). -/
theorem holds_allocAll (σ : State C Γ) (x : Var) (R : RefTy) (φ : Fml C (.mem R :: Γ)) :
    holds σ (.allocAll x R φ) ↔
      ∀ o : MObj σ.H R, holds ((σ.alloc o).1.push (t := .mem R) (some (σ.alloc o).2)) φ :=
  Iff.rfl
/-- **A fresh array of `n` elements** (`new T[](n)`, `copySt(memory,
newArr(n))`) read at its own identity: its length is `n`
(`newArrT_copy_len`; Lean only). -/
theorem lenU_withMem_newArr {H : HTy} (g : GlobT C H) (μ : Grown H (fun _ => Unit))
    (E : Ty) (n : PrimTy.uint.Denote) (h : (RefTy.array E).newArrOk = true)
    (hU : (Ty.ref (.array E)).mapFree = true) :
    (g.withMem (μ.then ((newArrT (.array E) n h).copyStToM μ.heap hU))).val.memT.heap.lenU
      ((newArrT (.array E) n h).copyStToM μ.heap hU).val = n := by
  apply Subtype.ext
  show ((((newArrT (.array E) n h).copyStToM μ.heap hU).heap.len
    ((newArrT (.array E) n h).copyStToM μ.heap hU).val .dyn : Nat) : Int) = n.val
  rw [newArrT_copy_len]
  have := n.2
  simp only [PrimTy.inRange, decide_eq_true_eq] at this
  omega

/-- A storage read in the Theory, by its operands' Theory values (`Op2.denote`,
`Op0.denote`): what `sol_close_denote` reads a storage alias's `ensures`
by. -/
theorem denote_len {E : Ty} (σ : State C Γ) (s : Tm C Γ .st)
    (q : Tm C Γ (.path (.ref (.array E)))) :
    (Tm.app2 .len s q).denote σ = lenW ((s.denote σ).len (q.denote σ)) := rfl
theorem denote_find {p : PrimTy} (σ : State C Γ) (s : Tm C Γ .st) (q : Tm C Γ (.path (.prim p))) :
    (Tm.app2 .find s q).denote σ = some ((s.denote σ).word (q.denote σ)) := rfl
theorem denote_storage (σ : State C Γ) :
    (Tm.app0 .storage : Tm C Γ .st).denote σ = σ.storage.obs := rfl
theorem denote_root (σ : State C Γ) (r : Name) {T : Ty} (h : C.rootType r = some T) :
    (Tm.app0 (.root r h) : Tm C Γ (.path T)).denote σ = .ref (SRef.ofRoot r h) := rfl
theorem denote_pvP {R : RefTy} (σ : State C Γ) (i : Idx Γ (.alias R)) :
    (Tm.pvP i).denote σ =
      Option.elim (σ.locV (.alias R) i) (SLoc.dangling _ .nil) (SLoc.ref (T := .ref R)) := by
  have e : σ.locV (.alias R) i = (TEnv.get i σ.env : Option (SRef C (.ref R))) := rfl
  rw [e]
  simp only [Tm.denote]
  cases (TEnv.get i σ.env : Option (SRef C (.ref R))) <;> rfl
theorem denote_at {R : RefTy} {k : PrimTy} {V : Ty} (σ : State C Γ) (it : IndexTy R k V)
    (x : Tm C Γ (.path (.ref R))) (y : Tm C Γ (.val k)) :
    (Tm.app2 (.at it) x y).denote σ =
      ObsLoc.app (x.denote σ) (Path.index it ((y.denote σ).getD (PrimTy.dflt _))) := rfl

/-- **`selectOnSaveCons`** at a word, both branches (`\if (a1 = a2)`): a word
read after a write of a word is the word written where the read goes through
the write, the old read elsewhere (`Obs.findOnSave`, `Obs.findOnSaveFrame`).
What `sol_close_save_cases` splits a read at a symbolic index by. -/
theorem copyTo_word_ite {L : Ty → Type} [ObsLoc L] (o : Obs L) {P : PrimTy}
    (p q : L (.prim P)) (v : TVal (.prim P)) :
    (o.copyTo p v).word q = if (ObsLoc.strip? p q).isSome then v.word .nil else o.word q := by
  unfold Obs.copyTo Obs.save
  dsimp only
  split
  · rename_i r hr
    cases r
    simp only [hr, Option.isSome_some, if_true, TVal.overlay_prim]
  · rename_i hr
    simp only [hr, Option.isSome_none, Bool.false_eq_true, if_false]
/-- A read's location below a state variable, as the reference it reads. -/
theorem app_ref {U W : Ty} (r : SRef C U) (q : Path U W) :
    ObsLoc.app (SLoc.ref r) q = SLoc.ref (r.append q) := rfl
/-- The write's location and the read's, compared from their common root
(`SRef.strip?_append_append`). -/
theorem strip?_ref_append {U V W : Ty} (r : SRef C U) (p : Path U V) (q : Path U W) :
    ObsLoc.strip? (SLoc.ref (r.append p)) (SLoc.ref (r.append q)) = Path.strip? p q :=
  SRef.strip?_append_append r p q
theorem obs_word_prim_nil {P : PrimTy} (v : P.Denote) : (SVal.prim v).obs.word .nil = v := rfl

/-- `τ` is `σ` over a grown heap that keeps `σ`'s objects (`Fml.grow`). -/
def _root_.Solidity.State.GrowOf (σ τ : State C Γ) : Prop :=
  ∃ g : Grown σ.H (fun _ => Unit), Heap.Keeps g.ext σ.heap g.heap ∧ τ = (σ.adopt g).1

/-- **A heap grown keeping its objects** (`Fml.grow`): every state that
reads `σ`'s storage, ledger, funds, transaction and locals, and grew from
it.  The state is a variable, so the closer reads it through these
equations, not through the adopted heap. -/
theorem holds_grow (σ : State C Γ) (φ : Fml C Γ) :
    holds σ (.grow φ) ↔ ∀ τ : State C Γ, τ.storage = σ.storage → τ.net = σ.net →
      τ.selfBalance = σ.selfBalance → τ.tx = σ.tx → τ.locV = σ.locV → σ.GrowOf τ →
        holds τ φ := by
  refine ⟨fun h τ _ _ _ _ _ ⟨g, hk, e⟩ => e ▸ h g hk, fun h g hk => ?_⟩
  exact h _ rfl rfl rfl rfl (State.locV_adopt σ g) ⟨g, hk, rfl⟩
theorem adopt_storage {α : HTy → Type} (σ : State C Γ) (g : Grown σ.H α) :
    (σ.adopt g).1.storage = σ.storage := rfl
theorem adopt_net {α : HTy → Type} (σ : State C Γ) (g : Grown σ.H α) :
    (σ.adopt g).1.net = σ.net := rfl
theorem adopt_selfBalance {α : HTy → Type} (σ : State C Γ) (g : Grown σ.H α) :
    (σ.adopt g).1.selfBalance = σ.selfBalance := rfl
theorem adopt_tx {α : HTy → Type} (σ : State C Γ) (g : Grown σ.H α) :
    (σ.adopt g).1.tx = σ.tx := rfl
theorem alloc_storage {R : RefTy} (σ : State C Γ) (o : MObj σ.H R) :
    (σ.alloc o).1.storage = σ.storage := rfl
theorem alloc_net {R : RefTy} (σ : State C Γ) (o : MObj σ.H R) : (σ.alloc o).1.net = σ.net := rfl
theorem alloc_selfBalance {R : RefTy} (σ : State C Γ) (o : MObj σ.H R) :
    (σ.alloc o).1.selfBalance = σ.selfBalance := rfl
theorem alloc_tx {R : RefTy} (σ : State C Γ) (o : MObj σ.H R) : (σ.alloc o).1.tx = σ.tx := rfl
theorem locV_alloc {R : RefTy} (σ : State C Γ) (o : MObj σ.H R) :
    (σ.alloc o).1.locV = σ.locV := State.locV_adopt σ _
/-- The fresh object's identity: the next one. -/
theorem alloc_snd_id {R : RefTy} (σ : State C Γ) (o : MObj σ.H R) :
    ((σ.alloc o).2 : HRef (σ.alloc o).1.H R).id = σ.H.length := rfl
theorem push_lenId {t : LTy} (σ : State C Γ) (v : t.TDenote C σ.H) (E : Ty) (id : Nat) :
    (σ.push v).glob.memT.lenId E id = σ.glob.memT.lenId E id := rfl
theorem push_readT {t : LTy} (σ : State C Γ) (v : t.TDenote C σ.H) {T : Ty} (a : MAddrT T) :
    (σ.push v).glob.memT.readT a = σ.glob.memT.readT a := rfl
/-- An element of the fresh array of words: its list's. -/
theorem alloc_readT_index {p : PrimTy} (σ : State C Γ) (o : MObj σ.H (.array (.prim p)))
    (k : PrimTy.uint.Denote) :
    ((σ.alloc o).1.glob.memT.readT (T := .prim p) (MAddrT.index σ.H.length .dyn k) :
      Option p.Denote) =
      ((o : {l : List (MVal σ.H (.prim p)) // l.length < 2 ^ 256}).1[k.1.toNat]? :
        Option p.Denote) := by
  rw [← alloc_snd_id σ o]
  simp only [Grown.readT, MAddrT.resolve, HRef.ofId?_self, Option.map_some, bind, Option.bind]
  show Heap.index (σ.heap.alloc o).1 (σ.heap.alloc o).2 .dyn k = _
  simp only [Heap.index, Heap.get_alloc, MObj.elems_dyn, MObj.wk, List.getElem?_map]
  cases (o : {l : List (MVal σ.H (.prim p)) // l.length < 2 ^ 256}).1[k.1.toNat]? <;> rfl
theorem push_readId {t : LTy} (σ : State C Γ) (v : t.TDenote C σ.H) {T : Ty} (a : MAddrT T) :
    (σ.push v).glob.memT.readId a = σ.glob.memT.readId a := rfl

/-- Local updates preserve memory observations, including an anonymised loop counter. -/
theorem setLocal_lenId {t : LTy} (σ : State C Γ) (i : Idx Γ t)
    (v : t.TDenote C σ.H) (E : Ty) (id : Nat) :
    (σ.setLocal i v).glob.memT.lenId E id = σ.glob.memT.lenId E id := rfl
theorem setLocal_lenU {t : LTy} (σ : State C Γ) (i : Idx Γ t)
    (v : t.TDenote C σ.H) {E : Ty} (r : HRef σ.H (.array E)) :
    (σ.setLocal i v).glob.memT.heap.lenU r = σ.glob.memT.heap.lenU r := rfl
theorem setLocal_readT {t : LTy} (σ : State C Γ) (i : Idx Γ t)
    (v : t.TDenote C σ.H) {T : Ty} (a : MAddrT T) :
    (σ.setLocal i v).glob.memT.readT a = σ.glob.memT.readT a := rfl
theorem setLocal_readId {t : LTy} (σ : State C Γ) (i : Idx Γ t)
    (v : t.TDenote C σ.H) {T : Ty} (a : MAddrT T) :
    (σ.setLocal i v).glob.memT.readId a = σ.glob.memT.readId a := rfl

/-- A captured typed value is the witness once its integer observation is known. -/
theorem exists_val_eq {α : Type} {p : α → Prop} (w : Subtype p) (P : Subtype p → Prop) :
    (∃ a : Subtype p, w.val = a.val ∧ P a) ↔ P w :=
  ⟨fun ⟨_a, h, hP⟩ => (congrArg P (Subtype.ext h)).mpr hP,
    fun hP => ⟨w, rfl, hP⟩⟩

/-- Erase a rebuilt index's proof before first-order matching. -/
theorem index_uint_eta {R : RefTy} {E : Ty} (a : ArrTy R E) (id : Nat)
    (i : PrimTy.uint.Denote) (h : PrimTy.uint.inRange i.val = true) :
    (MAddrT.index id a ⟨i.val, h⟩ : MAddrT E) = MAddrT.index id a i := rfl

/-- Equal integer observations identify typed array indices. The reconstructed
index used by a universal instance may carry a different range proof. -/
theorem index_uint_congr {R : RefTy} {E : Ty} (a : ArrTy R E) (id : Nat)
    (i j : PrimTy.uint.Denote) (h : i.val = j.val) :
    (MAddrT.index id a i : MAddrT E) = MAddrT.index id a j :=
  congrArg (fun k => MAddrT.index id a k) (Subtype.ext h)
/-- An element of the fresh array of words, as the closer reads it: its
list's. -/
theorem alloc_readId_index {p : PrimTy} (σ : State C Γ) (o : MObj σ.H (.array (.prim p)))
    (k : PrimTy.uint.Denote) :
    ((σ.alloc o).1.glob.memT.readId (T := .prim p) (MAddrT.index σ.H.length .dyn k) :
      Option p.Denote) =
      ((o : {l : List (MVal σ.H (.prim p)) // l.length < 2 ^ 256}).1[k.1.toNat]? :
        Option p.Denote) := by
  unfold Grown.readId
  rw [alloc_readT_index]
  cases ((o : {l : List (MVal σ.H (.prim p)) // l.length < 2 ^ 256}).1[k.1.toNat]? :
    Option p.Denote) <;> rfl
/-- The fresh array's length: its list's (a free value, the object any). -/
theorem alloc_lenId {E : Ty} (σ : State C Γ) (o : MObj σ.H (.array E)) :
    (σ.alloc o).1.glob.memT.lenId E σ.H.length =
      some (lenU (o : {l : List (MVal σ.H E) // l.length < 2 ^ 256}).1.length o.2) := by
  rw [← alloc_snd_id σ o, Grown.lenId_ref (σ.alloc o).1.glob.memT (σ.alloc o).2]
  show some (Heap.lenU (σ.heap.alloc o).1 (σ.heap.alloc o).2) = _
  simp only [Heap.lenU, Heap.len, Heap.get_alloc, MObj.elems_dyn, MObj.wk, List.length_map]

end Leaf

end CloseS

/-! ## The set -/

attribute [close_rw_s high] CloseS.holds_eqAtom CloseS.holds_eqT CloseS.holds_eqA CloseS.atT_map_root

attribute [close_rw_s]
  -- formulas
  Fml.Atom.tm CloseS.holds_tt CloseS.holds_not CloseS.holds_and CloseS.holds_imp CloseS.holds_eq
  CloseS.holds_wellFormed CloseS.holds_upd CloseS.holds_havoc CloseS.holds_all
  CloseS.exh_pushFree Upd.pushFree UpdElem.pushFree Rhs.pushFree Tm.pushFree Op2.pushFree
  Op3.pushFree Bool.false_eq_true and_false
  CloseS.holds_bind_val CloseS.holds_bind_alias CloseS.holds_bind_mem CloseS.holds_bind_old
  CloseS.holds_bind_oldNet CloseS.holds_bind_kint CloseS.holds_anon CloseS.lenU_withMem_newArr
  CloseS.forall_uint CloseS.forall_int CloseS.ofLit_uint CloseS.ofLit_int
  CloseS.binopT_uint CloseS.binopT_int CloseS.binopT_and CloseS.binopT_or CloseS.binopT_bool
  CloseS.evalT_uint CloseS.evalT_int CloseS.evalT_bool CloseS.ofInt?_uint CloseS.ofInt?_int
  CloseS.optRes_ite_ok CloseS.optRes_ite CloseS.uintOf_val' CloseS.intOf_val' CloseS.eq_uintOf' CloseS.eq_intOf'
  CloseS.uint_eq_mk CloseS.int_eq_mk CloseS.mk_eq_uint CloseS.mk_eq_int and_assoc exists_prop
  BinOp.evalNum BinOp.evalBool BinOp.arithInt UnOp.evalT PrimTy.inRange
  CloseS.natCast_ofNat
  CloseS.denote_lit CloseS.denote_pvV CloseS.denote_env CloseS.denote_binop
  CloseS.denote_unop CloseS.denote_ite Option.some.injEq
  -- the typed state
  State.locV_push State.locV_setLocal State.locV_drop State.locV_thin CloseS.locV_havoc
  CloseS.glob_storage CloseS.glob_net CloseS.glob_selfBalance CloseS.glob_tx CloseS.glob_envVal
  CloseS.havoc_storage CloseS.havoc_net CloseS.havoc_selfBalance CloseS.havoc_tx
  CloseS.push_storage CloseS.push_net CloseS.push_selfBalance CloseS.push_tx CloseS.push_lenU
  CloseS.index_uint_eta
  CloseS.push_lenId CloseS.push_readT CloseS.push_readId
  CloseS.setLocal_lenId CloseS.setLocal_lenU CloseS.setLocal_readT CloseS.setLocal_readId
  CloseS.setLocal_storage CloseS.setLocal_net CloseS.setLocal_selfBalance CloseS.setLocal_tx
  CloseS.envVal_msgSender CloseS.envVal_msgValue CloseS.envVal_timestamp
  CloseS.envVal_selfBalance CloseS.envVal_selfAddress
  CloseS.Landed.storage_eq CloseS.Landed.net_eq CloseS.Landed.selfBalance_eq CloseS.Landed.tx_eq
  CloseS.Landed.hashId_eq CloseS.push_hashId CloseS.setLocal_hashId
  CloseS.withStorage_hashId CloseS.withNet_hashId CloseS.withBalance_hashId
  CloseS.Landed.locV_eq CloseS.Landed.glob_eq
  CloseS.set_push_here CloseS.set_push_there CloseS.drop_refl' CloseS.drop_push' CloseS.thin_refl'
  CloseS.thin_keep' CloseS.thin_drop'
  CloseS.landedAll_const CloseS.landedRest_def
  CloseS.landed_nonempty CloseS.landed_nonempty_push_uint
  CloseS.landed_nonempty_push_int CloseS.landed_nonempty_push_bool
  State.anon_nil State.anon_cons
  CloseS.vden_val CloseS.vden_alias CloseS.vden_mem CloseS.vden_old CloseS.vden_oldNet
  CloseS.vden_kint
  CloseS.optRes_some CloseS.optRes_none CloseS.optRes_bind CloseS.optRes_map
  -- updates
  CloseS.applyV_nil CloseS.applyV_snoc CloseS.applyV_decl CloseS.applyV_pop CloseS.applyV_drop
  CloseS.elem_local CloseS.elem_storage CloseS.elem_memory CloseS.elem_selfBalance
  CloseS.elem_net CloseS.elem_pay CloseS.elem_netMt CloseS.elem_setBalance
  CloseS.glob_storageE CloseS.glob_memoryE CloseS.glob_selfBalanceE
  CloseS.glob_netE CloseS.glob_payE CloseS.glob_netMtE CloseS.glob_setBalanceE
  GlobT.paid
  CloseS.withStorage_storage CloseS.withStorage_net CloseS.withStorage_selfBalance
  CloseS.withStorage_tx CloseS.withMem_storage CloseS.withMem_net CloseS.withMem_selfBalance
  CloseS.withMem_tx CloseS.withNet_storage CloseS.withNet_net CloseS.withNet_selfBalance
  CloseS.withNet_tx CloseS.withBalance_storage CloseS.withBalance_net
  CloseS.withBalance_selfBalance CloseS.withBalance_tx CloseS.globG_val
  CloseS.push_here CloseS.push_there CloseS.set_here_here CloseS.set_here_there
  CloseS.set_there_here CloseS.set_there_there CloseS.drop_apply CloseS.thin_apply
  CloseS.ext_refl CloseS.ext_push CloseS.wk_refl CloseS.wk_keep_here
  CloseS.wk_keep_there CloseS.wk_drop
  CloseS.rhs_val CloseS.rhs_path CloseS.rhs_unset CloseS.rhs_mref CloseS.rhs_store
  CloseS.rhs_saveNet CloseS.rhs_saveNetMt CloseS.rhs_zint IntOp.apply
  -- terms
  CloseS.eval_pvV CloseS.eval_pvP CloseS.eval_pvS CloseS.eval_pvI CloseS.eval_netOf
  CloseS.eval_pvZ CloseS.eval_zlit CloseS.eval_zbin CloseS.eval_zcmp BinOp.evalZ BinOp.cmpZ
  CloseS.eval_lit CloseS.eval_env CloseS.eval_root CloseS.eval_storage CloseS.eval_mtSt
  CloseS.eval_unop CloseS.eval_net CloseS.eval_delValue CloseS.eval_field CloseS.eval_next
  CloseS.eval_sval CloseS.eval_newArr CloseS.eval_mfield CloseS.eval_mval CloseS.eval_ref
  CloseS.eval_wt CloseS.eval_select CloseS.eval_toInt
  CloseS.eval_binop CloseS.eval_find CloseS.eval_sfind CloseS.eval_delAt CloseS.eval_at
  CloseS.eval_len CloseS.eval_pushSlot CloseS.eval_pop CloseS.eval_shrink CloseS.eval_extend
  CloseS.eval_nextIn CloseS.eval_mat
  CloseS.eval_ite CloseS.eval_save CloseS.eval_push
  CloseS.eval_memory CloseS.eval_alloc CloseS.eval_addM CloseS.eval_read CloseS.eval_mlen
  CloseS.eval_hash
  CloseS.eval_copyMem CloseS.eval_iread CloseS.eval_copy CloseS.eval_copySt CloseS.eval_write
  SVal.view_prim
  -- runs
  Modality.wp_ok Modality.wp_pure Modality.wp_error Modality.wp_bind Modality.wp_ite
  Modality.wp_diamond Modality.onHalt_box Modality.onHalt_diamond
  Close.pure_eq_ok Solidity.ok_bind Solidity.error_bind Close.bind_ok_right bind_assoc
  -- logic
  Except.ok.injEq Option.some.injEq Option.map_some Option.map_none Option.bind_some
  Option.bind_none Option.map_map Option.bind_map Option.map_bind Function.comp_apply
  Subtype.mk.injEq Prod.mk.injEq cond_true cond_false
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
  Int.reduceMod Int.reduceDiv Int.reduceTMod Int.reduceTDiv Semantics.uintBound Semantics.intBound
  Close.uintBitwise_ofNat Close.uintBitwise_ofNat_cast Close.uintBitwise_cast_ofNat
  Semantics.uintBitwise_natCast Nat.reduceAnd Nat.reduceOr Nat.reduceXor
  Close.uintBitwise_and_zero_right Close.uintBitwise_and_zero_left
  Close.uintBitwise_and_one_right Close.uintBitwise_and_one_left
  Close.lookupBy_ite Close.lookupBy_setBy_int CloseS.root_ofRoot CloseS.root_field CloseS.root_index CloseS.atT_bind
  CloseS.getD_ite Option.getD_some
  CloseS.uint_eq_iff CloseS.int_eq_iff CloseS.bool_eq_iff CloseS.view_eq_uint CloseS.view_eq_int
  Int.reduceAdd Int.reduceSub Int.reduceMul Int.reduceNeg Int.reduceLT Int.reduceLE

attribute [close_rw_s_last] Modality.wp_box



/-! ## The steps on a scoped goal -/

open Lean Elab Tactic Meta

/-- A Boolean of the formula's terms, evaluated (`Tm.agreeB`, `Tm.totB`,
`Tm.pushFree`); one that does not reduce to a literal (a term with a free
variable) fails, and `sol_close_unwrap` then leaves the leaf as it is. -/
private def evalBoolE (e : Expr) : MetaM Bool := do
  let e' ← whnfD e
  if e'.isConstOf ``Bool.true then return true
  if e'.isConstOf ``Bool.false then return false
  throwError "evalEqsE: {e} does not reduce"

/-- A local, a literal or a value of the transaction, read off the syntax, as
the atom (`Fml.Atom`) whose term it is. -/
private def atomE? (e : Expr) : MetaM (Option Expr) := do
  unless e.isAppOfArity ``Tm.pvV 4 || e.isAppOfArity ``Tm.app0 4 do return none
  let (C, Γ) := (e.getArg! 0, e.getArg! 1)
  if e.isAppOfArity ``Tm.pvV 4 then
    return some (← mkAppOptM ``Fml.Atom.loc #[C, Γ, e.getArg! 2, e.appArg!])
  if e.isAppOfArity ``Tm.app0 4 then
    let o := e.appArg!
    if o.isAppOfArity ``Op0.lit 3 then
      return some (← mkAppOptM ``Fml.Atom.lit #[C, Γ, o.getArg! 1, o.appArg!])
    if o.isAppOfArity ``Op0.env 2 then
      return some (← mkAppOptM ``Fml.Atom.env #[C, Γ, o.appArg!])
  return none

/-- `Fml.evalEqs goal φ` computed on the formula's syntax: each equation's
Booleans evaluated once (`evalBoolE`), the marks' proofs `rfl`.  The result
is definitionally `Fml.evalEqs goal φ`; a formula whose head does not reduce
to a connective is left under `Fml.evalEqs`. -/
private partial def evalEqsE (goal : Bool) (φ : Expr) : MetaM Expr := do
  let heads := [``Fml.tt, ``Fml.eq, ``Fml.wellFormed, ``Fml.not, ``Fml.and, ``Fml.imp, ``Fml.upd,
    ``Fml.modal, ``Fml.havoc, ``Fml.all, ``Fml.bind, ``Fml.anon, ``Fml.allocAll, ``Fml.grow]
  let φ ← whnfR φ
  let φ ← if heads.any φ.isAppOf then pure φ else whnfD φ
  let f := φ.getAppFn
  let args := φ.getAppArgs
  let last (g : Bool) : MetaM Expr := do
    return mkAppN f (args.pop.push (← evalEqsE g args.back!))
  match f.constName?, args.size with
  | some ``Fml.eq, 5 =>
    let (a, b) := (args[3]!, args[4]!)
    let ag ← mkAppM ``Bool.and #[← mkAppM ``Tm.agreeB #[a], ← mkAppM ``Tm.agreeB #[b]]
    let tot ← mkAppM ``Bool.or #[← mkAppM ``Tm.totB #[a], ← mkAppM ``Tm.totB #[b]]
    let rflT := mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Bool) (mkConst ``Bool.true)
    -- an equation of atoms, which the closer reads by value as it stands
    -- (`CloseS.holds_eq`, `CloseS.denote_pvV`, …); a capture's own is marked
    -- (`Fml.eqCap`, `CloseS.holds_eqAtom`)
    if (← atomE? a).isSome && (← atomE? b).isSome then return φ
    if ← evalBoolE ag then
      if ← evalBoolE tot then
        let h ← mkExpectedTypeHint rflT (← mkEq (← mkAppM ``Bool.and #[ag, tot]) (mkConst ``Bool.true))
        return ← mkAppM ``Fml.eqT #[a, b, h]
      let h ← mkExpectedTypeHint rflT (← mkEq ag (mkConst ``Bool.true))
      return ← mkAppM ``Fml.eqA #[a, b, h]
    if goal then
      if ← evalBoolE (← mkAppM ``Bool.and #[← mkAppM ``Tm.pushFree #[a], ← mkAppM ``Tm.pushFree #[b]]) then
        let e ← mkAppM ``Fml.eqCap #[mkConst ``Modality.diamond, a, b]
        return (← unfoldDefinition? e).getD e
    return φ
  | some ``Fml.not, 3 => last false
  | some ``Fml.and, 4 =>
    return mkAppN f #[args[0]!, args[1]!, ← evalEqsE goal args[2]!, ← evalEqsE goal args[3]!]
  | some ``Fml.imp, 4 =>
    return mkAppN f #[args[0]!, args[1]!, ← evalEqsE false args[2]!, ← evalEqsE goal args[3]!]
  | some ``Fml.upd, 6 | some ``Fml.all, 5 | some ``Fml.bind, 6 | some ``Fml.havoc, 3
  | some ``Fml.anon, 4 | some ``Fml.allocAll, 5 | some ``Fml.grow, 3 => last goal
  | some ``Fml.tt, _ | some ``Fml.wellFormed, _ | some ``Fml.modal, _ => return φ
  | _, _ => mkAppM ``Fml.evalEqs #[toExpr goal, φ]

/-- `sol_close_unwrap` on a scoped leaf `Fml.Valid ψ`: its equations read by the
interpreter (`Fml.Valid.of_evalEqs`, `Calculus/EvalEqs.lean`, computed by
`evalEqsE`), then `holds` in every typed state (`CloseS.valid_of_holds`). -/
@[tactic Solidity.tacticSol_close_unwrap]
def evalSolCloseUnwrapS : Tactic := fun _ => withMainContext do
  let g ← getMainGoal
  let ty ← instantiateMVars (← g.getType)
  unless ty.isAppOf ``Solidity.Fml.Valid do throwUnsupportedSyntax
  let tag ← g.getTag
  -- the pass where every equation's Booleans reduce, else the leaf as it is
  let g₂ ← try
      let φ' ← evalEqsE true ty.appArg!
      let [g₁] ← g.apply (← mkConstWithFreshMVarLevels ``Fml.Valid.of_evalEqs) | failure
      let ty₁ ← instantiateMVars (← g₁.getType)
      g₁.replaceTargetDefEq (mkApp ty₁.appFn! φ')
    catch _ => pure g
  let gs ← g₂.apply (← mkConstWithFreshMVarLevels ``CloseS.valid_of_holds)
  for g' in gs do g'.setTag tag
  replaceMainGoal gs

/-- `sol_close_unwrap_th`: `sol_close_unwrap` with no equation strengthened
(`Fml.Valid.of_evalEqsTh`): one that reads a storage alias stays a Theory
equation, for `sol_close_denote`. -/
@[tactic Solidity.tacticSol_close_unwrap_th]
def evalSolCloseUnwrapThS : Tactic := fun _ => withMainContext do
  let g ← getMainGoal
  let ty ← instantiateMVars (← g.getType)
  unless ty.isAppOf ``Solidity.Fml.Valid do throwUnsupportedSyntax
  let tag ← g.getTag
  let g₂ ← try
      let φ' ← evalEqsE false ty.appArg!
      let [g₁] ← g.apply (← mkConstWithFreshMVarLevels ``Fml.Valid.of_evalEqsTh) | failure
      let ty₁ ← instantiateMVars (← g₁.getType)
      g₁.replaceTargetDefEq (mkApp ty₁.appFn! φ')
    catch _ => pure g
  let gs ← g₂.apply (← mkConstWithFreshMVarLevels ``CloseS.valid_of_holds)
  for g' in gs do g'.setTag tag
  replaceMainGoal gs

/-- Run `tac` where the goal is a scoped leaf's, else step aside. -/
def onScoped (tac : TacticM Syntax) : Tactic := fun _ => do
  unless ← Close.scopedGoal do throwUnsupportedSyntax
  evalTactic (← tac)

/-- Whether the goal reads a fresh object (`Fml.allocAll`, or the state it
grew, `State.alloc`): only then are `sol_close`'s lemmas on fresh objects
added to its sets, so a leaf with none takes the same path as without them. -/
def allocInGoal : TacticM Bool := do
  let t ← instantiateMVars (← getMainTarget)
  return (t.find? fun e => e.isConstOf ``Fml.allocAll || e.isConstOf ``State.alloc ||
    e.isConstOf ``Fml.grow || e.isConstOf ``State.adopt).isSome

/-- `sol_close`'s lemmas on a fresh object (`Fml.allocAll`), outside
`close_rw_s`: `allocInGoal` adds them. -/
def allocLemmas : TacticM (Array (TSyntax ``Lean.Parser.Tactic.simpLemma)) :=
  #[``CloseS.holds_allocAll, ``CloseS.alloc_storage, ``CloseS.alloc_net,
    ``CloseS.alloc_selfBalance, ``CloseS.alloc_tx, ``CloseS.locV_alloc, ``CloseS.alloc_snd_id,
    ``CloseS.alloc_lenId, ``CloseS.alloc_readT_index,
    ``CloseS.alloc_readId_index, ``CloseS.holds_grow].mapM fun n =>
      `(Lean.Parser.Tactic.simpLemma| $(mkIdent n):ident)

/-- The extra lemmas where the goal reads a fresh object, none elsewhere. -/
def allocExtra : TacticM (Array (TSyntax ``Lean.Parser.Tactic.simpLemma)) := do
  if ← allocInGoal then allocLemmas else pure #[]

/-- The steps as `sol_close_facts` and `sol_close_reads` allow: a leaf of
nested landed states (`CloseS.LandedAll`) repeats its captures' terms in each
(`externalValue` of `tests/solc/FunctionTypes.sol` passes the default 100000). -/
@[tactic Solidity.tacticSol_close_eval, tactic Solidity.tacticSol_close_mt_eval]
def evalSolCloseEvalS : Tactic := onScoped do
  let ex ← allocExtra
  if ex.isEmpty then `(tactic| simp (config := { maxSteps := 400000 }) only [close_rw_s])
  else `(tactic| simp (config := { maxSteps := 400000 }) only [close_rw_s, $ex,*])

@[tactic Solidity.tacticSol_close_facts]
def evalSolCloseFactsS : Tactic := onScoped do
  let ex ← allocExtra
  if ex.isEmpty then `(tactic|
    simp (config := { contextual := true, maxSteps := 400000 }) only [close_rw_s])
  else `(tactic|
    simp (config := { contextual := true, maxSteps := 400000 }) only [close_rw_s, $ex,*])

@[tactic Solidity.tacticSol_close_reads]
def evalSolCloseReadsS : Tactic := onScoped do
  let ex ← allocExtra
  if ex.isEmpty then `(tactic|
    simp (config := { contextual := true, maxSteps := 400000 }) only [close_rw_s, close_rw_s_last])
  else `(tactic|
    simp (config := { contextual := true, maxSteps := 400000 }) only
      [close_rw_s, close_rw_s_last, $ex,*])

@[tactic Solidity.tacticSol_close_reads_all]
def evalSolCloseReadsAllS : Tactic := onScoped do
  let ex ← allocExtra
  if ex.isEmpty then `(tactic|
    simp_all (config := { maxSteps := 400000 }) only [close_rw_s, close_rw_s_last])
  else `(tactic|
    simp_all (config := { maxSteps := 400000 }) only [close_rw_s, close_rw_s_last, $ex,*])

/-- Whether the goal or a hypothesis reads a storage alias local inside a
Theory value (`Tm.denote` of a term with `Tm.pvP`). -/
def aliasDenoteLeft : TacticM Bool := withMainContext do
  let hit (e : Expr) : Bool := (e.find? fun x =>
    x.isAppOf ``Tm.denote && (x.find? (·.isConstOf ``Tm.pvP)).isSome).isSome
  if hit (← instantiateMVars (← getMainTarget)) then return true
  for d in ← getLCtx do
    if !d.isImplementationDetail && hit (← instantiateMVars d.type) then return true
  return false

@[tactic Solidity.tacticSol_close_alias_guard]
def evalSolCloseAliasGuard : Tactic := fun _ => withMainContext do
  let ty ← instantiateMVars (← getMainTarget)
  unless ty.isAppOf ``Solidity.Fml.Valid do throwError "sol_close_alias_guard: not a scoped leaf"
  let hasPvP (e : Expr) : Bool := (e.find? (·.isConstOf ``Tm.pvP)).isSome
  let hit := ty.find? fun x => x.isAppOfArity ``Fml.eq 5 && hasPvP x
  unless hit.isSome do throwError "sol_close_alias_guard: no equation reads a storage alias"

macro_rules
  | `(tactic| sol_close_landed) => `(tactic| simp only [CloseS.landedAll_def])

/-- Select the quantified-premise fallback without charging ordinary leaves. -/
elab "sol_close_all_guard" : tactic => withMainContext do
  let ty ← instantiateMVars (← getMainTarget)
  let rec hasAll (e : Expr) : Bool :=
    e.isAppOf ``Fml.all || (e.isAppOfArity ``Fml.and 4 &&
      (hasAll (e.getArg! 2) || hasAll (e.getArg! 3)))
  unless (ty.find? fun e => e.isAppOfArity ``Fml.imp 4 && hasAll (e.getArg! 2)).isSome do
    throwError "sol_close_quantified: no quantified premise"

/-- Open at most 128 logical constructors, reusing a captured value only
when the goal's equality identifies it. Each checked step has its own budget. -/
elab "sol_close_captures" : tactic => do
  let mut todo ← getGoals
  let mut leaves : List MVarId := []
  for _ in [0:128] do
    let g :: rest := todo | break
    setGoals [g]
    let saved ← saveState
    let ok ← tryCatchRuntimeEx (Budget.within 1000 do
        let step? ← g.withContext do
          let ty ← whnfR (← g.getType)
          if ty.isForall then return some (← `(tactic| intro _))
          if ty.isAppOf ``And then return some (← `(tactic| apply And.intro))
          if ty.isAppOf ``Exists then
            return some (← `(tactic| apply (CloseS.exists_val_eq _ _).2))
          return none
        let some step := step? | return false
        Term.withoutErrToSorry <| withoutRecover <| evalTactic step
        return true) (fun _ => pure false)
    if ok then todo := (← getUnsolvedGoals) ++ rest
    else
      saved.restore
      leaves := leaves ++ [g]
      todo := rest
  setGoals (leaves ++ todo)

/-- `sol_close_save_cases`'s first step: the Theory reads of the goal and of
the premises that read one (a `∀` premise's instances) unfolded alike to
`st.obs.word (.ref r)`; then the storage each landed on after a write
`st.write r v = some st'` read as the write's (`Storage.obs_write`), for at
most 8 writes the goal reads, and a read the leaf knows, `st.find r = some w`,
noted as the Theory's (`Storage.obs_word_ref_some`), at most 16.  Fails where
there is neither. -/
elab "sol_close_save_write" : tactic => withMainContext do
  -- cheap guard first: a write or a read of storage known, at most 256 premises
  let mut known := false
  let mut seen := 0
  for d in ← getLCtx do
    if seen == 256 then break
    seen := seen + 1
    if d.isImplementationDetail then continue
    let_expr Eq _ lhs rhs := (← instantiateMVars d.type) | continue
    if rhs.isAppOfArity ``Option.some 2 &&
        (lhs.isAppOf ``Storage.write || lhs.isAppOfArity ``Storage.find 4) then
      known := true
      break
  unless known do throwError "sol_close_save_cases: no write and no read of storage known"
  let mut hs : Array FVarId := #[]
  for d in ← getLCtx do
    if hs.size == 64 then break
    if d.isImplementationDetail then continue
    if ((← instantiateMVars d.type).find? (·.isAppOf ``Tm.denote)).isSome then
      hs := hs.push d.fvarId
  let (fs, g) ← (← getMainGoal).revert hs
  replaceMainGoal [g]
  evalTactic (← `(tactic| simp (config := { maxSteps := 100000 }) only [CloseS.denote_find,
      CloseS.denote_storage, CloseS.denote_root, CloseS.denote_at, CloseS.denote_pvV,
      Option.getD_some, Option.bind_some, CloseS.push_storage, CloseS.setLocal_storage,
      CloseS.havoc_storage, CloseS.Landed.storage_eq, CloseS.glob_storage,
      CloseS.withStorage_storage, CloseS.globG_val, State.locV_push, CloseS.push_here,
      CloseS.vden_val, Option.some.injEq, Path.index_dyn, Path.index_fixed, Path.index_map,
      CloseS.app_ref]))
  let (_, g) ← (← getMainGoal).introNP fs.size
  let mut g := g
  let mut writes := 0
  let mut reads := 0
  for d in ← g.withContext getLCtx do
    if d.isImplementationDetail then continue
    let_expr Eq _ lhs rhs := (← instantiateMVars d.type) | continue
    unless rhs.isAppOfArity ``Option.some 2 do continue
    if lhs.isAppOf ``Storage.write && writes < 8 then
      let target ← instantiateMVars (← g.getType)
      unless (target.find? fun e => e.isAppOfArity ``Storage.obs 2 &&
        e.appArg! == rhs.appArg!).isSome do continue
      let r ← g.withContext do g.rewrite target (← mkAppM ``Storage.obs_write #[d.toExpr])
      g ← g.replaceTargetEq r.eNew r.eqProof
      writes := writes + 1
    else if lhs.isAppOfArity ``Storage.find 4 && reads < 16 then
      let some pf ← g.withContext (observing? (mkAppM ``Storage.obs_word_ref_some #[d.toExpr]))
        | continue
      let (_, g') ← g.note `read pf
      g := g'
      reads := reads + 1
  if writes + reads == 0 then
    throwError "sol_close_save_cases: no write and no read of storage known"
  replaceMainGoal [g]

/-- **`selectOnSaveCons`** at a symbolic index, solkey's `\if (a1 = a2)`: a
word read after a word written (`sol_close_save_write`) is split on whether
the read goes through the write (`CloseS.copyTo_word_ite`, the paths
compared from their root, `CloseS.strip?_ref_append`): the written word where
the indices agree, the old storage's read, as the premises' instances and
the reads known read it, where they differ.  Each branch is closed as the
leaf's are; with 20000 heartbeats of its own, past which, or where a branch
stays open, it fails with the goal as it was. -/
elab "sol_close_save_cases" : tactic => do
  let saved ← saveState
  let ok ← tryCatchRuntimeEx (Budget.within 20000 do
      Term.withoutErrToSorry <| withoutRecover <| evalTactic (← `(tactic| (
        sol_close_save_write
        try simp only [CloseS.copyTo_word_ite, CloseS.strip?_ref_append, Path.strip?,
          CloseS.obs_word_prim_nil]
        repeat' split
        all_goals try simp only [Option.isSome_some, Option.isSome_none, if_true, if_false,
          Bool.false_eq_true, CloseS.uint_eq_mk, CloseS.int_eq_mk] at *
        all_goals first | decide | omega | grind [CloseS.index_uint_congr])))
      return (← getUnsolvedGoals).isEmpty) (fun _ => pure false)
  unless ok do
    saved.restore
    throwError "sol_close_save_cases: the goal stays open"

macro "sol_close_quantified_core" : tactic => `(tactic| (
    sol_close_all_guard
    sol_close_unwrap_th
    intro σ
    sol_close_eval
    all_goals try sol_close_facts
    all_goals try sol_close_reads
    all_goals try sol_close_landed
    all_goals try (intros; sol_close_reads_all)
    all_goals try (subst_vars; sol_close_reads_all)
    all_goals try intros
    all_goals try simp only [Close.exists_unit, Close.forall_unit, exists_const, forall_const] at *
    all_goals try sol_close_witness
    all_goals (repeat' (first | intro _ | apply And.intro))
    all_goals try sol_close_enrich
    all_goals try sol_close_all
    all_goals try sol_close_enrich
    all_goals try sol_close_reads_all
    sol_close_captures
    all_goals first
      | omega | assumption | rfl | grind [CloseS.index_uint_congr]
      -- a read past a write at a symbolic index (`selectOnSaveCons`)
      | sol_close_save_cases))

elab_rules : tactic
  | `(tactic| sol_close_quantified) => do
    let saved ← saveState
    -- bounded by the declaration's heartbeats, as it always was: its option
    -- of 20000 never bound it (`checkMaxHeartbeats` reads the context's
    -- limit), and the ABI scans of `Examples/Tactics/ArrayScans.lean` use
    -- most of a declaration's
    let ok ← tryCatchRuntimeEx (do
        Term.withoutErrToSorry <| withoutRecover <| evalTactic (← `(tactic| sol_close_quantified_core))
        return (← getUnsolvedGoals).isEmpty) (fun _ => pure false)
    unless ok do
      saved.restore
      throwError "sol_close_quantified: the quantified fallback left the original goal open"

macro_rules
  | `(tactic| sol_close_witness) => `(tactic| (
    (try sol_close_landed)
    intros
    refine ⟨⟨_, by decide⟩, rfl, ?_⟩
    try dsimp only))

macro_rules
  | `(tactic| sol_close_alias) => `(tactic| (
    sol_close_alias_guard
    sol_close_unwrap_th
    intro σ
    sol_close_eval
    all_goals try sol_close_facts
    all_goals try sol_close_reads
    all_goals (try simp only [CloseS.landedAll_def])
    all_goals try (intros; sol_close_reads_all)
    all_goals try (subst_vars; sol_close_reads_all)
    all_goals (try intros)
    all_goals sol_close_denote))

/-! ### A joined `if`'s values (`sol_close_join`) -/

/-- A value read as a fresh `a` and its defining fact: where `X` returns,
`∃ a, X = some a ∧ P a` holds when `P` holds of whatever it returns. -/
theorem CloseS.exists_some_of {α : Type} {X : Option α} {P : α → Prop} (ht : X.isSome = true)
    (h : ∀ a, X = some a → P a) : ∃ a, X = some a ∧ P a := by
  cases hX : X with
  | none => rw [hX] at ht; cases ht
  | some a => exact ⟨a, rfl, h a hX⟩

/-- A conditional's value, as an implication per case: what `omega` reads
with one case split each. -/
theorem CloseS.ite_eq_some_iff {α : Type} {p : Prop} [Decidable p] {x y : Option α} {z : α} :
    (if p then x else y) = some z ↔ (p → x = some z) ∧ (¬p → y = some z) := by
  by_cases h : p <;> simp only [h, if_true, if_false, true_implies, false_implies, and_true,
    true_and, not_true_eq_false, not_false_eq_true]

/-- A checked result: its check a fact, its value the result's. -/
theorem CloseS.ite_some_none_eq {α : Type} {p : Prop} [Decidable p] {y z : α} :
    (if p then some y else none) = some z ↔ p ∧ y = z := by
  by_cases h : p <;> simp only [h, if_true, if_false, Option.some.injEq, true_and, reduceCtorEq,
    false_and]

/-- A value under its own check: the check holds, so the value is the
checked one. -/
theorem CloseS.and_eq_ite_self {α : Type} {p : Prop} [Decidable p] {z a b : α} :
    (p ∧ z = if p then a else b) ↔ (p ∧ z = a) := by
  by_cases h : p <;> simp only [h, if_true, if_false, true_and, false_and]

/-- A conditional's value, as the disjunction of its cases. -/
theorem CloseS.ite_eq_iff' {α : Type} {p : Prop} [Decidable p] {x y : α} {z : α} :
    (if p then x else y) = z ↔ (p ∧ x = z) ∨ (¬p ∧ y = z) := by
  by_cases h : p <;> simp only [h, if_true, if_false, true_and, false_and, or_false,
    false_or, not_true_eq_false, not_false_eq_true]

/-- A value set to a conditional, as the disjunction of its cases. -/
theorem CloseS.eq_ite_iff' {α : Type} {p : Prop} [Decidable p] {x y : α} {z : α} :
    z = (if p then x else y) ↔ (p ∧ z = x) ∨ (¬p ∧ z = y) := by
  by_cases h : p <;> simp only [h, if_true, if_false, true_and, false_and, or_false,
    false_or, not_true_eq_false, not_false_eq_true]

theorem CloseS.uintOf_eq' (n : Int) (a : PrimTy.uint.Denote) :
    CloseS.uintOf n = a ↔ a.val = if 0 ≤ n ∧ n < uintBound then n else 0 :=
  eq_comm.trans (CloseS.eq_uintOf' n a)

theorem CloseS.intOf_eq' (n : Int) (a : PrimTy.int.Denote) :
    CloseS.intOf n = a ↔ a.val = if -intBound ≤ n ∧ n < intBound then n else 0 :=
  eq_comm.trans (CloseS.eq_intOf' n a)

/-- The words' bounds as literals, which `omega` reads. -/
theorem CloseS.uintBound_eq :
    uintBound = 115792089237316195423570985008687907853269984665640564039457584007913129639936 :=
  rfl

theorem CloseS.intBound_eq :
    intBound = 57896044618658097711785492504343953926634992332820282019728792003956564819968 :=
  rfl

/-- Whether `e` reads a conditional value (`cond`), or a conditional whose
condition the evaluation has decided away but a checked value's `ite`
remains (`if c then some v else none`, a joined `x + 1` once `brk` is known). -/
def readsCond (e : Expr) : Bool :=
  (e.find? fun x => x.isAppOfArity ``cond 4 || x.isAppOfArity ``ite 5).isSome

/-- Fails unless the goal reads a conditional value. -/
elab "sol_close_has_cond" : tactic => do
  unless readsCond (← instantiateMVars (← getMainTarget)) do
    throwError "sol_close_has_cond: no conditional value"

/-- The landed states and their witnesses cleared from the context, the
arithmetic left for `omega`. -/
elab "sol_close_clear_landed" : tactic => withMainContext do
  let mut g ← getMainGoal
  for d in (← getLCtx).decls.toArray.reverse do
    let some d := d | continue
    if d.isImplementationDetail then continue
    let t ← instantiateMVars d.type
    if t.isAppOf ``CloseS.Landed || t.isAppOf ``Nonempty || t.isAppOf ``State then
      g ← g.tryClear d.fvarId
  replaceMainGoal [g]

/-- A defining fact `h : X = some a` as `omega` reads it: an implication
per condition, a checked value its check and its integer. -/
syntax "sol_close_join_fact " ident : tactic

macro_rules
  | `(tactic| sol_close_join_fact $h:ident) => `(tactic| (
    (try simp only [Bool.cond_eq_ite, decide_eq_true_eq, decide_eq_false_iff_not,
      Bool.not_eq_true] at $h:ident)
    (try simp only [CloseS.ite_some_none_eq, CloseS.ite_eq_some_iff, Option.some.injEq,
      reduceCtorEq, imp_false, Classical.not_not] at $h:ident)
    (try simp only [CloseS.uintOf_eq', CloseS.intOf_eq'] at $h:ident)
    (try simp only [CloseS.uint_eq_iff, CloseS.int_eq_iff, CloseS.uintBound_eq,
      CloseS.intBound_eq] at $h:ident)
    (try simp only [CloseS.and_eq_ite_self, CloseS.eq_ite_iff', and_self, true_and, and_true,
      ite_true, ite_false, if_true, if_false] at $h:ident)
    -- the literal checks decided, a case's own check assumed in it
    (try simp (config := { contextual := true }) only [Int.reduceLT, Int.reduceLE, and_true,
      true_and, and_self, or_false, false_or, not_true_eq_false, false_and, and_false,
      not_false_eq_true, true_implies, implies_true, Classical.not_not] at $h:ident)))

/-- The condition of the first `if` of `e` that tests a Boolean (`b = true`,
a `bif` rewritten) and reads no bound variable. -/
def boolCondOf? (e : Expr) : Option Expr :=
  (e.find? fun x => x.isAppOfArity ``ite 5 && (x.getArg! 1).isAppOfArity ``Eq 3 &&
    ((x.getArg! 1).getArg! 0).isConstOf ``Bool && !(x.getArg! 1).hasLooseBVars &&
    !((x.getArg! 1).getArg! 1).isConstOf ``Bool.true &&
    !((x.getArg! 1).getArg! 1).isConstOf ``Bool.false).map (·.getArg! 1)

/-- The most cases `sol_close_join` splits a leaf into (`splitBoolConds`):
each split adds one, so `n` conditions cost at most this many, not `2^n`. -/
def joinMaxCases : Nat := 64

/-- The goals split on the Boolean conditions they still read, into at most
`joinMaxCases` cases in all; past them it fails. -/
def splitBoolConds : TacticM Unit := do
  let mut todo := ← getGoals
  let mut out : Array MVarId := #[]
  let mut count := todo.length
  for _ in [0:4 * joinMaxCases + 4] do
    let g :: rest := todo | break
    todo := rest
    match boolCondOf? (← instantiateMVars (← g.getType)) with
    | none => out := out.push g
    | some c =>
      setGoals [g]
      g.withContext do
        let cs ← Term.exprToSyntax c
        evalTactic (← `(tactic| by_cases hc : $cs))
        evalTactic (← `(tactic| all_goals (
          (try simp only [hc, ite_true, ite_false, if_true, if_false, Bool.false_eq_true,
            ↓reduceIte])
          (try simp only [decide_eq_true_eq, Bool.not_eq_true, decide_eq_false_iff_not] at hc))))
      let gs ← getGoals
      count := count + gs.length - 1
      if count > joinMaxCases then
        throwError "sol_close_join: past {joinMaxCases} cases"
      todo := gs ++ todo
  unless todo.isEmpty do throwError "sol_close_join: past {joinMaxCases} cases"
  setGoals out.toList

/-- `sol_close_join`'s last cases: each Boolean condition the goal still
reads split, into at most `joinMaxCases` cases. -/
elab "sol_close_cond_cases" : tactic => do
  evalTactic (← `(tactic| all_goals (try simp only [Bool.cond_eq_ite])))
  splitBoolConds

macro_rules
  | `(tactic| sol_close_join) => `(tactic| (
    sol_close_has_cond
    repeat' (first
      | intro _
      | apply And.intro
      | (refine CloseS.exists_some_of ?_ (fun _ hX => ?_)
         rotate_left
         sol_close_join_fact hX
         rotate_left
         -- the value returns: a case per condition, the halting one refuted
         focus
           (try simp only [Bool.cond_eq_ite])
           repeat' split
           all_goals first | rfl | (exfalso; sol_close_clear_landed; grind)))
    all_goals sol_close_clear_landed
    -- what is still conditional: a case per condition
    all_goals (try sol_close_cond_cases)
    all_goals (repeat' intro _)
    all_goals first | trivial | omega | (simp_all; done) | grind))

/-! ### A joined leaf one update at a time (`sol_close_join_steps`) -/

/-- A conditional value returns where each case's does. -/
theorem CloseS.isSome_cond {α : Type} {c : Bool} {x y : Option α}
    (h₁ : c = true → x.isSome = true) (h₂ : c = false → y.isSome = true) :
    (bif c then x else y).isSome = true := by
  cases c
  · exact h₂ rfl
  · exact h₁ rfl

/-- A checked value returns where its check holds. -/
theorem CloseS.isSome_ite {α : Type} {p : Prop} [Decidable p] {x y : Option α}
    (h₁ : p → x.isSome = true) (h₂ : ¬p → y.isSome = true) :
    (if p then x else y).isSome = true := by
  by_cases hp : p
  · rw [if_pos hp]; exact h₁ hp
  · rw [if_neg hp]; exact h₂ hp

/-- The box over a value: whatever it returns, read as a fresh value and
its defining fact. -/
theorem CloseS.wp_box_optRes {α : Type} {X : Option α} {P : α → Prop} :
    Modality.box.wp (Close.optRes X) P ↔ ∀ a, X = some a → P a := by
  rw [Modality.wp_box]
  cases X with
  | none => exact ⟨fun _ a h => (nomatch h), fun _ a h => (nomatch h)⟩
  | some b => exact ⟨fun h a e => h a (by cases e; rfl), fun h a e => h a (by cases e; rfl)⟩

namespace CloseJ

/-- The leaves with at least this many joined updates (`countJoins`) take
`sol_close_join_steps` first; those with fewer, and those it does not
close, go on to `sol_close`'s join alternative.  Two: the join alternative
evaluates the leaf whole, which costs about `n³` (`n = 5` near 170 k
heartbeats, past its budget), the steps about `5 k` a join. -/
def stepsMin : Nat := 2

/-- The updates of `e` whose values are conditional (`Op3.ite`: a joined
`if`'s), counted up to `stepsMin`. -/
partial def countJoins (e : Expr) (acc : Nat) (cap : Nat := stepsMin) : Nat :=
  if acc ≥ cap then acc
  else if e.isAppOfArity ``Fml.upd 6 then
    let acc := if ((e.getArg! 4).find? (·.isConstOf ``Op3.ite)).isSome then acc + 1 else acc
    countJoins (e.getArg! 5) acc cap
  else match e with
    | .app f x => countJoins x (countJoins f acc cap) cap
    | .mdata _ b => countJoins b acc cap
    | _ => acc

/-- The most joined updates a leaf may have for `sol_close` to evaluate it
whole (its join alternative, `sol_close_quantified`, its last
alternative) where `sol_close_join_steps` did not close it: whole, each
update's rest is visited again under every rewrite above it, past the
default heartbeats from six (`docs/automation.md`, M6), and a timeout
there is not caught.  Past it, `sol_close` fails where the steps do. -/
def wholeMax : Nat := 5

/-- `tac` on `g` alone; the goals it leaves. -/
def runOn (g : MVarId) (tac : TSyntax `tactic) : TacticM (List MVarId) := do
  let saved ← getGoals
  setGoals [g]
  try
    evalTactic tac
    getGoals
  finally
    setGoals saved

/-- `omega` on `p` in the local context cut down to `keep` and what they
and `p` mention, so that a call costs the same at every step of the leaf. -/
def omegaIn (keep : Array FVarId) (p : Expr) : TacticM (Option Expr) := do
  let lctx ← getLCtx
  let mut need : FVarIdSet := {}
  let mut todo : Array FVarId := keep ++ (collectFVars {} (← instantiateMVars p)).fvarIds
  while !todo.isEmpty do
    let f := todo.back!
    todo := todo.pop
    if need.contains f then continue
    need := need.insert f
    let some d := lctx.find? f | continue
    todo := todo ++ (collectFVars {} (← instantiateMVars d.type)).fvarIds
    if let some v := d.value? then
      todo := todo ++ (collectFVars {} (← instantiateMVars v)).fvarIds
  let lctx' := lctx.foldl (init := lctx) fun l d =>
    if need.contains d.fvarId then l else l.erase d.fvarId
  let insts := (← getLocalInstances).filter fun i => need.contains i.fvar.fvarId!
  let m ← mkFreshExprMVarAt lctx' insts p
  try
    let [] ← runOn m.mvarId! (← `(tactic| omega)) | return none
    return some (← instantiateMVars m)
  catch _ => return none

/-- What is known of a fresh value `a`: `L ≤ a.val ≤ H`, and that fact. -/
abbrev Bounds := Std.HashMap FVarId (Int × Int × FVarId)

/-- `lo ≤ a.val ∧ a.val ≤ hi`. -/
def intervalP (a lo hi : Expr) : MetaM Expr := do
  let av ← mkAppM ``Subtype.val #[a]
  mkAppM ``And #[← mkAppM ``LE.le #[lo, av], ← mkAppM ``LE.le #[av, hi]]

/-- `h : p`, proved by `e`, in front of `g`. -/
def assertH (g : MVarId) (n : Lean.Name) (p e : Expr) : MetaM (FVarId × MVarId) := do
  (← g.assert n p e).intro1P

/-- `t` as a base and an integer offset (`b + k`, `b - k`, a literal `k`,
else `t + 0`). -/
def affine (t : Expr) : Option Expr × Int :=
  let lit? (e : Expr) : Option Int := do
    if e.isAppOfArity ``OfNat.ofNat 3 then
      return ((← (e.getArg! 1).rawNatLit?) : Int)
    if e.isAppOfArity ``Neg.neg 3 && (e.getArg! 2).isAppOfArity ``OfNat.ofNat 3 then
      return -((← ((e.getArg! 2).getArg! 1).rawNatLit?) : Int)
    none
  if let some k := lit? t then (none, k)
  else if t.isAppOfArity ``HAdd.hAdd 6 then
    match lit? (t.getArg! 5) with
    | some k => (some (t.getArg! 4), k)
    | none => (some t, 0)
  else if t.isAppOfArity ``HSub.hSub 6 then
    match lit? (t.getArg! 5) with
    | some k => (some (t.getArg! 4), -k)
    | none => (some t, 0)
  else (some t, 0)

/-- The integer equations of `e`. -/
partial def intEqs (e : Expr) (acc : Array Expr) : Array Expr :=
  let acc := if e.isAppOfArity ``Eq 3 && (e.getArg! 0).isConstOf ``Int then acc.push e else acc
  match e with
  | .app f x => intEqs x (intEqs f acc)
  | .lam _ t b _ | .forallE _ t b _ => intEqs b (intEqs t acc)
  | .letE _ t v b _ => intEqs b (intEqs v (intEqs t acc))
  | .mdata _ b => intEqs b acc
  | _ => acc

/-- The values `a.val` is equated to in `e`, none of which reads `a`. -/
def valuesOf (a : Expr) (e : Expr) : Array Expr := Id.run do
  let isA (x : Expr) := x.isAppOfArity ``Subtype.val 3 && x.appArg! == a
  let mut out := #[]
  for x in intEqs e #[] do
    if isA (x.getArg! 1) && !(x.getArg! 2).containsFVar a.fvarId! then
      out := out.push (x.getArg! 2)
    else if isA (x.getArg! 2) && !(x.getArg! 1).containsFVar a.fvarId! then
      out := out.push (x.getArg! 1)
  return out

/-- From a defining fact `hX : X = some a`, the interval its cases give
when they are offsets of one base (KeY's join with the conditional's bounds
in the antecedent): relative to the base (`hint`) and, where the base's own
is known, absolute (`hintA`, recorded in `bounds`).  Each by `omega` from
the fact alone.  `none` where reading the fact closed the goal. -/
def addInterval (g : MVarId) (hX : FVarId) (bounds : Bounds) :
    TacticM (Option (MVarId × Bounds)) := g.withContext do
  let ty ← instantiateMVars (← hX.getType)
  unless ty.isAppOfArity ``Eq 3 do return some (g, bounds)
  let rhs := ty.getArg! 2
  unless rhs.isAppOfArity ``Option.some 2 && rhs.appArg!.isFVar do return some (g, bounds)
  let a := rhs.appArg!
  -- a copy of the fact, read as `omega` reads it
  let (_, g₂) ← assertH g `hjoin ty (mkFVar hX)
  let gs ← runOn g₂ (← `(tactic| sol_close_join_fact $(mkIdent `hjoin)))
  let [g₃] := gs | if gs.isEmpty then return none else throwError "sol_close_join_steps: a fact split"
  g₃.withContext do
    let some hkD := (← getLCtx).findFromUserName? `hjoin | return some (g₃, bounds)
    let hk := hkD.fvarId
    let done (g : MVarId) (b : Bounds) : MetaM (Option (MVarId × Bounds)) := do
      return some (← g.tryClear hk, b)
    let vs := valuesOf a (← instantiateMVars hkD.type)
    if vs.isEmpty then return ← done g₃ bounds
    let ps := vs.map affine
    let base := ps[0]!.1
    for q in ps do
      match q.1, base with
      | none, none => pure ()
      | some x, some y => unless ← withReducible (isDefEq x y) do return ← done g₃ bounds
      | _, _ => return ← done g₃ bounds
    let (iLo, iHi) := Id.run do
      let mut lo := 0
      let mut hi := 0
      for i in [0:ps.size] do
        if ps[i]!.2 < ps[lo]!.2 then lo := i
        if ps[i]!.2 > ps[hi]!.2 then hi := i
      return (lo, hi)
    let (cLo, cHi) := (ps[iLo]!.2, ps[iHi]!.2)
    let p ← intervalP a vs[iLo]! vs[iHi]!
    let some e ← omegaIn #[hk] p | return ← done g₃ bounds
    match base with
    | none =>
      let (h, g₄) ← assertH g₃ `hintA p e
      done g₄ (bounds.insert a.fvarId! (cLo, cHi, h))
    | some b =>
      let (h, g₄) ← assertH g₃ `hint p e
      let some (L, H, hb) := (if b.isAppOfArity ``Subtype.val 3 && b.appArg!.isFVar then
          bounds.get? b.appArg!.fvarId! else none) | done g₄ bounds
      g₄.withContext do
        let pA ← intervalP a (toExpr (L + cLo)) (toExpr (H + cHi))
        let some eA ← omegaIn #[h, hb] pA | done g₄ bounds
        let (hA, g₅) ← assertH g₄ `hintA pA eA
        done g₅ (bounds.insert a.fvarId! (L + cLo, H + cHi, hA))

/-- A value that must return (`X.isSome = true`): a case per condition
(`CloseS.isSome_cond`, `CloseS.isSome_ite`), a halting case refuted by
`omega` from its conditions and the absolute intervals of the values they
read. -/
partial def closeSide (g : MVarId) (bounds : Bounds) (hyps : Array FVarId := #[]) :
    TacticM Bool := g.withContext do
  let t ← instantiateMVars (← g.getType)
  unless t.isAppOfArity ``Eq 3 && (t.getArg! 1).isAppOfArity ``Option.isSome 2 do return false
  let X ← whnfR (t.getArg! 1).appArg!
  let cases (lem : Lean.Name) : TacticM Bool := do
    let gs ← try g.apply (← mkConstWithFreshMVarLevels lem) catch _ => return false
    for g' in gs do
      let (h, g'') ← g'.intro1P
      unless ← closeSide g'' bounds (hyps.push h) do return false
    return true
  if X.isAppOfArity ``cond 4 then return ← cases ``CloseS.isSome_cond
  if X.isAppOfArity ``ite 5 then return ← cases ``CloseS.isSome_ite
  if X.isAppOfArity ``Option.some 2 then return (← observing? g.refl).isSome
  if X.isAppOfArity ``Option.none 1 then
    let mut keep := hyps
    for h in hyps do
      for f in (collectFVars {} (← instantiateMVars (← h.getType))).fvarIds do
        if let some (_, _, hb) := bounds.get? f then keep := keep.push hb
    let some e ← omegaIn keep (mkConst ``False) | return false
    g.assign (← mkFalseElim t e)
    return true
  return false

/-- What one step of evaluation leaves in front, opened: binders, premises,
landed states (`CloseS.LandedAll`), and a value as a fresh `a` and its
defining fact `X = some a`: under the box whatever it returns
(`CloseS.wp_box_optRes`), under the diamond with a goal that it returns
(`CloseS.exists_some_of`).
The goals left, the main one last, and the facts. -/
partial def introFront (g : MVarId) : MetaM (List MVarId × List FVarId) := g.withContext do
  let t ← whnfR (← instantiateMVars (← g.getType))
  if t.isForall || t.isAppOfArity ``CloseS.LandedAll 5 then
    let (_, g') ← g.intro1
    return ← introFront g'
  if t.isAppOfArity ``Modality.wp 4 && (t.getArg! 1).isConstOf ``Modality.box &&
      (t.getArg! 2).isAppOfArity ``Close.optRes 2 then
    let [g₁] ← g.apply (← mkAppM ``Iff.mpr #[← mkAppOptM ``CloseS.wp_box_optRes
        #[none, (t.getArg! 2).appArg!, t.getArg! 3]])
      | throwError "sol_close_join_steps: the box's value"
    let (fs, g₂) ← g₁.introN 2
    let (rest, hs) ← introFront g₂
    return (rest, fs[1]! :: hs)
  if t.isAppOfArity ``Exists 2 then
    match ← g.apply (← mkConstWithFreshMVarLevels ``CloseS.exists_some_of) with
    | [gS, gH] =>
      let (fs, gH') ← gH.introN 2
      let (rest, hs) ← introFront gH'
      return (gS :: rest, fs[1]! :: hs)
    | gs => throwError "sol_close_join_steps: {gs.length} goals from an existential"
  return ([g], [])

/-- The facts `introFront` named, each with its interval; the side goals,
each closed or failing.  `none` where the main goal closed. -/
def settle (gs : List MVarId) (hs : List FVarId) (bounds : Bounds) :
    TacticM (Option (MVarId × Bounds)) := do
  let some gMain := gs.getLast? | throwError "sol_close_join_steps: no goal"
  for gS in gs.dropLast do
    unless ← closeSide gS bounds do
      throwError "sol_close_join_steps: a value is not shown to return"
  let mut gM := gMain
  let mut bounds := bounds
  for h in hs do
    let some (g', b') ← addInterval gM h bounds | return none
    (gM, bounds) := (g', b')
  return some (gM, bounds)

/-- The leaf's binders and updates one at a time, the rest of the formula
held opaque (a fresh `ψ` and `rest = ψ`), so that each step evaluates one
update with `close_rw_s` and every value is named once.  Stops at the
first formula that is not a binder or an update; `none` where the goal
closed on the way. -/
partial def peel (g : MVarId) (bounds : Bounds) : TacticM (Option (MVarId × Bounds)) :=
    g.withContext do
  let t ← instantiateMVars (← g.getType)
  unless t.isAppOfArity ``Solidity.holds 4 do return some (g, bounds)
  let φ ← whnfR t.appArg!
  let rest? : Option Expr :=
    if φ.isAppOfArity ``Fml.upd 6 || φ.isAppOfArity ``Fml.bind 6 then some (φ.getArg! 5)
    else if φ.isAppOfArity ``Fml.all 5 then some (φ.getArg! 4)
    else none
  let some rest := rest? | return some (g, bounds)
  -- `∀ ψ, rest = ψ → holds σ (head ψ)`, built in place (no `kabstract`)
  let ty ← withLocalDeclD `ψ (← inferType rest) fun ψ => do
    withLocalDeclD `hψ (← mkEq rest ψ) fun h => do
      mkForallFVars #[ψ, h] (mkApp t.appFn! (mkAppN φ.getAppFn (φ.getAppArgs.pop.push ψ)))
  let g' ← mkFreshExprSyntheticOpaqueMVar ty (← g.getTag)
  g.assign (mkApp2 g' rest (← mkEqRefl rest))
  let (fs, g₁) ← g'.mvarId!.introNP 2
  let (ψ, hψ) := (fs[0]!, fs[1]!)
  let gs ← runOn g₁ (← `(tactic| simp (config := { maxSteps := 400000 }) only [close_rw_s]))
  let [g₂] := gs | if gs.isEmpty then return none else
    throwError "sol_close_join_steps: a step split the goal"
  let (gs, hs) ← introFront g₂
  let some (gM, bounds) ← settle gs hs bounds | return none
  -- the rest back, by its equation
  let gM ← gM.withContext do
    let tgt ← whnfR (← instantiateMVars (← gM.getType))
    unless tgt.isAppOfArity ``Solidity.holds 4 && tgt.appArg! == mkFVar ψ do
      throwError "sol_close_join_steps: a step left {tgt}"
    gM.replaceTargetEq (mkApp tgt.appFn! rest)
      (← mkCongrArg tgt.appFn! (← mkEqSymm (mkFVar hψ)))
  peel gM bounds

/-- The leaf (`Fml.Valid ψ`) closed one update at a time (`peel`), the post
read as the updates were, then `omega` on the intervals, the defining facts'
cases only if it fails (`sol_close_finish`, within 20000 heartbeats of its
own: a false leaf fails in about the cost of a true one).  Fails where a
goal is left. -/
def closeSteps : TacticM Unit := do
  evalTactic (← `(tactic| (sol_close_unwrap; intro σ)))
  let some (g, bounds) ← peel (← getMainGoal) {} | setGoals []; return
  let gs ← runOn g (← `(tactic| sol_close_eval))
  let mut rest : Array MVarId := #[]
  for g in gs do
    let (gs', hs) ← introFront g
    if let some (g', _) ← settle gs' hs bounds then rest := rest.push g'
  setGoals rest.toList
  evalTactic (← `(tactic| all_goals first | omega | sol_skip_after 20000 sol_close_finish))
  unless (← getGoals).isEmpty do throwError "sol_close_join_steps: goals left"

/-- `sol_close_join_steps`'s budget, in thousands of heartbeats, within the
declaration's own. -/
def budget : Nat := 100000

end CloseJ

@[tactic Solidity.tacticSol_close_few_joins]
def evalSolCloseFewJoins : Tactic := fun _ => withMainContext do
  let ty ← instantiateMVars (← getMainTarget)
  if CloseJ.countJoins ty 0 (CloseJ.wholeMax + 1) > CloseJ.wholeMax then
    throwError "sol_close_few_joins: more than {CloseJ.wholeMax} joined updates"

@[tactic Solidity.tacticSol_close_join_steps]
def evalSolCloseJoinSteps : Tactic := fun _ => withMainContext do
  let ty ← instantiateMVars (← getMainTarget)
  unless ty.isAppOf ``Solidity.Fml.Valid && CloseJ.countJoins ty 0 ≥ CloseJ.stepsMin do
    throwError "sol_close_join_steps: fewer than {CloseJ.stepsMin} joined updates"
  let saved ← saveState
  let ok ← tryCatchRuntimeEx (Budget.within CloseJ.budget do
      Term.withoutErrToSorry <| withoutRecover CloseJ.closeSteps
      pure true) (fun _ => pure false)
  unless ok do
    saved.restore
    throwError "sol_close_join_steps: the leaf did not close"

@[tactic Solidity.tacticSol_close_denote]
def evalSolCloseDenote : Tactic := fun _ => withMainContext do
  unless ← aliasDenoteLeft do throwError "sol_close_denote: no alias read left as a Theory value"
  -- the equations of Theory values in scope, back into the goal: read alike
  -- with it, nothing else rewritten (the landed states others depend on)
  let mut hs : Array FVarId := #[]
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    if ty.isEq && (ty.find? (·.isAppOf ``Tm.denote)).isSome then hs := hs.push d.fvarId
  let (_, g) ← (← getMainGoal).revert hs
  replaceMainGoal [g]
  -- read in the Theory, the alias at the path it holds: an `ensures` the
  -- frame below gave and the frame's own read alike
  evalTactic (← `(tactic| (
    simp (config := { maxSteps := 100000 }) only [CloseS.denote_len, CloseS.denote_find,
      CloseS.denote_storage, CloseS.denote_root, CloseS.denote_pvP, Option.elim_some,
      CloseS.Landed.locV_eq, CloseS.Landed.storage_eq, State.locV_push, CloseS.push_here,
      CloseS.push_there, CloseS.push_storage, CloseS.glob_storage]
    all_goals intros
    all_goals first | rfl | assumption)))

/-- Typed values occurring under projections, including dependent anonymous locals.
Inspect at most 8,192 local declarations/expression nodes and add at most
128 range facts. Unresolved types are left alone. -/
private def addRangeFacts (g : MVarId) : MetaM MVarId := g.withContext do
  let mut todo : Array Expr := #[← g.getType]
  let mut known : Array Expr := #[]
  let mut nodes := 0
  for d in ← getLCtx do
    if nodes ≥ 8192 then break
    nodes := nodes + 1
    unless d.isImplementationDetail do
      todo := todo.push d.type
      known := known.push d.type
  let unsigned ← whnfR (mkApp (mkConst ``PrimTy.Denote) (mkConst ``PrimTy.uint))
  let signed ← whnfR (mkApp (mkConst ``PrimTy.Denote) (mkConst ``PrimTy.int))
  let mut seen : Std.HashSet Expr := {}
  let mut values : Std.HashSet Expr := {}
  let mut goal := g
  let mut facts := 0
  while !todo.isEmpty && nodes < 8192 && facts < 128 do
    let e := todo.back!
    todo := todo.pop
    nodes := nodes + 1
    if seen.contains e then continue
    seen := seen.insert e
    let value? := if e.isAppOfArity ``Subtype.val 3 then some (e.getArg! 2)
      else match e with
        | .proj ``Subtype 0 v => some v
        | _ => none
    if let some v := value? then
      unless v.hasLooseBVars || v.hasMVar || values.contains v do
        values := values.insert v
        let ty ← whnfR (← inferType v)
        if ty.hasMVar then continue
        let lemma? ← if ← isDefEq ty unsigned then pure (some ``CloseS.uintRange)
          else if ← isDefEq ty signed then pure (some ``CloseS.intRange)
          else pure none
        if let some lemma := lemma? then
          let pf ← mkAppM lemma #[v]
          let ty ← inferType pf
          unless known.contains ty do
            let (_, next) ← goal.note `range pf
            goal := next
            known := known.push ty
            facts := facts + 1
    match e with
    | .app f a => todo := (todo.push f).push a
    | .lam _ t b _ | .forallE _ t b _ => todo := (todo.push t).push b
    | .letE _ t v b _ => todo := ((todo.push t).push v).push b
    | .mdata _ b | .proj _ _ b => todo := todo.push b
    | _ => pure ()
  return goal

/-- KeY's `exLeft` and `andLeft`, each a single-branch elimination.
Inspect at most 8,192 declarations across all scans and eliminate at most
128 witnesses/conjunctions. -/
private def exposeWitnesses (g : MVarId) : MetaM MVarId := do
  let mut goal := g
  let mut remaining := 8192
  for _ in [0:128] do
    let (selected, left) ← goal.withContext do
      let mut left := remaining
      for d in ← getLCtx do
        if left == 0 then return (none, 0)
        left := left - 1
        unless d.isImplementationDetail do
          if ← isProp d.type then
            let ty ← whnfR d.type
            if ty.isAppOf ``Exists || ty.isAppOf ``And then return (some d.fvarId, left)
      return (none, left)
    remaining := left
    let some h := selected | return goal
    let tag ← goal.getTag
    let branches ← goal.cases h
    let [branch] := branches.toList
      | throwError "sol_close_enrich: expected a single witness branch"
    goal := branch.mvarId
    goal.setTag tag
  return goal

/-- Expose intrinsic range facts and witnesses that become visible after a read.
Each operation constructs ordinary checked proofs; no arithmetic result is assumed. -/
@[tactic Solidity.tacticSol_close_enrich]
def evalSolCloseEnrichS : Tactic := fun _ => focus <| withMainContext do
  unless ← Close.scopedGoal do throwUnsupportedSyntax
  let g ← addRangeFacts (← getMainGoal)
  replaceMainGoal [g]
  evalTactic (← `(tactic| try simp_all only [CloseS.uintRange, CloseS.intRange,
    true_implies, not_true_eq_false, false_implies]))
  let some g := (← getUnsolvedGoals).head? | return
  let g ← exposeWitnesses g
  replaceMainGoal [g]
  evalTactic (← `(tactic| try simp_all only [Option.some.injEq, exists_eq_left', exists_eq',
    forall_eq', Classical.not_not]))
  let some g := (← getUnsolvedGoals).head? | return
  let g ← addRangeFacts g
  replaceMainGoal [g]

end Solidity
