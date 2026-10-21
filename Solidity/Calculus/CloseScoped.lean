import Solidity.Calculus.Close
import Solidity.Calculus.SeqRewrite
import Solidity.Theory.Typed.Mem
import Solidity.Calculus.EvalEqs
import Solidity.Calculus.TermAgree

/-!
# `sol_close` on a scoped leaf

`sol_symex` on a scoped goal (`⊨ dl!{ … }` under `open scoped Solidity.Scoped`)
leaves leaves `Valid ψ`, `ψ : Fml C []` with no modality.  `sol_close`,
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

theorem locV_havoc (σ : State C Γ) (st : Storage C) (nt : Ledger) :
    (σ.havoc st nt).locV = σ.locV := rfl

/-! The global part a field at a time: the leaf reads fields, never the
global part whole, so no rewrite changes a type that depends on it. -/

theorem glob_storage (σ : State C Γ) : σ.glob.storage = σ.storage := rfl
theorem glob_net (σ : State C Γ) : σ.glob.net = σ.net := rfl
theorem glob_selfBalance (σ : State C Γ) : σ.glob.selfBalance = σ.selfBalance := rfl
theorem glob_tx (σ : State C Γ) : σ.glob.tx = σ.tx := rfl
theorem glob_envVal (σ : State C Γ) (k : EnvKey) : σ.glob.envVal k = σ.envVal k := rfl
theorem havoc_storage (σ : State C Γ) (st : Storage C) (nt : Ledger) :
    (σ.havoc st nt).storage = st := rfl
theorem havoc_net (σ : State C Γ) (st : Storage C) (nt : Ledger) :
    (σ.havoc st nt).net = nt := rfl
theorem havoc_selfBalance (σ : State C Γ) (st : Storage C) (nt : Ledger) :
    (σ.havoc st nt).selfBalance = σ.selfBalance := rfl
theorem havoc_tx (σ : State C Γ) (st : Storage C) (nt : Ledger) :
    (σ.havoc st nt).tx = σ.tx := rfl
theorem push_storage {t : LTy} (σ : State C Γ) (v : t.TDenote C σ.H) :
    (σ.push v).storage = σ.storage := rfl
/-- A memory array's length read through a pushed local is the state's: the
length is a number, so the rewrite changes no type that depends on the heap
typing (a premise read before a local and a goal read after it read one
length, `allLeftHide`'s instances among them). -/
theorem push_lenU {t : LTy} (σ : State C Γ) (v : t.TDenote C σ.H) {E : Ty}
    (r : HRef σ.H (.array E)) : (σ.push v).glob.memT.heap.lenU r = σ.glob.memT.heap.lenU r := rfl
theorem push_keccakId {t : LTy} (σ : State C Γ) (v : t.TDenote C σ.H) (R : RefTy) (id : Nat) :
    (σ.push v).glob.memT.keccakId R id = σ.glob.memT.keccakId R id := rfl
theorem push_net {t : LTy} (σ : State C Γ) (v : t.TDenote C σ.H) : (σ.push v).net = σ.net := rfl
theorem push_selfBalance {t : LTy} (σ : State C Γ) (v : t.TDenote C σ.H) :
    (σ.push v).selfBalance = σ.selfBalance := rfl
theorem push_tx {t : LTy} (σ : State C Γ) (v : t.TDenote C σ.H) : (σ.push v).tx = σ.tx := rfl
theorem setLocal_storage {t : LTy} (σ : State C Γ) (i : Idx Γ t) (v : t.TDenote C σ.H) :
    (σ.setLocal i v).storage = σ.storage := rfl
theorem setLocal_keccakId {t : LTy} (σ : State C Γ) (i : Idx Γ t) (v : t.TDenote C σ.H)
    (R : RefTy) (id : Nat) :
    (σ.setLocal i v).glob.memT.keccakId R id = σ.glob.memT.keccakId R id := rfl
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
theorem eval_keccak {R : RefTy} (m : Tm C Γ .mem) (i : Tm C Γ (.ident R)) :
    (Tm.app2 .keccak m i).eval σ = (m.eval σ).bind fun g => (i.eval σ).bind fun id =>
      some (g.keccakId R id) := rfl
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
      (r.eval σ₀).bind fun addr => (a.eval σ₀).map fun amt =>
        g.withNet (if addr.1 = σ₀.tx.selfAddress.1 then g.1.net
          else setBy addr ((lookupBy addr g.1.net).getD 0 - amt.1) g.1.net) := by
  show (r.eval σ₀).bind _ = _
  cases r.eval σ₀ with
  | none => rfl
  | some _ => show Option.bind _ _ = _; cases a.eval σ₀ <;> rfl
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
theorem withStorage_keccakId {H : HTy} (g : GlobT C H) (st : Storage C) (R : RefTy) (id : Nat) :
    (g.withStorage st).1.memT.keccakId R id = g.1.memT.keccakId R id := rfl
theorem withNet_keccakId {H : HTy} (g : GlobT C H) (nt : Ledger) (R : RefTy) (id : Nat) :
    (g.withNet nt).1.memT.keccakId R id = g.1.memT.keccakId R id := rfl
theorem withBalance_keccakId {H : HTy} (g : GlobT C H) (b : PrimTy.uint.Denote) (R : RefTy)
    (id : Nat) : (g.withBalance b).1.memT.keccakId R id = g.1.memT.keccakId R id := rfl
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
theorem valid_of_holds {φ : Fml C []} (h : ∀ σ : State C [], holds σ φ) : Valid φ := h

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
theorem Landed.keccakId_eq {Δ : Ctx} {g : State C []} {ℓ : LocsV C Δ} (x : Landed g ℓ)
    (R : RefTy) (id : Nat) : x.val.glob.memT.keccakId R id = g.memT.keccakId R id := by
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
    holds σ (.havoc φ) ↔ ∀ (st : Storage C) nt, holds (σ.havoc st nt) φ := Iff.rfl
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
  CloseS.holds_bind_oldNet CloseS.holds_bind_kint CloseS.holds_anon
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
  CloseS.setLocal_storage CloseS.setLocal_net CloseS.setLocal_selfBalance CloseS.setLocal_tx
  CloseS.envVal_msgSender CloseS.envVal_msgValue CloseS.envVal_timestamp
  CloseS.envVal_selfBalance CloseS.envVal_selfAddress
  CloseS.Landed.storage_eq CloseS.Landed.net_eq CloseS.Landed.selfBalance_eq CloseS.Landed.tx_eq
  CloseS.Landed.keccakId_eq CloseS.push_keccakId CloseS.setLocal_keccakId
  CloseS.withStorage_keccakId CloseS.withNet_keccakId CloseS.withBalance_keccakId
  CloseS.Landed.locV_eq
  CloseS.set_push_here CloseS.set_push_there CloseS.drop_refl' CloseS.drop_push' CloseS.thin_refl'
  CloseS.thin_keep' CloseS.thin_drop'
  CloseS.landedAll_const CloseS.landedRest_def
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
  CloseS.eval_keccak
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
    ``Fml.modal, ``Fml.havoc, ``Fml.all, ``Fml.bind, ``Fml.anon, ``Fml.allocAll]
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
  | some ``Fml.anon, 4 | some ``Fml.allocAll, 5 => last goal
  | some ``Fml.tt, _ | some ``Fml.wellFormed, _ | some ``Fml.modal, _ => return φ
  | _, _ => mkAppM ``Fml.evalEqs #[toExpr goal, φ]

/-- `sol_close_unwrap` on a scoped leaf `Valid ψ`: its equations read by the
interpreter (`Valid.of_evalEqs`, `Calculus/EvalEqs.lean`, computed by
`evalEqsE`), then `holds` in every typed state (`CloseS.valid_of_holds`). -/
@[tactic Solidity.tacticSol_close_unwrap]
def evalSolCloseUnwrapS : Tactic := fun _ => withMainContext do
  let g ← getMainGoal
  let ty ← instantiateMVars (← g.getType)
  unless ty.isAppOf ``Solidity.Valid do throwUnsupportedSyntax
  let tag ← g.getTag
  -- the pass where every equation's Booleans reduce, else the leaf as it is
  let g₂ ← try
      let φ' ← evalEqsE true ty.appArg!
      let [g₁] ← g.apply (← mkConstWithFreshMVarLevels ``Valid.of_evalEqs) | failure
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
  return (t.find? fun e => e.isConstOf ``Fml.allocAll || e.isConstOf ``State.alloc).isSome

/-- `sol_close`'s lemmas on a fresh object (`Fml.allocAll`), outside
`close_rw_s`: `allocInGoal` adds them. -/
def allocLemmas : TacticM (Array (TSyntax ``Lean.Parser.Tactic.simpLemma)) :=
  #[``CloseS.holds_allocAll, ``CloseS.alloc_storage, ``CloseS.alloc_net,
    ``CloseS.alloc_selfBalance, ``CloseS.alloc_tx, ``CloseS.locV_alloc, ``CloseS.alloc_snd_id,
    ``CloseS.push_lenId, ``CloseS.alloc_lenId, ``CloseS.push_readT, ``CloseS.alloc_readT_index,
    ``CloseS.push_readId, ``CloseS.alloc_readId_index].mapM fun n =>
      `(Lean.Parser.Tactic.simpLemma| $(mkIdent n):ident)

/-- The extra lemmas where the goal reads a fresh object, none elsewhere. -/
def allocExtra : TacticM (Array (TSyntax ``Lean.Parser.Tactic.simpLemma)) := do
  if ← allocInGoal then allocLemmas else pure #[]

@[tactic Solidity.tacticSol_close_eval, tactic Solidity.tacticSol_close_mt_eval]
def evalSolCloseEvalS : Tactic := onScoped do
  let ex ← allocExtra
  if ex.isEmpty then `(tactic| simp only [close_rw_s])
  else `(tactic| simp only [close_rw_s, $ex,*])

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
  evalTactic (← `(tactic| simp_all only [CloseS.uintRange, CloseS.intRange,
    true_implies, not_true_eq_false, false_implies]))
  let some g := (← getUnsolvedGoals).head? | return
  let g ← exposeWitnesses g
  replaceMainGoal [g]
  evalTactic (← `(tactic| simp_all only [Option.some.injEq, exists_eq_left', exists_eq',
    forall_eq', Classical.not_not]))
  let some g := (← getUnsolvedGoals).head? | return
  let g ← addRangeFacts g
  replaceMainGoal [g]

end Solidity
