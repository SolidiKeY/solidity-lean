import Solidity.Calculus.TermEval

/-!
# Lowering scoped expressions to terms

`Update.lean`'s lowering (Maude's `lower(LV, C)`) on the scoped syntax, at
the typed sorts (`Signature.lean`; `docs/intrinsic.md`, W9.8.2 and W9.8.3):
a program expression read in `Γ` becomes a term read in `Γ`, a local its
position.  A root or a member carries the `rootType`/`fieldType` proof the
scoped syntax already holds (`Loc.root r h`, `Loc.field b f h`), so nothing
is re-proved by `rfl`.  Beside it, the update elements the arms of
`Stmt.step` build (`Calculus/Arms.lean`): `UpdElem.save`, `OpLoc.set`, …

**What has no term of its own.**  A memory path at a word (`MPath.loc l`,
`l : MLoc C Γ (.prim p)`) reads no identity: `MPath.lower` gives it its
address (`Ty.mpathSrt`); no arm reads a word through it.
-/

namespace Solidity

variable {C : Contract} {Γ : Ctx}

/-! ## Casts and constants -/

/-- A term at one word type read at an equal one (`hq ▸`, named so the
bridge has one lemma for it). -/
def Tm.castV {p q : PrimTy} (h : p = q) (t : Tm C Γ (.val p)) : Tm C Γ (.val q) := h ▸ t

/-- `1` at a numeric type. -/
def Tm.one (p : PrimTy) (hp : p.isNumeric = true) : Tm C Γ (.val p) :=
  .app0 (.lit (PrimTy.ofLit p 1 (by cases p <;> first | rfl | exact absurd hp Bool.false_ne_true)))

/-- `0` at a numeric type, as in the outer guard of `sp.push() /= se`. -/
def Tm.zero (p : PrimTy) (hp : p.isNumeric = true) : Tm C Γ (.val p) :=
  .app0 (.lit (PrimTy.ofLit p 0 (by cases p <;> first | rfl | exact absurd hp Bool.false_ne_true)))

/-- The zero compared with `se` in `sp.push() /= se`: infer its numeric type
from the term, independent of the names of the rule's type/proof binders. -/
def Tm.zeroLike {p : PrimTy} (_ : Tm C Γ (.val p))
    (hp : p.isNumeric = true := by first | rfl | assumption) : Tm C Γ (.val p) := Tm.zero p hp

/-- A compound operator (`+=` …) takes and returns its numeric type. -/
theorem BinOp.compound_accepts {op : BinOp} (hop : op.hasCompoundAssign = true) {p : PrimTy}
    (hp : p.isNumeric = true) : op.accepts p = true := by
  cases op <;> simp only [BinOp.hasCompoundAssign, Bool.false_eq_true] at hop <;> exact hp

theorem BinOp.compound_ret {op : BinOp} (hop : op.hasCompoundAssign = true) (p : PrimTy) :
    op.ret p = p := by
  cases op <;> simp only [BinOp.hasCompoundAssign, Bool.false_eq_true] at hop <;> rfl

/-- `++`/`--`'s operator is a compound one. -/
theorem IncDec.binOp_compound (op : IncDec) : op.binOp.hasCompoundAssign = true := by
  cases op <;> rfl

/-! ## Expressions -/

/-- A simple value's term. -/
def Simple.lower : {p : PrimTy} → Simple C Γ p → Tm C Γ (.val p)
  | p, .lit n h => .app0 (.lit (PrimTy.ofLit p n h))
  | _, .bool b => .app0 (.lit (p := .bool) b)
  | _, .local i => .pvV i
  | _, .env k hp => Tm.castV hp.symm (.app0 (.env k))


/-- The sort a memory path lowers to: an identity at a reference, an address
at a word (which holds no identity: the module docstring). -/
@[reducible] def Ty.mpathSrt : Ty → Srt
  | .ref R => .ident R
  | .prim p => .addr (.prim p)

/-- A memory location read as a path: `iread(memory, l)` at a reference,
the address itself at a word. -/
def Tm.mread : (T : Ty) → Tm C Γ (.addr T) → Tm C Γ T.mpathSrt
  | .ref _, a => .app2 .iread (.app0 .memory) a
  | .prim _, a => a

mutual

def SPath.lower : {T : Ty} → SPath C Γ T → Tm C Γ (.path T)
  | _, .alias i => .pvP i
  | _, .loc l => l.lower

def Loc.lower : {T : Ty} → Loc C Γ T → Tm C Γ (.path T)
  | _, .root r h => .app0 (.root r h)
  | _, .field b _ h => .app1 (.field h) b.lower
  | _, .index it b i => .app2 (.at it) b.lower i.lower

def MPath.lower : {T : Ty} → MPath C Γ T → Tm C Γ T.mpathSrt
  | _, .var i _ => .pvI i
  | T, .loc l => Tm.mread T l.lower

def MLoc.lower : {T : Ty} → MLoc C Γ T → Tm C Γ (.addr T)
  | _, .field b _ h => .app1 (.mfield h) b.lower
  | _, .index a b i => .app2 (.mat a) b.lower i.lower

def Val.lower : {p : PrimTy} → Val C Γ p → Tm C Γ (.val p)
  | _, .simple s => s.lower
  | _, .read l => .app2 .find (.app0 .storage) l.lower
  | _, .binop op h hq a b => Tm.castV hq (.app2 (.binop op h) a.lower b.lower)
  | _, .unop op h hq a => Tm.castV hq (.app1 (.unop op h) a.lower)
  | _, .ternary c a b => .app3 .ite c.lower a.lower b.lower
  | _, .readMem l => .app2 .read (.app0 .memory) l.lower
  | _, .len b hp => Tm.castV hp.symm (.app2 .len (.app0 .storage) b.lower)
  | _, .mlen b hp => Tm.castV hp.symm (.app2 .mlen (.app0 .memory) b.lower)
  | _, .modular op a b k => .app3 (.modular op) a.lower b.lower k.lower
  | _, .keccak b hp => Tm.castV hp.symm (.app2 .keccak (.app0 .memory) b.lower)

end

/-- A write's source as a storage value. -/
def Src.lower {T : Ty} : Src C Γ T → Tm C Γ (.sv T)
  | .val v => .app1 .sval v.lower
  | .copy p _ => .app2 .sfind (.app0 .storage) p.lower
  | .fixedCopy p shape _ => .app1 (.fixedCopy shape) (.app2 .sfind (.app0 .storage) p.lower)
  | .copyMem p => .app2 .copyMem (.app0 .memory) p.lower

/-- A memory write's source. -/
def MSrc.lower {T : Ty} : MSrc C Γ T → Tm C Γ (.mv T)
  | .val v => .app1 .mval v.lower
  | .ref p => .app1 .ref p.lower

/-! ## The update elements of the arms

The elements `Calculus/Arms.lean`'s premises update by, and what a
compound assignment or an increment reads and writes. -/

namespace UpdElem

/-- `{v := e}` (`Premise.setLocal`). -/
def setLocal {p : PrimTy} (i : Idx Γ (.val p)) (v : Val C Γ p) : UpdElem C Γ Γ :=
  .local i (.val v.lower)

/-- `storage := save(storage, l, src)` (`Premise.save`). -/
def save {T : Ty} (l : Loc C Γ T) (r : Src C Γ T) : UpdElem C Γ Γ :=
  .storage (.app3 .save (.app0 .storage) l.lower r.lower)

/-- `storage := save(storage, l, copyMem(memory, p))` (`Premise.saveMem`), at
one reference type. -/
def saveMem {R : RefTy} (l : Loc C Γ (.ref R)) (p : MPath C Γ (.ref R)) : UpdElem C Γ Γ :=
  .storage (.app3 .save (.app0 .storage) l.lower (.app2 .copyMem (.app0 .memory) p.lower))

/-- `storage := delAt(storage, l)` (`Premise.delAt`). -/
def delAt {T : Ty} (l : Loc C Γ T) : UpdElem C Γ Γ :=
  .storage (.app2 .delAt (.app0 .storage) l.lower)

/-- `memory := write(memory, l, src)` (`Premise.writeMem`). -/
def writeMem {T : Ty} (l : MLoc C Γ T) (r : MSrc C Γ T) : UpdElem C Γ Γ :=
  .memory (.app3 .write (.app0 .memory) l.lower r.lower)

/-- `delete` of the memory slot at `a` (`Premise.clearMem`): a reference
written a fresh default, which takes its type free of mappings (the
`MPath.var` it is read through proves it). -/
def clearMem : (T : Ty) → Tm C Γ (.addr T) → T.mapFree = true → UpdElem C Γ Γ
  | .prim p, a, _ => .memory (.app3 .write (.app0 .memory) a (.app1 .mval (.app0 (.lit (PrimTy.dflt p)))))
  | .ref R, a, h => .memory (.app3 .write (.app1 (.addM R h) (.app0 .memory)) a
      (.app1 .ref (.app1 (.alloc R h) (.app0 .memory))))

/-- `storage := pushSlot(storage, b)` (`storagePushLengthSave`). -/
def pushSlot {E : Ty} (b : SPath C Γ (.array E)) : UpdElem C Γ Γ :=
  .storage (.app2 .pushSlot (.app0 .storage) b.lower)

/-- `storage := pushSlot(storage, b)` at a mapping element: the same
length-only save. -/
abbrev extend {E : Ty} (b : SPath C Γ (.array E)) : UpdElem C Γ Γ := pushSlot b

/-- `storage := push(storage, b, src)` (`storagePushValueSave`, `…CopySource`). -/
def push {E : Ty} (b : SPath C Γ (.array E)) (v : Src C Γ E) : UpdElem C Γ Γ :=
  .storage (.app3 .push (.app0 .storage) b.lower v.lower)

/-- `storage := pop(storage, b)` (`storagePopSave`). -/
def pop {E : Ty} (b : SPath C Γ (.array E)) : UpdElem C Γ Γ :=
  .storage (.app2 .pop (.app0 .storage) b.lower)

/-- `storage := shrink(storage, b)` (`storagePopSaveMappingElement`). -/
def shrink {E : Ty} (b : SPath C Γ (.array E)) : UpdElem C Γ Γ :=
  .storage (.app2 .shrink (.app0 .storage) b.lower)

/-- A payment (`UpdElem.payTo`). -/
def payTo (r a : Simple C Γ .uint) : UpdElem C Γ Γ := .pay r.lower a.lower

/-- `lsv := p` (`rebindStep`). -/
def rebind {R : RefTy} (i : Idx Γ (.alias R)) (p : SPath C Γ (.ref R)) : UpdElem C Γ Γ :=
  .local i (.path p.lower)

/-- `mv := p` (`rebindMemStep`). -/
def rebindMem {R : RefTy} (i : Idx Γ (.mem R)) (p : MPath C Γ (.ref R)) : UpdElem C Γ Γ :=
  .local i (.mref p.lower)

end UpdElem

namespace Upd

/-- `{mv := freshId(copySt(memory, v)) ‖ memory := copySt(memory, v)}`
(`Premise.allocCopy`): the copied type free of mappings. -/
def allocCopy {R : RefTy} (i : Idx Γ (.mem R)) (h : (Ty.ref R).mapFree = true)
    (v : Tm C Γ (.sv (.ref R))) : Upd C Γ Γ :=
  (Upd.nil.snoc (.local i (.mref (.app2 (.copy h) (.app0 .memory) v)))).snoc
    (.memory (.app2 (.copySt h) (.app0 .memory) v))

/-- `{mv := freshId(addM(memory)) ‖ memory := addM(memory)}`
(`memoryRootDeleteFreshRebind`). -/
def allocFresh {R : RefTy} (i : Idx Γ (.mem R)) (h : (Ty.ref R).mapFree = true) : Upd C Γ Γ :=
  (Upd.nil.snoc (.local i (.mref (.app1 (.alloc R h) (.app0 .memory))))).snoc
    (.memory (.app1 (.addM R h) (.app0 .memory)))

/-- `{storage := pushSlot(storage, b) ‖ lsv := b[b.length]}`
(`storageLocalRootPushBind`). -/
def pushBind {R : RefTy} (i : Idx Γ (.alias R)) (b : SPath C Γ (.array (.ref R))) : Upd C Γ Γ :=
  (Upd.nil.snoc (.storage (.app2 .pushSlot (.app0 .storage) b.lower))).snoc
    (.local i (.path (.app1 .next b.lower)))

/-- A mapping slot retained while the array grows and its alias binds. -/
def pushBindMapping {R : RefTy} (i : Idx Γ (.alias R)) (b : SPath C Γ (.array (.ref R))) : Upd C Γ Γ :=
  (Upd.nil.snoc (.storage (.app2 .pushSlot (.app0 .storage) b.lower))).snoc
    (.local i (.path (.app1 .next b.lower)))

/-- `{storage := pushSlot(storage, b) ‖ v := defVal(T)}`
(`storageLocalPrimitivePushBind`): `uint y = values.push();`, `y` the default
the cleared slot holds. -/
def pushBindPrim {p : PrimTy} (i : Idx Γ (.val p)) (b : SPath C Γ (.array (.prim p))) : Upd C Γ Γ :=
  (Upd.nil.snoc (UpdElem.pushSlot b)).snoc (.local i (.val (.app0 (.lit (PrimTy.dflt p)))))

end Upd

/-! ### Compound assignment and `++`/`--` -/

/-- The value a compound target holds, as the rules read it: `v`,
`find(storage, l)`, `read(memory, l)`. -/
def OpLoc.cur {p : PrimTy} : OpLoc C Γ p → Tm C Γ (.val p)
  | .local i => .pvV i
  | .root r h => (Val.read (Γ := Γ) (.root r h)).lower
  | .field b f h => (Val.read (.field b f h)).lower
  | .index it b ie => (Val.read (.index it b (.simple ie))).lower
  | .mfield b f h => (Val.readMem (.field b f h)).lower
  | .mindex a b ie => (Val.readMem (.index a b (.simple ie))).lower

/-- The compound target set to `t`: `v := t`, `storage := save(storage, l, t)`,
`memory := write(memory, l, t)`. -/
def OpLoc.set {p : PrimTy} : OpLoc C Γ p → Tm C Γ (.val p) → UpdElem C Γ Γ
  | .local i, t => .local i (.val t)
  | .root r h, t =>
    .storage (.app3 .save (.app0 .storage) (Loc.root (Γ := Γ) r h).lower (.app1 .sval t))
  | .field b f h, t =>
    .storage (.app3 .save (.app0 .storage) (Loc.field b f h).lower (.app1 .sval t))
  | .index it b ie, t =>
    .storage (.app3 .save (.app0 .storage) (Loc.index it b (.simple ie)).lower (.app1 .sval t))
  | .mfield b f h, t =>
    .memory (.app3 .write (.app0 .memory) (MLoc.field b f h).lower (.app1 .mval t))
  | .mindex a b ie, t =>
    .memory (.app3 .write (.app0 .memory) (MLoc.index a b (.simple ie)).lower (.app1 .mval t))

/-- `l ⊕ t`, at a compound operator and a numeric type. -/
def OpLoc.op {p : PrimTy} (l : OpLoc C Γ p) (op : BinOp) (hop : op.hasCompoundAssign = true)
    (hp : p.isNumeric = true) (t : Tm C Γ (.val p)) : Tm C Γ (.val p) :=
  Tm.castV (BinOp.compound_ret hop p) (.app2 (.binop op (BinOp.compound_accepts hop hp)) l.cur t)

/-- The value `t++` has: the bumped one for `++t`, the old one for `t++`
(the rule lines' `t⊕⊕`). -/
def Tm.bumped (op : IncDec) {p : PrimTy} (hp : p.isNumeric = true) (t : Tm C Γ (.val p)) :
    Tm C Γ (.val p) :=
  if op.isPre then
    Tm.castV (BinOp.compound_ret op.binOp_compound p)
      (.app2 (.binop op.binOp (BinOp.compound_accepts op.binOp_compound hp)) t (Tm.one p hp))
  else t

/-! ### Primitive push followed by a compound update -/

namespace PushSuffix

/-- Division and remainder test their simple source before either update. -/
def needsZeroGuard (op : BinOp) : Bool := op == .div || op == .mod

/-- `se != 0`, the outer condition of `sp.push() /= se` and `%= se`. -/
def nonzero {p : PrimTy} (hp : p.isNumeric = true) (se : Simple C Γ p) : Fml C Γ :=
  .not (.eq se.lower (Tm.zero p hp))

/-- `size(sp) - 1`, read after the push update in `sp.push() += se`. -/
def lastIndex {E : Ty} (b : SPath C Γ (.array E)) : Tm C Γ (.val .uint) :=
  .app2 (.binop .sub rfl) (.app2 .len (.app0 .storage) b.lower)
    (.app0 (.lit ⟨1, rfl⟩))

/-- The appended primitive slot, addressed in the storage left by the push. -/
def lastPath {p : PrimTy} (b : SPath C Γ (.array (.prim p))) : Tm C Γ (.path (.prim p)) :=
  .app2 (.at (.arr .dyn)) b.lower (lastIndex b)

/-- The second update of `sp.push() += se`: read and modify the appended slot. -/
def saveOp {p : PrimTy} (op : BinOp) (hop : op.hasCompoundAssign = true)
    (hp : p.isNumeric = true) (b : SPath C Γ (.array (.prim p)))
    (se : Simple C Γ p) : Upd C Γ Γ :=
  Upd.nil.snoc (.storage (.app3 .save (.app0 .storage) (lastPath b) (.app1 .sval
    (Tm.castV (BinOp.compound_ret hop p) (.app2 (.binop op (BinOp.compound_accepts hop hp))
      (.app2 .find (.app0 .storage) (lastPath b)) se.lower)))))

end PushSuffix

end Solidity
