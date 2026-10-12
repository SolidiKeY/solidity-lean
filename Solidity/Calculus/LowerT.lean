import Solidity.Calculus.TypedTerm

/-!
# Lowering scoped expressions to typed terms

`Calculus/Lower.lean`'s lowering at the typed sorts of `Signature.lean`
(W9.8.2): a program expression read in `Γ` becomes a `TmT` read in `Γ`.  A
root or a member carries the `rootType`/`fieldType` proof the scoped syntax
already holds (`Loc.root r h`, `Loc.field b f h`), so nothing is re-proved
by `rfl`.  Beside it, the update elements the arms of `Stmt.step` build
(`Calculus/Arms.lean`), typed: `UpdElemT.save`, `OpLoc.setT`, …

Each has its bridge, `(x.lowerT).erase = x.lower` (`Simple.lowerT_erase`,
…, `OpLoc.setT_erase`): the typed lowering erases to the untyped one,
term for term, so a rule stated on `lowerT` is the rule stated on `lower`.

It sits above `Calculus/TypedTerm.lean`, so above `Calculus/Arms.lean` and
`Calculus/Rules.lean`: nothing below reads it yet (W9.8.3 moves `TmT` under
the rules, `docs/intrinsic.md`, "W9.8.2 lower record").

**What has no typed form.**  A memory path at a word (`MPath.loc l`,
`l : MLoc C Γ (.prim p)`): `MPath.lower` writes `iread(memory, l)`, which
reads an identity, and a word slot holds none.  `MPath.lowerT` gives such a
path its address (`Ty.mpathSrt`), and `MPath.eraseT` puts the untyped
`iread` back, so the bridge is exact; no arm reads a word through it.
-/

namespace Solidity

variable {C : Contract} {Γ : Ctx}

/-! ## Casts and constants -/

/-- A term at one word type read at an equal one (`hq ▸`, named so the
bridge has one lemma for it). -/
def TmT.castV {p q : PrimTy} (h : p = q) (t : TmT C Γ (.val p)) : TmT C Γ (.val q) := h ▸ t

theorem TmT.castV_erase {p q : PrimTy} (h : p = q) (t : TmT C Γ (.val p)) :
    (TmT.castV h t).erase = t.erase := by
  subst h; rfl

/-- `1` at a numeric type. -/
def TmT.one (p : PrimTy) (hp : p.isNumeric = true) : TmT C Γ (.val p) :=
  .app0 (.lit (PrimTy.ofLit p 1 (by cases p <;> first | rfl | exact absurd hp Bool.false_ne_true)))

theorem TmT.one_erase (p : PrimTy) (hp : p.isNumeric = true) :
    (TmT.one (C := C) (Γ := Γ) p hp).erase = .app0 (.lit (.int 1)) := by
  cases p <;> first | rfl | exact absurd hp Bool.false_ne_true

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
def Simple.lowerT : {p : PrimTy} → Simple C Γ p → TmT C Γ (.val p)
  | p, .lit n h => .app0 (.lit (PrimTy.ofLit p n h))
  | _, .bool b => .app0 (.lit (p := .bool) b)
  | _, .local i => .pvV i
  | _, .env k hp => TmT.castV hp.symm (.app0 (.env k))

/-- An index as the word it is hashed as (`Tm.keyAt`). -/
def TmT.keyAt : (k : PrimTy) → TmT C Γ (.val k) → TmT C Γ (.val k.keyTy)
  | .bool, t => .app3 .ite t (.app0 (.lit (p := .uint) ⟨1, rfl⟩))
      (.app0 (.lit (p := .uint) ⟨0, rfl⟩))
  | .uint, t => t
  | .int, t => t

/-- The sort a memory path lowers to: an identity at a reference, an address
at a word (which holds no identity: the module docstring). -/
@[reducible] def Ty.mpathSrt : Ty → SrtT
  | .ref R => .ident R
  | .prim p => .addr (.prim p)

/-- A memory location read as a path: `iread(memory, l)` at a reference,
the address itself at a word. -/
def TmT.mread : (T : Ty) → TmT C Γ (.addr T) → TmT C Γ T.mpathSrt
  | .ref _, a => .app2 .iread (.app0 .memory) a
  | .prim _, a => a

/-- The untyped term of a memory path: `MPath.lower`'s, `iread` put back at a
word. -/
def MPath.eraseT : (T : Ty) → TmT C Γ T.mpathSrt → Tm C Γ .ident
  | .ref _, t => t.erase
  | .prim _, t => .app2 .iread (.app0 .memory) t.erase

mutual

def SPath.lowerT : {T : Ty} → SPath C Γ T → TmT C Γ (.path T)
  | _, .alias i => .pvP i
  | _, .loc l => l.lowerT

def Loc.lowerT : {T : Ty} → Loc C Γ T → TmT C Γ (.path T)
  | _, .root r h => .app0 (.root r h)
  | _, .field b _ h => .app1 (.field h) b.lowerT
  | _, .index (k := k) it b i => .app2 (.at it) b.lowerT (TmT.keyAt k i.lowerT)

def MPath.lowerT : {T : Ty} → MPath C Γ T → TmT C Γ T.mpathSrt
  | _, .var i _ => .pvI i
  | T, .loc l => TmT.mread T l.lowerT

def MLoc.lowerT : {T : Ty} → MLoc C Γ T → TmT C Γ (.addr T)
  | _, .field b _ h => .app1 (.mfield h) b.lowerT
  | _, .index a b i => .app2 (.mat a) b.lowerT i.lowerT

def Val.lowerT : {p : PrimTy} → Val C Γ p → TmT C Γ (.val p)
  | _, .simple s => s.lowerT
  | _, .read l => .app2 .find (.app0 .storage) l.lowerT
  | _, .binop op h hq a b => TmT.castV hq (.app2 (.binop op h) a.lowerT b.lowerT)
  | _, .unop op h hq a => TmT.castV hq (.app1 (.unop op h) a.lowerT)
  | _, .ternary c a b => .app3 .ite c.lowerT a.lowerT b.lowerT
  | _, .readMem l => .app2 .read (.app0 .memory) l.lowerT
  | _, .len b hp => TmT.castV hp.symm (.app2 .len (.app0 .storage) b.lowerT)
  | _, .mlen b hp => TmT.castV hp.symm (.app2 .mlen (.app0 .memory) b.lowerT)

end

/-- A write's source as a storage value. -/
def Src.lowerT {T : Ty} : Src C Γ T → TmT C Γ (.sv T)
  | .val v => .app1 .sval v.lowerT
  | .copy p _ => .app2 .sfind (.app0 .storage) p.lowerT

/-- A memory write's source. -/
def MSrc.lowerT {T : Ty} : MSrc C Γ T → TmT C Γ (.mv T)
  | .val v => .app1 .mval v.lowerT
  | .ref p => .app1 .ref p.lowerT

/-! ## The bridge: the typed lowering erased -/

theorem Simple.lowerT_erase {p : PrimTy} (s : Simple C Γ p) : s.lowerT.erase = s.lower := by
  cases s with
  | lit n h => cases p <;> first | rfl | simp only [PrimTy.inRange, Bool.false_eq_true] at h
  | bool b => rfl
  | «local» i => rfl
  | env k hp => subst hp; rfl

theorem TmT.keyAt_erase (k : PrimTy) (t : TmT C Γ (.val k)) :
    (TmT.keyAt k t).erase = Tm.keyAt k t.erase := by
  cases k <;> rfl

mutual

theorem SPath.lowerT_erase : {T : Ty} → (b : SPath C Γ T) → b.lowerT.erase = b.lower
  | _, .alias _ => rfl
  | _, .loc l => Loc.lowerT_erase l

theorem Loc.lowerT_erase : {T : Ty} → (l : Loc C Γ T) → l.lowerT.erase = l.lower
  | _, .root _ _ => rfl
  | _, .field b _ _ => by
    simp only [Loc.lowerT, Loc.lower, TmT.erase, SPath.lowerT_erase b]
    rfl
  | _, .index (k := k) _ b i => by
    simp only [Loc.lowerT, Loc.lower, TmT.erase, SPath.lowerT_erase b, TmT.keyAt_erase,
      Val.lowerT_erase i]
    rfl

theorem MPath.lowerT_erase : {T : Ty} → (b : MPath C Γ T) → MPath.eraseT T b.lowerT = b.lower
  | _, .var _ _ => rfl
  | .ref _, .loc l => by
    simp only [MPath.lowerT, MPath.lower, TmT.mread, MPath.eraseT, TmT.erase, MLoc.lowerT_erase l]
    rfl
  | .prim _, .loc l => by
    simp only [MPath.lowerT, MPath.lower, TmT.mread, MPath.eraseT, MLoc.lowerT_erase l]

theorem MLoc.lowerT_erase : {T : Ty} → (l : MLoc C Γ T) → l.lowerT.erase = l.lower
  | _, .field b _ _ => by
    have hb := MPath.lowerT_erase b
    simp only [MPath.eraseT] at hb
    simp only [MLoc.lowerT, MLoc.lower, TmT.erase, hb]
    rfl
  | _, .index _ b i => by
    have hb := MPath.lowerT_erase b
    simp only [MPath.eraseT] at hb
    simp only [MLoc.lowerT, MLoc.lower, TmT.erase, hb, Val.lowerT_erase i]
    rfl

theorem Val.lowerT_erase : {p : PrimTy} → (v : Val C Γ p) → v.lowerT.erase = v.lower
  | _, .simple s => Simple.lowerT_erase s
  | _, .read l => by
    simp only [Val.lowerT, Val.lower, TmT.erase, Loc.lowerT_erase l]
    rfl
  | _, .binop _ _ _ a b => by
    simp only [Val.lowerT, Val.lower, TmT.castV_erase, TmT.erase, Val.lowerT_erase a,
      Val.lowerT_erase b]
    rfl
  | _, .unop _ _ _ a => by
    simp only [Val.lowerT, Val.lower, TmT.castV_erase, TmT.erase, Val.lowerT_erase a]
    rfl
  | _, .ternary c a b => by
    simp only [Val.lowerT, Val.lower, TmT.erase, Val.lowerT_erase c, Val.lowerT_erase a,
      Val.lowerT_erase b]
    rfl
  | _, .readMem l => by
    simp only [Val.lowerT, Val.lower, TmT.erase, MLoc.lowerT_erase l]
    rfl
  | _, .len b _ => by
    simp only [Val.lowerT, Val.lower, TmT.castV_erase, TmT.erase, SPath.lowerT_erase b]
    rfl
  | _, .mlen b _ => by
    have hb := MPath.lowerT_erase b
    simp only [MPath.eraseT] at hb
    simp only [Val.lowerT, Val.lower, TmT.castV_erase, TmT.erase, hb]
    rfl

end

theorem Src.lowerT_erase {T : Ty} (r : Src C Γ T) : r.lowerT.erase = r.lower := by
  cases r with
  | val v => simp only [Src.lowerT, Src.lower, TmT.erase, Val.lowerT_erase v]; rfl
  | copy p _ => simp only [Src.lowerT, Src.lower, TmT.erase, SPath.lowerT_erase p]; rfl

theorem MSrc.lowerT_erase {T : Ty} (r : MSrc C Γ T) : r.lowerT.erase = r.lower := by
  cases r with
  | val v => simp only [MSrc.lowerT, MSrc.lower, TmT.erase, Val.lowerT_erase v]; rfl
  | ref p =>
    have hp := MPath.lowerT_erase p
    simp only [MPath.eraseT] at hp
    simp only [MSrc.lowerT, MSrc.lower, TmT.erase, hp]
    rfl

/-- A memory path at a reference: its typed term erases to its term. -/
theorem MPath.lowerT_erase_ref {R : RefTy} (b : MPath C Γ (.ref R)) : b.lowerT.erase = b.lower :=
  MPath.lowerT_erase b

/-! ## The update elements of the arms

The elements `Calculus/Arms.lean`'s premises update by, typed.  Each
bridge states the untyped element as the arm writes it. -/

namespace UpdElemT

/-- `{v := e}` (`Premise.setLocal`). -/
def setLocal {p : PrimTy} (i : Idx Γ (.val p)) (v : Val C Γ p) : UpdElemT C Γ Γ :=
  .local i (.val v.lowerT)

/-- `storage := save(storage, l, src)` (`Premise.save`). -/
def save {T : Ty} (l : Loc C Γ T) (r : Src C Γ T) : UpdElemT C Γ Γ :=
  .storage (.app3 .save (.app0 .storage) l.lowerT r.lowerT)

/-- `storage := save(storage, l, copyMem(memory, p))` (`Premise.saveMem`), at
one reference type (the untyped builder takes any two; its one caller,
`assignFromMem`, has one). -/
def saveMem {R : RefTy} (l : Loc C Γ (.ref R)) (p : MPath C Γ (.ref R)) : UpdElemT C Γ Γ :=
  .storage (.app3 .save (.app0 .storage) l.lowerT (.app2 .copyMem (.app0 .memory) p.lowerT))

/-- `storage := delAt(storage, l)` (`Premise.delAt`). -/
def delAt {T : Ty} (l : Loc C Γ T) : UpdElemT C Γ Γ :=
  .storage (.app2 .delAt (.app0 .storage) l.lowerT)

/-- `memory := write(memory, l, src)` (`Premise.writeMem`). -/
def writeMem {T : Ty} (l : MLoc C Γ T) (r : MSrc C Γ T) : UpdElemT C Γ Γ :=
  .memory (.app3 .write (.app0 .memory) l.lowerT r.lowerT)

/-- `delete` of the memory slot at `a` (`Premise.clearMem`): a reference
written a fresh default, which takes its type free of mappings (the
`MPath.var` it is read through proves it). -/
def clearMem : (T : Ty) → TmT C Γ (.addr T) → T.mapFree = true → UpdElemT C Γ Γ
  | .prim p, a, _ => .memory (.app3 .write (.app0 .memory) a (.app1 .mval (.app0 (.lit (PrimTy.dflt p)))))
  | .ref R, a, h => .memory (.app3 .write (.app1 (.addM R h) (.app0 .memory)) a
      (.app1 .ref (.app1 (.alloc R h) (.app0 .memory))))

/-- `storage := pushSlot(storage, b)` (`storagePushLengthSave`). -/
def pushSlot {E : Ty} (b : SPath C Γ (.array E)) : UpdElemT C Γ Γ :=
  .storage (.app2 .pushSlot (.app0 .storage) b.lowerT)

/-- `storage := extend(storage, b)`. -/
def extend {E : Ty} (b : SPath C Γ (.array E)) : UpdElemT C Γ Γ :=
  .storage (.app2 .extend (.app0 .storage) b.lowerT)

/-- `storage := push(storage, b, src)` (`storagePushValueSave`, `…CopySource`). -/
def push {E : Ty} (b : SPath C Γ (.array E)) (v : Src C Γ E) : UpdElemT C Γ Γ :=
  .storage (.app3 .push (.app0 .storage) b.lowerT v.lowerT)

/-- `storage := pop(storage, b)` (`storagePopSave`). -/
def pop {E : Ty} (b : SPath C Γ (.array E)) : UpdElemT C Γ Γ :=
  .storage (.app2 .pop (.app0 .storage) b.lowerT)

/-- `storage := shrink(storage, b)` (`storagePopSaveMappingElement`). -/
def shrink {E : Ty} (b : SPath C Γ (.array E)) : UpdElemT C Γ Γ :=
  .storage (.app2 .shrink (.app0 .storage) b.lowerT)

/-- A payment (`UpdElem.payTo`). -/
def payTo (r a : Simple C Γ .uint) : UpdElemT C Γ Γ := .pay r.lowerT a.lowerT

/-- `lsv := p` (`rebindStep`). -/
def rebind {R : RefTy} (i : Idx Γ (.alias R)) (p : SPath C Γ (.ref R)) : UpdElemT C Γ Γ :=
  .local i (.path p.lowerT)

/-- `mv := p` (`rebindMemStep`). -/
def rebindMem {R : RefTy} (i : Idx Γ (.mem R)) (p : MPath C Γ (.ref R)) : UpdElemT C Γ Γ :=
  .local i (.mref p.lowerT)

theorem setLocal_erase {p : PrimTy} (i : Idx Γ (.val p)) (v : Val C Γ p) :
    (setLocal i v).erase = .local i (.val v.lower) := by
  simp only [setLocal, UpdElemT.erase, RhsT.erase, Val.lowerT_erase]

theorem save_erase {T : Ty} (l : Loc C Γ T) (r : Src C Γ T) :
    (save l r).erase = .storage (.app3 .save .storage l.lower r.lower) := by
  simp only [save, UpdElemT.erase, TmT.erase, Loc.lowerT_erase, Src.lowerT_erase]; rfl

theorem saveMem_erase {R : RefTy} (l : Loc C Γ (.ref R)) (p : MPath C Γ (.ref R)) :
    (saveMem l p).erase = .storage (.app3 .save .storage l.lower (.app2 .copyMem .memory p.lower)) := by
  simp only [saveMem, UpdElemT.erase, TmT.erase, Loc.lowerT_erase, MPath.lowerT_erase_ref]; rfl

theorem delAt_erase {T : Ty} (l : Loc C Γ T) :
    (delAt l).erase = .storage (.app2 .delAt .storage l.lower) := by
  simp only [delAt, UpdElemT.erase, TmT.erase, Loc.lowerT_erase]; rfl

theorem writeMem_erase {T : Ty} (l : MLoc C Γ T) (r : MSrc C Γ T) :
    (writeMem l r).erase = .memory (.app3 .write .memory l.lower r.lower) := by
  simp only [writeMem, UpdElemT.erase, TmT.erase, MLoc.lowerT_erase, MSrc.lowerT_erase]; rfl

theorem clearMem_erase : (T : Ty) → (a : TmT C Γ (.addr T)) → (h : T.mapFree = true) →
    .upd1 (clearMem T a h).erase = Premise.clearMem (C := C) a.erase T
  | .prim p, _, _ => by cases p <;> rfl
  | .ref _, _, _ => rfl

theorem pushSlot_erase {E : Ty} (b : SPath C Γ (.array E)) :
    (pushSlot b).erase = .storage (.app2 (.pushSlot E) .storage b.lower) := by
  simp only [pushSlot, UpdElemT.erase, TmT.erase, SPath.lowerT_erase]; rfl

theorem extend_erase {E : Ty} (b : SPath C Γ (.array E)) :
    (extend b).erase = .storage (.app2 (.extend E) .storage b.lower) := by
  simp only [extend, UpdElemT.erase, TmT.erase, SPath.lowerT_erase]; rfl

theorem push_erase {E : Ty} (b : SPath C Γ (.array E)) (v : Src C Γ E) :
    (push b v).erase = .storage (.app3 .push .storage b.lower v.lower) := by
  simp only [push, UpdElemT.erase, TmT.erase, SPath.lowerT_erase, Src.lowerT_erase]; rfl

theorem pop_erase {E : Ty} (b : SPath C Γ (.array E)) :
    (pop b).erase = .storage (.app2 .pop .storage b.lower) := by
  simp only [pop, UpdElemT.erase, TmT.erase, SPath.lowerT_erase]; rfl

theorem shrink_erase {E : Ty} (b : SPath C Γ (.array E)) :
    (shrink b).erase = .storage (.app2 .shrink .storage b.lower) := by
  simp only [shrink, UpdElemT.erase, TmT.erase, SPath.lowerT_erase]; rfl

theorem payTo_erase (r a : Simple C Γ .uint) : (payTo r a).erase = UpdElem.payTo r a := by
  simp only [payTo, UpdElemT.erase, Simple.lowerT_erase]

theorem rebind_erase {R : RefTy} (i : Idx Γ (.alias R)) (p : SPath C Γ (.ref R)) :
    (rebind i p).erase = .local i (.path p.lower) := by
  simp only [rebind, UpdElemT.erase, RhsT.erase, SPath.lowerT_erase]

theorem rebindMem_erase {R : RefTy} (i : Idx Γ (.mem R)) (p : MPath C Γ (.ref R)) :
    (rebindMem i p).erase = .local i (.mref p.lower) := by
  simp only [rebindMem, UpdElemT.erase, RhsT.erase, MPath.lowerT_erase_ref]

end UpdElemT

namespace UpdT

/-- `{mv := freshId(copySt(memory, v)) ‖ memory := copySt(memory, v)}`
(`Premise.allocCopy`): the copied type free of mappings. -/
def allocCopy {R : RefTy} (i : Idx Γ (.mem R)) (h : (Ty.ref R).mapFree = true)
    (v : TmT C Γ (.sv (.ref R))) : UpdT C Γ Γ :=
  (UpdT.nil.snoc (.local i (.mref (.app2 (.copy h) (.app0 .memory) v)))).snoc
    (.memory (.app2 (.copySt h) (.app0 .memory) v))

/-- `{mv := freshId(addM(memory)) ‖ memory := addM(memory)}`
(`memoryRootDeleteFreshRebind`). -/
def allocFresh {R : RefTy} (i : Idx Γ (.mem R)) (h : (Ty.ref R).mapFree = true) : UpdT C Γ Γ :=
  (UpdT.nil.snoc (.local i (.mref (.app1 (.alloc R h) (.app0 .memory))))).snoc
    (.memory (.app1 (.addM R h) (.app0 .memory)))

/-- `{storage := extend(storage, b) ‖ lsv := b[b.length]}`
(`storageLocalRootPushBind`). -/
def pushBind {R : RefTy} (i : Idx Γ (.alias R)) (b : SPath C Γ (.array (.ref R))) : UpdT C Γ Γ :=
  (UpdT.nil.snoc (.storage (.app2 .extend (.app0 .storage) b.lowerT))).snoc
    (.local i (.path (.app1 .next b.lowerT)))

theorem allocCopy_erase {R : RefTy} (i : Idx Γ (.mem R)) (h : (Ty.ref R).mapFree = true)
    (v : TmT C Γ (.sv (.ref R))) :
    (allocCopy i h v).erase = (Upd.nil.snoc (.local i (.mref (.app2 .copy .memory v.erase)))).snoc
      (.memory (.app2 .copySt .memory v.erase)) := rfl

theorem allocFresh_erase {R : RefTy} (i : Idx Γ (.mem R)) (h : (Ty.ref R).mapFree = true) :
    (allocFresh (C := C) i h).erase =
      (Upd.nil.snoc (.local i (.mref (.app1 (.alloc R) rfl .memory)))).snoc
        (.memory (.app1 (.addM R) rfl .memory)) := rfl

theorem pushBind_erase {R : RefTy} (i : Idx Γ (.alias R)) (b : SPath C Γ (.array (.ref R))) :
    (pushBind i b).erase =
      (Upd.nil.snoc (.storage (.app2 (.extend (.ref R)) .storage b.lower))).snoc
        (.local i (.path (.app1 .next rfl b.lower))) := by
  simp only [pushBind, UpdT.erase, UpdElemT.erase, RhsT.erase, TmT.erase, SPath.lowerT_erase]
  rfl

end UpdT

/-! ### Compound assignment and `++`/`--` -/

/-- The value a compound target holds (`OpLoc.cur`). -/
def OpLoc.curT {p : PrimTy} : OpLoc C Γ p → TmT C Γ (.val p)
  | .local i => .pvV i
  | .root r h => (Val.read (Γ := Γ) (.root r h)).lowerT
  | .field b f h => (Val.read (.field b f h)).lowerT
  | .index it b ie => (Val.read (.index it b (.simple ie))).lowerT
  | .mfield b f h => (Val.readMem (.field b f h)).lowerT
  | .mindex a b ie => (Val.readMem (.index a b (.simple ie))).lowerT

/-- The compound target set to `t` (`OpLoc.set`). -/
def OpLoc.setT {p : PrimTy} : OpLoc C Γ p → TmT C Γ (.val p) → UpdElemT C Γ Γ
  | .local i, t => .local i (.val t)
  | .root r h, t =>
    .storage (.app3 .save (.app0 .storage) (Loc.root (Γ := Γ) r h).lowerT (.app1 .sval t))
  | .field b f h, t =>
    .storage (.app3 .save (.app0 .storage) (Loc.field b f h).lowerT (.app1 .sval t))
  | .index it b ie, t =>
    .storage (.app3 .save (.app0 .storage) (Loc.index it b (.simple ie)).lowerT (.app1 .sval t))
  | .mfield b f h, t =>
    .memory (.app3 .write (.app0 .memory) (MLoc.field b f h).lowerT (.app1 .mval t))
  | .mindex a b ie, t =>
    .memory (.app3 .write (.app0 .memory) (MLoc.index a b (.simple ie)).lowerT (.app1 .mval t))

/-- `l ⊕ t` (`OpLoc.op`), at a compound operator and a numeric type: the
untyped one applies any operator. -/
def OpLoc.opT {p : PrimTy} (l : OpLoc C Γ p) (op : BinOp) (hop : op.hasCompoundAssign = true)
    (hp : p.isNumeric = true) (t : TmT C Γ (.val p)) : TmT C Γ (.val p) :=
  TmT.castV (BinOp.compound_ret hop p) (.app2 (.binop op (BinOp.compound_accepts hop hp)) l.curT t)

/-- The value `t++` has (`Tm.bumped`). -/
def TmT.bumped (op : IncDec) {p : PrimTy} (hp : p.isNumeric = true) (t : TmT C Γ (.val p)) :
    TmT C Γ (.val p) :=
  if op.isPre then
    TmT.castV (BinOp.compound_ret op.binOp_compound p)
      (.app2 (.binop op.binOp (BinOp.compound_accepts op.binOp_compound hp)) t (TmT.one p hp))
  else t

theorem OpLoc.curT_erase {p : PrimTy} (l : OpLoc C Γ p) : l.curT.erase = l.cur := by
  cases l <;> first | rfl | exact Val.lowerT_erase _

theorem OpLoc.setT_erase {p : PrimTy} (l : OpLoc C Γ p) (t : TmT C Γ (.val p)) :
    (l.setT t).erase = l.set t.erase := by
  cases l <;>
    simp only [OpLoc.setT, OpLoc.set, UpdElemT.erase, RhsT.erase, TmT.erase, Loc.lowerT_erase,
      MLoc.lowerT_erase] <;> rfl

theorem OpLoc.opT_erase {p : PrimTy} (l : OpLoc C Γ p) (op : BinOp)
    (hop : op.hasCompoundAssign = true) (hp : p.isNumeric = true) (t : TmT C Γ (.val p)) :
    (l.opT op hop hp t).erase = l.op op t.erase := by
  simp only [OpLoc.opT, TmT.castV_erase, TmT.erase, OpLoc.curT_erase]
  rfl

theorem TmT.bumped_erase (op : IncDec) {p : PrimTy} (hp : p.isNumeric = true)
    (t : TmT C Γ (.val p)) : (TmT.bumped op hp t).erase = Tm.bumped op p t.erase := by
  unfold TmT.bumped Tm.bumped
  split
  · simp only [TmT.castV_erase, TmT.erase, TmT.one_erase]
    rfl
  · rfl

end Solidity
