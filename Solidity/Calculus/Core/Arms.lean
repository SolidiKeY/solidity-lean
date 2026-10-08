import Solidity.Calculus.Core.Shift

/-!
# The rule of each statement, on scoped statements

`Completeness.lean`'s arms of `Stmt.step` over the scoped syntax
(`docs/intrinsic.md`, M6a): for each statement, the premise of the one
taclet of `Calculus/Rules.lean` whose side conditions hold, in the order
`Completeness.lean` tries them (Step 1 unfolds a read, Step 2 decomposes a
write, Step 3 is an update).  Each arm names the taclet it fires; the
premise's erasure is what that taclet leaves (`Examples/Tactics/CoreStep.lean`
pins it, statement by statement, against today's strategy).

What scoping adds to a rule, as `docs/intrinsic.md` ("how `dl{ … }` will
write a scoped taclet") lays out:

* a fresh local (`se`, `sp`, `ie`, `mv`) is pushed by its declaration, and
  the parts of the `\find` read after it are shifted under it (`Val.up` and
  its kin, `Calculus/Core/Shift.lean`); the premise pops it after the
  statement (`Premise.unfold`'s `Ext`, a `pop .capture`, invisible);
* a declaration with an initializer binds its local in front of the rest
  (`Premise.bind`);
* a call's body, closed over its frame, is read under the caller's locals
  (`Prog.wk (Thin.atop …)`, once per call, as `ifElseUnfold` weakens its
  branches), and the frame is dropped under the return variables it leaves
  (`Premise.inline`'s `Thin`).

Where the kernel evaluates these functions, they follow Gate G0's
condition 1: a `match` only on the expression families, whose context is a
parameter, or on types; the context-indexed families (`Args`, `CallRet`,
`Binders`, `Stmt`, `Prog`) by `casesOn` with a motive over their indices.
-/

namespace Solidity.Core

open Solidity (Srt Op0 Op1 Op2 Op3 Modality Mutability)

variable {C : Contract}

/-! ## The premises the rules build -/

section Builders

variable {Γ : Ctx}

/-- `storage`, the term. -/
abbrev Tm.storage : Tm C Γ .st := .app0 .storage
/-- `memory`, the term. -/
abbrev Tm.memory : Tm C Γ .mem := .app0 .memory
/-- A literal. -/
abbrev Tm.lit (v : Semantics.Value) : Tm C Γ .val := .app0 (.lit v)

/-- `se = true`, the condition of a branch's goal (`Fml.eq`, as the rules
write it). -/
def Fml.isBool (t : Tm C Γ .val) (b : Bool) : Fml C Γ :=
  .eq t (.app0 (.lit (.bool b)))

/-- `t ≐ b` with both sides defined (`Fml.eqD`). -/
abbrev Fml.isBoolD (t : Tm C Γ .val) (b : Bool) : Fml C Γ := .eqD t (Tm.lit (.bool b))

/-- `{v := v'}`: a local set to a value's term. -/
def Premise.setLocal {p : PrimTy} (i : Idx Γ (.val p)) (v : Val C Γ p) : Premise C Γ Γ :=
  .update (Upd.nil.snoc (.local i (.val v.lower)))

/-- `{e}`: one assigning element. -/
abbrev Premise.upd1 (e : UpdElem C Γ Γ) : Premise C Γ Γ := .update (Upd.nil.snoc e)

/-- `{storage := save(storage, l, src)}`. -/
def Premise.save {T : Ty} (l : Loc C Γ T) (r : Src C Γ T) : Premise C Γ Γ :=
  .upd1 (.storage (.app3 .save .storage l.lower r.lower))

/-- `{storage := save(storage, l, copyMem(memory, p))}`. -/
def Premise.saveMem {T T' : Ty} (l : Loc C Γ T) (p : MPath C Γ T') : Premise C Γ Γ :=
  .upd1 (.storage (.app3 .save .storage l.lower (.app2 .copyMem .memory p.lower)))

/-- `{storage := delAt(storage, l)}`. -/
def Premise.delAt {T : Ty} (l : Loc C Γ T) : Premise C Γ Γ :=
  .upd1 (.storage (.app2 .delAt .storage l.lower))

/-- `{memory := write(memory, l, src)}`. -/
def Premise.writeMem {T : Ty} (l : MLoc C Γ T) (r : MSrc C Γ T) : Premise C Γ Γ :=
  .upd1 (.memory (.app3 .write .memory l.lower r.lower))

/-- `delete` of a memory slot at the address `a`, by its type: a primitive
reset to its default, a reference written a fresh default object. -/
def Premise.clearMem (a : Tm C Γ .addr) : Ty → Premise C Γ Γ
  | .prim p => .upd1 (.memory (.app3 .write .memory a (.app1 .mval rfl (Tm.lit p.default))))
  | .ref R => .upd1 (.memory (.app3 .write (.app1 (.addM R) rfl .memory) a
      (.app1 .ref rfl (.app1 (.alloc R) rfl .memory))))

/-- `{mv := freshId(copySt(memory, v)) ‖ memory := copySt(memory, v)}`. -/
def Premise.allocCopy {R : RefTy} (i : Idx Γ (.mem R)) (v : Tm C Γ .sv) : Premise C Γ Γ :=
  .update ((Upd.nil.snoc (.local i (.mref (.app2 .copy .memory v)))).snoc
    (.memory (.app2 .copySt .memory v)))

/-- The fresh names of a rule fired at index `k`. -/
abbrev fse (k : Nat) : Var := .fresh "se" k
abbrev fsp (k : Nat) : Var := .fresh "sp" k
abbrev fie (k : Nat) : Var := .fresh "ie" k
abbrev fmv (k : Nat) : Var := .fresh "mv" k

/-- `T se = nse; s`: a value captured into the fresh local `x`, `s` read with
it on top, the local popped after `s`. -/
def Premise.capture (p : PrimTy) (x : Var) (e : Val C Γ p)
    (s : Stmt C (.val p :: Γ) (.val p :: Γ)) : Premise C Γ Γ :=
  .unfold (.cons (.declLocal p x (some e)) (.cons s .nil)) (.push .refl)

/-- `T storage sp = nsp; s`. -/
def Premise.captureSP {R : RefTy} (x : Var) (b : SPath C Γ (.ref R))
    (s : Stmt C (.alias R :: Γ) (.alias R :: Γ)) : Premise C Γ Γ :=
  .unfold (.cons (.declStorage R x (some (.path b))) (.cons s .nil)) (.push .refl)

/-- `T memory mv = nmp; s`. -/
def Premise.captureMV {R : RefTy} (x : Var) (b : MPath C Γ (.ref R))
    (s : Stmt C (.mem R :: Γ) (.mem R :: Γ)) : Premise C Γ Γ :=
  .unfold (.cons (.declMem R x (some (.alias b)) rfl b.mapFree) (.cons s .nil)) (.push .refl)

end Builders

/-! ## Where a read or a value lands

`Rules.lean`'s holes: a statement with a path missing, the same rule
unfolding a read into each. -/

/-- Where a storage path lands: `v = □`, `lsv = □`, `loc = □`. -/
inductive SHole (C : Contract) (Γ : Ctx) : Ty → Type where
  | local {p : PrimTy} (i : Idx Γ (.val p)) : SHole C Γ (.prim p)
  | rebind {R : RefTy} (i : Idx Γ (.alias R)) : SHole C Γ (.ref R)
  | copy {R : RefTy} (l : Loc C Γ (.ref R)) (h : (Ty.ref R).mapFree = true) : SHole C Γ (.ref R)

/-- Where a memory location lands: `v = □`, `mv = □`, `mloc = □`. -/
inductive MHole (C : Contract) (Γ : Ctx) : Ty → Type where
  | local {p : PrimTy} (i : Idx Γ (.val p)) : MHole C Γ (.prim p)
  | rebind {R : RefTy} (i : Idx Γ (.mem R)) : MHole C Γ (.ref R)
  | write {R : RefTy} (l : MLoc C Γ (.ref R)) : MHole C Γ (.ref R)

/-- Where a value lands: a local, a storage location, a memory location. -/
inductive VHole (C : Contract) (Γ : Ctx) (p : PrimTy) where
  | local (i : Idx Γ (.val p))
  | store (l : Loc C Γ (.prim p))
  | mem (l : MLoc C Γ (.prim p))

section Holes

variable {Γ : Ctx} {t : LTy}

def SHole.fill : {T : Ty} → SHole C Γ T → SPath C Γ T → Stmt C Γ Γ
  | _, .local i, .loc l => .assignLocal i (.read l)
  | _, .rebind i, p => .rebind i (.path p)
  | _, .copy l h, p => .assign l (.copy p h)

def SHole.up : {T : Ty} → SHole C Γ T → SHole C (t :: Γ) T
  | _, .local i => .local i.there
  | _, .rebind i => .rebind i.there
  | _, .copy l h => .copy l.up h

def MHole.fill : {T : Ty} → MHole C Γ T → MLoc C Γ T → Stmt C Γ Γ
  | _, .local i, l => .assignLocal i (.readMem l)
  | _, .rebind i, l => .rebindMem i (.alias (.loc l))
  | _, .write l', l => .assignMem l' (.ref (.loc l))

def MHole.up : {T : Ty} → MHole C Γ T → MHole C (t :: Γ) T
  | _, .local i => .local i.there
  | _, .rebind i => .rebind i.there
  | _, .write l => .write l.up

def VHole.fill {p : PrimTy} : VHole C Γ p → Val C Γ p → Stmt C Γ Γ
  | .local i, v => .assignLocal i v
  | .store l, v => .assign l (.val v)
  | .mem l, v => .assignMem l (.val v)

def VHole.up {p : PrimTy} : VHole C Γ p → VHole C (t :: Γ) p
  | .local i => .local i.there
  | .store l => .store l.up
  | .mem l => .mem l.up

/-- Where a fresh array lands, written with the memory local it was bound to. -/
def NewLhs.fill {R : RefTy} : NewLhs C Γ R → MPath C Γ (.ref R) → Stmt C Γ Γ
  | .store l, p => .assignFromMem l p
  | .mem l, p => .assignMem l (.ref p)

end Holes

/-! ## The rules -/

section Rules

variable (k : Nat) {Γ : Ctx}

/-- **Step 1** for a storage location read into the hole `lhs`
(`Completeness.lean`'s `Hole.readStep`): a state variable, a member of a
simple path, an entry of one at a simple index take the hole's own rule;
any other unfolds its receiver or its index first. -/
def SHole.readStep {T : Ty} (lhs : SHole C Γ T)
    (root : (r : Name) → C.rootType r = some T → Option (Premise C Γ Γ))
    (field : {s : Name} → SPath C Γ (.struct s) → (f : Name) → C.fieldType s f = some T →
      Option (Premise C Γ Γ))
    (index : {R : RefTy} → {kp : PrimTy} → IndexTy R kp T → SPath C Γ (.ref R) → Simple C Γ kp →
      Option (Premise C Γ Γ)) :
    Loc C Γ T → Option (Premise C Γ Γ)
  | .root r h => root r h
  | .field b f hf =>
    if b.isSimple then field b f hf
    -- storageFieldRead_unfold_rightFst
    else some (.captureSP (fsp k) b (lhs.up.fill (.loc (.field (.alias .here) f hf))))
  | @Loc.index _ _ _ kp _ it b i =>
    if b.isSimple then
      match i with
      | .simple ie => index it b ie
      -- storageIndexRead_unfold_rightSndIndex
      | i => some (.capture kp (fie k) i (lhs.up.fill (.loc (.index it b.up (.simple (.local .here))))))
    -- storageIndexRead_unfold_rightFst
    else some (.captureSP (fsp k) b (lhs.up.fill (.loc (.index it (.alias .here) i.up))))

/-- **Step 1** for a memory location read into the hole `lhs`
(`MHole.readStep`): a member of a memory local, or an element of one at a
simple index, takes the hole's own rule; any other unfolds its receiver or
its index first. -/
def MHole.readStep {T : Ty} (lhs : MHole C Γ T)
    (field : {s : Name} → (mv : Idx Γ (.mem (.struct s))) → (Ty.ref (.struct s)).mapFree = true →
      (f : Name) → C.fieldType s f = some T → Option (Premise C Γ Γ))
    (index : {R : RefTy} → ArrTy R T → (mv : Idx Γ (.mem R)) → (Ty.ref R).mapFree = true →
      Simple C Γ .uint → Option (Premise C Γ Γ)) :
    MLoc C Γ T → Option (Premise C Γ Γ)
  | .field (.var mv hmv) f hf => field mv hmv f hf
  -- memoryFieldRead_unfold_rightFst
  | .field (.loc l) f hf =>
    some (.captureMV (fmv k) (.loc l) (lhs.up.fill (.field (.var .here (MPath.loc l).mapFree) f hf)))
  | .index a (.var mv hmv) (.simple ie) => index a mv hmv ie
  -- memoryIndexRead_unfold_rightSndIndex
  | .index a (.var mv hmv) i =>
    some (.capture .uint (fie k) i (lhs.up.fill (.index a (.var mv.there hmv) (.simple (.local .here)))))
  -- memoryIndexRead_unfold_rightFst
  | .index a (.loc l) i =>
    some (.captureMV (fmv k) (.loc l) (lhs.up.fill (.index a (.var .here (MPath.loc l).mapFree) i.up)))

/-- `lhs = c ? a : b;` becomes a branch on `c` (`ternaryToIf`), which is
captured first when it is not simple (`ternaryCaptureCond`). -/
def ternaryStep {p : PrimTy} (lhs : VHole C Γ p) :
    Val C Γ .bool → Val C Γ p → Val C Γ p → Option (Premise C Γ Γ)
  | .simple se, a, b =>
    some (.unfold (.cons (.ite (.simple se) (.cons (lhs.fill a) .nil) (.cons (lhs.fill b) .nil)) .nil)
      .refl)
  | c, a, b => some (.capture .bool (fse k) c (lhs.up.fill (.ternary (.simple (.local .here)) a.up b.up)))

/-- A value written to a target whose parts are all simple: a simple one by
`simple` (Step 3), a conditional lowered, any other captured (the
`…ValueRhsCapture`/`…UnfoldSource` rules: `T se = nse; lhs = se;`). -/
def VHole.step {p : PrimTy} (lhs : VHole C Γ p) (simple : Simple C Γ p → Option (Premise C Γ Γ)) :
    Val C Γ p → Option (Premise C Γ Γ)
  | .simple se => simple se
  | .ternary c a b => ternaryStep k lhs c a b
  | e => some (.capture p (fse k) e (lhs.up.fill (.simple (.local .here))))

/-- A value written by `other`, unless it is a conditional, lowered first. -/
def VHole.lower {p : PrimTy} (lhs : VHole C Γ p) (other : Option (Premise C Γ Γ)) :
    Val C Γ p → Option (Premise C Γ Γ)
  | .ternary c a b => ternaryStep k lhs c a b
  | _ => other

/-- `v = se && nse;`, `v = se || nse;`: the right operand evaluated only when
the left does not decide (`logicalAndShortCircuitRhs`,
`logicalOrShortCircuitRhs`). -/
def shortStep {p p' : PrimTy} (i : Idx Γ (.val p)) (op : BinOp) (ha : op.accepts p' = true)
    (hq : op.ret p' = p) (a : Simple C Γ p') (b : Val C Γ p') : Option (Premise C Γ Γ) :=
  match op, p', p, ha, hq, i, a, b with
  | .and, .bool, .bool, _, _, i, a, b =>
    some (.unfold (.cons (.ite (.simple a)
      (.cons (.assignLocal i b)
        (.cons (.assignLocal i (.binop .and rfl rfl (.simple (.local i)) (.simple (.bool true)))) .nil))
      (.cons (.assignLocal i (.simple (.bool false))) .nil)) .nil) .refl)
  | .or, .bool, .bool, _, _, i, a, b =>
    some (.unfold (.cons (.ite (.simple a)
      (.cons (.assignLocal i (.simple (.bool true))) .nil)
      (.cons (.assignLocal i b)
        (.cons (.assignLocal i (.binop .or rfl rfl (.simple (.local i)) (.simple (.bool false)))) .nil)))
      .nil) .refl)
  | _, _, _, _, _, _, _, _ => none

/-- A local assigned (`localStep`): a simple value, a read of a simple
location, an operator over simple operands is an update; anything else
unfolds the part that is not simple. -/
def localStep {p : PrimTy} (i : Idx Γ (.val p)) : Val C Γ p → Option (Premise C Γ Γ)
  -- localValueAssign
  | .simple s => some (.setLocal i (.simple s))
  -- storageRootReadSelect, storageFieldReadFind, storageIndexReadMappingFind,
  -- storageIndexReadArrayFind, or Step 1
  | .read l => (SHole.local i).readStep k (fun r h => some (.setLocal i (.read (.root r h))))
      (fun b f h => some (.setLocal i (.read (.field b f h))))
      (fun it b ie => some (.setLocal i (.read (.index it b (.simple ie))))) l
  -- binopAssignment
  | .binop op ha hq (.simple a) (.simple b) => some (.setLocal i (.binop op ha hq (.simple a) (.simple b)))
  | @Val.binop _ _ p' _ op ha hq (.simple a) b =>
    -- logicalAndShortCircuitRhs, logicalOrShortCircuitRhs
    if op.shortCircuits then shortStep i op ha hq a b
    -- binopUnfoldRight
    else some (.capture p' (fse k) b
      (.assignLocal i.there (.binop op ha hq (.simple a.up) (.simple (.local .here)))))
  -- binopUnfoldLeft
  | @Val.binop _ _ p' _ op ha hq a b =>
    some (.capture p' (fse k) a
      (.assignLocal i.there (.binop op ha hq (.simple (.local .here)) b.up)))
  -- unopAssignment
  | .unop op ha hq (.simple a) => some (.setLocal i (.unop op ha hq (.simple a)))
  -- unopCapture
  | @Val.unop _ _ p' _ op ha hq a =>
    some (.capture p' (fse k) a (.assignLocal i.there (.unop op ha hq (.simple (.local .here)))))
  -- ternaryToIf, ternaryCaptureCond
  | .ternary c a b => ternaryStep k (.local i) c a b
  -- memoryFieldRead, memoryIndexReadArrayValue, or Step 1
  | .readMem l => (MHole.local i).readStep k
      (fun mv hmv f hf => some (.setLocal i (.readMem (.field (.var mv hmv) f hf))))
      (fun a mv hmv ie => some (.setLocal i (.readMem (.index a (.var mv hmv) (.simple ie))))) l
  | .len b hp =>
    -- storageLengthRead
    if b.isSimple then some (.setLocal i (.len b hp))
    -- storageLengthRead_unfold_rightFst
    else some (.captureSP (fsp k) b (.assignLocal i.there (.len (.alias .here) hp)))
  -- memoryLengthRead
  | .mlen (.var mv hm) hp => some (.setLocal i (.mlen (.var mv hm) hp))
  -- memoryLengthRead_unfold_rightFst
  | .mlen (.loc l) hp =>
    some (.captureMV (fmv k) (.loc l) (.assignLocal i.there (.mlen (.var .here (MPath.loc l).mapFree) hp)))

/-- The elements of the array are mappings (`marr`; `darr` its negation). -/
def SPath.elemMapping {T : Ty} (_ : SPath C Γ T) : Bool := T.elemIsMapping

/-- The elements of the array are primitive (`parr`; `rarr` its negation). -/
def SPath.elemPrim {T : Ty} (_ : SPath C Γ T) : Bool := T.elemIsPrim

/-- An alias bound (`rebindStep`): to an alias or a location of simple parts
(`storageLocalRootRebind`, `…BindLocalRoot`), a location unfolded until it
is one, a push (`storageLocalRootPushBind`) on a simple receiver. -/
def rebindStep {R : RefTy} (i : Idx Γ (.alias R)) : ARhs C Γ R → Option (Premise C Γ Γ)
  -- storageLocalRootRebind
  | .path (.alias j) => some (.upd1 (.local i (.path (SPath.alias j).lower)))
  -- storageLocalRootRebind, storageFieldReadBindLocalRoot,
  -- storageIndexReadMappingBindLocalRoot, storageIndexReadArrayBindLocalRoot(MappingElement)
  | .path (.loc l) => (SHole.rebind i).readStep k
      (fun r h => some (.upd1 (.local i (.path (Loc.root (Γ := Γ) r h).lower))))
      (fun b f h => some (.upd1 (.local i (.path (Loc.field b f h).lower))))
      (fun it b ie => some (.upd1 (.local i (.path (Loc.index it b (.simple ie)).lower)))) l
  | .push b hd =>
    -- storageLocalRootPushBind, storageLocalRootPushBindMappingElement
    if b.isSimple then
      some (.update ((Upd.nil.snoc (.storage (.app2 (.extend (.ref R)) .storage b.lower))).snoc
        (.local i (.path (.app1 .next rfl b.lower)))))
    -- storageLocalRootPush_unfold_leftFstReceiver
    else some (.captureSP (fsp k) b (.rebind i.there (.push (.alias .here) hd)))

/-- A copy into a target whose parts are simple (`copyStep`): a simple
source is copied (Step 3), a member or entry of a simple path bound to an
alias first (`storageFieldRead_unfold_rightSndResult`,
`storageIndexRead_unfold_rightSndResult`), any other unfolded (Step 1). -/
def copyStep {R : RefTy} (l : Loc C Γ (.ref R)) (hm : (Ty.ref R).mapFree = true) :
    SPath C Γ (.ref R) → Option (Premise C Γ Γ)
  | .alias y => some (.save l (.copy (.alias y) hm))
  | .loc l' => (SHole.copy l hm).readStep k (fun _ _ => some (.save l (.copy (.loc l') hm)))
      (fun b f hf => some (.captureSP (fsp k) (.loc (.field b f hf)) (.assign l.up (.copy (.alias .here) hm))))
      (fun it b ie => some (.captureSP (fsp k) (.loc (.index it b (.simple ie)))
        (.assign l.up (.copy (.alias .here) hm)))) l'

/-- `T se = e₂; T storage sp = nsp; T ie = e₁; sp[ie] = se;`
(`storageIndexWriteCaptureAllComplexRecv`, and
`storageIndexWriteCaptureAllNonSimpleIndex` with `sp` for `nsp`). -/
def indexCaptureAll {R : RefTy} {kp p : PrimTy} (it : IndexTy R kp (.prim p)) (b : SPath C Γ (.ref R))
    (i : Val C Γ kp) (e : Val C Γ p) : Premise C Γ Γ :=
  .unfold (.cons (.declLocal p (fse k) (some e))
    (.cons (.declStorage R (fsp k) (some (.path b.up)))
    (.cons (.declLocal kp (fie k) (some i.up.up))
    (.cons (.assign (.index it (.alias (.there .here)) (.simple (.local .here)))
      (.val (.simple (.local (.there (.there .here)))))) .nil))))
    (.push (.push (.push .refl)))

/-- `T storage sp = nsp; T ie = e; sp[ie] = path;`
(`storageIndexWriteStorageRefCaptureAllComplexRecv`, `…NonSimpleIndex`). -/
def indexRefCaptureAll {R R' : RefTy} {kp : PrimTy} (it : IndexTy R kp (.ref R'))
    (b : SPath C Γ (.ref R)) (i : Val C Γ kp) (p : SPath C Γ (.ref R'))
    (hm : (Ty.ref R').mapFree = true) : Premise C Γ Γ :=
  .unfold (.cons (.declStorage R (fsp k) (some (.path b)))
    (.cons (.declLocal kp (fie k) (some i.up))
    (.cons (.assign (.index it (.alias (.there .here)) (.simple (.local .here))) (.copy p.up.up hm)) .nil)))
    (.push (.push .refl))

/-- A storage write (`assignStep`): the receiver unfolded first, then the
index, then the source. -/
def assignStep : {T : Ty} → Loc C Γ T → Src C Γ T → Option (Premise C Γ Γ)
  -- storageRootWriteStore, storageRootWriteValueRhsCapture
  | _, .root r h, .val e =>
    (VHole.store (.root r h)).step k (fun se => some (.save (.root r h) (.val (.simple se)))) e
  -- storageRootWriteCopySource
  | _, .root r h, .copy (.alias j) hm => some (.save (.root r h) (.copy (.alias j) hm))
  -- storageRootWriteCopySource, storageFieldReadStoreRoot,
  -- storageIndexReadMappingStoreRoot, storageIndexReadArrayStoreRoot, or Step 1
  | _, .root r h, .copy (.loc l) hm =>
    let done := some (.save (.root r h) (.copy (.loc l) hm))
    (SHole.copy (.root r h) hm).readStep k (fun _ _ => done) (fun _ _ _ => done) (fun _ _ _ => done) l
  | _, .field b f h, .val e =>
    -- storageFieldWriteSave, fieldWriteValueRhsCapture
    if b.isSimple then
      (VHole.store (.field b f h)).step k (fun se => some (.save (.field b f h) (.val (.simple se)))) e
    -- storageFieldWrite_unfold_leftFst
    else (VHole.store (.field b f h)).lower k (some (.unfold
      (.cons (.declLocal _ (fse k) (some e))
        (.cons (.declStorage _ (fsp k) (some (.path b.up)))
          (.cons (.assign (.field (.alias .here) f h) (.val (.simple (.local (.there .here))))) .nil)))
      (.push (.push .refl)))) e
  | _, .field b f h, .copy p hm =>
    -- storageFieldWriteCopySource, or the source unfolded
    if b.isSimple then copyStep k (.field b f h) hm p
    -- storageFieldWriteStorageRef_unfold_leftFst
    else some (.captureSP (fsp k) b (.assign (.field (.alias .here) f h) (.copy p.up hm)))
  | _, .index it b i, .val e =>
    if b.isSimple then
      match i with
      -- storageIndexWriteMappingSave, storageIndexWriteArraySave, indexWriteValueRhsCapture
      | .simple ie => (VHole.store (.index it b (.simple ie))).step k
          (fun se => some (.save (.index it b (.simple ie)) (.val (.simple se)))) e
      -- storageIndexWriteCaptureAllNonSimpleIndex
      | i => (VHole.store (.index it b i)).lower k (some (indexCaptureAll k it b i e)) e
    -- storageIndexWriteCaptureAllComplexRecv
    else (VHole.store (.index it b i)).lower k (some (indexCaptureAll k it b i e)) e
  | _, .index it b i, .copy p hm =>
    if b.isSimple then
      match i with
      -- storageIndexWriteMappingCopySource, storageIndexWriteArrayCopySource
      | .simple ie => copyStep k (.index it b (.simple ie)) hm p
      -- storageIndexWriteStorageRefCaptureAllNonSimpleIndex
      | i => some (indexRefCaptureAll k it b i p hm)
    -- storageIndexWriteStorageRefCaptureAllComplexRecv
    else some (indexRefCaptureAll k it b i p hm)

/-- A storage location written from memory (`assignFromMemStep`): the
receiver first, then the index; the memory path copied as it is. -/
def assignFromMemStep {R : RefTy} : Loc C Γ (.ref R) → MPath C Γ (.ref R) → Option (Premise C Γ Γ)
  -- memoryToStorageStoreRoot
  | .root r h, p => some (.saveMem (.root r h) p)
  | .field b f h, p =>
    -- memoryToStorageFieldCopyRoot
    if b.isSimple then some (.saveMem (.field b f h) p)
    -- memoryToStorageField_unfold_leftFst
    else some (.captureSP (fsp k) b (.assignFromMem (.field (.alias .here) f h) p.up))
  | @Loc.index _ _ R' kp _ it b i, p =>
    let capture : Premise C Γ Γ :=
      .unfold (.cons (.declStorage R' (fsp k) (some (.path b)))
        (.cons (.declLocal kp (fie k) (some i.up))
        (.cons (.assignFromMem (.index it (.alias (.there .here)) (.simple (.local .here))) p.up.up)
          .nil))) (.push (.push .refl))
    if b.isSimple then
      match i with
      -- memoryToStorageIndexMappingCopyRoot, memoryToStorageIndexArrayCopyRoot
      | .simple ie => some (.saveMem (.index it b (.simple ie)) p)
      -- memoryToStorageIndexCaptureAllNonSimpleIndex
      | _ => some capture
    -- memoryToStorageIndexCaptureAllComplexRecv
    else some capture

/-- `delete l;` (`deleteStep`): the receiver first, then the index. -/
def deleteStep {T : Ty} : Loc C Γ T → Option (Premise C Γ Γ)
  -- storageRootDelete
  | .root r h => some (.delAt (.root r h))
  | .field b f h =>
    -- storageFieldDelete
    if b.isSimple then some (.delAt (.field b f h))
    -- storageFieldDelete_unfold_leftFst
    else some (.captureSP (fsp k) b (.delete (.field (.alias .here) f h)))
  | @Loc.index _ _ _ kp _ it b i =>
    if b.isSimple then
      match i with
      -- storageIndexDelete, storageIndexArrayDelete
      | .simple ie => some (.delAt (.index it b (.simple ie)))
      -- storageIndexDeleteNonSimpleIndexCapture
      | i => some (.capture kp (fie k) i (.delete (.index it b.up (.simple (.local .here)))))
    -- storageIndexDelete_unfold_leftFst
    else some (.captureSP (fsp k) b (.delete (.index it (.alias .here) i.up)))

/-! ### Compound assignment and `++`/`--` -/

/-- The value a compound target holds, as the rules read it: `v`,
`find(storage, l)`, `read(memory, l)`. -/
def OpLoc.cur {p : PrimTy} : OpLoc C Γ p → Tm C Γ .val
  | .local i => .pvV i
  | .root r h => (Val.read (Γ := Γ) (.root r h)).lower
  | .field b f h => (Val.read (.field b f h)).lower
  | .index it b ie => (Val.read (.index it b (.simple ie))).lower
  | .mfield b f h => (Val.readMem (.field b f h)).lower
  | .mindex a b ie => (Val.readMem (.index a b (.simple ie))).lower

/-- The compound target set to `t`: `v := t`, `storage := save(storage, l, t)`,
`memory := write(memory, l, t)`. -/
def OpLoc.set {p : PrimTy} : OpLoc C Γ p → Tm C Γ .val → UpdElem C Γ Γ
  | .local i, t => .local i (.val t)
  | .root r h, t => .storage (.app3 .save .storage (Loc.root (Γ := Γ) r h).lower (.app1 .sval rfl t))
  | .field b f h, t => .storage (.app3 .save .storage (Loc.field b f h).lower (.app1 .sval rfl t))
  | .index it b ie, t =>
    .storage (.app3 .save .storage (Loc.index it b (.simple ie)).lower (.app1 .sval rfl t))
  | .mfield b f h, t => .memory (.app3 .write .memory (MLoc.field b f h).lower (.app1 .mval rfl t))
  | .mindex a b ie, t =>
    .memory (.app3 .write .memory (MLoc.index a b (.simple ie)).lower (.app1 .mval rfl t))

/-- `l ⊕ t` at the target's type. -/
abbrev OpLoc.op {p : PrimTy} (l : OpLoc C Γ p) (op : BinOp) (t : Tm C Γ .val) : Tm C Γ .val :=
  .app2 (.binop op p) l.cur t

/-- The target with a receiver that is not simple bound first
(`…UnfoldLeftFst`): `T storage sp = nsp; s`, `T memory mv = nmp; s`, with
`s` the statement on the bound receiver; `none` when the receiver is
simple. -/
def OpLoc.unfoldRecv {p : PrimTy} (s : {t : LTy} → OpLoc C (t :: Γ) p → Stmt C (t :: Γ) (t :: Γ)) :
    OpLoc C Γ p → Option (Premise C Γ Γ)
  | .field b f h =>
    if b.isSimple then none else some (.captureSP (fsp k) b (s (.field (.alias .here) f h)))
  | .index it b ie =>
    if b.isSimple then none else some (.captureSP (fsp k) b (s (.index it (.alias .here) ie.up)))
  | .mfield (.loc l) f h =>
    some (.captureMV (fmv k) (.loc l) (s (.mfield (.var .here (MPath.loc l).mapFree) f h)))
  | .mindex a (.loc l) ie =>
    some (.captureMV (fmv k) (.loc l) (s (.mindex a (.var .here (MPath.loc l).mapFree) ie.up)))
  | _ => none

/-- `l ⊕= r;` (`opStep`): the source first, then the receiver. -/
def opStep {p : PrimTy} (op : BinOp) (hop : op.hasCompoundAssign = true) (hp : p.isNumeric = true)
    (l : OpLoc C Γ p) : Val C Γ p → Option (Premise C Γ Γ)
  -- localOpAssign, storageRootOpAssign, storageFieldOpAssign,
  -- storageIndexMappingOpAssign, storageIndexArrayOpAssign, memoryFieldOpAssign,
  -- memoryIndexArrayOpAssign; or storageFieldOpAssignUnfoldLeftFst,
  -- storageIndexOpAssignUnfoldLeftFst, memoryFieldOpAssignUnfoldLeftFst,
  -- memoryIndexOpAssignUnfoldLeftFst
  | .simple se =>
    match l.unfoldRecv k (fun l' => .opAssign op hop hp l' (.simple se.up)) with
    | some q => some q
    | none => some (.upd1 (l.set (l.op op se.lower)))
  -- compoundAssignValueRhsCapture
  | r => some (.capture p (fse k) r (.opAssign op hop hp l.up (.simple (.local .here))))

/-- `1`, the step of `++`/`--`. -/
abbrev Tm.one {Γ : Ctx} : Tm C Γ .val := Tm.lit (.int 1)

/-- `l++;` (`incStep`): the receiver first. -/
def incStep {p : PrimTy} (op : IncDec) (hp : p.isNumeric = true) (l : OpLoc C Γ p) :
    Option (Premise C Γ Γ) :=
  -- storageFieldIncrementUnfoldLeftFst, storageIndexIncrementUnfoldLeftFst,
  -- memoryFieldIncrementUnfoldLeftFst, memoryIndexIncrementUnfoldLeftFst
  match l.unfoldRecv k (fun l' => .incDec op hp l') with
  | some q => some q
  -- localIncrement, storageRootIncrement, storageFieldIncrement,
  -- storageIndexIncrement, memoryFieldIncrement, memoryIndexArrayIncrement
  | none => some (.upd1 (l.set (l.op op.binOp .one)))

/-- The value `t++` has: the bumped one for `++t`, the old one for `t++`
(`Update.lean`'s `Term.bumped`). -/
def Tm.bumped (op : IncDec) (p : PrimTy) (t : Tm C Γ .val) : Tm C Γ .val :=
  if op.isPre then .app2 (.binop op.binOp p) t .one else t

/-- `v = l++;`, its receiver simple (`localAssignIncrement`,
`storageRootIncrementAssignment`, `storageFieldIncrementAssignment`,
`storageIndexIncrementAssignment`, `memoryFieldIncrementAssignment`,
`memoryIndexArrayIncrementAssignment`). -/
def assignIncStep {p : PrimTy} (i : Idx Γ (.val p)) (op : IncDec) (l : OpLoc C Γ p) :
    Option (Premise C Γ Γ) :=
  some (.update ((Upd.nil.snoc (l.set (l.op op.binOp .one))).snoc
    (.local i (.val (Tm.bumped op p l.cur)))))

/-! ### Arrays and payments -/

/-- `b.push(v);` (`pushStep`): the receiver first, then the argument. -/
def pushStep {E : Ty} (b : SPath C Γ (.array E)) (v : Option (Src C Γ E))
    (hd : (v.isSome || E.defaultOkS) = true) : Option (Premise C Γ Γ) :=
  if b.isSimple then
    match E, b, v with
    | E, b, none =>
      -- storagePushLengthSave
      if b.elemPrim then some (.upd1 (.storage (.app2 (.pushSlot E) .storage b.lower)))
      -- storagePushLengthSaveReferenceElement
      else some (.upd1 (.storage (.app2 (.extend E) .storage b.lower)))
    -- storagePushValueSave
    | _, b, some (.val (.simple se)) =>
      some (.upd1 (.storage (.app3 .push .storage b.lower (Src.val (Γ := Γ) (.simple se)).lower)))
    -- storagePushValue_unfold_rightSndArgument
    | _, b, some (.val e) => some (.capture _ (fse k) e (.push b.up (some (.val (.simple (.local .here)))) rfl))
    -- storagePushValueCopySource
    | _, b, some (.copy p hm) => some (.upd1 (.storage (.app3 .push .storage b.lower (Src.copy p hm).lower)))
  -- storagePush_unfold_leftFstReceiver, storagePushValue_unfold_leftFstReceiver
  else some (.captureSP (fsp k) b (.push (.alias .here) (v.map Src.up) (by
    cases v <;> exact hd)))

/-- `b.pop();` (`popStep`): the receiver first. -/
def popStep {E : Ty} (b : SPath C Γ (.array E)) : Option (Premise C Γ Γ) :=
  if b.isSimple then
    -- storagePopSaveMappingElement
    if b.elemMapping then some (.upd1 (.storage (.app2 .shrink .storage b.lower)))
    -- storagePopSave
    else some (.upd1 (.storage (.app2 .pop .storage b.lower)))
  -- storagePop_unfold_leftFstReceiver
  else some (.captureSP (fsp k) b (.pop (.alias .here)))

/-- `{net := if(sadr = this) then net else store(net, at(sadr), net(sadr) - se)}`. -/
abbrev UpdElem.payTo (r a : Simple C Γ .uint) : UpdElem C Γ Γ := .pay r.lower a.lower

/-- `r.transfer(a);` (`transferStep`): the receiver first, then the amount. -/
def transferStep (m : Modality) : Val C Γ .uint → Val C Γ .uint → Option (Premise C Γ Γ)
  | .simple sadr, .simple se => match m with
    -- transferNoCallbackBox
    | .box => some (.upd1 (.payTo sadr se))
    -- transferDiamond (Lean)
    | .diamond => some (.done false)
  -- transfer_unfold_rightSndArgument
  | .simple sadr, a => some (.capture .uint (fse k) a (.transfer (.simple sadr.up) (.simple (.local .here))))
  -- transfer_unfold_leftFstReceiver
  | r, a => some (.capture .uint (fse k) r (.transfer (.simple (.local .here)) a.up))

/-- `pv = r.send(a);` (`sendStep`): the receiver first, then the amount;
both simple, the send's two outcomes. -/
def sendStep (m : Modality) (pv : Idx Γ (.val .bool)) :
    Val C Γ .uint → Val C Γ .uint → Option (Premise C Γ Γ)
  | .simple sadr, .simple se =>
    let us : List (Upd C Γ Γ) :=
      [(Upd.nil.snoc (.payTo sadr se)).snoc (.local pv (.val (Tm.lit (.bool true)))),
        Upd.nil.snoc (.local pv (.val (Tm.lit (.bool false))))]
    match m with
    -- sendNoCallbackBox
    | .box => some (.cases [] us)
    -- sendNoCallbackDiamond
    | .diamond =>
      some (.cases [.isBoolD (.app2 (.binop .le .uint) (Tm.lit (.int 0)) se.lower) true] us)
  -- send_unfold_rightSndArgument
  | .simple sadr, a =>
    some (.capture .uint (fse k) a (.send pv.there (.simple sadr.up) (.simple (.local .here))))
  -- send_unfold_leftFstReceiver
  | r, a => some (.capture .uint (fse k) r (.send pv.there (.simple (.local .here)) a.up))

/-! ### Memory -/

/-- A memory local bound (`rebindMemStep`): to a memory local
(`memoryRootRebind`), a location of one, unfolded until it is
(`memoryFieldReadAliasRoot`, `memoryIndexReadArrayMemory`), a deep copy of
storage (`memoryStorageCopy`, `memoryStorageCopyUnfold`), a fresh array
(`memoryArrayFreshAlloc`). -/
def rebindMemStep {R : RefTy} (i : Idx Γ (.mem R)) : MRhs C Γ R → Option (Premise C Γ Γ)
  | .alias (.var j hj) => some (.upd1 (.local i (.mref (MPath.var j hj).lower)))
  | .alias (.loc l) => (MHole.rebind i).readStep k
      (fun mv hmv f hf => some (.upd1 (.local i (.mref (MPath.loc (.field (.var mv hmv) f hf)).lower))))
      (fun a mv hmv ie =>
        some (.upd1 (.local i (.mref (MPath.loc (.index a (.var mv hmv) (.simple ie))).lower)))) l
  | .copy sp hm =>
    if sp.isSimple then some (.allocCopy i (.app2 .sfind .storage sp.lower))
    else some (.captureSP (fsp k) sp (.rebindMem i.there (.copy (.alias .here) hm)))
  | .newArr n _ => some (.allocCopy i (.app1 (.newArr R) rfl n.lower))

/-- A memory reference written to the target `l` (`memRefStep`): a memory
local or a bindable location is written (`memoryFieldWriteCopy`,
`memoryIndexWriteCopy`), any other source unfolded (Step 1). -/
def memRefStep {R : RefTy} (l : MLoc C Γ (.ref R)) : MPath C Γ (.ref R) → Option (Premise C Γ Γ)
  | .var y hy => some (.writeMem l (.ref (.var y hy)))
  | .loc sl => (MHole.write l).readStep k
      (fun mv hmv f hf => some (.writeMem l (.ref (.loc (.field (.var mv hmv) f hf)))))
      (fun a mv hmv ie => some (.writeMem l (.ref (.loc (.index a (.var mv hmv) (.simple ie)))))) sl

/-- A memory location written (`assignMemStep`): the receiver first, then
the index, then the source. -/
def assignMemStep : {T : Ty} → MLoc C Γ T → MSrc C Γ T → Option (Premise C Γ Γ)
  -- memoryFieldWrite, memoryFieldWriteUnfoldSource
  | _, .field (.var mv hmv) f hf, .val e => (VHole.mem (.field (.var mv hmv) f hf)).step k
      (fun se => some (.writeMem (.field (.var mv hmv) f hf) (.val (.simple se)))) e
  | _, .field (.var mv hmv) f hf, .ref src => memRefStep k (.field (.var mv hmv) f hf) src
  -- memoryFieldWrite_unfold_leftFst
  | _, .field (.loc l) f hf, r =>
    some (.captureMV (fmv k) (.loc l) (.assignMem (.field (.var .here (MPath.loc l).mapFree) f hf) r.up))
  -- memoryIndexWriteArray, memoryIndexWriteUnfoldSource
  | _, .index a (.var mv hmv) (.simple ie), .val e => (VHole.mem (.index a (.var mv hmv) (.simple ie))).step k
      (fun se => some (.writeMem (.index a (.var mv hmv) (.simple ie)) (.val (.simple se)))) e
  | _, .index a (.var mv hmv) (.simple ie), .ref src => memRefStep k (.index a (.var mv hmv) (.simple ie)) src
  -- memoryIndexWriteCaptureAllNonSimpleIndex
  | _, .index a (.var mv hmv) i, .val e =>
    some (.unfold (.cons (.declLocal _ (fse k) (some e))
      (.cons (.declLocal .uint (fie k) (some i.up))
      (.cons (.assignMem (.index a (.var mv.there.there hmv) (.simple (.local .here)))
        (.val (.simple (.local (.there .here))))) .nil))) (.push (.push .refl)))
  -- memoryIndexWriteMemRefCaptureAllNonSimpleIndex
  | _, .index a (.var mv hmv) i, .ref src =>
    some (.capture .uint (fie k) i (.assignMem (.index a (.var mv.there hmv) (.simple (.local .here)))
      (.ref src.up)))
  -- memoryIndexWriteCaptureAllComplexRecv
  | _, @MLoc.index _ _ R _ a (.loc l) i, .val e =>
    some (.unfold (.cons (.declLocal _ (fse k) (some e))
      (.cons (.declMem R (fmv k) (some (.alias (MPath.loc l).up)) rfl (MPath.loc l).mapFree)
      (.cons (.declLocal .uint (fie k) (some i.up.up))
      (.cons (.assignMem (.index a (.var (.there .here) (MPath.loc l).mapFree) (.simple (.local .here)))
        (.val (.simple (.local (.there (.there .here)))))) .nil))))
      (.push (.push (.push .refl))))
  -- memoryIndexWriteMemRefCaptureAllComplexRecv
  | _, @MLoc.index _ _ R _ a (.loc l) i, .ref src =>
    some (.unfold (.cons (.declMem R (fmv k) (some (.alias (.loc l))) rfl (MPath.loc l).mapFree)
      (.cons (.declLocal .uint (fie k) (some i.up))
      (.cons (.assignMem (.index a (.var (.there .here) (MPath.loc l).mapFree) (.simple (.local .here)))
        (.ref src.up.up)) .nil))) (.push (.push .refl)))

/-- `delete p;` on memory (`deleteMemStep`): a memory local bound to a fresh
default object, a member or element of one reset by the rule its type
picks, any other receiver bound first, a complex index captured. -/
def deleteMemStep : {T : Ty} → MPath C Γ T → T.defaultOkS = true → Option (Premise C Γ Γ)
  -- memoryRootDeleteFreshRebind
  | _, @MPath.var _ _ R i _, _ =>
    some (.update ((Upd.nil.snoc (.local i (.mref (.app1 (.alloc R) rfl .memory)))).snoc
      (.memory (.app1 (.addM R) rfl .memory))))
  -- memoryFieldDeletePrimitive, memoryFieldDeleteReference
  | _, .loc (@MLoc.field _ _ _ T (.var mv hmv) f hf), _ =>
    some (.clearMem (MLoc.field (.var mv hmv) f hf).lower T)
  -- memoryFieldDelete_unfold_leftFst
  | _, .loc (.field (.loc l) f hf), hd =>
    some (.captureMV (fmv k) (.loc l) (.deleteMem (.loc (.field (.var .here (MPath.loc l).mapFree) f hf)) hd))
  -- memoryIndexDeletePrimitive, memoryIndexDeleteReference
  | _, .loc (@MLoc.index _ _ _ T a (.var mv hmv) (.simple ie)), _ =>
    some (.clearMem (MLoc.index a (.var mv hmv) (.simple ie)).lower T)
  -- memoryIndexDeleteNonSimpleIndexCapture
  | _, .loc (.index a (.var mv hmv) i), hd =>
    some (.capture .uint (fie k) i (.deleteMem (.loc (.index a (.var mv.there hmv) (.simple (.local .here)))) hd))
  -- memoryIndexDelete_unfold_leftFst
  | _, .loc (.index a (.loc l) i), hd =>
    some (.captureMV (fmv k) (.loc l) (.deleteMem (.loc (.index a (.var .here (MPath.loc l).mapFree) i.up)) hd))

/-- `tgt = new T(se);` (`newArrayCapture`): the fresh array bound to a fresh
memory local first. -/
def assignNewStep {R : RefTy} (l : NewLhs C Γ R) (n : Simple C Γ .uint) (h : R.newArrOk = true) :
    Option (Premise C Γ Γ) :=
  some (.unfold (.cons (.declMem R (fmv k) (some (.newArr n h)) rfl (MRhs.newArr (C := C) (Γ := Γ) n h).mapFree)
    (.cons (l.up.fill (.var .here (MRhs.newArr (C := C) (Γ := Γ) n h).mapFree)) .nil)) (.push .refl))

/-! ### Control flow -/

/-- `if (c) …`: split on a simple condition (`ifElseSplit`), capture any
other (`ifElseUnfold`), the branches read with the capture on top: weakened
by `Prog.wk up`, which the kernel runs on every captured condition. -/
def iteStep {Γ₁ Γ₂ : Ctx} (c : Val C Γ .bool) (thn : Prog C Γ Γ₁) (els : Prog C Γ Γ₂) :
    Option (Premise C Γ Γ) :=
  match c with
  | .simple s => some (.split .block (Fml.isBool s.lower true) (Fml.isBool s.lower false) thn els)
  | c => some (.capture .bool (fse k) c
      (.ite (.simple (.local .here)) (thn.wk up).2.2 (els.wk up).2.2))

/-- `require(c);`: two goals on a simple condition (`requireSimple`), the
condition captured otherwise (`requireConditionCapture`). -/
def requireStep : Val C Γ .bool → Option (Premise C Γ Γ)
  | .simple s => some (.split .capture (Fml.isBool s.lower true) (Fml.isBool s.lower false) .nil
      (.cons .revert .nil))
  | c => some (.capture .bool (fse k) c (.require (.simple (.local .here))))

/-- `assert(c);`: the check of a simple condition (`assertSimple`), the
condition captured otherwise (`assertConditionCapture`). -/
def assertStep : Val C Γ .bool → Option (Premise C Γ Γ)
  | .simple s => some (.check (Fml.isBool s.lower true))
  | c => some (.capture .bool (fse k) c (.assert (.simple (.local .here))))

end Rules

end Solidity.Core
