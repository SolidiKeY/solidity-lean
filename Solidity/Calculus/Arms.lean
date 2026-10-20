import Solidity.Calculus.Shift
import Solidity.Syntax.PushSource

/-!
# The rule of each statement, on scoped statements

master's arms of `Stmt.step` (`Calculus/Completeness.lean` at `ad728b16`)
over the scoped syntax (`docs/intrinsic.md`, M6a): for each statement, the
premise of the one taclet of `Calculus/Rules.lean` whose side conditions
hold, in the order master tried them (Step 1 unfolds a read, Step 2
decomposes a write, Step 3 is an update).  Each arm names the taclet it
fires (`Examples/Tactics/Step.lean` runs every arm in the kernel).

What scoping adds to a rule, as `docs/intrinsic.md` ("how `dl{ … }` will
write a scoped taclet") lays out:

* a fresh local (`se`, `sp`, `ie`, `mv`) is pushed by its declaration, and
  the parts of the `\find` read after it are shifted under it (`Val.up` and
  its kin, `Calculus/Shift.lean`); the premise pops it after the
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

namespace Solidity

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
abbrev Tm.lit {p : PrimTy} (v : p.Denote) : Tm C Γ (.val p) := .app0 (.lit v)

/-- `se = true`, the condition of a branch's goal (`Fml.eq`, as the rules
write it). -/
abbrev Fml.isBool (t : Tm C Γ (.val .bool)) (b : Bool) : Fml C Γ :=
  .eq t (.app0 (.lit (p := .bool) b))

/-- `{v := v'}`: a local set to a value's term. -/
def Premise.setLocal {p : PrimTy} (i : Idx Γ (.val p)) (v : Val C Γ p) : Premise C Γ Γ :=
  .update (Upd.nil.snoc (UpdElem.setLocal i v))

/-- `{e}`: one assigning element. -/
abbrev Premise.upd1 (e : UpdElem C Γ Γ) : Premise C Γ Γ := .update (Upd.nil.snoc e)

/-- `{storage := save(storage, l, src)}`. -/
def Premise.save {T : Ty} (l : Loc C Γ T) (r : Src C Γ T) : Premise C Γ Γ :=
  .upd1 (UpdElem.save l r)

/-- `{storage := save(storage, l, copyMem(memory, p))}`. -/
def Premise.saveMem {R : RefTy} (l : Loc C Γ (.ref R)) (p : MPath C Γ (.ref R)) : Premise C Γ Γ :=
  .upd1 (UpdElem.saveMem l p)

/-- `{storage := delAt(storage, l)}`. -/
def Premise.delAt {T : Ty} (l : Loc C Γ T) : Premise C Γ Γ :=
  .upd1 (UpdElem.delAt l)

/-- `{memory := write(memory, l, src)}`. -/
def Premise.writeMem {T : Ty} (l : MLoc C Γ T) (r : MSrc C Γ T) : Premise C Γ Γ :=
  .upd1 (UpdElem.writeMem l r)

/-- `delete` of a memory slot at the address `a`, by its type: a primitive
reset to its default, a reference written a fresh default object (its type
free of mappings, `h`). -/
def Premise.clearMem : (T : Ty) → Tm C Γ (.addr T) → T.mapFree = true → Premise C Γ Γ
  | .prim p, a, h => .upd1 (UpdElem.clearMem (.prim p) a h)
  | .ref R, a, h => .upd1 (UpdElem.clearMem (.ref R) a h)

/-- `{mv := freshId(copySt(memory, v)) ‖ memory := copySt(memory, v)}`. -/
def Premise.allocCopy {R : RefTy} (i : Idx Γ (.mem R)) (h : (Ty.ref R).mapFree = true)
    (v : Tm C Γ (.sv (.ref R))) : Premise C Γ Γ :=
  .update (Upd.allocCopy i h v)

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
(master's `Hole.readStep`, `Calculus/Completeness.lean` at `ad728b16`): a
state variable, a member of a simple path, an entry of one at a simple index
take the hole's own rule; any other unfolds its receiver or its index
first. -/
def SHole.readStep {T : Ty} (lhs : SHole C Γ T)
    (root : (r : Name) → C.rootType r = some T → Premise C Γ Γ)
    (field : {s : Name} → SPath C Γ (.struct s) → (f : Name) → C.fieldType s f = some T →
      Premise C Γ Γ)
    (index : {R : RefTy} → {kp : PrimTy} → IndexTy R kp T → SPath C Γ (.ref R) → Simple C Γ kp →
      Premise C Γ Γ) :
    Loc C Γ T → Premise C Γ Γ
  | .root r h => root r h
  | .field b f hf =>
    if b.isSimple then field b f hf
    -- storageFieldRead_unfold_rightFst
    else .captureSP (fsp k) b (lhs.up.fill (.loc (.field (.alias .here) f hf)))
  | @Loc.index _ _ _ kp _ it b i =>
    if b.isSimple then
      match i with
      | .simple ie => index it b ie
      -- storageIndexRead_unfold_rightSndIndex
      | i => .capture kp (fie k) i (lhs.up.fill (.loc (.index it b.up (.simple (.local .here)))))
    -- storageIndexRead_unfold_rightFst
    else .captureSP (fsp k) b (lhs.up.fill (.loc (.index it (.alias .here) i.up)))

/-- **Step 1** for a memory location read into the hole `lhs`
(`MHole.readStep`): a member of a memory local, or an element of one at a
simple index, takes the hole's own rule; any other unfolds its receiver or
its index first. -/
def MHole.readStep {T : Ty} (lhs : MHole C Γ T)
    (field : {s : Name} → (mv : Idx Γ (.mem (.struct s))) → (Ty.ref (.struct s)).mapFree = true →
      (f : Name) → C.fieldType s f = some T → Premise C Γ Γ)
    (index : {R : RefTy} → ArrTy R T → (mv : Idx Γ (.mem R)) → (Ty.ref R).mapFree = true →
      Simple C Γ .uint → Premise C Γ Γ) :
    MLoc C Γ T → Premise C Γ Γ
  | .field (.var mv hmv) f hf => field mv hmv f hf
  -- memoryFieldRead_unfold_rightFst
  | .field (.loc l) f hf =>
    .captureMV (fmv k) (.loc l) (lhs.up.fill (.field (.var .here (MPath.loc l).mapFree) f hf))
  | .index a (.var mv hmv) (.simple ie) => index a mv hmv ie
  -- memoryIndexRead_unfold_rightSndIndex
  | .index a (.var mv hmv) i =>
    .capture .uint (fie k) i (lhs.up.fill (.index a (.var mv.there hmv) (.simple (.local .here))))
  -- memoryIndexRead_unfold_rightFst
  | .index a (.loc l) i =>
    .captureMV (fmv k) (.loc l) (lhs.up.fill (.index a (.var .here (MPath.loc l).mapFree) i.up))

/-- `lhs = c ? a : b;` becomes a branch on `c` (`ternaryToIf`), which is
captured first when it is not simple (`ternaryCaptureCond`). -/
def ternaryStep {p : PrimTy} (lhs : VHole C Γ p) :
    Val C Γ .bool → Val C Γ p → Val C Γ p → Premise C Γ Γ
  | .simple se, a, b =>
    .unfold (.cons (.ite (.simple se) (.cons (lhs.fill a) .nil) (.cons (lhs.fill b) .nil)) .nil)
      .refl
  | c, a, b => .capture .bool (fse k) c (lhs.up.fill (.ternary (.simple (.local .here)) a.up b.up))

/-- A value written to a target whose parts are all simple: a simple one by
`simple` (Step 3), a conditional lowered, any other captured (the
`…ValueRhsCapture`/`…UnfoldSource` rules: `T se = nse; lhs = se;`). -/
def VHole.step {p : PrimTy} (lhs : VHole C Γ p) (simple : Simple C Γ p → Premise C Γ Γ) :
    Val C Γ p → Premise C Γ Γ
  | .simple se => simple se
  | .ternary c a b => ternaryStep k lhs c a b
  | e => .capture p (fse k) e (lhs.up.fill (.simple (.local .here)))

/-- A value written by `other`, unless it is a conditional, lowered first. -/
def VHole.lower {p : PrimTy} (lhs : VHole C Γ p) (other : Premise C Γ Γ) :
    Val C Γ p → Premise C Γ Γ
  | .ternary c a b => ternaryStep k lhs c a b
  | _ => other

/-- `v = se && nse;`, `v = se || nse;`: the right operand evaluated only when
the left does not decide (`logicalAndShortCircuitRhs`,
`logicalOrShortCircuitRhs`).  `localStep` calls it only where
`op.shortCircuits`, so on `&&` and `||` over `bool`: any other operator is
`false` (`.done false`), never reached. -/
def shortStep {p p' : PrimTy} (i : Idx Γ (.val p)) (op : BinOp) (ha : op.accepts p' = true)
    (hq : op.ret p' = p) (a : Simple C Γ p') (b : Val C Γ p') : Premise C Γ Γ :=
  match op, p', p, ha, hq, i, a, b with
  | .and, .bool, .bool, _, _, i, a, b =>
    .unfold (.cons (.ite (.simple a)
      (.cons (.assignLocal i b)
        (.cons (.assignLocal i (.binop .and rfl rfl (.simple (.local i)) (.simple (.bool true)))) .nil))
      (.cons (.assignLocal i (.simple (.bool false))) .nil)) .nil) .refl
  | .or, .bool, .bool, _, _, i, a, b =>
    .unfold (.cons (.ite (.simple a)
      (.cons (.assignLocal i (.simple (.bool true))) .nil)
      (.cons (.assignLocal i b)
        (.cons (.assignLocal i (.binop .or rfl rfl (.simple (.local i)) (.simple (.bool false)))) .nil)))
      .nil) .refl
  | _, _, _, _, _, _, _, _ => .done false

/-- A local assigned (`localStep`): a simple value, a read of a simple
location, an operator over simple operands is an update; anything else
unfolds the part that is not simple. -/
def localStep {p : PrimTy} (i : Idx Γ (.val p)) : Val C Γ p → Premise C Γ Γ
  -- localValueAssign
  | .simple s => .setLocal i (.simple s)
  -- storageRootReadSelect, storageFieldReadFind, storageIndexReadMappingFind,
  -- storageIndexReadArrayFind, or Step 1
  | .read l => (SHole.local i).readStep k (fun r h => .setLocal i (.read (.root r h)))
      (fun b f h => .setLocal i (.read (.field b f h)))
      (fun it b ie => .setLocal i (.read (.index it b (.simple ie)))) l
  -- binopAssignment
  | .binop op ha hq (.simple a) (.simple b) => .setLocal i (.binop op ha hq (.simple a) (.simple b))
  | @Val.binop _ _ p' _ op ha hq (.simple a) b =>
    -- logicalAndShortCircuitRhs, logicalOrShortCircuitRhs
    if op.shortCircuits then shortStep i op ha hq a b
    -- binopUnfoldRight
    else .capture p' (fse k) b
      (.assignLocal i.there (.binop op ha hq (.simple a.up) (.simple (.local .here))))
  -- binopUnfoldLeft
  | @Val.binop _ _ p' _ op ha hq a b =>
    .capture p' (fse k) a
      (.assignLocal i.there (.binop op ha hq (.simple (.local .here)) b.up))
  -- unopAssignment
  | .unop op ha hq (.simple a) => .setLocal i (.unop op ha hq (.simple a))
  -- unopCapture
  | @Val.unop _ _ p' _ op ha hq a =>
    .capture p' (fse k) a (.assignLocal i.there (.unop op ha hq (.simple (.local .here))))
  -- ternaryToIf, ternaryCaptureCond
  | .ternary c a b => ternaryStep k (.local i) c a b
  -- memoryFieldRead, memoryIndexReadArrayValue, or Step 1
  | .readMem l => (MHole.local i).readStep k
      (fun mv hmv f hf => .setLocal i (.readMem (.field (.var mv hmv) f hf)))
      (fun a mv hmv ie => .setLocal i (.readMem (.index a (.var mv hmv) (.simple ie)))) l
  | .len b hp =>
    -- storageLengthRead
    if b.isSimple then .setLocal i (.len b hp)
    -- storageLengthRead_unfold_rightFst
    else .captureSP (fsp k) b (.assignLocal i.there (.len (.alias .here) hp))
  -- memoryLengthRead
  | .mlen (.var mv hm) hp => .setLocal i (.mlen (.var mv hm) hp)
  -- memoryLengthRead_unfold_rightFst
  | .mlen (.loc l) hp =>
    .captureMV (fmv k) (.loc l) (.assignLocal i.there (.mlen (.var .here (MPath.loc l).mapFree) hp))
  -- Native modular builtin; its operands remain lazy typed terms.
  | .modular op a b modulus => .setLocal i (.modular op a b modulus)
  -- Lean only: the hash read at once, as `size` is (no solkey taclet)
  | .keccak b hp => .setLocal i (.keccak b hp)

/-- The elements of the array are mappings (`marr`; `darr` its negation). -/
def SPath.elemMapping {T : Ty} (_ : SPath C Γ T) : Bool := T.elemIsMapping

/-- The elements of the array are primitive (`parr`; `rarr` its negation). -/
def SPath.elemPrim {T : Ty} (_ : SPath C Γ T) : Bool := T.elemIsPrim

/-- An alias bound (`rebindStep`): to an alias or a location of simple parts
(`storageLocalRootRebind`, `…BindLocalRoot`), a location unfolded until it
is one, a push (`storageLocalRootPushBind`) on a simple receiver. -/
def rebindStep {R : RefTy} (i : Idx Γ (.alias R)) : ARhs C Γ R → Premise C Γ Γ
  -- storageLocalRootRebind
  | .path (.alias j) => .upd1 (.local i (.path (SPath.alias j).lower))
  -- storageLocalRootRebind, storageFieldReadBindLocalRoot,
  -- storageIndexReadMappingBindLocalRoot, storageIndexReadArrayBindLocalRoot(MappingElement)
  | .path (.loc l) => (SHole.rebind i).readStep k
      (fun r h => .upd1 (.local i (.path (Loc.root (Γ := Γ) r h).lower)))
      (fun b f h => .upd1 (.local i (.path (Loc.field b f h).lower)))
      (fun it b ie => .upd1 (.local i (.path (Loc.index it b (.simple ie)).lower))) l
  | .push b hd =>
    -- storageLocalRootPushBind, storageLocalRootPushBindMappingElement
    if b.isSimple then
      if b.elemMapping then .update (Upd.pushBindMapping i b)
      else .update (Upd.pushBind i b)
    -- storageLocalRootPush_unfold_leftFstReceiver
    else .captureSP (fsp k) b (.rebind i.there (.push (.alias .here) hd))

/-- A copy into a target whose parts are simple (`copyStep`): a simple
source is copied (Step 3), a member or entry of a simple path bound to an
alias first (`storageFieldRead_unfold_rightSndResult`,
`storageIndexRead_unfold_rightSndResult`), any other unfolded (Step 1). -/
def copyStep {R : RefTy} (l : Loc C Γ (.ref R)) (hm : (Ty.ref R).mapFree = true) :
    SPath C Γ (.ref R) → Premise C Γ Γ
  | .alias y => .save l (.copy (.alias y) hm)
  | .loc l' => (SHole.copy l hm).readStep k (fun _ _ => .save l (.copy (.loc l') hm))
      (fun b f hf => .captureSP (fsp k) (.loc (.field b f hf)) (.assign l.up (.copy (.alias .here) hm)))
      (fun it b ie => .captureSP (fsp k) (.loc (.index it b (.simple ie)))
        (.assign l.up (.copy (.alias .here) hm))) l'

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
def assignStep : {T : Ty} → Loc C Γ T → Src C Γ T → Premise C Γ Γ
  | _, l, .copyMem p => .save l (.copyMem p)
  | _, l, .fixedCopy p shape hm => .save l (.fixedCopy p shape hm)
  -- storageRootWriteStore, storageRootWriteValueRhsCapture
  | _, .root r h, .val e =>
    (VHole.store (.root r h)).step k (fun se => .save (.root r h) (.val (.simple se))) e
  -- storageRootWriteCopySource
  | _, .root r h, .copy (.alias j) hm => .save (.root r h) (.copy (.alias j) hm)
  -- storageRootWriteCopySource, storageFieldReadStoreRoot,
  -- storageIndexReadMappingStoreRoot, storageIndexReadArrayStoreRoot, or Step 1
  | _, .root r h, .copy (.loc l) hm =>
    let done := .save (.root r h) (.copy (.loc l) hm)
    (SHole.copy (.root r h) hm).readStep k (fun _ _ => done) (fun _ _ _ => done) (fun _ _ _ => done) l
  | _, .field b f h, .val e =>
    -- storageFieldWriteSave, fieldWriteValueRhsCapture
    if b.isSimple then
      (VHole.store (.field b f h)).step k (fun se => .save (.field b f h) (.val (.simple se))) e
    -- storageFieldWrite_unfold_leftFst
    else (VHole.store (.field b f h)).lower k (.unfold
      (.cons (.declLocal _ (fse k) (some e))
        (.cons (.declStorage _ (fsp k) (some (.path b.up)))
          (.cons (.assign (.field (.alias .here) f h) (.val (.simple (.local (.there .here))))) .nil)))
      (.push (.push .refl))) e
  | _, .field b f h, .copy p hm =>
    -- storageFieldWriteCopySource, or the source unfolded
    if b.isSimple then copyStep k (.field b f h) hm p
    -- storageFieldWriteStorageRef_unfold_leftFst
    else .captureSP (fsp k) b (.assign (.field (.alias .here) f h) (.copy p.up hm))
  | _, .index it b i, .val e =>
    if b.isSimple then
      match i with
      -- storageIndexWriteMappingSave, storageIndexWriteArraySave, indexWriteValueRhsCapture
      | .simple ie => (VHole.store (.index it b (.simple ie))).step k
          (fun se => .save (.index it b (.simple ie)) (.val (.simple se))) e
      -- storageIndexWriteCaptureAllNonSimpleIndex
      | i => (VHole.store (.index it b i)).lower k (indexCaptureAll k it b i e) e
    -- storageIndexWriteCaptureAllComplexRecv
    else (VHole.store (.index it b i)).lower k (indexCaptureAll k it b i e) e
  | _, .index it b i, .copy p hm =>
    if b.isSimple then
      match i with
      -- storageIndexWriteMappingCopySource, storageIndexWriteArrayCopySource
      | .simple ie => copyStep k (.index it b (.simple ie)) hm p
      -- storageIndexWriteStorageRefCaptureAllNonSimpleIndex
      | i => indexRefCaptureAll k it b i p hm
    -- storageIndexWriteStorageRefCaptureAllComplexRecv
    else indexRefCaptureAll k it b i p hm

/-- A storage location written from memory (`assignFromMemStep`): the
receiver first, then the index; the memory path copied as it is. -/
def assignFromMemStep {R : RefTy} : Loc C Γ (.ref R) → MPath C Γ (.ref R) → Premise C Γ Γ
  -- memoryToStorageStoreRoot
  | .root r h, p => .saveMem (.root r h) p
  | .field b f h, p =>
    -- memoryToStorageFieldCopyRoot
    if b.isSimple then .saveMem (.field b f h) p
    -- memoryToStorageField_unfold_leftFst
    else .captureSP (fsp k) b (.assignFromMem (.field (.alias .here) f h) p.up)
  | @Loc.index _ _ R' kp _ it b i, p =>
    let capture : Premise C Γ Γ :=
      .unfold (.cons (.declStorage R' (fsp k) (some (.path b)))
        (.cons (.declLocal kp (fie k) (some i.up))
        (.cons (.assignFromMem (.index it (.alias (.there .here)) (.simple (.local .here))) p.up.up)
          .nil))) (.push (.push .refl))
    if b.isSimple then
      match i with
      -- memoryToStorageIndexMappingCopyRoot, memoryToStorageIndexArrayCopyRoot
      | .simple ie => .saveMem (.index it b (.simple ie)) p
      -- memoryToStorageIndexCaptureAllNonSimpleIndex
      | _ => capture
    -- memoryToStorageIndexCaptureAllComplexRecv
    else capture

/-- `delete l;` (`deleteStep`): the receiver first, then the index. -/
def deleteStep {T : Ty} : Loc C Γ T → Premise C Γ Γ
  -- storageRootDelete
  | .root r h => .delAt (.root r h)
  | .field b f h =>
    -- storageFieldDelete
    if b.isSimple then .delAt (.field b f h)
    -- storageFieldDelete_unfold_leftFst
    else .captureSP (fsp k) b (.delete (.field (.alias .here) f h))
  | @Loc.index _ _ _ kp _ it b i =>
    if b.isSimple then
      match i with
      -- storageIndexDelete, storageIndexArrayDelete
      | .simple ie => .delAt (.index it b (.simple ie))
      -- storageIndexDeleteNonSimpleIndexCapture
      | i => .capture kp (fie k) i (.delete (.index it b.up (.simple (.local .here))))
    -- storageIndexDelete_unfold_leftFst
    else .captureSP (fsp k) b (.delete (.index it (.alias .here) i.up))

/-! ### Compound assignment and `++`/`--` -/

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
    (l : OpLoc C Γ p) : Val C Γ p → Premise C Γ Γ
  -- localOpAssign, storageRootOpAssign, storageFieldOpAssign,
  -- storageIndexMappingOpAssign, storageIndexArrayOpAssign, memoryFieldOpAssign,
  -- memoryIndexArrayOpAssign; or storageFieldOpAssignUnfoldLeftFst,
  -- storageIndexOpAssignUnfoldLeftFst, memoryFieldOpAssignUnfoldLeftFst,
  -- memoryIndexOpAssignUnfoldLeftFst
  | .simple se =>
    match l.unfoldRecv k (fun l' => .opAssign op hop hp l' (.simple se.up)) with
    | some q => q
    | none => .upd1 (l.set (l.op op hop hp se.lower))
  -- compoundAssignValueRhsCapture
  | r => .capture p (fse k) r (.opAssign op hop hp l.up (.simple (.local .here)))

/-- `l++;` (`incStep`): the receiver first. -/
def incStep {p : PrimTy} (op : IncDec) (hp : p.isNumeric = true) (l : OpLoc C Γ p) :
    Premise C Γ Γ :=
  -- storageFieldIncrementUnfoldLeftFst, storageIndexIncrementUnfoldLeftFst,
  -- memoryFieldIncrementUnfoldLeftFst, memoryIndexIncrementUnfoldLeftFst
  match l.unfoldRecv k (fun l' => .incDec op hp l') with
  | some q => q
  -- localIncrement, storageRootIncrement, storageFieldIncrement,
  -- storageIndexIncrement, memoryFieldIncrement, memoryIndexArrayIncrement
  | none => .upd1 (l.set (l.op op.binOp (IncDec.binOp_compound op) hp (Tm.one p hp)))

/-- `v = l++;`, its receiver simple (`localAssignIncrement`,
`storageRootIncrementAssignment`, `storageFieldIncrementAssignment`,
`storageIndexIncrementAssignment`, `memoryFieldIncrementAssignment`,
`memoryIndexArrayIncrementAssignment`). -/
def assignIncStep {p : PrimTy} (i : Idx Γ (.val p)) (op : IncDec) (hp : p.isNumeric = true)
    (l : OpLoc C Γ p) : Premise C Γ Γ :=
  .update ((Upd.nil.snoc (l.set (l.op op.binOp (IncDec.binOp_compound op) hp (Tm.one p hp)))).snoc
    (.local i (.val (Tm.bumped op hp l.cur))))

/-! ### Arrays and payments -/

/-- `v = b.push()`: bind a complex receiver before appending its zero. -/
def assignLocalPushStep {p : PrimTy} (i : Idx Γ (.val p))
    (b : SPath C Γ (.array (.prim p))) : Premise C Γ Γ :=
  if b.isSimple then .update (Upd.pushBindPrim i b)
  else .captureSP (fsp k) b (.assignLocalPush i.there (.alias .here))

/-- `b.push() op= rhs`: capture the source first, then the receiver, and
keep the append and arithmetic as two successive updates. -/
def pushOpStep {p : PrimTy} (op : BinOp) (hop : op.hasCompoundAssign = true)
    (hp : p.isNumeric = true) (b : SPath C Γ (.array (.prim p))) :
    Val C Γ p → Premise C Γ Γ
  | .simple se =>
    if b.isSimple then
      if PushSuffix.needsZeroGuard op then
        .guardedUpdates (PushSuffix.nonzero hp se) (Upd.nil.snoc (UpdElem.pushSlot b))
          (PushSuffix.saveOp op hop hp b se)
      else .updates (Upd.nil.snoc (UpdElem.pushSlot b)) (PushSuffix.saveOp op hop hp b se)
    else .captureSP (fsp k) b (.pushOpAssign op hop hp (.alias .here) (.simple se.up))
  | r => .capture p (fse k) r (.pushOpAssign op hop hp b.up (.simple (.local .here)))

/-- `++b.push()` or `b.push()++` as a statement: capture the receiver once,
append, then modify the new slot. The expression's value is discarded. -/
def pushIncStep {p : PrimTy} (op : IncDec) (hp : p.isNumeric = true)
    (b : SPath C Γ (.array (.prim p))) : Premise C Γ Γ :=
  if b.isSimple then
    .updates (Upd.nil.snoc (UpdElem.pushSlot b))
      (PushSuffix.saveOp op.binOp op.binOp_compound hp b
        (.lit 1 (by cases p <;> first | rfl | exact absurd hp Bool.false_ne_true)))
  else .captureSP (fsp k) b (.pushIncDec op hp (.alias .here))

/-- `b.push(v);` (`pushStep`): the receiver first, then the argument. -/
def pushStep {E : Ty} (b : SPath C Γ (.array E)) (v : Option (Src C Γ E))
    (hd : (v.isSome || E.defaultOkS) = true) : Premise C Γ Γ :=
  if b.isSimple then
    match E, b, v with
    | E, b, none =>
      -- storagePushLengthSave
      if b.elemPrim then .upd1 (UpdElem.pushSlot b)
      -- Every element is kept as it is: the push saves only the length.
      else if b.elemMapping then .upd1 (UpdElem.extend b)
      else .upd1 (UpdElem.pushSlot b)
    -- storagePushValueSave
    | _, b, some (.val (.simple se)) =>
      .upd1 (UpdElem.push b (.val (.simple se)))
    -- storagePushValue_unfold_rightSndArgument
    | _, b, some (.val e) =>
      .capture _ (if e.complexStorageRead then .fresh "source" k else fse k) e
        (.push b.up (some (.val (.simple (.local .here)))) rfl)
    -- storagePushValueCopySource
    | _, b, some (.copy p hm) =>
      if p.isSimple then .upd1 (UpdElem.push b (.copy p hm))
      else .captureSP (.fresh "source" k) p
        (.push b.up (some (.copy (.alias .here) hm)) rfl)
    | _, b, some (.copyMem p) =>
      if p.isSimple then .upd1 (UpdElem.push b (.copyMem p))
      else .captureMV (fmv k) p
        (.push b.up (some (.copyMem (.var .here p.mapFree))) rfl)
    | _, b, some (.fixedCopy p shape hm) => .upd1 (UpdElem.push b (.fixedCopy p shape hm))
  -- storagePush_unfold_leftFstReceiver, storagePushValue_unfold_leftFstReceiver
  else .captureSP (fsp k) b (.push (.alias .here) (v.map Src.up) (by
    cases v <;> exact hd))

/-- `b.pop();` (`popStep`): the receiver first. -/
def popStep {E : Ty} (b : SPath C Γ (.array E)) : Premise C Γ Γ :=
  if b.isSimple then
    -- storagePopSaveMappingElement
    if b.elemMapping then .upd1 (UpdElem.shrink b)
    -- storagePopSave
    else .upd1 (UpdElem.pop b)
  -- storagePop_unfold_leftFstReceiver
  else .captureSP (fsp k) b (.pop (.alias .here))

/-- `r.transfer(a);` (`transferStep`): the receiver first, then the amount. -/
def transferStep (m : Modality) : Val C Γ .uint → Val C Γ .uint → Premise C Γ Γ
  | .simple sadr, .simple se => match m with
    -- transferNoCallbackBox
    | .box => .upd1 (UpdElem.payTo sadr se)
    -- transferDiamond (Lean)
    | .diamond => .done false
  -- transfer_unfold_rightSndArgument
  | .simple sadr, a => .capture .uint (fse k) a (.transfer (.simple sadr.up) (.simple (.local .here)))
  -- transfer_unfold_leftFstReceiver
  | r, a => .capture .uint (fse k) r (.transfer (.simple (.local .here)) a.up)

/-- `pv = r.send(a);` (`sendStep`): the receiver first, then the amount;
both simple, the send's two outcomes. -/
def sendStep (m : Modality) (pv : Idx Γ (.val .bool)) (full : Bool) :
    Val C Γ .uint → Val C Γ .uint → Premise C Γ Γ
  | .simple sadr, .simple se =>
    let us : List (Upd C Γ Γ) :=
      [(Upd.nil.snoc (UpdElem.payTo sadr se)).snoc (.local pv (.val (Tm.lit (p := .bool) true))),
        Upd.nil.snoc (.local pv (.val (Tm.lit (p := .bool) false)))]
    match m with
    -- sendNoCallbackBox
    | .box => .cases [] us
    -- sendNoCallbackDiamond
    | .diamond =>
      .cases [.isBool (.app2 (.binop .le (p := .uint) rfl) (Tm.lit (p := .uint) ⟨0, rfl⟩) se.lower)
        true] us
  -- send_unfold_rightSndArgument
  | .simple sadr, a =>
    .capture .uint (fse k) a (.send pv.there (.simple sadr.up) (.simple (.local .here)) full)
  -- send_unfold_leftFstReceiver
  | r, a => .capture .uint (fse k) r (.send pv.there (.simple (.local .here)) a.up full)

/-! ### Memory -/

/-- A memory local bound (`rebindMemStep`): to a memory local
(`memoryRootRebind`), a location of one, unfolded until it is
(`memoryFieldReadAliasRoot`, `memoryIndexReadArrayMemory`), a deep copy of
storage (`memoryStorageCopy`, `memoryStorageCopyUnfold`), a fresh array
(`memoryArrayFreshAlloc`). -/
def rebindMemStep {R : RefTy} (i : Idx Γ (.mem R)) : MRhs C Γ R → Premise C Γ Γ
  | .alias (.var j hj) => .upd1 (.local i (.mref (MPath.var j hj).lower))
  | .alias (.loc l) => (MHole.rebind i).readStep k
      (fun mv hmv f hf => .upd1 (.local i (.mref (MPath.loc (.field (.var mv hmv) f hf)).lower)))
      (fun a mv hmv ie =>
        .upd1 (.local i (.mref (MPath.loc (.index a (.var mv hmv) (.simple ie))).lower))) l
  | .copy sp hm =>
    if sp.isSimple then .allocCopy i hm (.app2 .sfind Tm.storage sp.lower)
    else .captureSP (fsp k) sp (.rebindMem i.there (.copy (.alias .here) hm))
  | .newArr n h => .allocCopy i (RefTy.mapFree_of_newArrOk h) (.app1 (.newArr h) n.lower)

/-- A memory reference written to the target `l` (`memRefStep`): a memory
local or a bindable location is written (`memoryFieldWriteCopy`,
`memoryIndexWriteCopy`), any other source unfolded (Step 1). -/
def memRefStep {R : RefTy} (l : MLoc C Γ (.ref R)) : MPath C Γ (.ref R) → Premise C Γ Γ
  | .var y hy => .writeMem l (.ref (.var y hy))
  | .loc sl => (MHole.write l).readStep k
      (fun mv hmv f hf => .writeMem l (.ref (.loc (.field (.var mv hmv) f hf))))
      (fun a mv hmv ie => .writeMem l (.ref (.loc (.index a (.var mv hmv) (.simple ie))))) sl

/-- A memory location written (`assignMemStep`): the receiver first, then
the index, then the source. -/
def assignMemStep : {T : Ty} → MLoc C Γ T → MSrc C Γ T → Premise C Γ Γ
  -- memoryFieldWrite, memoryFieldWriteUnfoldSource
  | _, .field (.var mv hmv) f hf, .val e => (VHole.mem (.field (.var mv hmv) f hf)).step k
      (fun se => .writeMem (.field (.var mv hmv) f hf) (.val (.simple se))) e
  | _, .field (.var mv hmv) f hf, .ref src => memRefStep k (.field (.var mv hmv) f hf) src
  -- memoryFieldWrite_unfold_leftFst
  | _, .field (.loc l) f hf, r =>
    .captureMV (fmv k) (.loc l) (.assignMem (.field (.var .here (MPath.loc l).mapFree) f hf) r.up)
  -- memoryIndexWriteArray, memoryIndexWriteUnfoldSource
  | _, .index a (.var mv hmv) (.simple ie), .val e => (VHole.mem (.index a (.var mv hmv) (.simple ie))).step k
      (fun se => .writeMem (.index a (.var mv hmv) (.simple ie)) (.val (.simple se))) e
  | _, .index a (.var mv hmv) (.simple ie), .ref src => memRefStep k (.index a (.var mv hmv) (.simple ie)) src
  -- memoryIndexWriteCaptureAllNonSimpleIndex
  | _, .index a (.var mv hmv) i, .val e =>
    .unfold (.cons (.declLocal _ (fse k) (some e))
      (.cons (.declLocal .uint (fie k) (some i.up))
      (.cons (.assignMem (.index a (.var mv.there.there hmv) (.simple (.local .here)))
        (.val (.simple (.local (.there .here))))) .nil))) (.push (.push .refl))
  -- memoryIndexWriteMemRefCaptureAllNonSimpleIndex
  | _, .index a (.var mv hmv) i, .ref src =>
    .capture .uint (fie k) i (.assignMem (.index a (.var mv.there hmv) (.simple (.local .here)))
      (.ref src.up))
  -- memoryIndexWriteCaptureAllComplexRecv
  | _, @MLoc.index _ _ R _ a (.loc l) i, .val e =>
    .unfold (.cons (.declLocal _ (fse k) (some e))
      (.cons (.declMem R (fmv k) (some (.alias (MPath.loc l).up)) rfl (MPath.loc l).mapFree)
      (.cons (.declLocal .uint (fie k) (some i.up.up))
      (.cons (.assignMem (.index a (.var (.there .here) (MPath.loc l).mapFree) (.simple (.local .here)))
        (.val (.simple (.local (.there (.there .here)))))) .nil))))
      (.push (.push (.push .refl)))
  -- memoryIndexWriteMemRefCaptureAllComplexRecv
  | _, @MLoc.index _ _ R _ a (.loc l) i, .ref src =>
    .unfold (.cons (.declMem R (fmv k) (some (.alias (.loc l))) rfl (MPath.loc l).mapFree)
      (.cons (.declLocal .uint (fie k) (some i.up))
      (.cons (.assignMem (.index a (.var (.there .here) (MPath.loc l).mapFree) (.simple (.local .here)))
        (.ref src.up.up)) .nil))) (.push (.push .refl))

/-- `delete p;` on memory (`deleteMemStep`): a memory local bound to a fresh
default object, a member or element of one reset by the rule its type
picks, any other receiver bound first, a complex index captured. -/
def deleteMemStep : {T : Ty} → MPath C Γ T → T.defaultOkS = true → Premise C Γ Γ
  -- memoryRootDeleteFreshRebind
  | _, @MPath.var _ _ _ i hm, _ => .update (Upd.allocFresh i hm)
  -- memoryFieldDeletePrimitive, memoryFieldDeleteReference
  | _, .loc (@MLoc.field _ _ _ T (.var mv hmv) f hf), _ =>
    .clearMem T (MLoc.field (.var mv hmv) f hf).lower (MLoc.field (.var mv hmv) f hf).mapFree
  -- memoryFieldDelete_unfold_leftFst
  | _, .loc (.field (.loc l) f hf), hd =>
    .captureMV (fmv k) (.loc l) (.deleteMem (.loc (.field (.var .here (MPath.loc l).mapFree) f hf)) hd)
  -- memoryIndexDeletePrimitive, memoryIndexDeleteReference
  | _, .loc (@MLoc.index _ _ _ T a (.var mv hmv) (.simple ie)), _ =>
    .clearMem T (MLoc.index a (.var mv hmv) (.simple ie)).lower
      (MLoc.index a (.var mv hmv) (.simple ie)).mapFree
  -- memoryIndexDeleteNonSimpleIndexCapture
  | _, .loc (.index a (.var mv hmv) i), hd =>
    .capture .uint (fie k) i (.deleteMem (.loc (.index a (.var mv.there hmv) (.simple (.local .here)))) hd)
  -- memoryIndexDelete_unfold_leftFst
  | _, .loc (.index a (.loc l) i), hd =>
    .captureMV (fmv k) (.loc l) (.deleteMem (.loc (.index a (.var .here (MPath.loc l).mapFree) i.up)) hd)

/-- `tgt = new T(se);` (`newArrayCapture`): the fresh array bound to a fresh
memory local first. -/
def assignNewStep {R : RefTy} (l : NewLhs C Γ R) (n : Simple C Γ .uint) (h : R.newArrOk = true) :
    Premise C Γ Γ :=
  .unfold (.cons (.declMem R (fmv k) (some (.newArr n h)) rfl (MRhs.newArr (C := C) (Γ := Γ) n h).mapFree)
    (.cons (l.up.fill (.var .here (MRhs.newArr (C := C) (Γ := Γ) n h).mapFree)) .nil)) (.push .refl)

/-! ### Control flow -/

/-- `if (c) …`: split on a simple condition (`ifElseSplit`), capture any
other (`ifElseUnfold`), the branches read with the capture on top: weakened
by `Prog.wk up`, which the kernel runs on every captured condition. -/
def iteStep {Γ₁ Γ₂ : Ctx} (c : Val C Γ .bool) (thn : Prog C Γ Γ₁) (els : Prog C Γ Γ₂) :
    Premise C Γ Γ :=
  match c with
  | .simple s => .split .block (Fml.isBool s.lower true) (Fml.isBool s.lower false) thn els
  | c => .capture .bool (fse k) c
      (.ite (.simple (.local .here)) (thn.wk up).2.2 (els.wk up).2.2)

/-- `require(c);`: two goals on a simple condition (`requireSimple`), the
condition captured otherwise (`requireConditionCapture`). -/
def requireStep : Val C Γ .bool → Premise C Γ Γ
  | .simple s => .split .capture (Fml.isBool s.lower true) (Fml.isBool s.lower false) .nil
      (.cons .revert .nil)
  | c => .capture .bool (fse k) c (.require (.simple (.local .here)))

/-- `assert(c);`: the check of a simple condition (`assertSimple`), the
condition captured otherwise (`assertConditionCapture`). -/
def assertStep : Val C Γ .bool → Premise C Γ Γ
  | .simple s => .check (Fml.isBool s.lower true)
  | c => .capture .bool (fse k) c (.assert (.simple (.local .here)))

end Rules

end Solidity
