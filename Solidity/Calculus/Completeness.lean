import Solidity.Calculus.Rules

/-!
# Every statement has a rule

`Stmt.step k m s` is the rule for the statement `s` under the modality `m`:
its premise, and the derivation `Taclet C k m s p` (`Rules.lean`), its fresh
variables declared at index `k`.  It is a **total function** over the typed
syntax, so Lean's exhaustiveness check on its patterns is the coverage
proof; `Stmt.complete` states it.  A combination the types rule out (a value
written to an alias, a `delete` of a local, a memory mapping) needs no arm.

Each arm fires the one rule whose side conditions (`Rules.lean`) hold of
the statement, and proves them (`side_cond`) from what the arm knows: the
constructors it matched, and the facts its branches bring into scope
(`if h : b.isSimple`, a callback's hypotheses).  So the arm and the
condition are the same thing written twice, and `Taclet.eq_step`
(`Uniqueness.lean`) checks they agree.  The rule depends on the
constructors of the statement and on whether its parts are simple — a
simple `SPath` is an alias or a state variable, a simple `MPath` a memory
local, a simple `Val` a literal or a local — in this order:

* **Step 1** unfolds a read whose receiver or index is not simple
  (`Hole.readStep`, `MHole.readStep`);
* **Step 2** decomposes a write: its receiver first, then its index, then
  its source;
* **Step 3** turns a statement whose parts are all simple into an update.

A conditional written somewhere is lowered to a branch (`ternaryStep`)
before any rule captures it into a local, and `&&`/`||` keep their right
operand behind a branch (`binopRightStep`).  A compound assignment captures
its source first, since its receiver rules take a simple one.
-/

namespace Solidity

variable {C : Contract} {k : Nat} {m : Modality}

/-- A rule for `s` under `m`: its premise and its derivation. -/
structure Step (k : Nat) (m : Modality) (s : Stmt C) where
  premise : Premise C
  taclet : Taclet C k m s premise

/-! ## Values -/

/-- `x = c ? a : b;` becomes a branch on `c`, which is captured first when it
is not simple (`bool se = people[i].adult;`).  The same two rules serve a
local, a storage location and a memory location: `lhs` is the hole. -/
def ternaryStep {p : PrimTy} (lhs : VHole C p) (hl : lhs.isTarget = true) :
    (c : Val C .bool) → (a b : Val C p) → Step k m (lhs.fill (.ternary c a b))
  | .simple _, _, _ => ⟨_, .ternaryToIf⟩
  | .read _, _, _ | .binop .., _, _ | .unop .., _, _ | .ternary .., _, _ | .readMem _, _, _
  | .len .., _, _ | .mlen .., _, _ =>
    ⟨_, .ternaryCaptureCond⟩

/-- A value written to `lhs` by `other`, unless it is a conditional, which is
lowered first: `people[i].age = b ? 1 : 2;` branches before it captures
anything. -/
def VHole.lower {p : PrimTy} (lhs : VHole C p) (hl : lhs.isTarget = true) :
    (e : Val C p) → (e.notTernary = true → Step k m (lhs.fill e)) → Step k m (lhs.fill e)
  | .ternary c a b, _ => ternaryStep lhs hl c a b
  | .simple _, other | .read _, other | .binop .., other | .unop .., other
  | .readMem _, other | .len .., other | .mlen .., other => other rfl

/-- A value written to `lhs` whose target is all simple: a simple value by
`simple` (Step 3, `alice.age = 10;`), a conditional lowered, anything else
captured by `capture` (`alice.age = bob.age + 1;`). -/
def VHole.step {p : PrimTy} (lhs : VHole C p) (hl : lhs.isTarget = true)
    (simple : (se : Simple C p) → Step k m (lhs.fill (.simple se))) :
    (e : Val C p) → (e.isSimple = false → e.notTernary = true → Step k m (lhs.fill e)) →
      Step k m (lhs.fill e)
  | .simple se, _ => simple se
  | .ternary c a b, _ => ternaryStep lhs hl c a b
  | .read _, capture | .binop .., capture | .unop .., capture | .readMem _, capture
  | .len .., capture | .mlen .., capture =>
    capture rfl rfl

/-! ## Step 1: reads -/

/-- A storage location read into the hole `lhs` (`v = □`, `lsv = □`,
`loc = □`): a state variable, a member of a simple path or an entry of one at
a simple index take the hole's own rule (`root`, `field`, `index`); any other
unfolds its receiver (`x = people[i].age;`) or its index (`x = ages[i + 1];`)
first. -/
def Hole.readStep {T : Ty} (lhs : Hole C T) (ht : lhs.isTarget = true)
    (root : (r : Name) → (h : C.rootType r = some T) → Step k m (lhs.fill (.loc (.root r h))))
    (field : {s : Name} → (sp : SPath C (.struct s)) → (f : Name) →
      (hf : C.fieldType s f = some T) → sp.isSimple = true →
      Step k m (lhs.fill (.loc (.field sp f hf))))
    (index : {R : RefTy} → {kp : PrimTy} → (it : IndexTy R kp T) → (sp : SPath C (.ref R)) →
      (ie : Simple C kp) → sp.isSimple = true →
      Step k m (lhs.fill (.loc (.index it sp (.simple ie))))) :
    (l : Loc C T) → Step k m (lhs.fill (.loc l))
  | .root r h => root r h
  | .field b f hf =>
    if hb : b.isSimple then field b f hf hb else ⟨_, .storageFieldRead_unfold_rightFst⟩
  | .index it b i =>
    if hb : b.isSimple then
      match i with
      | .simple ie => index it b ie hb
      | .read _ | .binop .. | .unop .. | .ternary .. | .readMem _ | .len .. | .mlen .. =>
        ⟨_, .storageIndexRead_unfold_rightSndIndex⟩
    else ⟨_, .storageIndexRead_unfold_rightFst⟩

/-- A memory location read into the hole `lhs` (`v = □`, `mv = □`,
`mloc = □`): a member of a memory local, or an element of one at a simple
index, takes the hole's own rule; any other unfolds its receiver
(`x = m.items[i];`) or its index (`x = m[i + 1];`) first. -/
def MHole.readStep {T : Ty} (lhs : MHole C T) (ht : lhs.isTarget = true)
    (field : {s : Name} → (mv : Var) → (f : Name) → (hf : C.fieldType s f = some T) →
      Step k m (lhs.fill (.field (.var mv) f hf)))
    (index : {R : RefTy} → (a : ArrTy R T) → (mv : Var) → (ie : Simple C .uint) →
      Step k m (lhs.fill (.index a (.var mv) (.simple ie)))) :
    (l : MLoc C T) → Step k m (lhs.fill l)
  | .field (.var mv) f hf => field mv f hf
  | .field (.loc _) _ _ => ⟨_, .memoryFieldRead_unfold_rightFst⟩
  | .index a (.var mv) (.simple ie) => index a mv ie
  | .index _ (.var _) (.read _) | .index _ (.var _) (.binop ..) | .index _ (.var _) (.unop ..)
  | .index _ (.var _) (.ternary ..) | .index _ (.var _) (.readMem _) | .index _ (.var _) (.len ..)
  | .index _ (.var _) (.mlen ..) =>
    ⟨_, .memoryIndexRead_unfold_rightSndIndex⟩
  | .index _ (.loc _) _ => ⟨_, .memoryIndexRead_unfold_rightFst⟩

/-! ## Locals and aliases -/

/-- `v = se ⊕ nse;`: `&&` and `||` evaluate `nse` only when `se` does not
decide, so they branch on it (`b = ok && people[i].adult;`); any other
operator captures `nse` (`v = 1 + people[i].age;`). -/
def binopRightStep {p q : PrimTy} (x : Var) (op : BinOp) (hop : op.accepts p = true)
    (hq : op.ret p = q) (se : Simple C p) (nse : Val C p) (hn : nse.isSimple = false) :
    Step k m (.assignLocal x (.binop op hop hq (.simple se) nse)) :=
  match op, hop, hq with
  | .and, hop, hq =>
    match p, q, hop, hq, se, nse, hn with
    | .bool, .bool, _, _, _, _, _ => ⟨_, .logicalAndShortCircuitRhs⟩
    | .bool, .uint, _, hq, _, _, _ | .bool, .int, _, hq, _, _, _ => absurd hq (by decide)
    | .uint, _, hop, _, _, _, _ | .int, _, hop, _, _, _, _ => absurd hop (by decide)
  | .or, hop, hq =>
    match p, q, hop, hq, se, nse, hn with
    | .bool, .bool, _, _, _, _, _ => ⟨_, .logicalOrShortCircuitRhs⟩
    | .bool, .uint, _, hq, _, _, _ | .bool, .int, _, hq, _, _, _ => absurd hq (by decide)
    | .uint, _, hop, _, _, _, _ | .int, _, hop, _, _, _, _ => absurd hop (by decide)
  | .add, _, _ | .sub, _, _ | .mul, _, _ | .pow, _, _ | .div, _, _ | .mod, _, _ | .lt, _, _
  | .gt, _, _ | .le, _, _ | .ge, _, _ | .eqB, _, _ | .neB, _, _ => ⟨_, .binopUnfoldRight⟩

/-- A local assigned: `x = 10;`, `x = people[i].age;` (a read, unfolded
until it is one), `x = a + b;`, `x = m.age;`. -/
def localStep {p : PrimTy} (x : Var) : (v : Val C p) → Step k m (.assignLocal x v)
  | .simple _ => ⟨_, .localValueAssign⟩
  | .read l =>
    (Hole.local x).readStep rfl (fun _ _ => ⟨_, .storageRootReadSelect⟩)
      (fun _ _ _ _ => ⟨_, .storageFieldReadFind⟩)
      (fun it sp ie _ => match it, sp, ie with
        | .map, _, _ => ⟨_, .storageIndexReadMappingFind⟩
        | .arr _, _, _ => ⟨_, .storageIndexReadArrayFind⟩) l
  | .binop _ _ _ (.simple _) (.simple _) => ⟨_, .binopAssignment⟩
  | .binop op hop hq (.simple se) (.read l) => binopRightStep x op hop hq se (.read l) rfl
  | .binop op hop hq (.simple se) (.binop op' hop' hq' a b) =>
    binopRightStep x op hop hq se (.binop op' hop' hq' a b) rfl
  | .binop op hop hq (.simple se) (.unop op' hop' hq' a) =>
    binopRightStep x op hop hq se (.unop op' hop' hq' a) rfl
  | .binop op hop hq (.simple se) (.ternary c a b) =>
    binopRightStep x op hop hq se (.ternary c a b) rfl
  | .binop op hop hq (.simple se) (.readMem l) => binopRightStep x op hop hq se (.readMem l) rfl
  | .binop op hop hq (.simple se) (.len b h) => binopRightStep x op hop hq se (.len b h) rfl
  | .binop op hop hq (.simple se) (.mlen b h) => binopRightStep x op hop hq se (.mlen b h) rfl
  | .binop _ _ _ (.read _) _ | .binop _ _ _ (.binop ..) _ | .binop _ _ _ (.unop ..) _
  | .binop _ _ _ (.ternary ..) _ | .binop _ _ _ (.readMem _) _ | .binop _ _ _ (.len ..) _
  | .binop _ _ _ (.mlen ..) _ => ⟨_, .binopUnfoldLeft⟩
  | .unop _ _ _ (.simple _) => ⟨_, .unopAssignment⟩
  | .unop _ _ _ (.read _) | .unop _ _ _ (.binop ..) | .unop _ _ _ (.unop ..)
  | .unop _ _ _ (.ternary ..) | .unop _ _ _ (.readMem _) | .unop _ _ _ (.len ..)
  | .unop _ _ _ (.mlen ..) => ⟨_, .unopCapture⟩
  | .ternary c a b => ternaryStep (.local x) rfl c a b
  | .readMem l =>
    (MHole.local x).readStep rfl (fun _ _ _ => ⟨_, .memoryFieldReadHeap⟩)
      (fun _ _ _ => ⟨_, .memoryIndexReadHeap⟩) l
  | .len b _ =>
    if hb : b.isSimple then ⟨_, .storageLengthRead⟩ else ⟨_, .storageLengthRead_unfold_rightFst⟩
  | .mlen (.var _) _ => ⟨_, .memoryLengthRead⟩
  | .mlen (.loc _) _ => ⟨_, .memoryLengthRead_unfold_rightFst⟩

/-- An alias bound: `lsv = alice;`, `lsv = people[i];` (a path, unfolded
until it is bindable), `lsv = people.push();` (its receiver first). -/
def rebindStep {R : RefTy} (x : Var) : (r : ARhs C R) → Step k m (.rebind x r)
  | .path (.alias _) => ⟨_, .storageLocalRootRebind⟩
  | .path (.loc l) =>
    (Hole.rebind x).readStep rfl (fun _ _ => ⟨_, .storageLocalRootRebind⟩)
      (fun _ _ _ _ => ⟨_, .storageFieldReadBindLocalRoot⟩)
      (fun it sp ie _ => match it, sp, ie with
        | .map, _, _ => ⟨_, .storageIndexReadMappingBindLocalRoot⟩
        | .arr _, sp, _ =>
          if hE : sp.elemMapping then ⟨_, .storageIndexReadArrayBindLocalRootMappingElement⟩
          else ⟨_, .storageIndexReadArrayBindLocalRoot⟩) l
  | .push b _ =>
    if hb : b.isSimple then
      if hE : b.elemMapping then ⟨_, .storageLocalRootPushBindMappingElement⟩
      else ⟨_, .storageLocalRootPushBind⟩
    else ⟨_, .storageLocalRootPush_unfold_leftFstReceiver⟩

/-! ## Storage writes -/

/-- A copy into a member or an entry at a target, `alice.account = src;`: a
simple source is copied by `copy` (Step 3); a member or an entry of a simple
path is bound to an alias first (`Account storage sp = bob.account;`); any
other source unfolds its own receiver or index (Step 1). -/
def copyStep {R : RefTy} (l : Loc C (.ref R)) (hm : (Ty.ref R).mapFree = true)
    (hl : l.isTarget = true) (hr : l.isRoot = false)
    (copy : (sp2 : SPath C (.ref R)) → sp2.isSimple = true → Step k m (.assign l (.copy sp2 hm))) :
    (sp2 : SPath C (.ref R)) → Step k m (.assign l (.copy sp2 hm))
  | .alias y => copy (.alias y) rfl
  | .loc l' =>
    (Hole.copy l hm).readStep hl (fun _ _ => copy _ rfl)
      (fun _ _ _ _ => ⟨_, .storageFieldRead_unfold_rightSndResult⟩)
      (fun _ _ _ _ => ⟨_, .storageIndexRead_unfold_rightSndResult⟩) l'

/-- A storage write, `alice.age = 10;`, `people[i] = bob;`: the receiver
unfolded first (`people[i].age = 10;`), then the index (`ages[i + 1] = 3;`),
then the source (`total = a + b;`). -/
def assignStep {T : Ty} : (l : Loc C T) → (r : Src C T) → Step k m (.assign l r)
  -- a state variable
  | .root r h, .val e =>
    (VHole.store (.root r h)).step rfl (fun _ => ⟨_, .storageRootWriteStore⟩) e
      (fun _ _ => ⟨_, .storageRootWriteValueRhsCapture⟩)
  | .root _ _, .copy (.alias _) _ => ⟨_, .storageRootWriteCopySource⟩
  | .root r h, .copy (.loc l) hm =>
    (Hole.copy (.root r h) hm).readStep rfl (fun _ _ => ⟨_, .storageRootWriteCopySource⟩)
      (fun _ _ _ _ => ⟨_, .storageFieldReadStoreRoot⟩)
      (fun it sp ie _ => match it, sp, ie with
        | .map, _, _ => ⟨_, .storageIndexReadMappingStoreRoot⟩
        | .arr _, _, _ => ⟨_, .storageIndexReadArrayStoreRoot⟩) l
  -- a member
  | .field b f hf, .val e =>
    if hb : b.isSimple then
      (VHole.store (.field b f hf)).step rfl (fun _ => ⟨_, .storageFieldWriteSave⟩) e
        (fun _ _ => ⟨_, .fieldWriteValueRhsCapture⟩)
    else (VHole.store (.field b f hf)).lower rfl e (fun _ => ⟨_, .storageFieldWrite_unfold_leftFst⟩)
  | .field b f hf, .copy sp2 hm =>
    if hb : b.isSimple then
      copyStep (.field b f hf) hm (by simp [Loc.isTarget, hb]) rfl
        (fun _ _ => ⟨_, .storageFieldWriteCopySource⟩) sp2
    else ⟨_, .storageFieldWriteStorageRef_unfold_leftFst⟩
  -- an entry
  | .index it b i, .val e =>
    if hb : b.isSimple then
      match i with
      | .simple ie =>
        (VHole.store (.index it b (.simple ie))).step rfl
          (fun se => match it, b, ie, se, hb with
            | .map, _, _, _, _ => ⟨_, .storageIndexWriteMappingSave⟩
            | .arr _, _, _, _, _ => ⟨_, .storageIndexWriteArraySave⟩)
          e (fun _ _ => ⟨_, .indexWriteValueRhsCapture⟩)
      | .read _ | .binop .. | .unop .. | .ternary .. | .readMem _ | .len .. | .mlen .. =>
        (VHole.store (.index it b _)).lower rfl e
          (fun _ => ⟨_, .storageIndexWriteCaptureAllNonSimpleIndex⟩)
    else
      (VHole.store (.index it b i)).lower rfl e
        (fun _ => ⟨_, .storageIndexWriteCaptureAllComplexRecv⟩)
  | .index it b i, .copy sp2 hm =>
    if hb : b.isSimple then
      match i with
      | .simple ie =>
        copyStep (.index it b (.simple ie)) hm (by simp [Loc.isTarget, hb, Val.isSimple]) rfl
          (fun _ _ => match it, b, ie, hb with
            | .map, _, _, _ => ⟨_, .storageIndexWriteMappingCopySource⟩
            | .arr _, _, _, _ => ⟨_, .storageIndexWriteArrayCopySource⟩) sp2
      | .read _ | .binop .. | .unop .. | .ternary .. | .readMem _ | .len .. | .mlen .. =>
        ⟨_, .storageIndexWriteStorageRefCaptureAllNonSimpleIndex⟩
    else ⟨_, .storageIndexWriteStorageRefCaptureAllComplexRecv⟩

/-- A storage location written from memory, `people[i] = m;`: the receiver
first, then the index; the memory path is copied as it is. -/
def assignFromMemStep {R : RefTy} :
    (l : Loc C (.ref R)) → (p : MPath C (.ref R)) → Step k m (.assignFromMem l p)
  | .root _ _, _ => ⟨_, .memoryToStorageStoreRoot⟩
  | .field b _ _, _ =>
    if hb : b.isSimple then ⟨_, .memoryToStorageFieldCopyRoot⟩
    else ⟨_, .memoryToStorageField_unfold_leftFst⟩
  | .index it b i, _ =>
    if hb : b.isSimple then
      match it, b, i, hb with
      | .map, _, .simple _, _ => ⟨_, .memoryToStorageIndexMappingCopyRoot⟩
      | .arr _, _, .simple _, _ => ⟨_, .memoryToStorageIndexArrayCopyRoot⟩
      | _, _, .read _, _ | _, _, .binop .., _ | _, _, .unop .., _ | _, _, .ternary .., _
      | _, _, .readMem _, _ | _, _, .len .., _ | _, _, .mlen .., _ =>
        ⟨_, .memoryToStorageIndexCaptureAllNonSimpleIndex⟩
    else ⟨_, .memoryToStorageIndexCaptureAllComplexRecv⟩

/-- `delete people[i].account;`: the receiver first, then the index. -/
def deleteStep {T : Ty} : (l : Loc C T) → Step k m (.delete l)
  | .root _ _ => ⟨_, .storageRootDelete⟩
  | .field b _ _ =>
    if hb : b.isSimple then ⟨_, .storageFieldDelete⟩ else ⟨_, .storageFieldDelete_unfold_leftFst⟩
  | .index it b i =>
    if hb : b.isSimple then
      match it, b, i, hb with
      | .map, _, .simple _, _ => ⟨_, .storageIndexDelete⟩
      | .arr _, _, .simple _, _ => ⟨_, .storageIndexArrayDelete⟩
      | _, _, .read _, _ | _, _, .binop .., _ | _, _, .unop .., _ | _, _, .ternary .., _
      | _, _, .readMem _, _ | _, _, .len .., _ | _, _, .mlen .., _ =>
        ⟨_, .storageIndexDeleteNonSimpleIndexCapture⟩
    else ⟨_, .storageIndexDelete_unfold_leftFst⟩

/-! ## Compound assignment and `++`/`--` -/

/-- `people[i].age += x + 1;`: the source first (the receiver rules take a
simple one), then the receiver. -/
def opStep {p : PrimTy} (op : BinOp) (hop : op.hasCompoundAssign = true)
    (hp : p.isNumeric = true) (l : OpLoc C p) : (r : Val C p) → Step k m (.opAssign op hop hp l r)
  | .simple _ =>
    match l with
    | .local _ => ⟨_, .localOpAssign⟩
    | .root _ _ => ⟨_, .storageRootOpAssign⟩
    | .field b _ _ =>
      if hb : b.isSimple then ⟨_, .storageFieldOpAssign⟩
      else ⟨_, .storageFieldOpAssignUnfoldLeftFst⟩
    | .index it b ie =>
      if hb : b.isSimple then
        match it, b, ie, hb with
        | .map, _, _, _ => ⟨_, .storageIndexMappingOpAssign⟩
        | .arr _, _, _, _ => ⟨_, .storageIndexArrayOpAssign⟩
      else ⟨_, .storageIndexOpAssignUnfoldLeftFst⟩
    | .mfield (.var _) _ _ => ⟨_, .memoryFieldOpAssign⟩
    | .mfield (.loc _) _ _ => ⟨_, .memoryFieldOpAssignUnfoldLeftFst⟩
    | .mindex _ (.var _) _ => ⟨_, .memoryIndexArrayOpAssign⟩
    | .mindex _ (.loc _) _ => ⟨_, .memoryIndexOpAssignUnfoldLeftFst⟩
  | .read _ | .binop .. | .unop .. | .ternary .. | .readMem _ | .len .. | .mlen .. =>
    ⟨_, .compoundAssignValueRhsCapture⟩

/-- `people[i].age++;`: the receiver first. -/
def incStep {p : PrimTy} (op : IncDec) (hp : p.isNumeric = true) :
    (l : OpLoc C p) → Step k m (.incDec op hp l)
  | .local _ => ⟨_, .localIncrement⟩
  | .root _ _ => ⟨_, .storageRootIncrement⟩
  | .field b _ _ =>
    if hb : b.isSimple then ⟨_, .storageFieldIncrement⟩
    else ⟨_, .storageFieldIncrementUnfoldLeftFst⟩
  | .index _ b _ =>
    if hb : b.isSimple then ⟨_, .storageIndexIncrement⟩
    else ⟨_, .storageIndexIncrementUnfoldLeftFst⟩
  | .mfield (.var _) _ _ => ⟨_, .memoryFieldIncrement⟩
  | .mfield (.loc _) _ _ => ⟨_, .memoryFieldIncrementUnfoldLeftFst⟩
  | .mindex _ (.var _) _ => ⟨_, .memoryIndexArrayIncrement⟩
  | .mindex _ (.loc _) _ => ⟨_, .memoryIndexIncrementUnfoldLeftFst⟩

/-- `v = alice.age++;`, whose receiver is simple (`hs`), so one update. -/
def assignIncStep {p : PrimTy} (v : Var) (op : IncDec) (hp : p.isNumeric = true) :
    (l : OpLoc C p) → (hs : l.recvSimple = true) → Step k m (.assignIncDec v op hp l hs)
  | .local _, _ => ⟨_, .localAssignIncrement⟩
  | .root _ _, _ => ⟨_, .storageRootIncrementAssignment⟩
  | .field _ _ _, hs => ⟨_, .storageFieldIncrementAssignment⟩
  | .index _ _ _, hs => ⟨_, .storageIndexIncrementAssignment⟩
  | .mfield (.var _) _ _, _ => ⟨_, .memoryFieldIncrementAssignment⟩
  | .mindex _ (.var _) _, _ => ⟨_, .memoryIndexArrayIncrementAssignment⟩
  | .mfield (.loc _) _ _, hs | .mindex _ (.loc _) _, hs => nomatch hs

/-! ## Arrays and transfers -/

/-- `people[i].values.push(x + 1);`: the receiver first, then the argument;
a copied path (`persons.push(people[i]);`) is read as it is. -/
def pushStep {E : Ty} (b : SPath C (.array E)) (v : Option (Src C E))
    (hd : (v.isSome || E.defaultOkS) = true) : Step k m (.push b v hd) :=
  if hb : b.isSimple then
    match E, b, v, hd, hb with
    | _, b, none, _, _ =>
      if hE : b.elemPrim then ⟨_, .storagePushLengthSave⟩
      else ⟨_, .storagePushLengthSaveReferenceElement⟩
    | _, _, some (.val (.simple _)), _, _ => ⟨_, .storagePushValueSave⟩
    | _, _, some (.val (.read _)), _, _ | _, _, some (.val (.binop ..)), _, _
    | _, _, some (.val (.unop ..)), _, _ | _, _, some (.val (.ternary ..)), _, _
    | _, _, some (.val (.readMem _)), _, _ | _, _, some (.val (.len ..)), _, _
    | _, _, some (.val (.mlen ..)), _, _ => ⟨_, .storagePushValue_unfold_rightSndArgument⟩
    | _, _, some (.copy _ _), _, _ => ⟨_, .storagePushValueCopySource⟩
  else
    match v, hd with
    | none, _ => ⟨_, .storagePush_unfold_leftFstReceiver⟩
    | some _, _ => ⟨_, .storagePushValue_unfold_leftFstReceiver⟩

/-- `people[i].values.pop();`: the receiver first.  The unfold rule leaves
the type its alias pops at free, so it is given: `E`. -/
def popStep {E : Ty} (b : SPath C (.array E)) : Step k m (.pop b) :=
  if hb : b.isSimple then
    if hE : b.elemMapping then ⟨_, .storagePopSaveMappingElement⟩ else ⟨_, .storagePopSave⟩
  else ⟨_, Taclet.storagePop_unfold_leftFstReceiver (E := E)⟩

/-- `people[i].wallet.transfer(x + 1);`: the receiver first, then the
amount. -/
def transferStep : (r a : Val C .uint) → Step k m (.transfer r a)
  | .simple _, .simple _ => ⟨_, .transferNoCallback⟩
  | .simple _, .read _ | .simple _, .binop .. | .simple _, .unop .. | .simple _, .ternary ..
  | .simple _, .readMem _ | .simple _, .len .. | .simple _, .mlen .. =>
    ⟨_, .transfer_unfold_rightSndArgument⟩
  | .read _, _ | .binop .., _ | .unop .., _ | .ternary .., _ | .readMem _, _ | .len .., _
  | .mlen .., _ => ⟨_, .transfer_unfold_leftFstReceiver⟩

/-! ## Memory -/

/-- A memory local bound: `m = n;`, `m = n.items[i];` (unfolded until it is
bindable), `m = people[i];` (a deep copy, of a simple path). -/
def rebindMemStep {R : RefTy} (x : Var) : (r : MRhs C R) → Step k m (.rebindMem x r)
  | .alias (.var _) => ⟨_, .memoryRootAlias⟩
  | .alias (.loc l) =>
    (MHole.rebind x).readStep rfl (fun _ _ _ => ⟨_, .memoryFieldReadAliasRoot⟩)
      (fun _ _ _ => ⟨_, .memoryIndexReadAliasRoot⟩) l
  | .copy sp _ =>
    if hs : sp.isSimple then ⟨_, .memoryStorageCopy⟩ else ⟨_, .memoryStorageCopyUnfold⟩
  | .newArr _ _ => ⟨_, .memoryArrayFreshAlloc⟩

/-- `delete mv.f;`: the member's type picks the rule. -/
def deleteMemFieldStep {s : Name} : (T : Ty) → (mv : Var) → (f : Name) →
    (hf : C.fieldType s f = some T) → (hd : T.defaultOkS = true) →
    Step k m (.deleteMem (.loc (.field (.var mv) f hf)) hd)
  | .prim _, _, _, _, _ => ⟨_, .memoryFieldDeletePrimitive⟩
  | .ref _, _, _, _, _ => ⟨_, .memoryFieldDeleteReference⟩

/-- `delete mv[ie];`: the element type picks the rule. -/
def deleteMemIndexStep {R : RefTy} : (T : Ty) → (a : ArrTy R T) → (mv : Var) →
    (ie : Simple C .uint) → (hd : T.defaultOkS = true) →
    Step k m (.deleteMem (.loc (.index a (.var mv) (.simple ie))) hd)
  | .prim _, _, _, _, _ => ⟨_, .memoryIndexDeletePrimitive⟩
  | .ref _, _, _, _, _ => ⟨_, .memoryIndexDeleteReference⟩

/-- `delete m;`, `delete m.items[i];`: a memory local is bound to a fresh
default object; a member of one, or an element at a simple index, is reset by
the rule its type picks (a primitive to its default, a reference to a fresh
object); any other receiver is bound first (`delete m.inner.age;`), a complex
index captured (`delete m.items[i + 1];`). -/
def deleteMemStep {T : Ty} : (p : MPath C T) → (hd : T.defaultOkS = true) →
    Step k m (.deleteMem p hd)
  | .var _, _ => ⟨_, .memoryRootDeleteFreshRebind⟩
  | .loc (.field (.var mv) f hf), hd => deleteMemFieldStep _ mv f hf hd
  | .loc (.field (.loc _) _ _), _ => ⟨_, .memoryFieldDelete_unfold_leftFst⟩
  | .loc (.index a (.var mv) (.simple ie)), hd => deleteMemIndexStep _ a mv ie hd
  | .loc (.index _ (.var _) (.read _)), _ | .loc (.index _ (.var _) (.binop ..)), _
  | .loc (.index _ (.var _) (.unop ..)), _ | .loc (.index _ (.var _) (.ternary ..)), _
  | .loc (.index _ (.var _) (.readMem _)), _ | .loc (.index _ (.var _) (.len ..)), _
  | .loc (.index _ (.var _) (.mlen ..)), _ => ⟨_, .memoryIndexDeleteNonSimpleIndexCapture⟩
  | .loc (.index _ (.loc _) _), _ => ⟨_, .memoryIndexDelete_unfold_leftFst⟩

/-- A memory reference written to the target `l`, `m.account = src;`: a
memory local or a bindable location (`n.account`, `n[ie]`) is written by
`copy`; any other source unfolds its own receiver or index (Step 1). -/
def memRefStep {R : RefTy} (l : MLoc C (.ref R)) (hl : l.isTarget = true)
    (copy : (src : MPath C (.ref R)) → src.isBindable = true → Step k m (.assignMem l (.ref src))) :
    (src : MPath C (.ref R)) → Step k m (.assignMem l (.ref src))
  | .var y => copy (.var y) rfl
  | .loc sl =>
    (MHole.write l).readStep hl (fun _ _ _ => copy _ rfl) (fun _ _ _ => copy _ rfl) sl

/-- `mv[ie] = src;`: a value stored (lowered first if it is a conditional,
captured if it is not simple), a reference written as `memRefStep` does. -/
def memIndexWriteStep {R : RefTy} : (T : Ty) → (r : MSrc C T) → (a : ArrTy R T) → (mv : Var) →
    (ie : Simple C .uint) → Step k m (.assignMem (.index a (.var mv) (.simple ie)) r)
  | _, .val (p := p) e, a, mv, ie =>
    (VHole.mem (.index a (.var mv) (.simple ie))).step rfl (fun _ => ⟨_, .memoryIndexWriteStore⟩) e
      (fun _ _ => ⟨_, Taclet.memoryIndexWriteUnfoldSource (p := p)⟩)
  | _, .ref src, a, mv, ie =>
    memRefStep (.index a (.var mv) (.simple ie)) rfl (fun _ _ => ⟨_, .memoryIndexWriteCopy⟩) src

/-- A memory location written, `m.age = 3;`, `m.items[i] = n;`: the
receiver first (`m.inner.age = 3;`), then the index, then the source.
`memoryIndexWriteUnfoldSource` leaves the element type of its premise's
write free, so it is given: `p`, the source's. -/
def assignMemStep {T : Ty} : (l : MLoc C T) → (r : MSrc C T) → Step k m (.assignMem l r)
  | .field (.var mv) f hf, .val e =>
    (VHole.mem (.field (.var mv) f hf)).step rfl (fun _ => ⟨_, .memoryFieldWriteStore⟩) e
      (fun _ _ => ⟨_, .memoryFieldWriteUnfoldSource⟩)
  | .field (.var mv) f hf, .ref src =>
    memRefStep (.field (.var mv) f hf) rfl (fun _ _ => ⟨_, .memoryFieldWriteCopy⟩) src
  | .field (.loc _) _ _, _ => ⟨_, .memoryFieldWrite_unfold_leftFst⟩
  | .index a (.var mv) (.simple ie), r => memIndexWriteStep _ r a mv ie
  | .index _ (.var _) (.read _), .val _ | .index _ (.var _) (.binop ..), .val _
  | .index _ (.var _) (.unop ..), .val _ | .index _ (.var _) (.ternary ..), .val _
  | .index _ (.var _) (.readMem _), .val _ | .index _ (.var _) (.len ..), .val _
  | .index _ (.var _) (.mlen ..), .val _ => ⟨_, .memoryIndexWriteCaptureAllNonSimpleIndex⟩
  | .index _ (.var _) (.read _), .ref _ | .index _ (.var _) (.binop ..), .ref _
  | .index _ (.var _) (.unop ..), .ref _ | .index _ (.var _) (.ternary ..), .ref _
  | .index _ (.var _) (.readMem _), .ref _ | .index _ (.var _) (.len ..), .ref _
  | .index _ (.var _) (.mlen ..), .ref _ => ⟨_, .memoryIndexWriteMemRefCaptureAllNonSimpleIndex⟩
  | .index _ (.loc _) _, .val _ => ⟨_, .memoryIndexWriteCaptureAllComplexRecv⟩
  | .index _ (.loc _) _, .ref _ => ⟨_, .memoryIndexWriteMemRefCaptureAllComplexRecv⟩

/-- A call: its first argument that is not simple is captured, and with
every argument simple its body is inlined. -/
def callStep (f : Name) (args : List (Arg C)) (hsep : Arg.separatedFrom [] args = true)
    (ret : CallRet) (body : List (Stmt C)) : Step k m (.call f args hsep ret body) :=
  match h : Arg.firstNonSimple args with
  | none => ⟨_, .functionBodyExpand h⟩
  | some _ => ⟨_, .functionCallArgCapture h⟩

/-! ## The rule for a statement -/

/-- **The rule for a statement** under the modality `m`, its fresh variables
declared at index `k`.  Total: every statement has one. -/
def Stmt.step (k : Nat) (m : Modality) : (s : Stmt C) → Step k m s
  | .assign l r => assignStep l r
  | .rebind x r => rebindStep x r
  | .assignLocal x v => localStep x v
  | .declLocal _ _ none => ⟨_, .valueDeclSkip⟩
  | .declLocal _ _ (some _) => ⟨_, .localValueDeclInitDrop⟩
  | .declStorage _ _ none => ⟨_, .storageLocalDeclSkip⟩
  | .declStorage _ _ (some _) => ⟨_, .storageLocalDeclInitDrop⟩
  | .opAssign op hop hp l r => opStep op hop hp l r
  | .incDec op hp l => incStep op hp l
  | .assignIncDec x op hp l hs => assignIncStep x op hp l hs
  | .push b v hd => pushStep b v hd
  | .pop b => popStep b
  | .transfer r a => transferStep r a
  | .declMem _ _ none _ => ⟨_, .memoryReferenceDeclFreshAlloc⟩
  | .declMem _ _ (some _) _ => ⟨_, .memoryLocalDeclInitDrop⟩
  | .rebindMem x r => rebindMemStep x r
  | .assignFromMem l p => assignFromMemStep l p
  | .assignMem l r => assignMemStep l r
  | .delete l => deleteStep l
  | .deleteMem p hd => deleteMemStep p hd
  | .assignNew _ _ _ => ⟨_, .newArrayCapture⟩
  | .ite (.simple _) _ _ => ⟨_, .ifElseSplit⟩
  | .ite (.read _) _ _ | .ite (.binop ..) _ _ | .ite (.unop ..) _ _ | .ite (.ternary ..) _ _
  | .ite (.readMem _) _ _ | .ite (.len ..) _ _ | .ite (.mlen ..) _ _ => ⟨_, .ifElseUnfold⟩
  | .require (.simple _) => ⟨_, .requireSimple⟩
  | .require (.read _) | .require (.binop ..) | .require (.unop ..) | .require (.ternary ..)
  | .require (.readMem _) | .require (.len ..) | .require (.mlen ..) =>
    ⟨_, .requireConditionCapture⟩
  | .assert (.simple _) => ⟨_, .assertSimple⟩
  | .assert (.read _) | .assert (.binop ..) | .assert (.unop ..) | .assert (.ternary ..)
  | .assert (.readMem _) | .assert (.len ..) | .assert (.mlen ..) =>
    ⟨_, .assertConditionCapture⟩
  | .revert =>
    match m with
    | .box => ⟨_, .revertBox⟩
    | .diamond => ⟨_, .revertDiamond⟩
  | .call f args hsep ret body => callStep f args hsep ret body

/-- **Completeness**: under either modality, every statement has a rule.  No
hypothesis and no residue: `uint x = people[i].age;`, `alice = bob;`,
`delete folks[i + 1];` each have one, and so does anything else `sol{ … }`
writes. -/
theorem Stmt.complete (k : Nat) (m : Modality) (s : Stmt C) : ∃ p, Taclet C k m s p :=
  ⟨(s.step k m).premise, (s.step k m).taclet⟩

end Solidity
