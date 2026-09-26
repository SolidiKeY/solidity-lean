import Solidity.Calculus.Rules

/-!
# Every statement has a rule

`Stmt.step k m s` is the rule for the statement `s` under the modality `m`:
its premise, and the derivation `Taclet C k m s p` (`Rules.lean`), its fresh
variables declared at index `k`.  It is a **total function** over the typed
syntax, so Lean's exhaustiveness check on its patterns is the coverage
proof; `Stmt.complete` states it.  A combination the types rule out (a value
written to an alias, a `delete` of a local, a memory mapping) needs no arm.

A taclet says what is sound, not what fires: an unfold rule holds of a
simple part too.  Which rule fires is decided here, by the constructors of
the statement and by whether its parts are simple — a simple `SPath` is an
alias or a state variable, a simple `MPath` a memory local, a simple `Val` a
literal or a local — in this order:

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
def ternaryStep {p : PrimTy} (lhs : VHole C p) :
    (c : Val C .bool) → (a b : Val C p) → Step k m (lhs.fill (.ternary c a b))
  | .simple _, _, _ => ⟨_, .ternaryToIf⟩
  | _, _, _ => ⟨_, .ternaryCaptureCond⟩

/-- A value written to `lhs` by `other`, unless it is a conditional, which is
lowered first: `people[i].age = b ? 1 : 2;` branches before it captures
anything. -/
def VHole.lower {p : PrimTy} (lhs : VHole C p) :
    (e : Val C p) → Step k m (lhs.fill e) → Step k m (lhs.fill e)
  | .ternary c a b, _ => ternaryStep lhs c a b
  | _, other => other

/-- A value written to `lhs` whose target is all simple: a simple value by
`simple` (Step 3, `alice.age = 10;`), a conditional lowered, anything else
captured by `capture` (`alice.age = bob.age + 1;`). -/
def VHole.step {p : PrimTy} (lhs : VHole C p)
    (simple : (se : Simple C p) → Step k m (lhs.fill (.simple se))) :
    (e : Val C p) → Step k m (lhs.fill e) → Step k m (lhs.fill e)
  | .simple se, _ => simple se
  | e, capture => lhs.lower e capture

/-! ## Step 1: reads -/

/-- A storage location read into the hole `lhs` (`v = □`, `lsv = □`,
`loc = □`): a state variable, a member of a simple path or an entry of one at
a simple index take the hole's own rule (`root`, `field`, `index`); any other
unfolds its receiver (`x = people[i].age;`) or its index (`x = ages[i + 1];`)
first. -/
def Hole.readStep {T : Ty} (lhs : Hole C T)
    (root : (r : Name) → (h : C.rootType r = some T) → Step k m (lhs.fill (.loc (.root r h))))
    (field : {s : Name} → (sp : SPath C (.struct s)) → (f : Name) →
      (hf : C.fieldType s f = some T) → Step k m (lhs.fill (.loc (.field sp f hf))))
    (index : {R : RefTy} → {kp : PrimTy} → (it : IndexTy R kp T) → (sp : SPath C (.ref R)) →
      (ie : Simple C kp) → Step k m (lhs.fill (.loc (.index it sp (.simple ie))))) :
    (l : Loc C T) → Step k m (lhs.fill (.loc l))
  | .root r h => root r h
  | .field b f hf => if b.isSimple then field b f hf else ⟨_, .storageFieldRead_unfold_rightFst⟩
  | .index it b i =>
    if b.isSimple then
      match i with
      | .simple ie => index it b ie
      | _ => ⟨_, .storageIndexRead_unfold_rightSndIndex⟩
    else ⟨_, .storageIndexRead_unfold_rightFst⟩

/-- A memory location read into the hole `lhs` (`v = □`, `mv = □`,
`mloc = □`): a member of a memory local, or an element of one at a simple
index, takes the hole's own rule; any other unfolds its receiver
(`x = m.items[i];`) or its index (`x = m[i + 1];`) first. -/
def MHole.readStep {T : Ty} (lhs : MHole C T)
    (field : {s : Name} → (mv : Var) → (f : Name) → (hf : C.fieldType s f = some T) →
      Step k m (lhs.fill (.field (.var mv) f hf)))
    (index : (mv : Var) → (ie : Simple C .uint) →
      Step k m (lhs.fill (.index (.var mv) (.simple ie)))) :
    (l : MLoc C T) → Step k m (lhs.fill l)
  | .field (.var mv) f hf => field mv f hf
  | .field _ _ _ => ⟨_, .memoryFieldRead_unfold_rightFst⟩
  | .index (.var mv) (.simple ie) => index mv ie
  | .index (.var _) _ => ⟨_, .memoryIndexRead_unfold_rightSndIndex⟩
  | .index _ _ => ⟨_, .memoryIndexRead_unfold_rightFst⟩

/-! ## Locals and aliases -/

/-- `v = se ⊕ nse;`: `&&` and `||` evaluate `nse` only when `se` does not
decide, so they branch on it (`b = ok && people[i].adult;`); any other
operator captures `nse` (`v = 1 + people[i].age;`). -/
def binopRightStep {p q : PrimTy} (x : Var) (op : BinOp) (hop : op.accepts p = true)
    (hq : op.ret p = q) (se : Simple C p) (nse : Val C p) :
    Step k m (.assignLocal x (.binop op hop hq (.simple se) nse)) :=
  match p, q, op, hop, hq, se, nse with
  | .bool, .bool, .and, _, _, _, _ => ⟨_, .logicalAndShortCircuitRhs⟩
  | .bool, .bool, .or, _, _, _, _ => ⟨_, .logicalOrShortCircuitRhs⟩
  | .bool, .uint, .and, _, hq, _, _ | .bool, .int, .and, _, hq, _, _
  | .bool, .uint, .or, _, hq, _, _ | .bool, .int, .or, _, hq, _, _ => absurd hq (by decide)
  | .uint, _, .and, hop, _, _, _ | .int, _, .and, hop, _, _, _
  | .uint, _, .or, hop, _, _, _ | .int, _, .or, hop, _, _, _ => absurd hop (by decide)
  | _, _, .add, _, _, _, _ | _, _, .sub, _, _, _, _ | _, _, .mul, _, _, _, _
  | _, _, .pow, _, _, _, _ | _, _, .div, _, _, _, _ | _, _, .mod, _, _, _, _
  | _, _, .lt, _, _, _, _ | _, _, .gt, _, _, _, _ | _, _, .le, _, _, _, _
  | _, _, .ge, _, _, _, _ | _, _, .eqB, _, _, _, _ | _, _, .neB, _, _, _, _ =>
    ⟨_, .binopUnfoldRight rfl⟩

/-- A local assigned: `x = 10;`, `x = people[i].age;` (a read, unfolded
until it is one), `x = a + b;`, `x = m.age;`. -/
def localStep {p : PrimTy} (x : Var) : (v : Val C p) → Step k m (.assignLocal x v)
  | .simple _ => ⟨_, .localValueAssign⟩
  | .read l =>
    (Hole.local x).readStep (fun _ _ => ⟨_, .storageRootReadSelect⟩)
      (fun _ _ _ => ⟨_, .storageFieldReadFind⟩)
      (fun it sp ie => match it, sp, ie with
        | .map, _, _ => ⟨_, .storageIndexReadMappingFind⟩
        | .arr, _, _ => ⟨_, .storageIndexReadArrayFind⟩) l
  | .binop _ _ _ (.simple _) (.simple _) => ⟨_, .binopAssignment⟩
  | .binop op hop hq (.simple se) nse => binopRightStep x op hop hq se nse
  | .binop _ _ _ _ _ => ⟨_, .binopUnfoldLeft⟩
  | .unop _ _ _ (.simple _) => ⟨_, .unopAssignment⟩
  | .unop _ _ _ _ => ⟨_, .unopCapture⟩
  | .ternary c a b => ternaryStep (.local x) c a b
  | .readMem l =>
    (MHole.local x).readStep (fun _ _ _ => ⟨_, .memoryFieldReadHeap⟩)
      (fun _ _ => ⟨_, .memoryIndexReadHeap⟩) l

/-- An alias bound: `lsv = alice;`, `lsv = people[i];` (a path, unfolded
until it is bindable), `lsv = people.push();` (its receiver first). -/
def rebindStep {R : RefTy} (x : Var) : (r : ARhs C R) → Step k m (.rebind x r)
  | .path (.alias _) => ⟨_, .storageLocalRootRebind⟩
  | .path (.loc l) =>
    (Hole.rebind x).readStep (fun _ _ => ⟨_, .storageLocalRootRebind⟩)
      (fun _ _ _ => ⟨_, .storageFieldReadBindLocalRoot⟩)
      (fun it sp ie => match it, sp, ie with
        | .map, _, _ => ⟨_, .storageIndexReadMappingBindLocalRoot⟩
        | .arr, _, _ => ⟨_, .storageIndexReadArrayBindLocalRoot⟩) l
  | .push b _ =>
    if b.isSimple then ⟨_, .storageLocalRootPushBind⟩
    else ⟨_, .storageLocalRootPush_unfold_leftFstReceiver⟩

/-! ## Storage writes -/

/-- A copy into a member or an entry, `alice.account = src;`: a simple source
is copied by `copy` (Step 3); a member or an entry of a simple path is bound
to an alias first (`Account storage sp = bob.account;`); any other source
unfolds its own receiver or index (Step 1). -/
def copyStep {R : RefTy} (l : Loc C (.ref R)) (hm : (Ty.ref R).mapFree = true)
    (copy : (sp2 : SPath C (.ref R)) → Step k m (.assign l (.copy sp2 hm))) :
    (sp2 : SPath C (.ref R)) → Step k m (.assign l (.copy sp2 hm))
  | .alias y => copy (.alias y)
  | .loc l' =>
    (Hole.copy l hm).readStep (fun _ _ => copy _)
      (fun _ _ _ => ⟨_, .storageFieldRead_unfold_rightSndResult⟩)
      (fun _ _ _ => ⟨_, .storageIndexRead_unfold_rightSndResult⟩) l'

/-- A storage write, `alice.age = 10;`, `people[i] = bob;`: the receiver
unfolded first (`people[i].age = 10;`), then the index (`ages[i + 1] = 3;`),
then the source (`total = a + b;`). -/
def assignStep {T : Ty} : (l : Loc C T) → (r : Src C T) → Step k m (.assign l r)
  -- a state variable
  | .root r h, .val e =>
    (VHole.store (.root r h)).step (fun _ => ⟨_, .storageRootWriteStore⟩) e
      ⟨_, .storageRootWriteValueRhsCapture⟩
  | .root _ _, .copy (.alias _) _ => ⟨_, .storageRootWriteCopySource⟩
  | .root r h, .copy (.loc l) hm =>
    (Hole.copy (.root r h) hm).readStep (fun _ _ => ⟨_, .storageRootWriteCopySource⟩)
      (fun _ _ _ => ⟨_, .storageFieldReadStoreRoot⟩)
      (fun it sp ie => match it, sp, ie with
        | .map, _, _ => ⟨_, .storageIndexReadMappingStoreRoot⟩
        | .arr, _, _ => ⟨_, .storageIndexReadArrayStoreRoot⟩) l
  -- a member
  | .field b f hf, .val e =>
    if b.isSimple then
      (VHole.store (.field b f hf)).step (fun _ => ⟨_, .storageFieldWriteSave⟩) e
        ⟨_, .fieldWriteValueRhsCapture⟩
    else (VHole.store (.field b f hf)).lower e ⟨_, .storageFieldWrite_unfold_leftFst⟩
  | .field b f hf, .copy sp2 hm =>
    if b.isSimple then copyStep (.field b f hf) hm (fun _ => ⟨_, .storageFieldWriteCopySource⟩) sp2
    else ⟨_, .storageFieldWriteStorageRef_unfold_leftFst⟩
  -- an entry
  | .index it b i, .val e =>
    if b.isSimple then
      match i with
      | .simple ie =>
        (VHole.store (.index it b (.simple ie))).step
          (fun se => match it, b, ie, se with
            | .map, _, _, _ => ⟨_, .storageIndexWriteMappingSave⟩
            | .arr, _, _, _ => ⟨_, .storageIndexWriteArraySave⟩)
          e ⟨_, .indexWriteValueRhsCapture⟩
      | nse => (VHole.store (.index it b nse)).lower e ⟨_, .storageIndexWriteNonSimpleIndexCapture⟩
    else (VHole.store (.index it b i)).lower e ⟨_, .storageIndexWrite_unfold_leftFst⟩
  | .index it b i, .copy sp2 hm =>
    if b.isSimple then
      match i with
      | .simple ie =>
        copyStep (.index it b (.simple ie)) hm
          (fun _ => match it, b, ie with
            | .map, _, _ => ⟨_, .storageIndexWriteMappingCopySource⟩
            | .arr, _, _ => ⟨_, .storageIndexWriteArrayCopySource⟩) sp2
      | _ => ⟨_, .storageIndexWriteStorageRefNonSimpleIndexCapture⟩
    else ⟨_, .storageIndexWriteStorageRef_unfold_leftFst⟩

/-- A storage location written from memory, `people[i] = m;`: the receiver
first, then the index; the memory path is copied as it is. -/
def assignFromMemStep {R : RefTy} :
    (l : Loc C (.ref R)) → (p : MPath C (.ref R)) → Step k m (.assignFromMem l p)
  | .root _ _, _ => ⟨_, .memoryToStorageStoreRoot⟩
  | .field b _ _, _ =>
    if b.isSimple then ⟨_, .memoryToStorageFieldCopyRoot⟩
    else ⟨_, .memoryToStorageField_unfold_leftFst⟩
  | .index it b i, _ =>
    if b.isSimple then
      match it, b, i with
      | .map, _, .simple _ => ⟨_, .memoryToStorageIndexMappingCopyRoot⟩
      | .arr, _, .simple _ => ⟨_, .memoryToStorageIndexArrayCopyRoot⟩
      | _, _, _ => ⟨_, .memoryToStorageIndexNonSimpleIndexCapture⟩
    else ⟨_, .memoryToStorageIndex_unfold_leftFst⟩

/-- `delete people[i].account;`: the receiver first, then the index. -/
def deleteStep {T : Ty} : (l : Loc C T) → Step k m (.delete l)
  | .root _ _ => ⟨_, .storageRootDelete⟩
  | .field b _ _ =>
    if b.isSimple then ⟨_, .storageFieldDelete⟩ else ⟨_, .storageFieldDelete_unfold_leftFst⟩
  | .index _ b i =>
    if b.isSimple then
      match i with
      | .simple _ => ⟨_, .storageIndexDelete⟩
      | _ => ⟨_, .storageIndexDeleteNonSimpleIndexCapture⟩
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
      if b.isSimple then ⟨_, .storageFieldOpAssign⟩ else ⟨_, .storageFieldOpAssignUnfoldLeftFst⟩
    | .index it b ie =>
      if b.isSimple then
        match it, b, ie with
        | .map, _, _ => ⟨_, .storageIndexMappingOpAssign⟩
        | .arr, _, _ => ⟨_, .storageIndexArrayOpAssign⟩
      else ⟨_, .storageIndexOpAssignUnfoldLeftFst⟩
    | .mfield (.var _) _ _ => ⟨_, .memoryFieldOpAssign⟩
    | .mfield (.loc _) _ _ => ⟨_, .memoryFieldOpAssignUnfoldLeftFst⟩
    | .mindex (.var _) _ => ⟨_, .memoryIndexArrayOpAssign⟩
    | .mindex (.loc _) _ => ⟨_, .memoryIndexOpAssignUnfoldLeftFst⟩
  | _ => ⟨_, .compoundAssignValueRhsCapture⟩

/-- `people[i].age++;`: the receiver first. -/
def incStep {p : PrimTy} (op : IncDec) (hp : p.isNumeric = true) :
    (l : OpLoc C p) → Step k m (.incDec op hp l)
  | .local _ => ⟨_, .localIncrement⟩
  | .root _ _ => ⟨_, .storageRootIncrement⟩
  | .field b _ _ =>
    if b.isSimple then ⟨_, .storageFieldIncrement⟩ else ⟨_, .storageFieldIncrementUnfoldLeftFst⟩
  | .index _ b _ =>
    if b.isSimple then ⟨_, .storageIndexIncrement⟩ else ⟨_, .storageIndexIncrementUnfoldLeftFst⟩
  | .mfield (.var _) _ _ => ⟨_, .memoryFieldIncrement⟩
  | .mfield (.loc _) _ _ => ⟨_, .memoryFieldIncrementUnfoldLeftFst⟩
  | .mindex (.var _) _ => ⟨_, .memoryIndexArrayIncrement⟩
  | .mindex (.loc _) _ => ⟨_, .memoryIndexIncrementUnfoldLeftFst⟩

/-- `v = alice.age++;`, whose receiver is simple (`hs`), so one update. -/
def assignIncStep {p : PrimTy} (v : Var) (op : IncDec) (hp : p.isNumeric = true) :
    (l : OpLoc C p) → (hs : l.recvSimple = true) → Step k m (.assignIncDec v op hp l hs)
  | .local _, _ => ⟨_, .localAssignIncrement⟩
  | .root _ _, _ => ⟨_, .storageRootIncrementAssignment⟩
  | .field _ _ _, _ => ⟨_, .storageFieldIncrementAssignment⟩
  | .index _ _ _, _ => ⟨_, .storageIndexIncrementAssignment⟩
  | .mfield (.var _) _ _, _ => ⟨_, .memoryFieldIncrementAssignment⟩
  | .mindex (.var _) _, _ => ⟨_, .memoryIndexArrayIncrementAssignment⟩
  | .mfield (.loc _) _ _, hs | .mindex (.loc _) _, hs => nomatch hs

/-! ## Arrays and transfers -/

/-- `people[i].values.push(x + 1);`: the receiver first, then the argument;
a copied path (`persons.push(people[i]);`) is read as it is. -/
def pushStep {E : Ty} (b : SPath C (.array E)) (v : Option (Src C E))
    (hd : (v.isSome || E.defaultOkS) = true) : Step k m (.push b v hd) :=
  if b.isSimple then
    match E, b, v, hd with
    | _, _, none, _ => ⟨_, .storagePushLengthSave⟩
    | _, _, some (.val (.simple _)), _ => ⟨_, .storagePushValueSave⟩
    | _, _, some (.val _), _ => ⟨_, .storagePushValue_unfold_rightSndArgument⟩
    | _, _, some (.copy _ _), _ => ⟨_, .storagePushValueCopySource⟩
  else
    match v, hd with
    | none, _ => ⟨_, .storagePush_unfold_leftFstReceiver⟩
    | some _, _ => ⟨_, .storagePushValue_unfold_leftFstReceiver⟩

/-- `people[i].values.pop();`: the receiver first.  The unfold rule leaves
the type its alias pops at free, so it is given: `E`. -/
def popStep {E : Ty} (b : SPath C (.array E)) : Step k m (.pop b) :=
  if b.isSimple then ⟨_, .storagePopSave⟩
  else ⟨_, @Taclet.storagePop_unfold_leftFstReceiver _ _ E _ _ _⟩

/-- `people[i].wallet.transfer(x + 1);`: the receiver first, then the
amount. -/
def transferStep : (r a : Val C .uint) → Step k m (.transfer r a)
  | .simple _, .simple _ => ⟨_, .transferNoCallback⟩
  | .simple _, _ => ⟨_, .transfer_unfold_rightSndArgument⟩
  | _, _ => ⟨_, .transfer_unfold_leftFstReceiver⟩

/-! ## Memory -/

/-- A memory local bound: `m = n;`, `m = n.items[i];` (unfolded until it is
bindable), `m = people[i];` (a deep copy, of a simple path). -/
def rebindMemStep {R : RefTy} (x : Var) : (r : MRhs C R) → Step k m (.rebindMem x r)
  | .alias (.var _) => ⟨_, .memoryRootAlias⟩
  | .alias (.loc l) =>
    (MHole.rebind x).readStep (fun _ _ _ => ⟨_, .memoryFieldReadAliasRoot⟩)
      (fun _ _ => ⟨_, .memoryIndexReadAliasRoot⟩) l
  | .copy sp _ =>
    if sp.isSimple then ⟨_, .memoryStorageCopy⟩ else ⟨_, .memoryStorageCopyUnfold⟩

/-- A memory reference written to `l`, `m.account = src;`: a memory local or
a bindable location (`n.account`, `n[ie]`) is written by `copy`; any other
source unfolds its own receiver or index (Step 1). -/
def memRefStep {R : RefTy} (l : MLoc C (.ref R))
    (copy : (src : MPath C (.ref R)) → Step k m (.assignMem l (.ref src))) :
    (src : MPath C (.ref R)) → Step k m (.assignMem l (.ref src))
  | .var y => copy (.var y)
  | .loc sl => (MHole.write l).readStep (fun _ _ _ => copy _) (fun _ _ => copy _) sl

/-- A memory location written, `m.age = 3;`, `m.items[i] = n;`: the
receiver first (`m.inner.age = 3;`), then the index, then the source.
`memoryIndexWriteUnfoldSource` leaves the element type of its premise's
write free, so it is given: `p`, the source's. -/
def assignMemStep {T : Ty} : (l : MLoc C T) → (r : MSrc C T) → Step k m (.assignMem l r)
  | .field (.var mv) f hf, .val e =>
    (VHole.mem (.field (.var mv) f hf)).step (fun _ => ⟨_, .memoryFieldWriteStore⟩) e
      ⟨_, .memoryFieldWriteUnfoldSource⟩
  | .field (.var mv) f hf, .ref src =>
    memRefStep (.field (.var mv) f hf) (fun _ => ⟨_, .memoryFieldWriteCopy⟩) src
  | .field (.loc _) _ _, _ => ⟨_, .memoryFieldWrite_unfold_leftFst⟩
  | .index (.var mv) (.simple ie), .val (p := p) e =>
    (VHole.mem (.index (.var mv) (.simple ie))).step (fun _ => ⟨_, .memoryIndexWriteStore⟩) e
      ⟨_, @Taclet.memoryIndexWriteUnfoldSource _ _ p _ _ _ _ _⟩
  | .index (.var mv) (.simple ie), .ref src =>
    memRefStep (.index (.var mv) (.simple ie)) (fun _ => ⟨_, .memoryIndexWriteCopy⟩) src
  | .index (.var _) _, _ => ⟨_, .memoryIndexWriteNonSimpleIndexCapture⟩
  | .index (.loc _) _, _ => ⟨_, .memoryIndexWrite_unfold_leftFst⟩

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
  | .ite (.simple _) _ _ => ⟨_, .ifElseSplit⟩
  | .ite _ _ _ => ⟨_, .ifElseUnfold⟩
  | .require (.simple _) => ⟨_, .requireSimple⟩
  | .require _ => ⟨_, .requireConditionCapture⟩
  | .assert (.simple _) => ⟨_, .assertSimple⟩
  | .assert _ => ⟨_, .assertConditionCapture⟩
  | .revert =>
    match m with
    | .box => ⟨_, .revertBox⟩
    | .diamond => ⟨_, .revertDiamond⟩

/-- **Completeness**: under either modality, every statement has a rule.  No
hypothesis and no residue: `uint x = people[i].age;`, `alice = bob;`,
`delete folks[i + 1];` each have one, and so does anything else `sol{ … }`
writes. -/
theorem Stmt.complete (k : Nat) (m : Modality) (s : Stmt C) : ∃ p, Taclet C k m s p :=
  ⟨(s.step k m).premise, (s.step k m).taclet⟩

end Solidity
