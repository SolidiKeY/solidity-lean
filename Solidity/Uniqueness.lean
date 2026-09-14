import Solidity.Rules
import Solidity.Completeness

set_option maxHeartbeats 4000000
-- The big dispatch proof `applicable_eq_candidate` shares simp argument lists
-- across dozens of similar cases; not every argument fires in every case.
set_option linter.unusedSimpArgs false

namespace Solidity

open Rules

def StepApplicable (mode : Modality) (stmt : Stmt) (step : StepCase) : Prop :=
  (step.effect.mode stmt).applies mode = true ∧ step.effect.cond stmt

namespace UniquenessAux

/-- Pick the box or diamond variant of a rule depending on the modality. -/
def pick (mode : Modality) (box diamond : RuleName) : RuleName :=
  match mode with
  | .box => box
  | .diamond => diamond

/-- Boolean test mirroring `Rules.isArray`. -/
def arrayTyB (e : WrappedExpr) : Bool :=
  match e.ty with
  | Ty.ref (RefTy.array _) => true
  | _ => false

/-- Boolean test mirroring `Rules.isMapping`. -/
def mappingTyB (e : WrappedExpr) : Bool :=
  match e.ty with
  | Ty.ref (RefTy.mapping _ _) => true
  | _ => false

theorem arrayTyB_of_isArray {e : WrappedExpr} (h : Rules.isArray e) :
    arrayTyB e = true := by
  obtain ⟨elem, hty⟩ := h
  simp [arrayTyB, hty]

theorem mappingTyB_of_isMapping {e : WrappedExpr} (h : Rules.isMapping e) :
    mappingTyB e = true := by
  obtain ⟨key, value, hty⟩ := h
  simp [mappingTyB, hty]

theorem arrayTyB_eq_false_of_isMapping {e : WrappedExpr}
    (h : Rules.isMapping e) : arrayTyB e = false := by
  obtain ⟨key, value, hty⟩ := h
  simp [arrayTyB, hty]

theorem kind_of_isStorage {e : WrappedExpr} (h : e.isStorage = true) :
    e.kind = Kind.storage := by
  simpa [Typed.WrappedExpr.isStorage] using h

theorem kind_of_isMemory {e : WrappedExpr} (h : e.isMemory = true) :
    e.kind = Kind.memory := by
  simpa [Typed.WrappedExpr.isMemory] using h

theorem kind_of_isStack {e : WrappedExpr} (h : e.isStack = true) :
    e.kind = Kind.stack := by
  simpa [Typed.WrappedExpr.isStack] using h

theorem isStorage_of_kind {e : WrappedExpr} (h : e.kind = Kind.storage) :
    e.isStorage = true := by
  simp [Typed.WrappedExpr.isStorage, h]

theorem isStorage_eq_false_of_isMemory {e : WrappedExpr}
    (h : e.isMemory = true) : e.isStorage = false := by
  simp [Typed.WrappedExpr.isStorage, kind_of_isMemory h]

theorem isStorage_eq_false_of_isStack {e : WrappedExpr}
    (h : e.isStack = true) : e.isStorage = false := by
  simp [Typed.WrappedExpr.isStorage, kind_of_isStack h]

theorem isMemory_eq_false_of_isStorage {e : WrappedExpr}
    (h : e.isStorage = true) : e.isMemory = false := by
  simp [Typed.WrappedExpr.isMemory, kind_of_isStorage h]

theorem isMemory_eq_false_of_isStack {e : WrappedExpr}
    (h : e.isStack = true) : e.isMemory = false := by
  simp [Typed.WrappedExpr.isMemory, kind_of_isStack h]

theorem isStack_eq_false_of_isStorage {e : WrappedExpr}
    (h : e.isStorage = true) : e.isStack = false := by
  simp [Typed.WrappedExpr.isStack, kind_of_isStorage h]

theorem isStack_eq_false_of_isMemory {e : WrappedExpr}
    (h : e.isMemory = true) : e.isStack = false := by
  simp [Typed.WrappedExpr.isStack, kind_of_isMemory h]

theorem complex_eq_false_of_simple {e : WrappedExpr} (h : e.simple = true) :
    e.complex = false := by
  simp [Typed.WrappedExpr.complex, h]

theorem simple_eq_false_of_complex {e : WrappedExpr} (h : e.complex = true) :
    e.simple = false := by
  cases hs : e.simple <;> simp_all [Typed.WrappedExpr.complex]

theorem isLocal_shape : ∀ {e : WrappedExpr}, e.isLocal = true ->
    ∃ ty fld, e = WrappedExpr.var Kind.storage ty fld ∧
      fld.origin = some StorageOrigin.local
  | .var Kind.storage ty fld, h =>
      ⟨ty, fld, rfl, by simpa [Typed.WrappedExpr.isLocal] using h⟩

theorem isGlobal_shape : ∀ {e : WrappedExpr}, e.isGlobal = true ->
    ∃ ty fld, e = WrappedExpr.var Kind.storage ty fld ∧
      fld.origin = some StorageOrigin.global
  | .var Kind.storage ty fld, h =>
      ⟨ty, fld, rfl, by simpa [Typed.WrappedExpr.isGlobal] using h⟩

/--
Dispatch for assignments under a *simple* right-hand side: mirrors the
(now mutually disjoint) write-rule conditions.
-/
def assignSimpleCandidate
    (mode : Modality) (lexpr rhs : WrappedExpr) : Option RuleName :=
  match lexpr with
  | .field Kind.storage _ path _ =>
      if path.complex then
        if rhs.isMemory then some .memoryToStorageUnfoldLeftFstTarget
        else some .storageFieldWriteUnfoldLeftFst
      else
        if rhs.isStorage then some .storageFieldWriteCopySource
        else if rhs.isStack then some .storageFieldWriteSave
        else if rhs.isMemory then some .memoryToStorageFieldCopyRoot
        else none
  | .index Kind.storage _ path index =>
      if path.complex then some .storageIndexWriteUnfoldLeftFst
      else if index.complex then
        if rhs.isMemory then some .memoryToStorageUnfoldLeftSndTargetIndex
        else some .storageIndexWriteUnfoldLeftSndIndex
      else
        if rhs.isStorage then
          if arrayTyB path then
            some (pick mode .storageIndexWriteArrayCopySourceBox
              .storageIndexWriteArrayCopySourceDiamond)
          else if mappingTyB path then some .storageIndexWriteMappingCopySource
          else none
        else if rhs.isStack then
          if arrayTyB path then
            some (pick mode .storageIndexWriteArraySaveBox
              .storageIndexWriteArraySaveDiamond)
          else if mappingTyB path then some .storageIndexWriteMappingSave
          else none
        else if rhs.isMemory then
          if arrayTyB path then
            some (pick mode .memoryToStorageIndexArrayCopyRootBox
              .memoryToStorageIndexArrayCopyRootDiamond)
          else if mappingTyB path then some .memoryToStorageIndexMappingCopyRoot
          else none
        else none
  | .field Kind.memory _ path _ =>
      if path.complex then some .memoryFieldWriteUnfoldLeftFst
      else if rhs.isMemory then some .memoryFieldWriteCopy
      else if rhs.isStack then some .memoryFieldWriteStore
      else none
  | .index Kind.memory _ path index =>
      if path.complex then some .memoryIndexWriteUnfoldLeftFst
      else if index.complex then some .memoryIndexWriteUnfoldLeftSndIndex
      else if rhs.isMemory then
        some (pick mode .memoryIndexWriteCopyBox .memoryIndexWriteCopyDiamond)
      else if rhs.isStack then
        some (pick mode .memoryIndexWriteStoreBox .memoryIndexWriteStoreDiamond)
      else none
  | .pushPlace target =>
      if target.kind = Kind.storage then some .storagePushLhsToPushValue
      else none
  | .var Kind.storage _ fld =>
      if fld.origin = some StorageOrigin.local then
        if rhs.isStorage then some .storageLocalRootRebind
        else if rhs.isMemory then some .memoryToStorageStoreRoot
        else none
      else if fld.origin = some StorageOrigin.global then
        if rhs.isStorage then some .storageRootWriteCopySource
        else if rhs.isStack then some .storageRootWriteStore
        else if rhs.isMemory then some .memoryToStorageStoreRoot
        else none
      else
        if rhs.isMemory then some .memoryToStorageStoreRoot
        else none
  | .var Kind.memory _ _ =>
      if rhs.isMemory then some .memoryRootAlias
      else if rhs.isStorage then some .memoryStorageCopy
      else none
  | _ =>
      if lexpr.isStack && rhs.isStorage then some .storageRootReadSelect
      else if lexpr.isStack && lexpr.simple && rhs.isStack then
        some .localValueAssign
      else none

/-- Dispatch for the `*ValueRhsCapture` trio: a storage-write target whose
nonsimple primitive RHS must be hoisted first (KeY RHS-before-LHS
evaluation order). -/
def valueRhsCaptureCandidate (lexpr : WrappedExpr) : Option RuleName :=
  match lexpr with
  | .var Kind.storage _ fld =>
      if fld.origin = some StorageOrigin.global then
        some .storageRootWriteValueRhsCapture
      else none
  | .field Kind.storage _ _ _ => some .fieldWriteValueRhsCapture
  | .index Kind.storage _ _ _ => some .indexWriteValueRhsCapture
  | _ => none

/--
Dispatch for assignments under a *complex* right-hand side: mirrors the
(now mutually disjoint) read-rule conditions.
-/
def assignComplexCandidate
    (mode : Modality) (lexpr rhs : WrappedExpr) : Option RuleName :=
  if lexpr.kind = Kind.memory ∧ lexpr.complex = true then
    match rhs with
    | .field Kind.memory _ path _ =>
        if path.complex then some .memoryFieldReadUnfoldRightFst
        else some .memoryFieldReadUnfoldRightSndResult
    | .index Kind.memory _ path index =>
        if path.complex then some .memoryIndexReadUnfoldRightFst
        else if index.complex then some .memoryIndexReadUnfoldRightSndIndex
        else some .memoryIndexReadUnfoldRightSndResult
    | _ => some .memoryWriteUnfoldRightSndResult
  else if lexpr.kind = Kind.storage ∧ rhs.isMemory = true then
    some .memoryToStorageUnfoldRightFstSource
  else
    match rhs with
    | .field Kind.storage _ path _ =>
        if path.complex then some .storageFieldReadUnfoldRightFst
        else
          if lexpr.isStorage then
            if lexpr.complex then some .storageFieldReadUnfoldRightSndResult
            else if lexpr.isLocal then some .storageFieldReadBindLocalRoot
            else if lexpr.isGlobal then some .storageFieldReadStoreRoot
            else none
          else if lexpr.isStack then some .storageFieldReadFind
          else if lexpr.kind = Kind.memory then some .memoryStorageCopyUnfold
          else none
    | .index Kind.storage _ path index =>
        if path.complex then some .storageIndexReadUnfoldRightFst
        else if index.complex then some .storageIndexReadUnfoldRightSndIndex
        else
          if lexpr.isStorage then
            if lexpr.complex then some .storageIndexReadUnfoldRightSndResult
            else if lexpr.isLocal then
              if arrayTyB path then
                some (pick mode .storageIndexReadArrayBindLocalRootBox
                  .storageIndexReadArrayBindLocalRootDiamond)
              else if mappingTyB path then
                some .storageIndexReadMappingBindLocalRoot
              else none
            else if lexpr.isGlobal then
              if arrayTyB path then
                some (pick mode .storageIndexReadArrayStoreRootBox
                  .storageIndexReadArrayStoreRootDiamond)
              else if mappingTyB path then
                some .storageIndexReadMappingStoreRoot
              else none
            else none
          else if lexpr.isStack then
            if arrayTyB path then
              some (pick mode .storageIndexReadArrayFindBox
                .storageIndexReadArrayFindDiamond)
            else if mappingTyB path then some .storageIndexReadMappingFind
            else none
          else if lexpr.kind = Kind.memory then some .memoryStorageCopyUnfold
          else none
    | .field Kind.memory _ path _ =>
        if path.complex then some .memoryFieldReadUnfoldRightFst
        else
          if lexpr.isStack then some .memoryFieldReadHeap
          else if lexpr.kind = Kind.memory then some .memoryFieldReadAliasRoot
          else none
    | .index Kind.memory _ path index =>
        if path.complex then some .memoryIndexReadUnfoldRightFst
        else if index.complex then some .memoryIndexReadUnfoldRightSndIndex
        else
          if lexpr.isStack then
            some (pick mode .memoryIndexReadHeapBox .memoryIndexReadHeapDiamond)
          else if lexpr.kind = Kind.memory then
            some (pick mode .memoryIndexReadAliasRootBox
              .memoryIndexReadAliasRootDiamond)
          else none
    | .pushPlace target =>
        if target.complex then some .storageLocalRootPushUnfoldLeftFstReceiver
        else if lexpr.isLocal then some .storageLocalRootPushBind
        else none
    | .mkBinop op l r =>
        if lexpr.isStack && lexpr.simple then
          if l.complex then some (.binopUnfoldLeft op)
          else if r.complex then
            match op with
            | .and => some .logicalAndShortCircuitRhs
            | .or => some .logicalOrShortCircuitRhs
            | _ => some (.binopUnfoldRight op)
          else some (.binopAssignment op)
        else if op.isArith && l.simple && r.simple then
          some (.binopUnfoldResult op)
        else valueRhsCaptureCandidate lexpr
    | .mkUnop op arg =>
        if lexpr.isStack && lexpr.simple then
          if arg.complex then some (.unopCapture op)
          else some (.unopAssignment op)
        else valueRhsCaptureCandidate lexpr
    | .mkIncDec op target =>
        if lexpr.isStack && lexpr.simple then
          if target.isStack && target.simple then
            some (.localAssignIncDec op)
          else
            match target with
            | .var Kind.storage _ fld =>
                if fld.origin = some StorageOrigin.global then
                  some (.storageRootIncDecAssignment op)
                else none
            | .field Kind.storage _ path _ =>
                if path.complex then none
                else some (.storageFieldIncDecAssignment op)
            | .index Kind.storage _ path index =>
                if path.complex || index.complex then none
                else some (.storageIndexIncDecAssignment op)
            | .field Kind.memory _ path _ =>
                if path.complex then none
                else some (.memoryFieldIncDecAssignment op)
            | .index Kind.memory _ path index =>
                if path.complex || index.complex then none
                else some (.memoryIndexIncDecAssignment op)
            | _ => none
        else valueRhsCaptureCandidate lexpr
    | .mkTernary c _ _ =>
        if c.complex then some .ternaryCaptureCond
        else if lexpr.isStack && lexpr.simple then some .ternaryToIf
        else if lexpr.isStorage then some .ternaryToIfStorage
        else none
    | _ => none

def assignCandidate (mode : Modality) (lexpr rhs : WrappedExpr) :
    Option RuleName :=
  if rhs.simple then assignSimpleCandidate mode lexpr rhs
  else assignComplexCandidate mode lexpr rhs

def memoryDeclCandidate (init : Option WrappedExpr) : Option RuleName :=
  match init with
  | none => some .memoryDeclFreshAlloc
  | some rhs =>
      if rhs.isMemory then some .memoryLocalDeclInitDrop
      else
        match rhs with
        | .field Kind.storage _ path _ =>
            if path.complex then some .storageToMemoryDeclUnfoldRightFst
            else some .storageToMemoryDeclCopyField
        | _ =>
            if rhs.isStorage && rhs.simple then
              some .storageToMemoryDeclCopyRoot
            else none

def deleteCandidate (target : WrappedExpr) : Option RuleName :=
  match target with
  | .var Kind.storage _ fld =>
      if fld.origin = some StorageOrigin.global then
        some .storageDeleteSimpleTarget
      else none
  | .field Kind.storage _ path _ =>
      if path.complex then some .storageDeleteComplexTarget
      else some .storageDeleteSimpleTarget
  | .index Kind.storage _ path index =>
      if path.complex then some .storageDeleteComplexTarget
      else if index.complex then some .storageDeleteComplexTarget
      else if arrayTyB path || mappingTyB path then
        some .storageDeleteSimpleTarget
      else none
  | .pushPlace path =>
      if path.kind = Kind.storage then
        if path.complex then some .storageDeleteComplexTarget
        else some .storageDeleteSimpleTarget
      else none
  | .var Kind.memory _ _ => some .memoryDeleteSimpleTarget
  | .field Kind.memory _ path _ =>
      if path.complex then some .memoryDeleteComplexTarget
      else some .memoryDeleteSimpleTarget
  | .index Kind.memory _ path index =>
      if path.complex then some .memoryDeleteComplexTarget
      else if index.complex then some .memoryDeleteComplexTarget
      else some .memoryDeleteSimpleTarget
  | _ => none

def pushCandidate (target : WrappedExpr) (value : Option WrappedExpr) :
    Option RuleName :=
  if target.kind = Kind.storage then
    if target.complex then
      match value with
      | some _ => some .storagePushValueUnfoldLeftFstReceiver
      | none => some .storagePushUnfoldLeftFstReceiver
    else
      match value with
      | none => some .storagePushLengthSave
      | some rhs =>
          if rhs.complex then some .storagePushValueUnfoldRightSndArgument
          else if rhs.isStorage then some .storagePushValueCopySource
          else if rhs.isStack then some .storagePushValueSave
          else none
  else none

def popCandidate (mode : Modality) (target : WrappedExpr) : Option RuleName :=
  if target.kind = Kind.storage then
    if target.complex then some .storagePopUnfoldLeftFstReceiver
    else some (pick mode .storagePopSaveBox .storagePopSaveDiamond)
  else none

def compoundAssignCandidate (op : BinOp) (lexpr rhs : WrappedExpr) :
    Option RuleName :=
  if op.hasCompoundAssign then
    if rhs.isStack && rhs.simple then
      if lexpr.isStack && lexpr.simple then some (.localCompoundAssign op)
      else
        match lexpr with
        | .var Kind.storage _ fld =>
            if fld.origin = some StorageOrigin.global then
              some (.storageRootCompoundAssign op)
            else none
        | .field Kind.storage _ path _ =>
            if path.complex then some (.storageFieldCompoundAssignUnfoldLeftFst op)
            else some (.storageFieldCompoundAssign op)
        | .index Kind.storage _ path index =>
            if index.complex then none
            else if path.complex then
              some (.storageIndexCompoundAssignUnfoldLeftFst op)
            else some (.storageIndexCompoundAssign op)
        | .field Kind.memory _ path _ =>
            if path.complex then some (.memoryFieldCompoundAssignUnfoldLeftFst op)
            else some (.memoryFieldCompoundAssign op)
        | .index Kind.memory _ path index =>
            if index.complex then none
            else if path.complex then
              some (.memoryIndexCompoundAssignUnfoldLeftFst op)
            else some (.memoryIndexCompoundAssign op)
        | _ => none
    else some (.compoundAssignValueRhsCapture op)
  else none

def incDecStmtCandidate (op : IncDec) (target : WrappedExpr) :
    Option RuleName :=
  if target.isStack && target.simple then some (.localIncDec op)
  else
    match target with
    | .var Kind.storage _ fld =>
        if fld.origin = some StorageOrigin.global then
          some (.storageRootIncDec op)
        else none
    | .field Kind.storage _ path _ =>
        if path.complex then some (.storageFieldIncDecUnfoldLeftFst op)
        else some (.storageFieldIncDec op)
    | .index Kind.storage _ path index =>
        if index.complex then none
        else if path.complex then some (.storageIndexIncDecUnfoldLeftFst op)
        else some (.storageIndexIncDec op)
    | .field Kind.memory _ path _ =>
        if path.complex then some (.memoryFieldIncDecUnfoldLeftFst op)
        else some (.memoryFieldIncDec op)
    | .index Kind.memory _ path index =>
        if index.complex then none
        else if path.complex then some (.memoryIndexIncDecUnfoldLeftFst op)
        else some (.memoryIndexIncDec op)
    | _ => none

def exprCandidate (expr : WrappedExpr) : Option RuleName :=
  match expr with
  | .mkIncDec op target => incDecStmtCandidate op target
  | _ => some .exprStmtCapture

def assertCandidate (cond : WrappedExpr) : Option RuleName :=
  if cond.complex then some .assertConditionCapture
  else some .assertSimple

def requireCandidate (cond : WrappedExpr) : Option RuleName :=
  if cond.complex then some .requireConditionCapture
  else some .requireSimple

def iteCandidate (cond : WrappedExpr) : Option RuleName :=
  match cond with
  | .bool true => some .ifElseTrue
  | .bool false => some .ifElseFalse
  | .mkUnop UnOp.not inner =>
      if inner.complex then some .ifElseUnfold
      else some .ifElseNegated
  | _ =>
      if cond.complex then some .ifElseUnfold
      else none

def transferCandidate (recipient amount : WrappedExpr) : Option RuleName :=
  if recipient.complex then some .transferUnfoldLeftFstReceiver
  else if amount.complex then some .transferUnfoldRightSndArgument
  else some .transferNoCallback

/--
Total dispatch: returns the unique rule of the calculus that can apply to a statement
under the given modality (the value is unconstrained where no rule applies).
-/
def candidate (mode : Modality) : Stmt -> Option RuleName
  | Stmt.expr expr => exprCandidate expr
  | Stmt.assign lhs rhs => assignCandidate mode (lhs : WrappedExpr) rhs
  | Stmt.compoundAssign op lhs rhs =>
      compoundAssignCandidate op (lhs : WrappedExpr) rhs
  | Stmt.storageDecl _ _ init =>
      if init.isSome then some .storageLocalDeclInitDrop
      else some .storageLocalDeclSkip
  | Stmt.storagePlaceAlias _ _ _ => some .storagePlaceAlias
  | Stmt.stackDecl _ _ init =>
      if init.isSome then some .localValueDeclInitDrop
      else some .valueDeclSkip
  | Stmt.memoryDecl _ _ init => memoryDeclCandidate init
  | Stmt.delete target => deleteCandidate (target : WrappedExpr)
  | Stmt.push target value => pushCandidate (target : WrappedExpr) value
  | Stmt.pop target => popCandidate mode (target : WrappedExpr)
  | Stmt.revert _ => some (pick mode .revertBox .revertDiamond)
  | Stmt.assertStmt cond => assertCandidate cond
  | Stmt.requireStmt cond => requireCandidate cond
  | Stmt.ite cond _ _ => iteCandidate cond
  | Stmt.transfer recipient amount => transferCandidate recipient amount
  | Stmt.callStmt res fn args =>
      if (Rules.captureFirstComplexArg args).isSome then
        some .functionCallArgCapture
      else if (SoliditySyntax.expandCall res fn args).isSome then
        some .functionBodyExpand
      else none
  | Stmt.pushAssign _ _ => some .pushAssignLower
  | Stmt.pushFieldAssign _ _ _ => some .pushFieldAssignLower

/-- Dispatch under KeY's `transferSemantics:withCallback` choice: the
default dispatch with the transfer rule swapped. -/
def candidateWithCallback (mode : Modality) (stmt : Stmt) :
    Option RuleName :=
  match candidate mode stmt with
  | some .transferNoCallback => some .transferWithCallback
  | r => r

theorem coe_eq_expr (p : PlaceExpr) : (p : WrappedExpr) = p.expr := rfl

theorem not_kind_storage {e : WrappedExpr} (h : e.isStorage = false) :
    ¬ e.kind = Kind.storage := by
  simpa [Typed.WrappedExpr.isStorage] using h

theorem kind_var (k : Kind) (t : Ty) (f : Field) :
    (WrappedExpr.var k t f).kind = k := rfl
theorem kind_field (k : Kind) (t : Ty) (b : WrappedExpr) (f : Field) :
    (WrappedExpr.field k t b f).kind = k := rfl
theorem kind_index (k : Kind) (t : Ty) (b i : WrappedExpr) :
    (WrappedExpr.index k t b i).kind = k := rfl
theorem kind_pushPlace (t : WrappedExpr) :
    (WrappedExpr.pushPlace t).kind = Kind.storage := rfl
theorem kind_bool (v : Bool) :
    (WrappedExpr.bool v).kind = Kind.stack := rfl
theorem simple_var (k : Kind) (t : Ty) (f : Field) :
    (WrappedExpr.var k t f).simple = true := rfl
theorem simple_field (k : Kind) (t : Ty) (b : WrappedExpr) (f : Field) :
    (WrappedExpr.field k t b f).simple = false := rfl
theorem simple_index (k : Kind) (t : Ty) (b i : WrappedExpr) :
    (WrappedExpr.index k t b i).simple = false := rfl
theorem simple_pushPlace (t : WrappedExpr) :
    (WrappedExpr.pushPlace t).simple = false := rfl
theorem simple_bool (v : Bool) :
    (WrappedExpr.bool v).simple = true := rfl
theorem complex_var (k : Kind) (t : Ty) (f : Field) :
    (WrappedExpr.var k t f).complex = false := rfl
theorem complex_field (k : Kind) (t : Ty) (b : WrappedExpr) (f : Field) :
    (WrappedExpr.field k t b f).complex = true := rfl
theorem complex_index (k : Kind) (t : Ty) (b i : WrappedExpr) :
    (WrappedExpr.index k t b i).complex = true := rfl
theorem complex_pushPlace (t : WrappedExpr) :
    (WrappedExpr.pushPlace t).complex = true := rfl
theorem complex_bool (v : Bool) :
    (WrappedExpr.bool v).complex = false := rfl
theorem isLocal_var (t : Ty) (f : Field) :
    (WrappedExpr.var Kind.storage t f).isLocal
      = decide (f.origin = some StorageOrigin.local) := rfl
theorem isGlobal_var (t : Ty) (f : Field) :
    (WrappedExpr.var Kind.storage t f).isGlobal
      = decide (f.origin = some StorageOrigin.global) := rfl
theorem kind_intLit (t : Ty) (v : Int) :
    (WrappedExpr.intLit t v).kind = Kind.stack := rfl
theorem kind_binop (o : BinOp) (l r : WrappedExpr) :
    (Typed.WrappedExpr.mkBinop o l r).kind = Kind.stack := rfl
theorem kind_unop (o : UnOp) (a : WrappedExpr) :
    (Typed.WrappedExpr.mkUnop o a).kind = Kind.stack := rfl
theorem kind_incDec (o : IncDec) (t : WrappedExpr) :
    (Typed.WrappedExpr.mkIncDec o t).kind = Kind.stack := rfl
theorem simple_intLit (t : Ty) (v : Int) :
    (WrappedExpr.intLit t v).simple = true := rfl
theorem simple_binop (o : BinOp) (l r : WrappedExpr) :
    (Typed.WrappedExpr.mkBinop o l r).simple = false := rfl
theorem simple_unop (o : UnOp) (a : WrappedExpr) :
    (Typed.WrappedExpr.mkUnop o a).simple = false := rfl
theorem simple_incDec (o : IncDec) (t : WrappedExpr) :
    (Typed.WrappedExpr.mkIncDec o t).simple = false := rfl
theorem complex_intLit (t : Ty) (v : Int) :
    (WrappedExpr.intLit t v).complex = false := rfl
theorem complex_binop (o : BinOp) (l r : WrappedExpr) :
    (Typed.WrappedExpr.mkBinop o l r).complex = true := rfl
theorem complex_unop (o : UnOp) (a : WrappedExpr) :
    (Typed.WrappedExpr.mkUnop o a).complex = true := rfl
theorem complex_incDec (o : IncDec) (t : WrappedExpr) :
    (Typed.WrappedExpr.mkIncDec o t).complex = true := rfl
theorem kind_ternary (c t e : WrappedExpr) :
    (Typed.WrappedExpr.mkTernary c t e).kind = Kind.stack := rfl
theorem simple_ternary (c t e : WrappedExpr) :
    (Typed.WrappedExpr.mkTernary c t e).simple = false := rfl
theorem complex_ternary (c t e : WrappedExpr) :
    (Typed.WrappedExpr.mkTernary c t e).complex = true := rfl

attribute [local simp] kind_var kind_field kind_index kind_pushPlace kind_bool
  simple_var simple_field simple_index simple_pushPlace simple_bool
  complex_var complex_field complex_index complex_pushPlace complex_bool
  isLocal_var isGlobal_var
  kind_intLit kind_binop kind_unop kind_incDec
  simple_intLit simple_binop simple_unop simple_incDec
  complex_intLit complex_binop complex_unop complex_incDec
  kind_ternary simple_ternary complex_ternary

theorem simple_storage_shape : ∀ {e : WrappedExpr}, e.simple = true ->
    e.kind = Kind.storage ->
    ∃ ty fld, e = WrappedExpr.var Kind.storage ty fld
  | .var Kind.storage ty fld, _, _ => ⟨ty, fld, rfl⟩
  | .var Kind.memory _ _, _, hk => by simp [Typed.WrappedExpr.kind] at hk
  | .var Kind.stack _ _, _, hk => by simp [Typed.WrappedExpr.kind] at hk
  | .bool _, _, hk => by simp [Typed.WrappedExpr.kind] at hk

theorem simple_memory_shape : ∀ {e : WrappedExpr}, e.simple = true ->
    e.kind = Kind.memory ->
    ∃ ty fld, e = WrappedExpr.var Kind.memory ty fld
  | .var Kind.memory ty fld, _, _ => ⟨ty, fld, rfl⟩
  | .var Kind.storage _ _, _, hk => by simp [Typed.WrappedExpr.kind] at hk
  | .var Kind.stack _ _, _, hk => by simp [Typed.WrappedExpr.kind] at hk
  | .bool _, _, hk => by simp [Typed.WrappedExpr.kind] at hk

/--
Whenever a rule of the calculus is applicable to a statement under a modality, the
dispatch function `candidate` selects exactly that rule.
-/
theorem applicable_eq_candidate {mode : Modality} {stmt : Stmt}
    {rule : RuleName} (hmem : rule ∈ Rules.ruleNames)
    (hmode : ((Rules.ruleEffect rule).mode stmt).applies mode = true)
    (hcond : (Rules.ruleEffect rule).cond stmt) :
    candidate mode stmt = some rule := by
  cases rule
  case transferWithCallback => exact absurd hmem (by decide)
  case exprStmtCapture =>
    cases stmt <;>
      simp only [Rules.ruleEffect, Rules.exprEffect] at hcond
    next e =>
      cases e <;> simp_all [candidate, exprCandidate]
  case pushAssignLower =>
    cases stmt <;> simp only [Rules.ruleEffect] at hcond
    next target value =>
      simp [candidate]
  case pushFieldAssignLower =>
    cases stmt <;> simp only [Rules.ruleEffect] at hcond
    next target fld value =>
      simp [candidate]
  case storageLocalDeclInitDrop =>
    cases stmt <;>
      simp only [Rules.ruleEffect, Rules.storageDeclEffect] at hcond
    next ty name init =>
      simp [candidate, hcond]
  case storageLocalDeclSkip =>
    cases stmt <;>
      simp only [Rules.ruleEffect, Rules.storageDeclEffect] at hcond
    next ty name init =>
      simp [candidate, hcond]
  case storagePlaceAlias =>
    cases stmt <;>
      simp only [Rules.ruleEffect] at hcond
    simp [candidate]
  case memoryLocalDeclInitDrop =>
    cases stmt <;>
      simp only [Rules.ruleEffect, Rules.memoryDeclEffect] at hcond
    next ty name init =>
      split at hcond
      · next rhs =>
          simp only [Rules.isMemory] at hcond
          simp [candidate, memoryDeclCandidate, hcond]
      · exact hcond.elim
  case memoryDeclFreshAlloc =>
    cases stmt <;>
      simp only [Rules.ruleEffect, Rules.memoryDeclEffect] at hcond
    next ty name init =>
      subst hcond
      simp [candidate, memoryDeclCandidate]
  case storageToMemoryDeclUnfoldRightFst =>
    cases stmt <;>
      simp only [Rules.ruleEffect, Rules.memoryDeclEffect] at hcond
    next ty name init =>
      split at hcond
      · next rhsTy path fld =>
          simp only [Rules.isComplex] at hcond
          simp [candidate, memoryDeclCandidate, Typed.WrappedExpr.isMemory,
            Typed.WrappedExpr.kind, hcond]
      · exact hcond.elim
  case storageToMemoryDeclCopyField =>
    cases stmt <;>
      simp only [Rules.ruleEffect, Rules.memoryDeclEffect] at hcond
    next ty name init =>
      split at hcond
      · next rhsTy path fld =>
          simp only [Rules.isSimple] at hcond
          simp [candidate, memoryDeclCandidate, Typed.WrappedExpr.isMemory,
            Typed.WrappedExpr.kind, complex_eq_false_of_simple hcond]
      · exact hcond.elim
  case storageToMemoryDeclCopyRoot =>
    cases stmt <;>
      simp only [Rules.ruleEffect, Rules.memoryDeclEffect] at hcond
    next ty name init =>
      split at hcond
      · next rhs =>
          obtain ⟨h1, h2⟩ := hcond
          simp only [Rules.isStorage, Rules.isSimple] at h1 h2
          obtain ⟨vty, fld, hshape⟩ :=
            simple_storage_shape h2 (kind_of_isStorage h1)
          subst hshape
          simp [candidate, memoryDeclCandidate, Typed.WrappedExpr.isMemory,
            Typed.WrappedExpr.kind, h1, h2]
      · exact hcond.elim
  case storageDeleteComplexTarget =>
    cases stmt <;>
      simp only [Rules.ruleEffect, Rules.deleteEffect] at hcond
    next target =>
      rw [Rules.isComplexStorageDeleteTarget.eq_def] at hcond
      split at hcond
      · next ty path fld heq =>
          simp only [Rules.isComplex] at hcond
          simp [candidate, deleteCandidate, coe_eq_expr, heq, hcond]
      · next ty path idx heq =>
          rcases hcond with h | ⟨h1, h2⟩
          · simp only [Rules.isComplex] at h
            simp [candidate, deleteCandidate, coe_eq_expr, heq, h]
          · simp only [Rules.isSimple, Rules.isComplex] at h1 h2
            simp [candidate, deleteCandidate, coe_eq_expr, heq, h2,
              complex_eq_false_of_simple h1]
      · next path heq =>
          obtain ⟨h1, h2⟩ := hcond
          simp only [Rules.isComplex] at h2
          simp [candidate, deleteCandidate, coe_eq_expr, heq, h1, h2]
      · exact hcond.elim
  case storageDeleteSimpleTarget =>
    cases stmt <;>
      simp only [Rules.ruleEffect, Rules.deleteEffect] at hcond
    next target =>
      rw [Rules.isSimpleStorageDeleteTarget.eq_def] at hcond
      split at hcond
      · next ty fld heq =>
          simp only [Rules.isGlobal, Typed.WrappedExpr.isGlobal,
            decide_eq_true_eq] at hcond
          simp [candidate, deleteCandidate, coe_eq_expr, heq, hcond]
      · next ty path fld heq =>
          simp only [Rules.isSimple] at hcond
          simp [candidate, deleteCandidate, coe_eq_expr, heq,
            complex_eq_false_of_simple hcond]
      · next ty path idx heq =>
          obtain ⟨h1, h2, h3⟩ := hcond
          simp only [Rules.isSimple] at h1 h2
          rcases h3 with harr | hmap
          · simp [candidate, deleteCandidate, coe_eq_expr, heq,
              complex_eq_false_of_simple h1, complex_eq_false_of_simple h2,
              arrayTyB_of_isArray harr]
          · simp [candidate, deleteCandidate, coe_eq_expr, heq,
              complex_eq_false_of_simple h1, complex_eq_false_of_simple h2,
              mappingTyB_of_isMapping hmap]
      · next path heq =>
          obtain ⟨h1, h2⟩ := hcond
          simp only [Rules.isSimple] at h2
          simp [candidate, deleteCandidate, coe_eq_expr, heq, h1,
            complex_eq_false_of_simple h2]
      · exact hcond.elim
  case memoryDeleteComplexTarget =>
    cases stmt <;>
      simp only [Rules.ruleEffect, Rules.deleteEffect] at hcond
    next target =>
      rw [Rules.isComplexMemoryDeleteTarget.eq_def] at hcond
      split at hcond
      · next ty path fld heq =>
          simp only [Rules.isComplex] at hcond
          simp [candidate, deleteCandidate, coe_eq_expr, heq, hcond]
      · next ty path idx heq =>
          rcases hcond with h | ⟨h1, h2⟩
          · simp only [Rules.isComplex] at h
            simp [candidate, deleteCandidate, coe_eq_expr, heq, h]
          · simp only [Rules.isSimple, Rules.isComplex] at h1 h2
            simp [candidate, deleteCandidate, coe_eq_expr, heq, h2,
              complex_eq_false_of_simple h1]
      · exact hcond.elim
  case memoryDeleteSimpleTarget =>
    cases stmt <;>
      simp only [Rules.ruleEffect, Rules.deleteEffect] at hcond
    next target =>
      rw [Rules.isSimpleMemoryDeleteTarget.eq_def] at hcond
      split at hcond
      · next ty fld heq =>
          simp [candidate, deleteCandidate, coe_eq_expr, heq]
      · next ty path fld heq =>
          obtain ⟨h1, _⟩ := hcond
          simp only [Rules.isSimple] at h1
          simp [candidate, deleteCandidate, coe_eq_expr, heq,
            complex_eq_false_of_simple h1]
      · next ty path idx heq =>
          obtain ⟨h1, h2, _⟩ := hcond
          simp only [Rules.isSimple] at h1 h2
          simp [candidate, deleteCandidate, coe_eq_expr, heq,
            complex_eq_false_of_simple h1, complex_eq_false_of_simple h2]
      · exact hcond.elim
  case storagePushValueUnfoldLeftFstReceiver =>
    cases stmt <;>
      simp only [Rules.ruleEffect, Rules.pushEffect] at hcond
    next target value =>
      obtain ⟨h1, h2, h3⟩ := hcond
      simp only [Rules.isComplex, PlaceExpr.kind, coe_eq_expr] at h1 h2
      cases value
      · simp at h3
      · simp [candidate, pushCandidate, coe_eq_expr, h1, h2]
  case storagePushValueUnfoldRightSndArgument =>
    cases stmt <;>
      simp only [Rules.ruleEffect, Rules.pushEffect] at hcond
    next target value =>
      obtain ⟨h1, h2, h3⟩ := hcond
      simp only [Rules.isSimple, PlaceExpr.kind, coe_eq_expr] at h1 h2
      cases value
      · simp at h3
      · next rhs =>
          simp only [Rules.isComplex] at h3
          simp [candidate, pushCandidate, coe_eq_expr, h1, h3,
            complex_eq_false_of_simple h2]
  case storagePushValueCopySource =>
    cases stmt <;>
      simp only [Rules.ruleEffect, Rules.pushEffect] at hcond
    next target value =>
      obtain ⟨h1, h2, h3⟩ := hcond
      simp only [Rules.isSimple, PlaceExpr.kind, coe_eq_expr] at h1 h2
      cases value
      · simp at h3
      · next rhs =>
          obtain ⟨h4, h5⟩ := h3
          simp only [Rules.isStorage, Rules.isSimple] at h4 h5
          simp [candidate, pushCandidate, coe_eq_expr, h1, h4,
            complex_eq_false_of_simple h2, complex_eq_false_of_simple h5]
  case storagePushValueSave =>
    cases stmt <;>
      simp only [Rules.ruleEffect, Rules.pushEffect] at hcond
    next target value =>
      obtain ⟨h1, h2, h3⟩ := hcond
      simp only [Rules.isSimple, PlaceExpr.kind, coe_eq_expr] at h1 h2
      cases value
      · simp at h3
      · next rhs =>
          obtain ⟨h4, h5⟩ := h3
          simp only [Rules.isStack, Rules.isSimple] at h4 h5
          simp [candidate, pushCandidate, coe_eq_expr, h1, h4,
            complex_eq_false_of_simple h2, complex_eq_false_of_simple h5,
            isStorage_eq_false_of_isStack h4]
  case storagePushUnfoldLeftFstReceiver =>
    cases stmt <;>
      simp only [Rules.ruleEffect, Rules.pushEffect] at hcond
    next target value =>
      obtain ⟨h1, h2, h3⟩ := hcond
      simp only [Rules.isComplex, PlaceExpr.kind, coe_eq_expr] at h1 h2
      subst h3
      simp [candidate, pushCandidate, coe_eq_expr, h1, h2]
  case storagePushLengthSave =>
    cases stmt <;>
      simp only [Rules.ruleEffect, Rules.pushEffect] at hcond
    next target value =>
      obtain ⟨h1, h2, h3⟩ := hcond
      simp only [Rules.isSimple, PlaceExpr.kind, coe_eq_expr] at h1 h2
      subst h3
      simp [candidate, pushCandidate, coe_eq_expr, h1,
        complex_eq_false_of_simple h2]
  case storagePopUnfoldLeftFstReceiver =>
    cases stmt <;>
      simp only [Rules.ruleEffect, Rules.popEffect] at hcond
    next target =>
      obtain ⟨h1, h2⟩ := hcond
      simp only [Rules.isComplex, PlaceExpr.kind, coe_eq_expr] at h1 h2
      simp [candidate, popCandidate, coe_eq_expr, h1, h2]
  case storagePopSaveBox =>
    cases mode
    case diamond =>
      simp [Rules.ruleEffect, Rules.popEffect, CaseMode.applies] at hmode
    case box =>
      cases stmt <;>
        simp only [Rules.ruleEffect, Rules.popEffect] at hcond
      next target =>
        obtain ⟨h1, h2⟩ := hcond
        simp only [Rules.isSimple, PlaceExpr.kind, coe_eq_expr] at h1 h2
        simp [candidate, popCandidate, pick, coe_eq_expr, h1,
          complex_eq_false_of_simple h2]
  case storagePopSaveDiamond =>
    cases mode
    case box =>
      simp [Rules.ruleEffect, Rules.popEffect, CaseMode.applies] at hmode
    case diamond =>
      cases stmt <;>
        simp only [Rules.ruleEffect, Rules.popEffect] at hcond
      next target =>
        obtain ⟨h1, h2⟩ := hcond
        simp only [Rules.isSimple, PlaceExpr.kind, coe_eq_expr] at h1 h2
        simp [candidate, popCandidate, pick, coe_eq_expr, h1,
          complex_eq_false_of_simple h2]
  case storageFieldWriteUnfoldLeftFst =>
    cases stmt <;>
      simp only [Rules.ruleEffect, Rules.assignEffect] at hcond
    next lhs rhs =>
      split at hcond
      · next ty path fld heq =>
          obtain ⟨h1, h2, h3⟩ := hcond
          simp only [Rules.isComplex, Rules.isSimple, Rules.isMemory]
            at h1 h2 h3
          rw [Bool.not_eq_true] at h3
          simp [candidate, assignCandidate, assignSimpleCandidate, coe_eq_expr,
            heq, h1, h2, h3]
      · exact hcond.elim
  case storageFieldWriteCopySource =>
    cases stmt <;>
      simp only [Rules.ruleEffect, Rules.assignEffect] at hcond
    next lhs rhs =>
      split at hcond
      · next ty path fld heq =>
          obtain ⟨h1, h2, h3⟩ := hcond
          simp only [Rules.isSimple, Rules.isStorage] at h1 h2 h3
          simp [candidate, assignCandidate, assignSimpleCandidate, coe_eq_expr,
            heq, h2, h3, complex_eq_false_of_simple h1]
      · exact hcond.elim
  case storageFieldWriteSave =>
    cases stmt <;>
      simp only [Rules.ruleEffect, Rules.assignEffect] at hcond
    next lhs rhs =>
      split at hcond
      · next ty path fld heq =>
          obtain ⟨h1, h2, h3⟩ := hcond
          simp only [Rules.isSimple, Rules.isStack] at h1 h2 h3
          simp [candidate, assignCandidate, assignSimpleCandidate, coe_eq_expr,
            heq, h2, h3, complex_eq_false_of_simple h1,
            isStorage_eq_false_of_isStack h2]
      · exact hcond.elim
  case memoryToStorageUnfoldLeftFstTarget =>
    cases stmt <;>
      simp only [Rules.ruleEffect, Rules.assignEffect] at hcond
    next lhs rhs =>
      split at hcond
      · next ty path fld heq =>
          obtain ⟨h1, h2, h3⟩ := hcond
          simp only [Rules.isComplex, Rules.isMemory, Rules.isSimple]
            at h1 h2 h3
          simp [candidate, assignCandidate, assignSimpleCandidate, coe_eq_expr,
            heq, h1, h2, h3]
      · exact hcond.elim
  case memoryToStorageFieldCopyRoot =>
    cases stmt <;>
      simp only [Rules.ruleEffect, Rules.assignEffect] at hcond
    next lhs rhs =>
      split at hcond
      · next ty path fld heq =>
          obtain ⟨h1, h2, h3⟩ := hcond
          simp only [Rules.isSimple, Rules.isMemory] at h1 h2 h3
          simp [candidate, assignCandidate, assignSimpleCandidate, coe_eq_expr,
            heq, h2, h3, complex_eq_false_of_simple h1,
            isStorage_eq_false_of_isMemory h2, isStack_eq_false_of_isMemory h2]
      · exact hcond.elim
  case storageIndexWriteUnfoldLeftFst =>
    cases stmt <;>
      simp only [Rules.ruleEffect, Rules.assignEffect] at hcond
    next lhs rhs =>
      split at hcond
      · next ty path idx heq =>
          obtain ⟨h1, h2⟩ := hcond
          simp only [Rules.isComplex, Rules.isSimple] at h1 h2
          simp [candidate, assignCandidate, assignSimpleCandidate, coe_eq_expr,
            heq, h1, h2]
      · exact hcond.elim
  case storageIndexWriteUnfoldLeftSndIndex =>
    cases stmt <;>
      simp only [Rules.ruleEffect, Rules.assignEffect] at hcond
    next lhs rhs =>
      split at hcond
      · next ty path idx heq =>
          obtain ⟨h1, h2, h3, h4⟩ := hcond
          simp only [Rules.isSimple, Rules.isComplex, Rules.isMemory]
            at h1 h2 h3 h4
          rw [Bool.not_eq_true] at h4
          simp [candidate, assignCandidate, assignSimpleCandidate, coe_eq_expr,
            heq, h2, h3, h4, complex_eq_false_of_simple h1]
      · exact hcond.elim
  case memoryToStorageUnfoldLeftSndTargetIndex =>
    cases stmt <;>
      simp only [Rules.ruleEffect, Rules.assignEffect] at hcond
    next lhs rhs =>
      split at hcond
      · next ty path idx heq =>
          obtain ⟨h1, h2, h3, h4⟩ := hcond
          simp only [Rules.isSimple, Rules.isComplex, Rules.isMemory]
            at h1 h2 h3 h4
          simp [candidate, assignCandidate, assignSimpleCandidate, coe_eq_expr,
            heq, h2, h3, h4, complex_eq_false_of_simple h1]
      · exact hcond.elim
  case storageIndexWriteArrayCopySourceBox =>
    cases mode
    case diamond =>
      simp [Rules.ruleEffect, Rules.withMode, CaseMode.applies] at hmode
    case box =>
      cases stmt <;>
        simp only [Rules.ruleEffect, Rules.withMode, Rules.assignEffect]
          at hcond
      next lhs rhs =>
        split at hcond
        · next ty path idx heq =>
            obtain ⟨h1, h2, h3, h4, h5⟩ := hcond
            simp only [Rules.isSimple, Rules.isStorage] at h1 h2 h3 h4
            simp [candidate, assignCandidate, assignSimpleCandidate, pick,
              coe_eq_expr, heq, h3, h4, complex_eq_false_of_simple h1,
              complex_eq_false_of_simple h2, arrayTyB_of_isArray h5]
        · exact hcond.elim
  case storageIndexWriteArrayCopySourceDiamond =>
    cases mode
    case box =>
      simp [Rules.ruleEffect, Rules.withMode, CaseMode.applies] at hmode
    case diamond =>
      cases stmt <;>
        simp only [Rules.ruleEffect, Rules.withMode, Rules.assignEffect]
          at hcond
      next lhs rhs =>
        split at hcond
        · next ty path idx heq =>
            obtain ⟨h1, h2, h3, h4, h5⟩ := hcond
            simp only [Rules.isSimple, Rules.isStorage] at h1 h2 h3 h4
            simp [candidate, assignCandidate, assignSimpleCandidate, pick,
              coe_eq_expr, heq, h3, h4, complex_eq_false_of_simple h1,
              complex_eq_false_of_simple h2, arrayTyB_of_isArray h5]
        · exact hcond.elim
  case storageIndexWriteMappingCopySource =>
    cases stmt <;>
      simp only [Rules.ruleEffect, Rules.assignEffect] at hcond
    next lhs rhs =>
      split at hcond
      · next ty path idx heq =>
          obtain ⟨h1, h2, h3, h4, h5⟩ := hcond
          simp only [Rules.isSimple, Rules.isStorage] at h1 h2 h3 h4
          simp [candidate, assignCandidate, assignSimpleCandidate, coe_eq_expr,
            heq, h3, h4, complex_eq_false_of_simple h1,
            complex_eq_false_of_simple h2, mappingTyB_of_isMapping h5,
            arrayTyB_eq_false_of_isMapping h5]
      · exact hcond.elim
  case storageIndexWriteArraySaveBox =>
    cases mode
    case diamond =>
      simp [Rules.ruleEffect, Rules.withMode, CaseMode.applies] at hmode
    case box =>
      cases stmt <;>
        simp only [Rules.ruleEffect, Rules.withMode, Rules.assignEffect]
          at hcond
      next lhs rhs =>
        split at hcond
        · next ty path idx heq =>
            obtain ⟨h1, h2, h3, h4, h5⟩ := hcond
            simp only [Rules.isSimple, Rules.isStack] at h1 h2 h3 h4
            simp [candidate, assignCandidate, assignSimpleCandidate, pick,
              coe_eq_expr, heq, h3, h4, complex_eq_false_of_simple h1,
              complex_eq_false_of_simple h2, arrayTyB_of_isArray h5,
              isStorage_eq_false_of_isStack h3]
        · exact hcond.elim
  case storageIndexWriteArraySaveDiamond =>
    cases mode
    case box =>
      simp [Rules.ruleEffect, Rules.withMode, CaseMode.applies] at hmode
    case diamond =>
      cases stmt <;>
        simp only [Rules.ruleEffect, Rules.withMode, Rules.assignEffect]
          at hcond
      next lhs rhs =>
        split at hcond
        · next ty path idx heq =>
            obtain ⟨h1, h2, h3, h4, h5⟩ := hcond
            simp only [Rules.isSimple, Rules.isStack] at h1 h2 h3 h4
            simp [candidate, assignCandidate, assignSimpleCandidate, pick,
              coe_eq_expr, heq, h3, h4, complex_eq_false_of_simple h1,
              complex_eq_false_of_simple h2, arrayTyB_of_isArray h5,
              isStorage_eq_false_of_isStack h3]
        · exact hcond.elim
  case storageIndexWriteMappingSave =>
    cases stmt <;>
      simp only [Rules.ruleEffect, Rules.assignEffect] at hcond
    next lhs rhs =>
      split at hcond
      · next ty path idx heq =>
          obtain ⟨h1, h2, h3, h4, h5⟩ := hcond
          simp only [Rules.isSimple, Rules.isStack] at h1 h2 h3 h4
          simp [candidate, assignCandidate, assignSimpleCandidate, coe_eq_expr,
            heq, h3, h4, complex_eq_false_of_simple h1,
            complex_eq_false_of_simple h2, mappingTyB_of_isMapping h5,
            arrayTyB_eq_false_of_isMapping h5,
            isStorage_eq_false_of_isStack h3]
      · exact hcond.elim
  case memoryToStorageIndexMappingCopyRoot =>
    cases stmt <;>
      simp only [Rules.ruleEffect, Rules.assignEffect] at hcond
    next lhs rhs =>
      split at hcond
      · next ty path idx heq =>
          obtain ⟨h1, h2, h3, h4, h5⟩ := hcond
          simp only [Rules.isSimple, Rules.isMemory] at h1 h2 h3 h4
          simp [candidate, assignCandidate, assignSimpleCandidate, coe_eq_expr,
            heq, h3, h4, complex_eq_false_of_simple h1,
            complex_eq_false_of_simple h2,
            isStorage_eq_false_of_isMemory h3, isStack_eq_false_of_isMemory h3,
            mappingTyB_of_isMapping h5, arrayTyB_eq_false_of_isMapping h5]
      · exact hcond.elim
  case memoryToStorageIndexArrayCopyRootBox =>
    cases mode
    case diamond =>
      simp [Rules.ruleEffect, Rules.withMode, CaseMode.applies] at hmode
    case box =>
      cases stmt <;>
        simp only [Rules.ruleEffect, Rules.withMode, Rules.assignEffect]
          at hcond
      next lhs rhs =>
        split at hcond
        · next ty path idx heq =>
            obtain ⟨h1, h2, h3, h4, h5⟩ := hcond
            simp only [Rules.isSimple, Rules.isMemory] at h1 h2 h3 h4
            simp [candidate, assignCandidate, assignSimpleCandidate, pick,
              coe_eq_expr, heq, h3, h4, complex_eq_false_of_simple h1,
              complex_eq_false_of_simple h2,
              isStorage_eq_false_of_isMemory h3, isStack_eq_false_of_isMemory h3,
              arrayTyB_of_isArray h5]
        · exact hcond.elim
  case memoryToStorageIndexArrayCopyRootDiamond =>
    cases mode
    case box =>
      simp [Rules.ruleEffect, Rules.withMode, CaseMode.applies] at hmode
    case diamond =>
      cases stmt <;>
        simp only [Rules.ruleEffect, Rules.withMode, Rules.assignEffect]
          at hcond
      next lhs rhs =>
        split at hcond
        · next ty path idx heq =>
            obtain ⟨h1, h2, h3, h4, h5⟩ := hcond
            simp only [Rules.isSimple, Rules.isMemory] at h1 h2 h3 h4
            simp [candidate, assignCandidate, assignSimpleCandidate, pick,
              coe_eq_expr, heq, h3, h4, complex_eq_false_of_simple h1,
              complex_eq_false_of_simple h2,
              isStorage_eq_false_of_isMemory h3, isStack_eq_false_of_isMemory h3,
              arrayTyB_of_isArray h5]
        · exact hcond.elim
  case memoryFieldWriteUnfoldLeftFst =>
    cases stmt <;>
      simp only [Rules.ruleEffect, Rules.assignEffect] at hcond
    next lhs rhs =>
      split at hcond
      · next ty path fld heq =>
          obtain ⟨h1, h2⟩ := hcond
          simp only [Rules.isComplex, Rules.isSimple] at h1 h2
          simp [candidate, assignCandidate, assignSimpleCandidate, coe_eq_expr,
            heq, h1, h2]
      · exact hcond.elim
  case memoryFieldWriteCopy =>
    cases stmt <;>
      simp only [Rules.ruleEffect, Rules.assignEffect] at hcond
    next lhs rhs =>
      split at hcond
      · next ty path fld heq =>
          obtain ⟨h1, h2, h3⟩ := hcond
          simp only [Rules.isSimple, Rules.isMemory] at h1 h2 h3
          simp [candidate, assignCandidate, assignSimpleCandidate, coe_eq_expr,
            heq, h2, h3, complex_eq_false_of_simple h1]
      · exact hcond.elim
  case memoryFieldWriteStore =>
    cases stmt <;>
      simp only [Rules.ruleEffect, Rules.assignEffect] at hcond
    next lhs rhs =>
      split at hcond
      · next ty path fld heq =>
          obtain ⟨h1, h2, h3⟩ := hcond
          simp only [Rules.isSimple, Rules.isStack] at h1 h2 h3
          simp [candidate, assignCandidate, assignSimpleCandidate, coe_eq_expr,
            heq, h2, h3, complex_eq_false_of_simple h1,
            isMemory_eq_false_of_isStack h2]
      · exact hcond.elim
  case memoryIndexWriteUnfoldLeftFst =>
    cases stmt <;>
      simp only [Rules.ruleEffect, Rules.assignEffect] at hcond
    next lhs rhs =>
      split at hcond
      · next ty path idx heq =>
          obtain ⟨h1, h2⟩ := hcond
          simp only [Rules.isComplex, Rules.isSimple] at h1 h2
          simp [candidate, assignCandidate, assignSimpleCandidate, coe_eq_expr,
            heq, h1, h2]
      · exact hcond.elim
  case memoryIndexWriteUnfoldLeftSndIndex =>
    cases stmt <;>
      simp only [Rules.ruleEffect, Rules.assignEffect] at hcond
    next lhs rhs =>
      split at hcond
      · next ty path idx heq =>
          obtain ⟨h1, h2, h3⟩ := hcond
          simp only [Rules.isSimple, Rules.isComplex] at h1 h2 h3
          simp [candidate, assignCandidate, assignSimpleCandidate, coe_eq_expr,
            heq, h2, h3, complex_eq_false_of_simple h1]
      · exact hcond.elim
  case memoryIndexWriteCopyBox =>
    cases mode
    case diamond =>
      simp [Rules.ruleEffect, Rules.withMode, CaseMode.applies] at hmode
    case box =>
      cases stmt <;>
        simp only [Rules.ruleEffect, Rules.withMode, Rules.assignEffect]
          at hcond
      next lhs rhs =>
        split at hcond
        · next ty path idx heq =>
            obtain ⟨h1, h2, h3, h4⟩ := hcond
            simp only [Rules.isSimple, Rules.isMemory] at h1 h2 h3 h4
            simp [candidate, assignCandidate, assignSimpleCandidate, pick,
              coe_eq_expr, heq, h3, h4, complex_eq_false_of_simple h1,
              complex_eq_false_of_simple h2]
        · exact hcond.elim
  case memoryIndexWriteStoreBox =>
    cases mode
    case diamond =>
      simp [Rules.ruleEffect, Rules.withMode, CaseMode.applies] at hmode
    case box =>
      cases stmt <;>
        simp only [Rules.ruleEffect, Rules.withMode, Rules.assignEffect]
          at hcond
      next lhs rhs =>
        split at hcond
        · next ty path idx heq =>
            obtain ⟨h1, h2, h3, h4⟩ := hcond
            simp only [Rules.isSimple, Rules.isStack] at h1 h2 h3 h4
            simp [candidate, assignCandidate, assignSimpleCandidate, pick,
              coe_eq_expr, heq, h3, h4, complex_eq_false_of_simple h1,
              complex_eq_false_of_simple h2,
              isMemory_eq_false_of_isStack h3]
        · exact hcond.elim
  case memoryIndexWriteCopyDiamond =>
    cases mode
    case box =>
      simp [Rules.ruleEffect, Rules.withMode, CaseMode.applies] at hmode
    case diamond =>
      cases stmt <;>
        simp only [Rules.ruleEffect, Rules.withMode, Rules.assignEffect]
          at hcond
      next lhs rhs =>
        split at hcond
        · next ty path idx heq =>
            obtain ⟨h1, h2, h3, h4⟩ := hcond
            simp only [Rules.isSimple, Rules.isMemory] at h1 h2 h3 h4
            simp [candidate, assignCandidate, assignSimpleCandidate, pick,
              coe_eq_expr, heq, h3, h4, complex_eq_false_of_simple h1,
              complex_eq_false_of_simple h2]
        · exact hcond.elim
  case memoryIndexWriteStoreDiamond =>
    cases mode
    case box =>
      simp [Rules.ruleEffect, Rules.withMode, CaseMode.applies] at hmode
    case diamond =>
      cases stmt <;>
        simp only [Rules.ruleEffect, Rules.withMode, Rules.assignEffect]
          at hcond
      next lhs rhs =>
        split at hcond
        · next ty path idx heq =>
            obtain ⟨h1, h2, h3, h4⟩ := hcond
            simp only [Rules.isSimple, Rules.isStack] at h1 h2 h3 h4
            simp [candidate, assignCandidate, assignSimpleCandidate, pick,
              coe_eq_expr, heq, h3, h4, complex_eq_false_of_simple h1,
              complex_eq_false_of_simple h2,
              isMemory_eq_false_of_isStack h3]
        · exact hcond.elim
  case storagePushLhsToPushValue =>
    cases stmt <;>
      simp only [Rules.ruleEffect, Rules.assignEffect] at hcond
    next lhs rhs =>
      split at hcond
      · next target heq =>
          obtain ⟨h1, h2⟩ := hcond
          simp only [Rules.isSimple] at h2
          simp [candidate, assignCandidate, assignSimpleCandidate, coe_eq_expr,
            heq, h1, h2]
      · exact hcond.elim
  case storageFieldReadUnfoldRightFst =>
    cases stmt <;>
      simp only [Rules.ruleEffect, Rules.assignEffect] at hcond
    next lhs rhs =>
      split at hcond
      · next ty path fld =>
          obtain ⟨h1, h2⟩ := hcond
          simp only [Rules.isComplex, PlaceExpr.kind, coe_eq_expr] at h1 h2
          simp [candidate, assignCandidate, assignComplexCandidate, coe_eq_expr,
            Typed.WrappedExpr.isMemory, h1, h2]
      · exact hcond.elim
  case storageFieldReadUnfoldRightSndResult =>
    cases stmt <;>
      simp only [Rules.ruleEffect, Rules.assignEffect] at hcond
    next lhs rhs =>
      split at hcond
      · next ty path fld =>
          obtain ⟨h1, h2, h3⟩ := hcond
          simp only [Rules.isStorage, Rules.isComplex, Rules.isSimple,
            coe_eq_expr] at h1 h2 h3
          simp [candidate, assignCandidate, assignComplexCandidate, coe_eq_expr,
            Typed.WrappedExpr.isMemory, Typed.WrappedExpr.isStorage,
            kind_of_isStorage h1, h2, complex_eq_false_of_simple h3]
      · exact hcond.elim
  case storageFieldReadFind =>
    cases stmt <;>
      simp only [Rules.ruleEffect, Rules.assignEffect] at hcond
    next lhs rhs =>
      split at hcond
      · next ty path fld =>
          obtain ⟨h1, h2⟩ := hcond
          simp only [Rules.isStack, Rules.isSimple, coe_eq_expr] at h1 h2
          simp [candidate, assignCandidate, assignComplexCandidate, coe_eq_expr,
            Typed.WrappedExpr.isMemory, Typed.WrappedExpr.isStorage,
            Typed.WrappedExpr.isStack, kind_of_isStack h1,
            complex_eq_false_of_simple h2]
      · exact hcond.elim
  case storageFieldReadBindLocalRoot =>
    cases stmt <;>
      simp only [Rules.ruleEffect, Rules.assignEffect] at hcond
    next lhs rhs =>
      split at hcond
      · next ty path fld =>
          obtain ⟨h1, h2⟩ := hcond
          simp only [Rules.isLocal, Rules.isSimple, coe_eq_expr] at h1 h2
          obtain ⟨ty', fld', heqL, horig⟩ := isLocal_shape h1
          simp [candidate, assignCandidate, assignComplexCandidate, coe_eq_expr,
            Typed.WrappedExpr.isMemory, Typed.WrappedExpr.isStorage,
            heqL, horig, complex_eq_false_of_simple h2]
      · exact hcond.elim
  case storageFieldReadStoreRoot =>
    cases stmt <;>
      simp only [Rules.ruleEffect, Rules.assignEffect] at hcond
    next lhs rhs =>
      split at hcond
      · next ty path fld =>
          obtain ⟨h1, h2, h3⟩ := hcond
          simp only [Rules.isSimple, Rules.isGlobal, coe_eq_expr] at h1 h2 h3
          obtain ⟨ty', fld', heqL, horig⟩ := isGlobal_shape h2
          simp [candidate, assignCandidate, assignComplexCandidate, coe_eq_expr,
            Typed.WrappedExpr.isMemory, Typed.WrappedExpr.isStorage,
            heqL, horig, complex_eq_false_of_simple h3]
      · exact hcond.elim
  case storageIndexReadUnfoldRightFst =>
    cases stmt <;>
      simp only [Rules.ruleEffect, Rules.assignEffect] at hcond
    next lhs rhs =>
      split at hcond
      · next ty path idx =>
          obtain ⟨h1, h2⟩ := hcond
          simp only [Rules.isComplex, PlaceExpr.kind, coe_eq_expr] at h1 h2
          simp [candidate, assignCandidate, assignComplexCandidate, coe_eq_expr,
            Typed.WrappedExpr.isMemory, h1, h2]
      · exact hcond.elim
  case storageIndexReadUnfoldRightSndIndex =>
    cases stmt <;>
      simp only [Rules.ruleEffect, Rules.assignEffect] at hcond
    next lhs rhs =>
      split at hcond
      · next ty path idx =>
          obtain ⟨h1, h2, h3⟩ := hcond
          simp only [Rules.isSimple, Rules.isComplex, PlaceExpr.kind,
            coe_eq_expr] at h1 h2 h3
          simp [candidate, assignCandidate, assignComplexCandidate, coe_eq_expr,
            Typed.WrappedExpr.isMemory, h2, h3,
            complex_eq_false_of_simple h1]
      · exact hcond.elim
  case storageIndexReadUnfoldRightSndResult =>
    cases stmt <;>
      simp only [Rules.ruleEffect, Rules.assignEffect] at hcond
    next lhs rhs =>
      split at hcond
      · next ty path idx =>
          obtain ⟨h1, h2, h3, h4⟩ := hcond
          simp only [Rules.isStorage, Rules.isComplex, Rules.isSimple,
            coe_eq_expr] at h1 h2 h3 h4
          simp [candidate, assignCandidate, assignComplexCandidate, coe_eq_expr,
            Typed.WrappedExpr.isMemory, Typed.WrappedExpr.isStorage,
            kind_of_isStorage h1, h2, complex_eq_false_of_simple h3,
            complex_eq_false_of_simple h4]
      · exact hcond.elim
  case storageIndexReadArrayFindBox =>
    cases mode
    case diamond =>
      simp [Rules.ruleEffect, Rules.withMode, CaseMode.applies] at hmode
    case box =>
      cases stmt <;>
        simp only [Rules.ruleEffect, Rules.withMode, Rules.assignEffect]
          at hcond
      next lhs rhs =>
        split at hcond
        · next ty path idx =>
            obtain ⟨h1, h2, h3, h4⟩ := hcond
            simp only [Rules.isStack, Rules.isSimple, coe_eq_expr] at h1 h2 h3
            simp [candidate, assignCandidate, assignComplexCandidate, pick,
              coe_eq_expr, Typed.WrappedExpr.isMemory,
              Typed.WrappedExpr.isStorage,
              Typed.WrappedExpr.isStack, kind_of_isStack h1,
              complex_eq_false_of_simple h2, complex_eq_false_of_simple h3,
              arrayTyB_of_isArray h4]
        · exact hcond.elim
  case storageIndexReadArrayFindDiamond =>
    cases mode
    case box =>
      simp [Rules.ruleEffect, Rules.withMode, CaseMode.applies] at hmode
    case diamond =>
      cases stmt <;>
        simp only [Rules.ruleEffect, Rules.withMode, Rules.assignEffect]
          at hcond
      next lhs rhs =>
        split at hcond
        · next ty path idx =>
            obtain ⟨h1, h2, h3, h4⟩ := hcond
            simp only [Rules.isStack, Rules.isSimple, coe_eq_expr] at h1 h2 h3
            simp [candidate, assignCandidate, assignComplexCandidate, pick,
              coe_eq_expr, Typed.WrappedExpr.isMemory,
              Typed.WrappedExpr.isStorage,
              Typed.WrappedExpr.isStack, kind_of_isStack h1,
              complex_eq_false_of_simple h2, complex_eq_false_of_simple h3,
              arrayTyB_of_isArray h4]
        · exact hcond.elim
  case storageIndexReadMappingFind =>
    cases stmt <;>
      simp only [Rules.ruleEffect, Rules.assignEffect] at hcond
    next lhs rhs =>
      split at hcond
      · next ty path idx =>
          obtain ⟨h1, h2, h3, h4⟩ := hcond
          simp only [Rules.isStack, Rules.isSimple, coe_eq_expr] at h1 h2 h3
          simp [candidate, assignCandidate, assignComplexCandidate, coe_eq_expr,
            Typed.WrappedExpr.isMemory, Typed.WrappedExpr.isStorage,
            Typed.WrappedExpr.isStack, kind_of_isStack h1,
            complex_eq_false_of_simple h2, complex_eq_false_of_simple h3,
            mappingTyB_of_isMapping h4, arrayTyB_eq_false_of_isMapping h4]
      · exact hcond.elim
  case storageIndexReadArrayBindLocalRootBox =>
    cases mode
    case diamond =>
      simp [Rules.ruleEffect, Rules.withMode, CaseMode.applies] at hmode
    case box =>
      cases stmt <;>
        simp only [Rules.ruleEffect, Rules.withMode, Rules.assignEffect]
          at hcond
      next lhs rhs =>
        split at hcond
        · next ty path idx =>
            obtain ⟨h1, h2, h3, h4⟩ := hcond
            simp only [Rules.isLocal, Rules.isSimple, coe_eq_expr] at h1 h2 h3
            obtain ⟨ty', fld', heqL, horig⟩ := isLocal_shape h1
            simp [candidate, assignCandidate, assignComplexCandidate, pick,
              coe_eq_expr, Typed.WrappedExpr.isMemory,
              Typed.WrappedExpr.isStorage,
              heqL, horig, complex_eq_false_of_simple h2,
              complex_eq_false_of_simple h3, arrayTyB_of_isArray h4]
        · exact hcond.elim
  case storageIndexReadArrayBindLocalRootDiamond =>
    cases mode
    case box =>
      simp [Rules.ruleEffect, Rules.withMode, CaseMode.applies] at hmode
    case diamond =>
      cases stmt <;>
        simp only [Rules.ruleEffect, Rules.withMode, Rules.assignEffect]
          at hcond
      next lhs rhs =>
        split at hcond
        · next ty path idx =>
            obtain ⟨h1, h2, h3, h4⟩ := hcond
            simp only [Rules.isLocal, Rules.isSimple, coe_eq_expr] at h1 h2 h3
            obtain ⟨ty', fld', heqL, horig⟩ := isLocal_shape h1
            simp [candidate, assignCandidate, assignComplexCandidate, pick,
              coe_eq_expr, Typed.WrappedExpr.isMemory,
              Typed.WrappedExpr.isStorage,
              heqL, horig, complex_eq_false_of_simple h2,
              complex_eq_false_of_simple h3, arrayTyB_of_isArray h4]
        · exact hcond.elim
  case storageIndexReadMappingBindLocalRoot =>
    cases stmt <;>
      simp only [Rules.ruleEffect, Rules.assignEffect] at hcond
    next lhs rhs =>
      split at hcond
      · next ty path idx =>
          obtain ⟨h1, h2, h3, h4⟩ := hcond
          simp only [Rules.isLocal, Rules.isSimple, coe_eq_expr] at h1 h2 h3
          obtain ⟨ty', fld', heqL, horig⟩ := isLocal_shape h1
          simp [candidate, assignCandidate, assignComplexCandidate, coe_eq_expr,
            Typed.WrappedExpr.isMemory, Typed.WrappedExpr.isStorage,
            heqL, horig, complex_eq_false_of_simple h2,
            complex_eq_false_of_simple h3, mappingTyB_of_isMapping h4,
            arrayTyB_eq_false_of_isMapping h4]
      · exact hcond.elim
  case storageIndexReadArrayStoreRootBox =>
    cases mode
    case diamond =>
      simp [Rules.ruleEffect, Rules.withMode, CaseMode.applies] at hmode
    case box =>
      cases stmt <;>
        simp only [Rules.ruleEffect, Rules.withMode, Rules.assignEffect]
          at hcond
      next lhs rhs =>
        split at hcond
        · next ty path idx =>
            obtain ⟨h1, h2, h3, h4, h5⟩ := hcond
            simp only [Rules.isSimple, Rules.isGlobal, coe_eq_expr]
              at h1 h2 h3 h4
            obtain ⟨ty', fld', heqL, horig⟩ := isGlobal_shape h2
            simp [candidate, assignCandidate, assignComplexCandidate, pick,
              coe_eq_expr, Typed.WrappedExpr.isMemory,
              Typed.WrappedExpr.isStorage,
              heqL, horig, complex_eq_false_of_simple h3,
              complex_eq_false_of_simple h4, arrayTyB_of_isArray h5]
        · exact hcond.elim
  case storageIndexReadArrayStoreRootDiamond =>
    cases mode
    case box =>
      simp [Rules.ruleEffect, Rules.withMode, CaseMode.applies] at hmode
    case diamond =>
      cases stmt <;>
        simp only [Rules.ruleEffect, Rules.withMode, Rules.assignEffect]
          at hcond
      next lhs rhs =>
        split at hcond
        · next ty path idx =>
            obtain ⟨h1, h2, h3, h4, h5⟩ := hcond
            simp only [Rules.isSimple, Rules.isGlobal, coe_eq_expr]
              at h1 h2 h3 h4
            obtain ⟨ty', fld', heqL, horig⟩ := isGlobal_shape h2
            simp [candidate, assignCandidate, assignComplexCandidate, pick,
              coe_eq_expr, Typed.WrappedExpr.isMemory,
              Typed.WrappedExpr.isStorage,
              heqL, horig, complex_eq_false_of_simple h3,
              complex_eq_false_of_simple h4, arrayTyB_of_isArray h5]
        · exact hcond.elim
  case storageIndexReadMappingStoreRoot =>
    cases stmt <;>
      simp only [Rules.ruleEffect, Rules.assignEffect] at hcond
    next lhs rhs =>
      split at hcond
      · next ty path idx =>
          obtain ⟨h1, h2, h3, h4, h5⟩ := hcond
          simp only [Rules.isSimple, Rules.isGlobal, coe_eq_expr] at h1 h2 h3 h4
          obtain ⟨ty', fld', heqL, horig⟩ := isGlobal_shape h2
          simp [candidate, assignCandidate, assignComplexCandidate, coe_eq_expr,
            Typed.WrappedExpr.isMemory, Typed.WrappedExpr.isStorage,
            heqL, horig, complex_eq_false_of_simple h3,
            complex_eq_false_of_simple h4,
            mappingTyB_of_isMapping h5, arrayTyB_eq_false_of_isMapping h5]
      · exact hcond.elim
  case memoryFieldReadUnfoldRightFst =>
    cases stmt <;>
      simp only [Rules.ruleEffect, Rules.assignEffect] at hcond
    next lhs rhs =>
      split at hcond
      · next ty path fld =>
          obtain ⟨h1, h2⟩ := hcond
          simp only [Rules.isComplex, Rules.isStorage, PlaceExpr.kind,
            coe_eq_expr] at h1 h2
          rw [Bool.not_eq_true] at h2
          simp [candidate, assignCandidate, assignComplexCandidate, coe_eq_expr,
            Typed.WrappedExpr.isMemory, h1, not_kind_storage h2]
      · exact hcond.elim
  case memoryFieldReadHeap =>
    cases stmt <;>
      simp only [Rules.ruleEffect, Rules.assignEffect] at hcond
    next lhs rhs =>
      split at hcond
      · next ty path fld =>
          obtain ⟨h1, h2⟩ := hcond
          simp only [Rules.isStack, Rules.isSimple, coe_eq_expr] at h1 h2
          simp [candidate, assignCandidate, assignComplexCandidate, coe_eq_expr,
            Typed.WrappedExpr.isMemory, Typed.WrappedExpr.isStack,
            kind_of_isStack h1, complex_eq_false_of_simple h2]
      · exact hcond.elim
  case memoryFieldReadAliasRoot =>
    cases stmt <;>
      simp only [Rules.ruleEffect, Rules.assignEffect] at hcond
    next lhs rhs =>
      split at hcond
      · next ty path fld =>
          obtain ⟨h1, h2, h3⟩ := hcond
          simp only [Rules.isSimple, PlaceExpr.kind, coe_eq_expr] at h1 h2 h3
          simp [candidate, assignCandidate, assignComplexCandidate, coe_eq_expr,
            Typed.WrappedExpr.isMemory, Typed.WrappedExpr.isStack,
            h1, complex_eq_false_of_simple h2, complex_eq_false_of_simple h3]
      · exact hcond.elim
  case memoryFieldReadUnfoldRightSndResult =>
    cases stmt <;>
      simp only [Rules.ruleEffect, Rules.assignEffect] at hcond
    next lhs rhs =>
      split at hcond
      · next ty path fld =>
          obtain ⟨h1, h2, h3⟩ := hcond
          simp only [Rules.isMemory, Rules.isComplex, Rules.isSimple,
            PlaceExpr.kind, coe_eq_expr] at h1 h2 h3
          simp [candidate, assignCandidate, assignComplexCandidate, coe_eq_expr,
            kind_of_isMemory h1, h2, complex_eq_false_of_simple h3]
      · exact hcond.elim
  case memoryIndexReadUnfoldRightFst =>
    cases stmt <;>
      simp only [Rules.ruleEffect, Rules.assignEffect] at hcond
    next lhs rhs =>
      split at hcond
      · next ty path idx =>
          obtain ⟨h1, h2⟩ := hcond
          simp only [Rules.isComplex, Rules.isStorage, PlaceExpr.kind,
            coe_eq_expr] at h1 h2
          rw [Bool.not_eq_true] at h2
          simp [candidate, assignCandidate, assignComplexCandidate, coe_eq_expr,
            Typed.WrappedExpr.isMemory, h1, not_kind_storage h2]
      · exact hcond.elim
  case memoryIndexReadUnfoldRightSndIndex =>
    cases stmt <;>
      simp only [Rules.ruleEffect, Rules.assignEffect] at hcond
    next lhs rhs =>
      split at hcond
      · next ty path idx =>
          obtain ⟨h1, h2, h3⟩ := hcond
          simp only [Rules.isSimple, Rules.isComplex, Rules.isStorage,
            PlaceExpr.kind, coe_eq_expr] at h1 h2 h3
          rw [Bool.not_eq_true] at h3
          simp [candidate, assignCandidate, assignComplexCandidate, coe_eq_expr,
            Typed.WrappedExpr.isMemory, h2, not_kind_storage h3,
            complex_eq_false_of_simple h1]
      · exact hcond.elim
  case memoryIndexReadHeapBox =>
    cases mode
    case diamond =>
      simp [Rules.ruleEffect, Rules.withMode, CaseMode.applies] at hmode
    case box =>
      cases stmt <;>
        simp only [Rules.ruleEffect, Rules.withMode, Rules.assignEffect]
          at hcond
      next lhs rhs =>
        split at hcond
        · next ty path idx =>
            obtain ⟨h1, h2, h3⟩ := hcond
            simp only [Rules.isStack, Rules.isSimple, coe_eq_expr] at h1 h2 h3
            simp [candidate, assignCandidate, assignComplexCandidate, pick,
              coe_eq_expr, Typed.WrappedExpr.isMemory,
              Typed.WrappedExpr.isStack,
              kind_of_isStack h1, complex_eq_false_of_simple h2,
              complex_eq_false_of_simple h3]
        · exact hcond.elim
  case memoryIndexReadHeapDiamond =>
    cases mode
    case box =>
      simp [Rules.ruleEffect, Rules.withMode, CaseMode.applies] at hmode
    case diamond =>
      cases stmt <;>
        simp only [Rules.ruleEffect, Rules.withMode, Rules.assignEffect]
          at hcond
      next lhs rhs =>
        split at hcond
        · next ty path idx =>
            obtain ⟨h1, h2, h3⟩ := hcond
            simp only [Rules.isStack, Rules.isSimple, coe_eq_expr] at h1 h2 h3
            simp [candidate, assignCandidate, assignComplexCandidate, pick,
              coe_eq_expr, Typed.WrappedExpr.isMemory,
              Typed.WrappedExpr.isStack,
              kind_of_isStack h1, complex_eq_false_of_simple h2,
              complex_eq_false_of_simple h3]
        · exact hcond.elim
  case memoryIndexReadAliasRootBox =>
    cases mode
    case diamond =>
      simp [Rules.ruleEffect, Rules.withMode, CaseMode.applies] at hmode
    case box =>
      cases stmt <;>
        simp only [Rules.ruleEffect, Rules.withMode, Rules.assignEffect]
          at hcond
      next lhs rhs =>
        split at hcond
        · next ty path idx =>
            obtain ⟨h1, h2, h3, h4⟩ := hcond
            simp only [Rules.isSimple, PlaceExpr.kind, coe_eq_expr]
              at h1 h2 h3 h4
            simp [candidate, assignCandidate, assignComplexCandidate, pick,
              coe_eq_expr, Typed.WrappedExpr.isMemory,
              Typed.WrappedExpr.isStack, h1, complex_eq_false_of_simple h2,
              complex_eq_false_of_simple h3, complex_eq_false_of_simple h4]
        · exact hcond.elim
  case memoryIndexReadAliasRootDiamond =>
    cases mode
    case box =>
      simp [Rules.ruleEffect, Rules.withMode, CaseMode.applies] at hmode
    case diamond =>
      cases stmt <;>
        simp only [Rules.ruleEffect, Rules.withMode, Rules.assignEffect]
          at hcond
      next lhs rhs =>
        split at hcond
        · next ty path idx =>
            obtain ⟨h1, h2, h3, h4⟩ := hcond
            simp only [Rules.isSimple, PlaceExpr.kind, coe_eq_expr]
              at h1 h2 h3 h4
            simp [candidate, assignCandidate, assignComplexCandidate, pick,
              coe_eq_expr, Typed.WrappedExpr.isMemory,
              Typed.WrappedExpr.isStack, h1, complex_eq_false_of_simple h2,
              complex_eq_false_of_simple h3, complex_eq_false_of_simple h4]
        · exact hcond.elim
  case memoryIndexReadUnfoldRightSndResult =>
    cases stmt <;>
      simp only [Rules.ruleEffect, Rules.assignEffect] at hcond
    next lhs rhs =>
      split at hcond
      · next ty path idx =>
          obtain ⟨h1, h2, h3, h4⟩ := hcond
          simp only [Rules.isMemory, Rules.isComplex, Rules.isSimple,
            PlaceExpr.kind, coe_eq_expr] at h1 h2 h3 h4
          simp [candidate, assignCandidate, assignComplexCandidate, coe_eq_expr,
            kind_of_isMemory h1, h2, complex_eq_false_of_simple h3,
            complex_eq_false_of_simple h4]
      · exact hcond.elim
  case storageLocalRootPushUnfoldLeftFstReceiver =>
    cases stmt <;>
      simp only [Rules.ruleEffect, Rules.assignEffect] at hcond
    next lhs rhs =>
      split at hcond
      · next target =>
          obtain ⟨h1, h2, h3⟩ := hcond
          simp only [Rules.isComplex, PlaceExpr.kind, coe_eq_expr] at h2 h3
          simp [candidate, assignCandidate, assignComplexCandidate, coe_eq_expr,
            Typed.WrappedExpr.isMemory, h1, h2, h3]
      · exact hcond.elim
  case storageLocalRootPushBind =>
    cases stmt <;>
      simp only [Rules.ruleEffect, Rules.assignEffect] at hcond
    next lhs rhs =>
      split at hcond
      · next target =>
          obtain ⟨h1, h2, h3⟩ := hcond
          simp only [Rules.isLocal, Rules.isSimple, coe_eq_expr] at h1 h3
          obtain ⟨ty', fld', heqL, horig⟩ := isLocal_shape h1
          simp [candidate, assignCandidate, assignComplexCandidate, coe_eq_expr,
            Typed.WrappedExpr.isMemory, Typed.WrappedExpr.isStorage,
            heqL, horig, complex_eq_false_of_simple h3]
      · exact hcond.elim
  case storageLocalRootRebind =>
    cases stmt <;>
      simp only [Rules.ruleEffect, Rules.assignEffect] at hcond
    next lhs rhs =>
      obtain ⟨h1, h2, h3⟩ := hcond
      simp only [Rules.isLocal, Rules.isStorage, Rules.isSimple,
        coe_eq_expr] at h1 h2 h3
      obtain ⟨ty', fld', heqL, horig⟩ := isLocal_shape h1
      simp [candidate, assignCandidate, assignSimpleCandidate, coe_eq_expr,
        heqL, horig, h2, h3]
  case storageRootWriteCopySource =>
    cases stmt <;>
      simp only [Rules.ruleEffect, Rules.assignEffect] at hcond
    next lhs rhs =>
      obtain ⟨h1, h2, h3⟩ := hcond
      simp only [Rules.isGlobal, Rules.isStorage, Rules.isSimple,
        coe_eq_expr] at h1 h2 h3
      obtain ⟨ty', fld', heqL, horig⟩ := isGlobal_shape h1
      simp [candidate, assignCandidate, assignSimpleCandidate, coe_eq_expr,
        heqL, horig, h2, h3]
  case storageRootWriteStore =>
    cases stmt <;>
      simp only [Rules.ruleEffect, Rules.assignEffect] at hcond
    next lhs rhs =>
      obtain ⟨h1, h2, h3⟩ := hcond
      simp only [Rules.isGlobal, Rules.isStack, Rules.isSimple,
        coe_eq_expr] at h1 h2 h3
      obtain ⟨ty', fld', heqL, horig⟩ := isGlobal_shape h1
      simp [candidate, assignCandidate, assignSimpleCandidate, coe_eq_expr,
        heqL, horig, h2, h3, isStorage_eq_false_of_isStack h2]
  case storageRootWriteValueRhsCapture =>
    cases stmt <;>
      simp only [Rules.ruleEffect, Rules.assignEffect] at hcond
    next lhs rhs =>
      obtain ⟨h1, h2⟩ := hcond
      simp only [Rules.isGlobal, coe_eq_expr] at h1
      obtain ⟨ty', fld', heqL, horig⟩ := isGlobal_shape h1
      cases rhs with
      | mkBinop op l r =>
          simp only [Rules.valueRhsCaptureRhs] at h2
          have hb : (op.isArith && l.simple && r.simple) = false := by
            simp only [Rules.isSimple] at h2
            cases hia : op.isArith <;> cases hls : l.simple <;>
              cases hrs : r.simple <;> simp_all
          simp [candidate, assignCandidate, assignComplexCandidate,
            valueRhsCaptureCandidate, coe_eq_expr, heqL, horig, hb,
            Typed.WrappedExpr.simple, Typed.WrappedExpr.kind,
            Typed.WrappedExpr.isStack, Typed.WrappedExpr.isMemory,
            Typed.WrappedExpr.complex]
          intro hia hls
          show Typed.WrappedExpr.simple r = false
          cases hrs : Typed.WrappedExpr.simple r
          · rfl
          · exact absurd
              ⟨hia, (show Typed.WrappedExpr.simple l = true from hls), hrs⟩ h2
      | mkUnop op arg =>
          simp [candidate, assignCandidate, assignComplexCandidate,
            valueRhsCaptureCandidate, coe_eq_expr, heqL, horig,
            Typed.WrappedExpr.simple, Typed.WrappedExpr.kind,
            Typed.WrappedExpr.isStack, Typed.WrappedExpr.isMemory,
            Typed.WrappedExpr.complex]
      | mkIncDec op target =>
          simp [candidate, assignCandidate, assignComplexCandidate,
            valueRhsCaptureCandidate, coe_eq_expr, heqL, horig,
            Typed.WrappedExpr.simple, Typed.WrappedExpr.kind,
            Typed.WrappedExpr.isStack, Typed.WrappedExpr.isMemory,
            Typed.WrappedExpr.complex]
      | var kind ty fld => simp [Rules.valueRhsCaptureRhs] at h2
      | field kind ty base fld =>
          simp [Rules.valueRhsCaptureRhs] at h2
      | index kind ty base index =>
          simp [Rules.valueRhsCaptureRhs] at h2
      | pushPlace target =>
          simp [Rules.valueRhsCaptureRhs] at h2
      | bool b => simp [Rules.valueRhsCaptureRhs] at h2
      | intLit ty v => simp [Rules.valueRhsCaptureRhs] at h2
      | mkCall kind ty name args =>
          simp [Rules.valueRhsCaptureRhs] at h2
      | mkTernary c t e =>
          simp [Rules.valueRhsCaptureRhs] at h2
  case fieldWriteValueRhsCapture =>
    cases stmt <;>
      simp only [Rules.ruleEffect, Rules.assignEffect] at hcond
    next lhs rhs =>
      split at hcond
      · next ty path fld heq =>
          cases rhs with
          | mkBinop op l r =>
              simp only [Rules.valueRhsCaptureRhs] at hcond
              have hb : (op.isArith && l.simple && r.simple) = false := by
                simp only [Rules.isSimple] at hcond
                cases hia : op.isArith <;> cases hls : l.simple <;>
                  cases hrs : r.simple <;> simp_all
              simp [candidate, assignCandidate, assignComplexCandidate,
                valueRhsCaptureCandidate, coe_eq_expr, heq, hb,
                Typed.WrappedExpr.simple, Typed.WrappedExpr.kind,
                Typed.WrappedExpr.isStack, Typed.WrappedExpr.isMemory,
                Typed.WrappedExpr.complex]
              intro hia hls
              show Typed.WrappedExpr.simple r = false
              cases hrs : Typed.WrappedExpr.simple r
              · rfl
              · exact absurd
                  ⟨hia, (show Typed.WrappedExpr.simple l = true from hls),
                    hrs⟩ hcond
          | mkUnop op arg =>
              simp [candidate, assignCandidate, assignComplexCandidate,
                valueRhsCaptureCandidate, coe_eq_expr, heq,
                Typed.WrappedExpr.simple, Typed.WrappedExpr.kind,
                Typed.WrappedExpr.isStack, Typed.WrappedExpr.isMemory,
                Typed.WrappedExpr.complex]
          | mkIncDec op target =>
              simp [candidate, assignCandidate, assignComplexCandidate,
                valueRhsCaptureCandidate, coe_eq_expr, heq,
                Typed.WrappedExpr.simple, Typed.WrappedExpr.kind,
                Typed.WrappedExpr.isStack, Typed.WrappedExpr.isMemory,
                Typed.WrappedExpr.complex]
          | var kind ty fld =>
              simp [Rules.valueRhsCaptureRhs] at hcond
          | field kind ty base fld =>
              simp [Rules.valueRhsCaptureRhs] at hcond
          | index kind ty base index =>
              simp [Rules.valueRhsCaptureRhs] at hcond
          | pushPlace target =>
              simp [Rules.valueRhsCaptureRhs] at hcond
          | bool b => simp [Rules.valueRhsCaptureRhs] at hcond
          | intLit ty v =>
              simp [Rules.valueRhsCaptureRhs] at hcond
          | mkCall kind ty name args =>
              simp [Rules.valueRhsCaptureRhs] at hcond
          | mkTernary c t e =>
              simp [Rules.valueRhsCaptureRhs] at hcond
      · exact hcond.elim
  case indexWriteValueRhsCapture =>
    cases stmt <;>
      simp only [Rules.ruleEffect, Rules.assignEffect] at hcond
    next lhs rhs =>
      split at hcond
      · next ty path index heq =>
          cases rhs with
          | mkBinop op l r =>
              simp only [Rules.valueRhsCaptureRhs] at hcond
              have hb : (op.isArith && l.simple && r.simple) = false := by
                simp only [Rules.isSimple] at hcond
                cases hia : op.isArith <;> cases hls : l.simple <;>
                  cases hrs : r.simple <;> simp_all
              simp [candidate, assignCandidate, assignComplexCandidate,
                valueRhsCaptureCandidate, coe_eq_expr, heq, hb,
                Typed.WrappedExpr.simple, Typed.WrappedExpr.kind,
                Typed.WrappedExpr.isStack, Typed.WrappedExpr.isMemory,
                Typed.WrappedExpr.complex]
              intro hia hls
              show Typed.WrappedExpr.simple r = false
              cases hrs : Typed.WrappedExpr.simple r
              · rfl
              · exact absurd
                  ⟨hia, (show Typed.WrappedExpr.simple l = true from hls),
                    hrs⟩ hcond
          | mkUnop op arg =>
              simp [candidate, assignCandidate, assignComplexCandidate,
                valueRhsCaptureCandidate, coe_eq_expr, heq,
                Typed.WrappedExpr.simple, Typed.WrappedExpr.kind,
                Typed.WrappedExpr.isStack, Typed.WrappedExpr.isMemory,
                Typed.WrappedExpr.complex]
          | mkIncDec op target =>
              simp [candidate, assignCandidate, assignComplexCandidate,
                valueRhsCaptureCandidate, coe_eq_expr, heq,
                Typed.WrappedExpr.simple, Typed.WrappedExpr.kind,
                Typed.WrappedExpr.isStack, Typed.WrappedExpr.isMemory,
                Typed.WrappedExpr.complex]
          | var kind ty fld =>
              simp [Rules.valueRhsCaptureRhs] at hcond
          | field kind ty base fld =>
              simp [Rules.valueRhsCaptureRhs] at hcond
          | index kind ty base index =>
              simp [Rules.valueRhsCaptureRhs] at hcond
          | pushPlace target =>
              simp [Rules.valueRhsCaptureRhs] at hcond
          | bool b => simp [Rules.valueRhsCaptureRhs] at hcond
          | intLit ty v =>
              simp [Rules.valueRhsCaptureRhs] at hcond
          | mkCall kind ty name args =>
              simp [Rules.valueRhsCaptureRhs] at hcond
          | mkTernary c t e =>
              simp [Rules.valueRhsCaptureRhs] at hcond
      · exact hcond.elim
  case storageRootReadSelect =>
    cases stmt <;>
      simp only [Rules.ruleEffect, Rules.assignEffect] at hcond
    next lhs rhs =>
      obtain ⟨h1, h2, h3⟩ := hcond
      simp only [Rules.isStack, Rules.isStorage, Rules.isSimple,
        coe_eq_expr] at h1 h2 h3
      obtain ⟨lexpr, hassign⟩ := lhs
      cases lexpr <;>
        simp_all [candidate, assignCandidate, assignSimpleCandidate,
          coe_eq_expr, Typed.WrappedExpr.isStack, Typed.WrappedExpr.isStorage,
          PlaceExpr.expr]
  case memoryWriteUnfoldRightSndResult =>
    cases stmt <;>
      simp only [Rules.ruleEffect, Rules.assignEffect] at hcond
    next lhs rhs =>
      obtain ⟨h1, h2, h3, h4⟩ := hcond
      simp only [Rules.isComplex, PlaceExpr.kind, coe_eq_expr] at h1 h2 h3
      simp only [candidate, assignCandidate, assignComplexCandidate, coe_eq_expr,
        h1, h2, simple_eq_false_of_complex h3, ite_true, Bool.true_and]
      split <;> simp_all
      split <;> simp_all
  case memoryRootAlias =>
    cases stmt <;>
      simp only [Rules.ruleEffect, Rules.assignEffect] at hcond
    next lhs rhs =>
      obtain ⟨h1, h2, h3, h4⟩ := hcond
      simp only [Rules.isSimple, Rules.isMemory, PlaceExpr.kind,
        coe_eq_expr] at h1 h2 h3 h4
      obtain ⟨ty', fld', heqM⟩ := simple_memory_shape h2 h1
      simp [candidate, assignCandidate, assignSimpleCandidate, coe_eq_expr,
        heqM, h3, h4]
  case memoryStorageCopy =>
    cases stmt <;>
      simp only [Rules.ruleEffect, Rules.assignEffect] at hcond
    next lhs rhs =>
      obtain ⟨h1, h2, h3, h4⟩ := hcond
      simp only [Rules.isSimple, Rules.isStorage, PlaceExpr.kind,
        coe_eq_expr] at h1 h2 h3 h4
      obtain ⟨ty', fld', heqM⟩ := simple_memory_shape h2 h1
      simp [candidate, assignCandidate, assignSimpleCandidate, coe_eq_expr,
        heqM, h3, h4, isMemory_eq_false_of_isStorage h3]
  case memoryStorageCopyUnfold =>
    cases stmt <;>
      simp only [Rules.ruleEffect, Rules.assignEffect] at hcond
    next lhs rhs =>
      obtain ⟨h1, h2, h3⟩ := hcond
      simp only [Rules.isSimple, PlaceExpr.kind, coe_eq_expr] at h1 h2
      obtain ⟨ty', fld', heqM⟩ := simple_memory_shape h2 h1
      cases rhs with
      | field kind ty base fld =>
          match kind, h3 with
          | Kind.storage, h3 =>
              simp only [Rules.isSimple, WrappedExpr.simple,
                Typed.WrappedExpr.simple] at h3
              simp [candidate, assignCandidate, assignComplexCandidate,
                coe_eq_expr, heqM, h3,
                Typed.WrappedExpr.simple, Typed.WrappedExpr.kind,
                Typed.WrappedExpr.isStorage, Typed.WrappedExpr.isMemory,
                Typed.WrappedExpr.isStack, Typed.WrappedExpr.complex]
      | index kind ty base index =>
          match kind, h3 with
          | Kind.storage, h3 =>
              obtain ⟨h3b, h3i⟩ := h3
              simp only [Rules.isSimple, WrappedExpr.simple,
                Typed.WrappedExpr.simple] at h3b h3i
              simp [candidate, assignCandidate, assignComplexCandidate,
                coe_eq_expr, heqM, h3b, h3i,
                Typed.WrappedExpr.simple, Typed.WrappedExpr.kind,
                Typed.WrappedExpr.isStorage, Typed.WrappedExpr.isMemory,
                Typed.WrappedExpr.isStack, Typed.WrappedExpr.complex]
      | var kind ty fld => exact h3.elim
      | pushPlace t => exact h3.elim
      | bool b => exact h3.elim
      | intLit ty v => exact h3.elim
      | mkCall kind ty name args => exact h3.elim
      | mkBinop op l r => exact h3.elim
      | mkUnop op arg => exact h3.elim
      | mkIncDec op target => exact h3.elim
      | mkTernary c t e => exact h3.elim
  case memoryToStorageUnfoldRightFstSource =>
    cases stmt <;>
      simp only [Rules.ruleEffect, Rules.assignEffect] at hcond
    next lhs rhs =>
      obtain ⟨h1, h2, h3⟩ := hcond
      simp only [Rules.isMemory, Rules.isComplex, PlaceExpr.kind,
        coe_eq_expr] at h1 h2 h3
      simp [candidate, assignCandidate, assignComplexCandidate, coe_eq_expr,
        h1, h2, simple_eq_false_of_complex h3]
  case memoryToStorageStoreRoot =>
    cases stmt <;>
      simp only [Rules.ruleEffect, Rules.assignEffect] at hcond
    next lhs rhs =>
      obtain ⟨h1, h2, h3, h4⟩ := hcond
      simp only [Rules.isStorage, Rules.isSimple, Rules.isMemory,
        coe_eq_expr] at h1 h2 h3 h4
      obtain ⟨ty', fld', heqS⟩ := simple_storage_shape h2 (kind_of_isStorage h1)
      simp [candidate, assignCandidate, assignSimpleCandidate, coe_eq_expr,
        heqS, h3, h4, isStorage_eq_false_of_isMemory h3,
        isStack_eq_false_of_isMemory h3]
  case localValueDeclInitDrop =>
    cases stmt <;>
      simp only [Rules.ruleEffect, Rules.stackDeclEffect] at hcond
    next ty name init =>
      simp [candidate, hcond]
  case valueDeclSkip =>
    cases stmt <;>
      simp only [Rules.ruleEffect, Rules.stackDeclEffect] at hcond
    next ty name init =>
      simp [candidate, hcond]
  case localValueAssign =>
    cases stmt <;>
      simp only [Rules.ruleEffect, Rules.assignEffect] at hcond
    next lhs rhs =>
      obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hcond
      simp only [Rules.isStack, Rules.isSimple, coe_eq_expr] at h1 h2 h3 h4
      obtain ⟨lexpr, hassign⟩ := lhs
      cases lexpr <;>
        simp_all [candidate, assignCandidate, assignSimpleCandidate,
          coe_eq_expr, Typed.WrappedExpr.isStack, Typed.WrappedExpr.isStorage,
          PlaceExpr.expr]
  case binopUnfoldLeft op =>
    cases stmt <;>
      simp only [Rules.ruleEffect, Rules.assignEffect] at hcond
    next lhs rhs =>
      split at hcond
      · next op' l r =>
          obtain ⟨rfl, ⟨h1, h2⟩, h3⟩ := hcond
          simp only [Rules.isStack, Rules.isSimple, Rules.isComplex,
            coe_eq_expr] at h1 h2 h3
          simp [candidate, assignCandidate, assignComplexCandidate,
            coe_eq_expr, h1, h2, h3, kind_of_isStack h1]
      · exact hcond.elim
  case binopUnfoldRight op =>
    cases stmt <;>
      simp only [Rules.ruleEffect, Rules.assignEffect] at hcond
    next lhs rhs =>
      split at hcond
      · next op' l r =>
          obtain ⟨rfl, hsc, ⟨h1, h2⟩, h3, h4⟩ := hcond
          simp only [Rules.isStack, Rules.isSimple, Rules.isComplex,
            coe_eq_expr] at h1 h2 h3 h4
          simp only [candidate, assignCandidate, assignComplexCandidate,
            coe_eq_expr, h1, h2, h4, kind_of_isStack h1,
            complex_eq_false_of_simple h3]
          cases op' <;> simp_all [BinOp.shortCircuits]
      · exact hcond.elim
  case logicalAndShortCircuitRhs =>
    cases stmt <;>
      simp only [Rules.ruleEffect, Rules.assignEffect] at hcond
    next lhs rhs =>
      split at hcond
      · next op' l r =>
          obtain ⟨rfl, ⟨h1, h2⟩, h3, h4⟩ := hcond
          simp only [Rules.isStack, Rules.isSimple, Rules.isComplex,
            coe_eq_expr] at h1 h2 h3 h4
          simp [candidate, assignCandidate, assignComplexCandidate,
            coe_eq_expr, h1, h2, h4, kind_of_isStack h1,
            complex_eq_false_of_simple h3]
      · exact hcond.elim
  case logicalOrShortCircuitRhs =>
    cases stmt <;>
      simp only [Rules.ruleEffect, Rules.assignEffect] at hcond
    next lhs rhs =>
      split at hcond
      · next op' l r =>
          obtain ⟨rfl, ⟨h1, h2⟩, h3, h4⟩ := hcond
          simp only [Rules.isStack, Rules.isSimple, Rules.isComplex,
            coe_eq_expr] at h1 h2 h3 h4
          simp [candidate, assignCandidate, assignComplexCandidate,
            coe_eq_expr, h1, h2, h4, kind_of_isStack h1,
            complex_eq_false_of_simple h3]
      · exact hcond.elim
  case binopUnfoldResult op =>
    cases stmt <;>
      simp only [Rules.ruleEffect, Rules.assignEffect] at hcond
    next lhs rhs =>
      split at hcond
      · next op' l r =>
          obtain ⟨rfl, harith, hnsv, hnmem, h3, h4⟩ := hcond
          simp only [Rules.isStackVar, Rules.isStack, Rules.isSimple,
            Rules.isComplex, PlaceExpr.kind, coe_eq_expr] at hnsv hnmem h3 h4
          simp [candidate, assignCandidate, assignComplexCandidate,
            coe_eq_expr, Typed.WrappedExpr.isMemory, harith, h3, h4,
            hnsv, hnmem, complex_eq_false_of_simple h3,
            complex_eq_false_of_simple h4]
      · exact hcond.elim
  case binopAssignment op =>
    cases stmt <;>
      simp only [Rules.ruleEffect, Rules.assignEffect] at hcond
    next lhs rhs =>
      split at hcond
      · next op' l r =>
          obtain ⟨rfl, ⟨h1, h2⟩, h3, h4⟩ := hcond
          simp only [Rules.isStack, Rules.isSimple, coe_eq_expr] at h1 h2 h3 h4
          simp [candidate, assignCandidate, assignComplexCandidate,
            coe_eq_expr, h1, h2, kind_of_isStack h1,
            complex_eq_false_of_simple h3, complex_eq_false_of_simple h4]
      · exact hcond.elim
  case unopCapture op =>
    cases stmt <;>
      simp only [Rules.ruleEffect, Rules.assignEffect] at hcond
    next lhs rhs =>
      split at hcond
      · next op' arg =>
          obtain ⟨rfl, ⟨h1, h2⟩, h3⟩ := hcond
          simp only [Rules.isStack, Rules.isSimple, Rules.isComplex,
            coe_eq_expr] at h1 h2 h3
          simp [candidate, assignCandidate, assignComplexCandidate,
            coe_eq_expr, h1, h2, h3, kind_of_isStack h1]
      · exact hcond.elim
  case unopAssignment op =>
    cases stmt <;>
      simp only [Rules.ruleEffect, Rules.assignEffect] at hcond
    next lhs rhs =>
      split at hcond
      · next op' arg =>
          obtain ⟨rfl, ⟨h1, h2⟩, h3⟩ := hcond
          simp only [Rules.isStack, Rules.isSimple, coe_eq_expr] at h1 h2 h3
          simp [candidate, assignCandidate, assignComplexCandidate,
            coe_eq_expr, h1, h2, kind_of_isStack h1,
            complex_eq_false_of_simple h3]
      · exact hcond.elim
  case ternaryCaptureCond =>
    cases stmt <;>
      simp only [Rules.ruleEffect, Rules.assignEffect] at hcond
    next lhs rhs =>
      split at hcond
      · next c t e =>
          obtain ⟨h1, hnm⟩ := hcond
          simp only [Rules.isComplex, PlaceExpr.kind, coe_eq_expr]
            at h1 hnm
          simp [candidate, assignCandidate, assignComplexCandidate,
            coe_eq_expr, h1, hnm, Typed.WrappedExpr.isMemory]
      · exact hcond.elim
  case ternaryToIf =>
    cases stmt <;>
      simp only [Rules.ruleEffect, Rules.assignEffect] at hcond
    next lhs rhs =>
      split at hcond
      · next c t e =>
          obtain ⟨h1, h2, h3⟩ := hcond
          simp only [Rules.isSimple, Rules.isStack, coe_eq_expr] at h1 h2 h3
          simp [candidate, assignCandidate, assignComplexCandidate,
            coe_eq_expr, h2, h3, kind_of_isStack h2,
            Typed.WrappedExpr.isMemory, complex_eq_false_of_simple h1]
      · exact hcond.elim
  case ternaryToIfStorage =>
    cases stmt <;>
      simp only [Rules.ruleEffect, Rules.assignEffect] at hcond
    next lhs rhs =>
      split at hcond
      · next c t e =>
          obtain ⟨h1, h2⟩ := hcond
          simp only [Rules.isSimple, Rules.isStorage, coe_eq_expr] at h1 h2
          simp [candidate, assignCandidate, assignComplexCandidate,
            coe_eq_expr, h2, kind_of_isStorage h2,
            isStack_eq_false_of_isStorage h2, Typed.WrappedExpr.isMemory,
            complex_eq_false_of_simple h1]
      · exact hcond.elim
  case storageRootCompoundAssign op =>
    cases stmt <;>
      simp only [Rules.ruleEffect, Rules.compoundAssignEffect] at hcond
    next opS lhs rhs =>
      obtain ⟨rfl, hca, hg, h3, h4⟩ := hcond
      simp only [Rules.isGlobal, Rules.isStack, Rules.isSimple,
        coe_eq_expr] at hg h3 h4
      obtain ⟨ty', fld', heqL, horig⟩ := isGlobal_shape hg
      have hLs : (WrappedExpr.var Kind.storage ty' fld' :
          WrappedExpr).isStack = false := rfl
      simp [candidate, compoundAssignCandidate, coe_eq_expr, heqL, horig,
        hca, h3, h4, hLs]
  case storageFieldCompoundAssign op =>
    cases stmt <;>
      simp only [Rules.ruleEffect, Rules.compoundAssignEffect] at hcond
    next opS lhs rhs =>
      split at hcond
      · next ty path fld heq =>
          obtain ⟨rfl, hca, h2, h3, h4⟩ := hcond
          simp only [Rules.isSimple, Rules.isStack, coe_eq_expr] at h2 h3 h4
          simp [candidate, compoundAssignCandidate, coe_eq_expr, heq, hca,
            h3, h4, complex_eq_false_of_simple h2]
      · exact hcond.elim
  case storageIndexCompoundAssign op =>
    cases stmt <;>
      simp only [Rules.ruleEffect, Rules.compoundAssignEffect] at hcond
    next opS lhs rhs =>
      split at hcond
      · next ty path index heq =>
          obtain ⟨rfl, hca, h2, h3, h4, h5⟩ := hcond
          simp only [Rules.isSimple, Rules.isStack, coe_eq_expr] at h2 h3 h4 h5
          simp [candidate, compoundAssignCandidate, coe_eq_expr, heq, hca,
            h4, h5, complex_eq_false_of_simple h2,
            complex_eq_false_of_simple h3]
      · exact hcond.elim
  case storageFieldCompoundAssignUnfoldLeftFst op =>
    cases stmt <;>
      simp only [Rules.ruleEffect, Rules.compoundAssignEffect] at hcond
    next opS lhs rhs =>
      split at hcond
      · next ty path fld heq =>
          obtain ⟨rfl, hca, h2, h3, h4⟩ := hcond
          simp only [Rules.isComplex, Rules.isStack, Rules.isSimple,
            coe_eq_expr] at h2 h3 h4
          simp [candidate, compoundAssignCandidate, coe_eq_expr, heq, hca,
            h2, h3, h4]
      · exact hcond.elim
  case storageIndexCompoundAssignUnfoldLeftFst op =>
    cases stmt <;>
      simp only [Rules.ruleEffect, Rules.compoundAssignEffect] at hcond
    next opS lhs rhs =>
      split at hcond
      · next ty path index heq =>
          obtain ⟨rfl, hca, h2, h3, h4, h5⟩ := hcond
          simp only [Rules.isComplex, Rules.isSimple, Rules.isStack,
            coe_eq_expr] at h2 h3 h4 h5
          simp [candidate, compoundAssignCandidate, coe_eq_expr, heq, hca,
            h2, h4, h5, complex_eq_false_of_simple h3]
      · exact hcond.elim
  case memoryFieldCompoundAssign op =>
    cases stmt <;>
      simp only [Rules.ruleEffect, Rules.compoundAssignEffect] at hcond
    next opS lhs rhs =>
      split at hcond
      · next ty path fld heq =>
          obtain ⟨rfl, hca, h2, h3, h4⟩ := hcond
          simp only [Rules.isSimple, Rules.isStack, coe_eq_expr] at h2 h3 h4
          simp [candidate, compoundAssignCandidate, coe_eq_expr, heq, hca,
            h3, h4, complex_eq_false_of_simple h2]
      · exact hcond.elim
  case memoryIndexCompoundAssign op =>
    cases stmt <;>
      simp only [Rules.ruleEffect, Rules.compoundAssignEffect] at hcond
    next opS lhs rhs =>
      split at hcond
      · next ty path index heq =>
          obtain ⟨rfl, hca, h2, h3, h4, h5⟩ := hcond
          simp only [Rules.isSimple, Rules.isStack, coe_eq_expr] at h2 h3 h4 h5
          simp [candidate, compoundAssignCandidate, coe_eq_expr, heq, hca,
            h4, h5, complex_eq_false_of_simple h2,
            complex_eq_false_of_simple h3]
      · exact hcond.elim
  case memoryFieldCompoundAssignUnfoldLeftFst op =>
    cases stmt <;>
      simp only [Rules.ruleEffect, Rules.compoundAssignEffect] at hcond
    next opS lhs rhs =>
      split at hcond
      · next ty path fld heq =>
          obtain ⟨rfl, hca, h2, h3, h4⟩ := hcond
          simp only [Rules.isComplex, Rules.isStack, Rules.isSimple,
            coe_eq_expr] at h2 h3 h4
          simp [candidate, compoundAssignCandidate, coe_eq_expr, heq, hca,
            h2, h3, h4]
      · exact hcond.elim
  case memoryIndexCompoundAssignUnfoldLeftFst op =>
    cases stmt <;>
      simp only [Rules.ruleEffect, Rules.compoundAssignEffect] at hcond
    next opS lhs rhs =>
      split at hcond
      · next ty path index heq =>
          obtain ⟨rfl, hca, h2, h3, h4, h5⟩ := hcond
          simp only [Rules.isComplex, Rules.isSimple, Rules.isStack,
            coe_eq_expr] at h2 h3 h4 h5
          simp [candidate, compoundAssignCandidate, coe_eq_expr, heq, hca,
            h2, h4, h5, complex_eq_false_of_simple h3]
      · exact hcond.elim
  case localCompoundAssign op =>
    cases stmt <;>
      simp only [Rules.ruleEffect, Rules.compoundAssignEffect] at hcond
    next opS lhs rhs =>
      obtain ⟨rfl, hca, ⟨h1, h2⟩, h3, h4⟩ := hcond
      simp only [Rules.isStack, Rules.isSimple, coe_eq_expr] at h1 h2 h3 h4
      simp [candidate, compoundAssignCandidate, coe_eq_expr, hca,
        h1, h2, h3, h4]
  case compoundAssignValueRhsCapture op =>
    cases stmt <;>
      simp only [Rules.ruleEffect, Rules.compoundAssignEffect] at hcond
    next opS lhs rhs =>
      obtain ⟨rfl, hca, hns⟩ := hcond
      simp only [Rules.isSe, Rules.isStack, Rules.isSimple] at hns
      have hb : (rhs.isStack && rhs.simple) = false := by
        cases hs : rhs.isStack <;> cases hp : rhs.simple <;> simp_all
      simp [candidate, compoundAssignCandidate, coe_eq_expr, hca, hb]
  case storageRootIncDec op =>
    cases stmt <;>
      simp only [Rules.ruleEffect, Rules.exprEffect] at hcond
    next expr =>
      split at hcond
      · next opS target =>
          obtain ⟨rfl, hg⟩ := hcond
          simp only [Rules.isGlobal] at hg
          obtain ⟨ty', fld', heqT, horig⟩ := isGlobal_shape hg
          simp [candidate, exprCandidate, incDecStmtCandidate, heqT, horig,
            Typed.WrappedExpr.isStack, Typed.WrappedExpr.kind]
      · exact hcond.elim
  case storageFieldIncDec op =>
    cases stmt <;>
      simp only [Rules.ruleEffect, Rules.exprEffect] at hcond
    next expr =>
      split at hcond
      · next opS ty path fld =>
          obtain ⟨rfl, h2⟩ := hcond
          simp only [Rules.isSimple] at h2
          simp [candidate, exprCandidate, incDecStmtCandidate,
            complex_eq_false_of_simple h2]
      · exact hcond.elim
  case storageIndexIncDec op =>
    cases stmt <;>
      simp only [Rules.ruleEffect, Rules.exprEffect] at hcond
    next expr =>
      split at hcond
      · next opS ty path index =>
          obtain ⟨rfl, h2, h3⟩ := hcond
          simp only [Rules.isSimple] at h2 h3
          simp [candidate, exprCandidate, incDecStmtCandidate,
            complex_eq_false_of_simple h2, complex_eq_false_of_simple h3]
      · exact hcond.elim
  case storageFieldIncDecUnfoldLeftFst op =>
    cases stmt <;>
      simp only [Rules.ruleEffect, Rules.exprEffect] at hcond
    next expr =>
      split at hcond
      · next opS ty path fld =>
          obtain ⟨rfl, h2⟩ := hcond
          simp only [Rules.isComplex] at h2
          simp [candidate, exprCandidate, incDecStmtCandidate, h2]
      · exact hcond.elim
  case storageIndexIncDecUnfoldLeftFst op =>
    cases stmt <;>
      simp only [Rules.ruleEffect, Rules.exprEffect] at hcond
    next expr =>
      split at hcond
      · next opS ty path index =>
          obtain ⟨rfl, h2, h3⟩ := hcond
          simp only [Rules.isComplex, Rules.isSimple] at h2 h3
          simp [candidate, exprCandidate, incDecStmtCandidate, h2,
            complex_eq_false_of_simple h3]
      · exact hcond.elim
  case memoryFieldIncDec op =>
    cases stmt <;>
      simp only [Rules.ruleEffect, Rules.exprEffect] at hcond
    next expr =>
      split at hcond
      · next opS ty path fld =>
          obtain ⟨rfl, h2⟩ := hcond
          simp only [Rules.isSimple] at h2
          simp [candidate, exprCandidate, incDecStmtCandidate,
            complex_eq_false_of_simple h2]
      · exact hcond.elim
  case memoryIndexIncDec op =>
    cases stmt <;>
      simp only [Rules.ruleEffect, Rules.exprEffect] at hcond
    next expr =>
      split at hcond
      · next opS ty path index =>
          obtain ⟨rfl, h2, h3⟩ := hcond
          simp only [Rules.isSimple] at h2 h3
          simp [candidate, exprCandidate, incDecStmtCandidate,
            complex_eq_false_of_simple h2, complex_eq_false_of_simple h3]
      · exact hcond.elim
  case memoryFieldIncDecUnfoldLeftFst op =>
    cases stmt <;>
      simp only [Rules.ruleEffect, Rules.exprEffect] at hcond
    next expr =>
      split at hcond
      · next opS ty path fld =>
          obtain ⟨rfl, h2⟩ := hcond
          simp only [Rules.isComplex] at h2
          simp [candidate, exprCandidate, incDecStmtCandidate, h2]
      · exact hcond.elim
  case memoryIndexIncDecUnfoldLeftFst op =>
    cases stmt <;>
      simp only [Rules.ruleEffect, Rules.exprEffect] at hcond
    next expr =>
      split at hcond
      · next opS ty path index =>
          obtain ⟨rfl, h2, h3⟩ := hcond
          simp only [Rules.isComplex, Rules.isSimple] at h2 h3
          simp [candidate, exprCandidate, incDecStmtCandidate, h2,
            complex_eq_false_of_simple h3]
      · exact hcond.elim
  case storageRootIncDecAssignment op =>
    cases stmt <;>
      simp only [Rules.ruleEffect, Rules.assignEffect] at hcond
    next lhs rhs =>
      split at hcond
      · next opS target =>
          obtain ⟨rfl, ⟨h1, h2⟩, hg⟩ := hcond
          simp only [Rules.isStack, Rules.isSimple, Rules.isGlobal,
            coe_eq_expr] at h1 h2 hg
          obtain ⟨ty', fld', heqT, horig⟩ := isGlobal_shape hg
          simp [candidate, assignCandidate, assignComplexCandidate,
            coe_eq_expr, h1, h2, kind_of_isStack h1, heqT, horig,
            Typed.WrappedExpr.isStack]
      · exact hcond.elim
  case storageFieldIncDecAssignment op =>
    cases stmt <;>
      simp only [Rules.ruleEffect, Rules.assignEffect] at hcond
    next lhs rhs =>
      split at hcond
      · next opS ty path fld =>
          obtain ⟨rfl, ⟨h1, h2⟩, h3⟩ := hcond
          simp only [Rules.isStack, Rules.isSimple, coe_eq_expr] at h1 h2 h3
          simp [candidate, assignCandidate, assignComplexCandidate,
            coe_eq_expr, h1, h2, kind_of_isStack h1,
            Typed.WrappedExpr.isStack, complex_eq_false_of_simple h3]
      · exact hcond.elim
  case storageIndexIncDecAssignment op =>
    cases stmt <;>
      simp only [Rules.ruleEffect, Rules.assignEffect] at hcond
    next lhs rhs =>
      split at hcond
      · next opS ty path index =>
          obtain ⟨rfl, ⟨h1, h2⟩, h3, h4⟩ := hcond
          simp only [Rules.isStack, Rules.isSimple, coe_eq_expr] at h1 h2 h3 h4
          simp [candidate, assignCandidate, assignComplexCandidate,
            coe_eq_expr, h1, h2, kind_of_isStack h1,
            Typed.WrappedExpr.isStack, complex_eq_false_of_simple h3,
            complex_eq_false_of_simple h4]
      · exact hcond.elim
  case memoryFieldIncDecAssignment op =>
    cases stmt <;>
      simp only [Rules.ruleEffect, Rules.assignEffect] at hcond
    next lhs rhs =>
      split at hcond
      · next opS ty path fld =>
          obtain ⟨rfl, ⟨h1, h2⟩, h3⟩ := hcond
          simp only [Rules.isStack, Rules.isSimple, coe_eq_expr] at h1 h2 h3
          simp [candidate, assignCandidate, assignComplexCandidate,
            coe_eq_expr, h1, h2, kind_of_isStack h1,
            Typed.WrappedExpr.isStack, complex_eq_false_of_simple h3]
      · exact hcond.elim
  case memoryIndexIncDecAssignment op =>
    cases stmt <;>
      simp only [Rules.ruleEffect, Rules.assignEffect] at hcond
    next lhs rhs =>
      split at hcond
      · next opS ty path index =>
          obtain ⟨rfl, ⟨h1, h2⟩, h3, h4⟩ := hcond
          simp only [Rules.isStack, Rules.isSimple, coe_eq_expr] at h1 h2 h3 h4
          simp [candidate, assignCandidate, assignComplexCandidate,
            coe_eq_expr, h1, h2, kind_of_isStack h1,
            Typed.WrappedExpr.isStack, complex_eq_false_of_simple h3,
            complex_eq_false_of_simple h4]
      · exact hcond.elim
  case localAssignIncDec op =>
    cases stmt <;>
      simp only [Rules.ruleEffect, Rules.assignEffect] at hcond
    next lhs rhs =>
      split at hcond
      · next opS target =>
          obtain ⟨rfl, ⟨h1, h2⟩, h3, h4⟩ := hcond
          simp only [Rules.isStack, Rules.isSimple, coe_eq_expr] at h1 h2 h3 h4
          simp [candidate, assignCandidate, assignComplexCandidate,
            coe_eq_expr, h1, h2, h3, h4, kind_of_isStack h1]
      · exact hcond.elim
  case localIncDec op =>
    cases stmt <;>
      simp only [Rules.ruleEffect, Rules.exprEffect] at hcond
    next expr =>
      split at hcond
      · next opS target =>
          obtain ⟨rfl, h1, h2⟩ := hcond
          simp only [Rules.isStack, Rules.isSimple] at h1 h2
          simp [candidate, exprCandidate, incDecStmtCandidate, h1, h2]
      · exact hcond.elim
  case revertBox =>
    cases mode
    case diamond =>
      simp [Rules.ruleEffect, Rules.revertEffect, CaseMode.applies]
        at hmode
    case box =>
      cases stmt <;>
        simp only [Rules.ruleEffect, Rules.revertEffect] at hcond
      next msg =>
        simp [candidate, pick]
  case revertDiamond =>
    cases mode
    case box =>
      simp [Rules.ruleEffect, Rules.revertEffect, CaseMode.applies]
        at hmode
    case diamond =>
      cases stmt <;>
        simp only [Rules.ruleEffect, Rules.revertEffect] at hcond
      next msg =>
        simp [candidate, pick]
  case assertConditionCapture =>
    cases stmt <;>
      simp only [Rules.ruleEffect, Rules.assertEffect] at hcond
    next c =>
      simp only [Rules.isComplex] at hcond
      simp [candidate, assertCandidate, hcond]
  case assertSimple =>
    cases stmt <;>
      simp only [Rules.ruleEffect, Rules.assertEffect] at hcond
    next c =>
      simp only [Rules.isSimple] at hcond
      simp [candidate, assertCandidate, complex_eq_false_of_simple hcond]
  case requireConditionCapture =>
    cases stmt <;>
      simp only [Rules.ruleEffect, Rules.requireEffect] at hcond
    next c =>
      simp only [Rules.isComplex] at hcond
      simp [candidate, requireCandidate, hcond]
  case requireSimple =>
    cases stmt <;>
      simp only [Rules.ruleEffect, Rules.requireEffect] at hcond
    next c =>
      simp only [Rules.isSimple] at hcond
      simp [candidate, requireCandidate, complex_eq_false_of_simple hcond]
  case functionCallArgCapture =>
    cases stmt <;>
      simp only [Rules.ruleEffect, Rules.callEffect] at hcond
    next res fn args =>
      simp [candidate, hcond]
  case functionBodyExpand =>
    cases stmt <;>
      simp only [Rules.ruleEffect, Rules.callEffect] at hcond
    next res fn args =>
      obtain ⟨hall, hsome⟩ := hcond
      have hnone : (Rules.captureFirstComplexArg args).isSome = false := by
        rw [Rules.captureFirstComplexArg_isSome]
        simp only [List.all_eq_true] at hall
        simp only [List.any_eq_false]
        intro a ha
        simp [Typed.WrappedExpr.complex, hall a ha]
      simp [candidate, hnone, hsome]
  case ifElseUnfold =>
    cases stmt <;>
      simp only [Rules.ruleEffect, Rules.iteEffect] at hcond
    next c thn els =>
      obtain ⟨hc, hall⟩ := hcond
      simp only [Rules.isComplex] at hc
      cases c <;>
        first
        | (simp_all [candidate, iteCandidate]
           done)
        | (rename_i uop arg
           cases uop
           · simp_all [candidate, iteCandidate]
           · have harg := hall arg rfl
             simp only [Rules.isComplex] at harg
             simp [candidate, iteCandidate, harg])
  case ifElseTrue =>
    cases stmt <;>
      simp only [Rules.ruleEffect, Rules.iteEffect] at hcond
    next c thn els =>
      split at hcond
      · simp [candidate, iteCandidate]
      · exact hcond.elim
  case ifElseFalse =>
    cases stmt <;>
      simp only [Rules.ruleEffect, Rules.iteEffect] at hcond
    next c thn els =>
      split at hcond
      · simp [candidate, iteCandidate]
      · exact hcond.elim
  case ifElseNegated =>
    cases stmt <;>
      simp only [Rules.ruleEffect, Rules.iteEffect] at hcond
    next c thn els =>
      split at hcond
      · next inner =>
          simp only [Rules.isSimple] at hcond
          simp [candidate, iteCandidate, complex_eq_false_of_simple hcond]
      · exact hcond.elim
  case transferUnfoldLeftFstReceiver =>
    cases stmt <;>
      simp only [Rules.ruleEffect, Rules.transferEffect] at hcond
    next recipient amount =>
      simp only [Rules.isComplex] at hcond
      simp [candidate, transferCandidate, hcond]
  case transferUnfoldRightSndArgument =>
    cases stmt <;>
      simp only [Rules.ruleEffect, Rules.transferEffect] at hcond
    next recipient amount =>
      obtain ⟨h1, h2⟩ := hcond
      simp only [Rules.isSimple, Rules.isComplex] at h1 h2
      simp [candidate, transferCandidate, h2,
        complex_eq_false_of_simple h1]
  case transferNoCallback =>
    cases stmt <;>
      simp only [Rules.ruleEffect, Rules.transferEffect] at hcond
    next recipient amount =>
      obtain ⟨h1, h2⟩ := hcond
      simp only [Rules.isSimple] at h1 h2
      simp [candidate, transferCandidate,
        complex_eq_false_of_simple h1, complex_eq_false_of_simple h2]

/-- `applicable_eq_candidate` for the withCallback rule set: dispatch
under `candidateWithCallback` is still a total function of the
statement, so the withCallback rules are mutually exclusive too. -/
theorem applicable_eq_candidateWithCallback {mode : Modality} {stmt : Stmt}
    {rule : RuleName} (hmem : rule ∈ Rules.ruleNamesWithCallback)
    (hmode : ((Rules.ruleEffect rule).mode stmt).applies mode = true)
    (hcond : (Rules.ruleEffect rule).cond stmt) :
    candidateWithCallback mode stmt = some rule := by
  rw [Rules.ruleNamesWithCallback, List.mem_append] at hmem
  cases hmem with
  | inr h =>
      simp only [List.mem_singleton] at h
      subst h
      rw [Rules.transferWithCallback_mode_eq] at hmode
      rw [Rules.transferWithCallback_cond_eq] at hcond
      have := applicable_eq_candidate (rule := .transferNoCallback)
        (by decide) hmode hcond
      rw [candidateWithCallback, this]
  | inl h =>
      have hne : rule ≠ .transferNoCallback := by
        intro hr
        subst hr
        exact absurd h (by decide)
      have := applicable_eq_candidate (List.mem_of_mem_erase h) hmode hcond
      rw [candidateWithCallback, this]
      cases rule <;> first | exact absurd rfl hne | rfl

/-! ### Mutual exclusion of rules

No two distinct rules of the calculus can apply to the same statement under the
same modality: `applicable_eq_candidate` sends every applicable rule to
the *same* `candidate` answer.  Exclusion is stated per `Modality`
(box/diamond).  Under the block modality `.both` a box/diamond twin pair
is applicable simultaneously — by design
(`SolidityModality.appliesCaseMode`) — and `FirstStepCase` picks the box
twin, which is listed first in `ruleNames`; the twins are
effect-identical up to mode (`CandidateStep.twinEffects`), so this is a
choice of name, not of behaviour.  The step relation is a partial function
for every modality, `.both` included (`FirstStepCase.functional`). -/

theorem stepApplicable_rule_iff {mode : Modality} {stmt : Stmt}
    {rule : RuleName} :
    StepApplicable mode stmt (Rules.stepCase rule) ↔
      ((Rules.ruleEffect rule).mode stmt).applies mode = true ∧
        (Rules.ruleEffect rule).cond stmt :=
  Iff.rfl

theorem rule_rule_eq {mode : Modality} {stmt : Stmt} {r1 r2 : RuleName}
    (h1mem : r1 ∈ Rules.ruleNames)
    (h2mem : r2 ∈ Rules.ruleNames)
    (h1 : StepApplicable mode stmt (Rules.stepCase r1))
    (h2 : StepApplicable mode stmt (Rules.stepCase r2)) :
    r1 = r2 := by
  rw [stepApplicable_rule_iff] at h1 h2
  have e1 := applicable_eq_candidate h1mem h1.1 h1.2
  have e2 := applicable_eq_candidate h2mem h2.1 h2.2
  exact Option.some.inj (e1.symm.trans e2)

theorem ruleName_exclusive {mode : Modality} {stmt : Stmt} {r1 r2 : RuleName}
    (h1mem : r1 ∈ Rules.ruleNames)
    (h2mem : r2 ∈ Rules.ruleNames)
    (hne : r1 ≠ r2)
    (h1 : StepApplicable mode stmt (Rules.stepCase r1))
    (h2 : StepApplicable mode stmt (Rules.stepCase r2)) :
    False :=
  hne (rule_rule_eq h1mem h2mem h1 h2)

/-- Every entry of `Rules.rules` is the canonical step case of its name. -/
theorem mem_rules_eq_stepCase {step : StepCase} (h : step ∈ Rules.rules) :
    step = Rules.stepCase step.rule := by
  obtain ⟨r, _, rfl⟩ := Rules.mem_stepCases_iff.mp h
  rfl

theorem rules_get_rule_mem (x : Fin Rules.rules.length) :
    (Rules.rules.get x).rule ∈ Rules.ruleNames := by
  rw [← Rules.rules_ruleNames]
  exact List.mem_map.mpr ⟨_, List.get_mem _ x, rfl⟩

/-- Distinct indices into `Rules.rules` carry distinct rule names. -/
theorem rules_get_rule_inj : ∀ (x y : Fin Rules.rules.length),
    (Rules.rules.get x).rule = (Rules.rules.get y).rule -> x = y := by
  native_decide

theorem rules_exclusive (mode : Modality) (stmt : Stmt)
    (x y : Fin Rules.rules.length) :
    x ≠ y ->
    StepApplicable mode stmt (Rules.rules.get x) ->
    ¬ StepApplicable mode stmt (Rules.rules.get y) := by
  intro hxy hx hy
  rw [mem_rules_eq_stepCase (List.get_mem _ x)] at hx
  rw [mem_rules_eq_stepCase (List.get_mem _ y)] at hy
  exact ruleName_exclusive (rules_get_rule_mem x) (rules_get_rule_mem y)
    (fun heq => hxy (rules_get_rule_inj x y heq)) hx hy

/-- No two distinct rules of the generated rule set apply to the same
statement under the same modality (`Modality`, i.e. box or diamond; see
the section docstring for `.both`). -/
theorem stepCases_exclusive
    (mode : Modality) (stmt : Stmt)
    (x y : Fin (Rules.stepCases).length) :
    x ≠ y ->
    StepApplicable mode stmt ((Rules.stepCases).get x) ->
    ¬ StepApplicable mode stmt ((Rules.stepCases).get y) :=
  rules_exclusive mode stmt x y

end UniquenessAux

namespace RuleSet

def ruleNames : List RuleName :=
  Rules.ruleNames

theorem ruleNames_nodup : ruleNames.Nodup := by
  native_decide

end RuleSet

/-- The discipline of the generated rule set, as three facts with content:
per-modality mutual exclusion, no duplicate names, and every step case is
a rule of the calculus (there is no internal tier). -/
structure RuleSetDisciplined : Prop where
  mutuallyExclusive :
    ∀ (mode : Modality) (stmt : Stmt)
      (x y : Fin (Rules.stepCases).length),
      x ≠ y ->
      StepApplicable mode stmt ((Rules.stepCases).get x) ->
      ¬ StepApplicable mode stmt ((Rules.stepCases).get y)
  ruleNamesNoDuplicates :
    RuleSet.ruleNames.Nodup
  everyStepIsRule :
    ∀ (x : Fin (Rules.stepCases).length),
      ((Rules.stepCases).get x).rule ∈ Rules.ruleNames

theorem ruleSet_disciplined :
    RuleSetDisciplined where
  mutuallyExclusive := UniquenessAux.stepCases_exclusive
  ruleNamesNoDuplicates := RuleSet.ruleNames_nodup
  everyStepIsRule := UniquenessAux.rules_get_rule_mem

end Solidity
