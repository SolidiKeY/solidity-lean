import Solidity.Typing.Sorts
import Solidity.Semantics.Run
import Solidity.Calculus.RuleShapes
import Solidity.SortCheck.Annotations


namespace Solidity
namespace SortFaithfulness

open TacletAnnotations

variable {C : Contract}


inductive Read (C : Contract) (Γ : Ctx) where
  | storage (T : Ty) (p : SPath C Γ T)
  | memory (T : Ty) (p : MPath C Γ T)
  | slen {E : Ty} (p : SPath C Γ (.array E))
  | mlen {E : Ty} (p : MPath C Γ (.array E))
  | sslot {E : Ty} (p : SPath C Γ (.array E))

def Read.domain {Γ : Ctx} : Read C Γ → ReadDomain
  | .storage .. | .slen _ | .sslot _ => .storage
  | .memory .. | .mlen _ => .memory

def Read.ty {Γ : Ctx} : Read C Γ → Ty
  | .storage T _ | .memory T _ => T
  | .slen _ | .mlen _ => .uint
  | .sslot (E := E) _ => E

def OpLoc.read? {Γ : Ctx} : {p : PrimTy} → OpLoc C Γ p → Option (Read C Γ)
  | _, .local _ => none
  | p, .root r h => some (.storage (.prim p) (.loc (.root r h)))
  | p, .field b f h => some (.storage (.prim p) (.loc (.field b f h)))
  | p, .index it b i => some (.storage (.prim p) (.loc (.index it b (.simple i))))
  | p, .mfield b f h => some (.memory (.prim p) (.loc (.field b f h)))
  | p, .mindex a b i => some (.memory (.prim p) (.loc (.index a b (.simple i))))

def Stmt.read? {Γ Γ' : Ctx} : Stmt C Γ Γ' → Option (Read C Γ)
  | @Stmt.assignLocal _ _ p _ (.read l) => some (.storage (.prim p) (.loc l))
  | @Stmt.assignLocal _ _ p _ (.readMem l) => some (.memory (.prim p) (.loc l))
  | @Stmt.assignLocal _ _ _ _ (.len b _) => some (.slen b)
  | @Stmt.assignLocal _ _ _ _ (.mlen b _) => some (.mlen b)
  | @Stmt.assign _ _ _ _ (@Src.copy _ _ R sp _) => some (.storage (.ref R) sp)
  | @Stmt.push _ _ _ _ (some (@Src.copy _ _ R sp _)) _ => some (.storage (.ref R) sp)
  | @Stmt.rebindMem _ _ R _ (.copy sp _) => some (.storage (.ref R) sp)
  | @Stmt.rebindMem _ _ R _ (.alias mp) => some (.memory (.ref R) mp)
  | @Stmt.assignFromMem _ _ R _ mp => some (.memory (.ref R) mp)
  | .opAssign _ _ _ l _ => OpLoc.read? l
  | .incDec _ _ l => OpLoc.read? l
  | .assignIncDec _ _ _ l _ => OpLoc.read? l
  | .assignLocalPush _ b => some (.sslot b)
  | .pushOpAssign _ _ _ b _ | .pushIncDec _ _ b => some (.sslot b)
  | _ => none


def SortOkS : ReadSort → {T : Ty} → SVal T → Bool
  | .generic _, _, _ => true
  | .fixed s, _, v => v.keySort.le s

def SortOkM {H : HTy} : ReadSort → (T : Ty) → MVal H T → Bool
  | .generic _, _, _ => true
  | .fixed s, T, mv => (MVal.keySort T mv).le s

def Read.SortOk {Γ : Ctx} (σ : State C Γ) (rs : ReadSort) : Read C Γ → Prop
  | .storage T p => ∀ r (v : SVal T), p.resolveT σ = .ok r → σ.storage.find r = some v →
      SortOkS rs v = true
  | .memory T p => ∀ mv, p.mvalT σ = .ok mv → SortOkM rs T mv = true
  | .slen p => ∀ v, (Val.len (p := .uint) p rfl).evalT σ = .ok v →
      SortOkS rs (SVal.prim v) = true
  | .mlen p => ∀ v, (Val.mlen (p := .uint) p rfl).evalT σ = .ok v →
      SortOkM (H := σ.H) rs (.prim .uint) v = true
  | .sslot (E := E) p => ∀ r (v : SVal (.ref (.array E))), p.resolveT σ = .ok r →
      σ.storage.find r = some v →
      SortOkS rs (pushSlot E (SVal.view v : ArrView E).shadow.toList).1 = true

inductive ReadClass where
  | any
  | numeric
  | reference
  deriving DecidableEq, Repr

def ReadClass.fits : ReadClass → Ty → Bool
  | .any, _ => true
  | .numeric, T => isNumericTy T
  | .reference, T => T.isReference

def ReadClass.supports (cls : ReadClass) : ReadDomain → ReadSort → Bool
  | _, .generic _ => true
  | .storage, .fixed .stValue => true
  | .memory, .fixed .memValue => true
  | _, .fixed .int => cls == .numeric
  | .storage, .fixed .struct => cls == .reference
  | .memory, .fixed .identity => cls == .reference
  | _, _ => false

theorem Read.sortOk {Γ : Ctx} (σ : State C Γ)
    {R : Read C Γ} {cls : ReadClass} (hfit : cls.fits R.ty = true) {rs : ReadSort}
    (hsup : cls.supports R.domain rs = true) : R.SortOk σ rs := by
  cases R with
  | storage T p =>
    unfold Read.SortOk
    intro r v _ _
    cases rs with
    | generic _ => rfl
    | fixed s =>
      show v.keySort.le s = true
      cases s <;> simp only [ReadClass.supports, Read.domain, beq_iff_eq] at hsup <;>
        (try exact Bool.noConfusion hsup) <;> subst_vars
      · exact SVal.keySort_le_stValue v
      · rw [SVal.keySort_numeric (T := T) hfit v]; rfl
      · rw [SVal.keySort_ref (T := T) hfit v]; exact KeySort.le_refl _
  | memory T p =>
    unfold Read.SortOk
    intro mv _
    cases rs with
    | generic _ => rfl
    | fixed s =>
      show (MVal.keySort T mv).le s = true
      cases s <;> simp only [ReadClass.supports, Read.domain, beq_iff_eq] at hsup <;>
        (try exact Bool.noConfusion hsup) <;> subst_vars
      · exact MVal.keySort_le_memValue T mv
      · rw [MVal.keySort_numeric (T := T) hfit mv]; rfl
      · rw [MVal.keySort_ref (T := T) hfit mv]; rfl
  | slen p =>
    unfold Read.SortOk
    intro v _
    cases rs with
    | generic _ => rfl
    | fixed s =>
      show (SVal.prim v).keySort.le s = true
      cases s <;> simp only [ReadClass.supports, Read.domain, beq_iff_eq] at hsup <;>
        (try exact Bool.noConfusion hsup) <;> subst_vars
      · exact SVal.keySort_le_stValue _
      · rfl
      · simp [ReadClass.fits, Read.ty, Ty.isReference, Ty.isPrimitive] at hfit
  | mlen p =>
    unfold Read.SortOk
    intro v _
    cases rs with
    | generic _ => rfl
    | fixed s =>
      show (MVal.keySort (H := σ.H) (.prim .uint) v).le s = true
      cases s <;> simp only [ReadClass.supports, Read.domain, beq_iff_eq] at hsup <;>
        (try exact Bool.noConfusion hsup) <;> subst_vars
      · exact MVal.keySort_le_memValue (H := σ.H) (.prim .uint) v
      · rfl
      · simp [ReadClass.fits, Read.ty, Ty.isReference, Ty.isPrimitive] at hfit
  | @sslot E p =>
    unfold Read.SortOk
    intro r v _ _
    generalize (pushSlot E (SVal.view v : ArrView E).shadow.toList).1 = x
    cases rs with
    | generic _ => rfl
    | fixed s =>
      show x.keySort.le s = true
      cases s <;> simp only [ReadClass.supports, Read.domain, beq_iff_eq] at hsup <;>
        (try exact Bool.noConfusion hsup) <;> subst_vars
      · exact SVal.keySort_le_stValue x
      · rw [SVal.keySort_numeric (T := E) hfit x]; rfl
      · rw [SVal.keySort_ref (T := E) hfit x]; exact KeySort.le_refl _


class TacletAbout (α : Prop) (C : outParam Contract) (Γ Γ' : outParam Ctx)
    (s : outParam (Stmt C Γ Γ')) : Prop where

instance {k : Nat} {m : Modality} {Γ Γ' : Ctx} {s : Stmt C Γ Γ'}
    {p : Premise C Γ Γ'} : TacletAbout (Taclet C k m s p) C Γ Γ' s := ⟨⟩

instance {P α : Prop} {Γ Γ' : Ctx} {s : Stmt C Γ Γ'} [TacletAbout α C Γ Γ' s] :
    TacletAbout (P → α) C Γ Γ' s := ⟨⟩

def stmtOf {α : Prop} {Γ Γ' : Ctx} {s : Stmt C Γ Γ'} [TacletAbout α C Γ Γ' s] (_ : α) :
    Stmt C Γ Γ' := s

def keyNamesOf (n : Lean.Name) : List String :=
  match RuleShapes.tacletOrigins.lookup n with
  | some o => o.taclets.map KeyTaclet.name
  | none => []

def ctorsOf (key : String) : List Lean.Name :=
  (RuleShapes.tacletOrigins.filter fun (_, o) => o.taclets.any (·.name == key)).map (·.1)

def rowsOf (n : Lean.Name) : List TacletReadAnn :=
  let names := keyNamesOf n
  tacletReadAnns.filter fun row => names.contains row.keyName

def valueReads (row : TacletReadAnn) : List TacletRead :=
  row.reads.filter (·.site == .value)

def rowsSupported (n : Lean.Name) (dom : ReadDomain) (cls : ReadClass) : Bool :=
  (rowsOf n).all fun row => (valueReads row).all fun r => r.domain == dom && cls.supports dom r.sort

def RowFaithful (row : TacletReadAnn) {Γ Γ' : Ctx} (s : Stmt C Γ Γ') : Prop :=
  ∀ r ∈ valueReads row, ∃ R, Stmt.read? s = some R ∧ R.domain = r.domain ∧
    ∀ σ : State C Γ, R.SortOk σ r.sort

def CtorFaithful (n : Lean.Name) {Γ Γ' : Ctx} (s : Stmt C Γ Γ') : Prop :=
  ∀ row ∈ rowsOf n, RowFaithful row s

theorem rowFaithful_of {row : TacletReadAnn} {Γ Γ' : Ctx} {s : Stmt C Γ Γ'}
    {R : Read C Γ} {dom : ReadDomain} {cls : ReadClass} (hR : Stmt.read? s = some R)
    (hdom : R.domain = dom) (hfit : cls.fits R.ty = true)
    (hrow : (valueReads row).all (fun r => r.domain == dom && cls.supports dom r.sort) = true) :
    RowFaithful row s := by
  intro r hr
  have h := List.all_eq_true.mp hrow r hr
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨R, hR, hdom.trans h.1.symm, fun σ => Read.sortOk σ hfit (hdom ▸ h.2)⟩

theorem ctorFaithful_of {n : Lean.Name} {Γ Γ' : Ctx} {s : Stmt C Γ Γ'} {R : Read C Γ}
    {dom : ReadDomain} {cls : ReadClass} (hR : Stmt.read? s = some R) (hdom : R.domain = dom)
    (hfit : cls.fits R.ty = true) (hrows : rowsSupported n dom cls = true) :
    CtorFaithful n s := fun row hrow =>
  rowFaithful_of hR hdom hfit (List.all_eq_true.mp hrows row hrow)


section Gen
open Lean Elab Command Term Meta

elab "faithful_theorem " r:ident dom:term:max cls:term:max : command => do
  let ctor := `Solidity.Taclet ++ r.getId
  let thm := (← getCurrNamespace) ++ (`faithful).appendAfter ("_" ++ r.getId.toString)
  let (ty, pf) ← liftTermElabM do
    let info ← getConstInfo ctor
    forallTelescope info.type fun xs _ => do
      let d ← exprToSyntax (mkAppN (mkConst ctor (info.levelParams.map mkLevelParam)) xs)
      let stmt ← elabType (← `(CtorFaithful $(quote ctor) (stmtOf $d)))
      let pf ← elabTermEnsuringType
        (← `(ctorFaithful_of (dom := $dom) (cls := $cls) rfl rfl (by first | rfl | assumption)
          (by decide +kernel))) stmt
      synthesizeSyntheticMVarsNoPostponing
      let stmt ← instantiateMVars stmt
      let pf ← instantiateMVars pf
      if pf.hasExprMVar then throwError "faithful_theorem: the proof of {ctor} is not closed"
      return (← mkForallFVars xs stmt, ← mkLambdaFVars xs pf)
  liftCoreM <| addDecl (.thmDecl { name := thm, levelParams := [], type := ty, value := pf })

end Gen

faithful_theorem storageRootWriteCopySource .storage .reference
faithful_theorem storageRootReadSelect .storage .any
faithful_theorem storageFieldWriteCopySource .storage .reference
faithful_theorem storageFieldReadFind .storage .any
faithful_theorem storageLengthRead .storage .any
faithful_theorem memoryLengthRead .memory .any
faithful_theorem storageFieldReadStoreRoot .storage .reference
faithful_theorem storageIndexReadMappingFind .storage .any
faithful_theorem storageIndexReadMappingStoreRoot .storage .reference
faithful_theorem storageIndexWriteMappingCopySource .storage .reference
faithful_theorem storageIndexReadArrayFind .storage .any
faithful_theorem storageIndexReadArrayStoreRoot .storage .reference
faithful_theorem storageIndexWriteArrayCopySource .storage .reference
faithful_theorem storagePushValueCopySource .storage .reference
faithful_theorem storageLocalPrimitivePushBind .storage .any
faithful_theorem storagePushAddAssign .storage .numeric
faithful_theorem storagePushSubAssign .storage .numeric
faithful_theorem storagePushMulAssign .storage .numeric
faithful_theorem storagePushDivAssign .storage .numeric
faithful_theorem storagePushModAssign .storage .numeric
faithful_theorem storagePushPreincrement .storage .numeric
faithful_theorem storagePushPostincrement .storage .numeric
faithful_theorem storagePushPredecrement .storage .numeric
faithful_theorem storagePushPostdecrement .storage .numeric
faithful_theorem memoryStorageCopy .storage .reference
faithful_theorem storageRootOpAssign .storage .numeric
faithful_theorem storageFieldOpAssign .storage .numeric
faithful_theorem storageIndexMappingOpAssign .storage .numeric
faithful_theorem storageIndexArrayOpAssign .storage .numeric
faithful_theorem storageRootIncrement .storage .numeric
faithful_theorem storageFieldIncrement .storage .numeric
faithful_theorem storageIndexIncrement .storage .numeric
faithful_theorem storageRootIncrementAssignment .storage .numeric
faithful_theorem storageFieldIncrementAssignment .storage .numeric
faithful_theorem storageIndexIncrementAssignment .storage .numeric
faithful_theorem memoryToStorageFieldCopyRoot .memory .reference
faithful_theorem memoryFieldRead .memory .any
faithful_theorem memoryFieldReadAliasRoot .memory .any
faithful_theorem memoryIndexReadArrayValue .memory .any
faithful_theorem memoryIndexReadArrayMemory .memory .reference
faithful_theorem memoryFieldOpAssign .memory .numeric
faithful_theorem memoryIndexArrayOpAssign .memory .numeric
faithful_theorem memoryFieldIncrement .memory .numeric
faithful_theorem memoryIndexArrayIncrement .memory .numeric
faithful_theorem memoryFieldIncrementAssignment .memory .numeric
faithful_theorem memoryIndexArrayIncrementAssignment .memory .numeric


structure Proved where
  ctor : Lean.Name
  claim : Prop
  proof : claim

def faithfulCtors : List Proved := [
  ⟨``Taclet.storageRootWriteCopySource, _, @faithful_storageRootWriteCopySource⟩,
  ⟨``Taclet.storageRootReadSelect, _, @faithful_storageRootReadSelect⟩,
  ⟨``Taclet.storageFieldWriteCopySource, _, @faithful_storageFieldWriteCopySource⟩,
  ⟨``Taclet.storageFieldReadFind, _, @faithful_storageFieldReadFind⟩,
  ⟨``Taclet.storageLengthRead, _, @faithful_storageLengthRead⟩,
  ⟨``Taclet.memoryLengthRead, _, @faithful_memoryLengthRead⟩,
  ⟨``Taclet.storageFieldReadStoreRoot, _, @faithful_storageFieldReadStoreRoot⟩,
  ⟨``Taclet.storageIndexReadMappingFind, _, @faithful_storageIndexReadMappingFind⟩,
  ⟨``Taclet.storageIndexReadMappingStoreRoot, _, @faithful_storageIndexReadMappingStoreRoot⟩,
  ⟨``Taclet.storageIndexWriteMappingCopySource, _, @faithful_storageIndexWriteMappingCopySource⟩,
  ⟨``Taclet.storageIndexReadArrayFind, _, @faithful_storageIndexReadArrayFind⟩,
  ⟨``Taclet.storageIndexReadArrayStoreRoot, _, @faithful_storageIndexReadArrayStoreRoot⟩,
  ⟨``Taclet.storageIndexWriteArrayCopySource, _, @faithful_storageIndexWriteArrayCopySource⟩,
  ⟨``Taclet.storagePushValueCopySource, _, @faithful_storagePushValueCopySource⟩,
  ⟨``Taclet.storageLocalPrimitivePushBind, _, @faithful_storageLocalPrimitivePushBind⟩,
  ⟨``Taclet.storagePushAddAssign, _, @faithful_storagePushAddAssign⟩,
  ⟨``Taclet.storagePushSubAssign, _, @faithful_storagePushSubAssign⟩,
  ⟨``Taclet.storagePushMulAssign, _, @faithful_storagePushMulAssign⟩,
  ⟨``Taclet.storagePushDivAssign, _, @faithful_storagePushDivAssign⟩,
  ⟨``Taclet.storagePushModAssign, _, @faithful_storagePushModAssign⟩,
  ⟨``Taclet.storagePushPreincrement, _, @faithful_storagePushPreincrement⟩,
  ⟨``Taclet.storagePushPostincrement, _, @faithful_storagePushPostincrement⟩,
  ⟨``Taclet.storagePushPredecrement, _, @faithful_storagePushPredecrement⟩,
  ⟨``Taclet.storagePushPostdecrement, _, @faithful_storagePushPostdecrement⟩,
  ⟨``Taclet.memoryStorageCopy, _, @faithful_memoryStorageCopy⟩,
  ⟨``Taclet.storageRootOpAssign, _, @faithful_storageRootOpAssign⟩,
  ⟨``Taclet.storageFieldOpAssign, _, @faithful_storageFieldOpAssign⟩,
  ⟨``Taclet.storageIndexMappingOpAssign, _, @faithful_storageIndexMappingOpAssign⟩,
  ⟨``Taclet.storageIndexArrayOpAssign, _, @faithful_storageIndexArrayOpAssign⟩,
  ⟨``Taclet.storageRootIncrement, _, @faithful_storageRootIncrement⟩,
  ⟨``Taclet.storageFieldIncrement, _, @faithful_storageFieldIncrement⟩,
  ⟨``Taclet.storageIndexIncrement, _, @faithful_storageIndexIncrement⟩,
  ⟨``Taclet.storageRootIncrementAssignment, _, @faithful_storageRootIncrementAssignment⟩,
  ⟨``Taclet.storageFieldIncrementAssignment, _, @faithful_storageFieldIncrementAssignment⟩,
  ⟨``Taclet.storageIndexIncrementAssignment, _, @faithful_storageIndexIncrementAssignment⟩,
  ⟨``Taclet.memoryToStorageFieldCopyRoot, _, @faithful_memoryToStorageFieldCopyRoot⟩,
  ⟨``Taclet.memoryFieldRead, _, @faithful_memoryFieldRead⟩,
  ⟨``Taclet.memoryFieldReadAliasRoot, _, @faithful_memoryFieldReadAliasRoot⟩,
  ⟨``Taclet.memoryIndexReadArrayValue, _, @faithful_memoryIndexReadArrayValue⟩,
  ⟨``Taclet.memoryIndexReadArrayMemory, _, @faithful_memoryIndexReadArrayMemory⟩,
  ⟨``Taclet.memoryFieldOpAssign, _, @faithful_memoryFieldOpAssign⟩,
  ⟨``Taclet.memoryIndexArrayOpAssign, _, @faithful_memoryIndexArrayOpAssign⟩,
  ⟨``Taclet.memoryFieldIncrement, _, @faithful_memoryFieldIncrement⟩,
  ⟨``Taclet.memoryIndexArrayIncrement, _, @faithful_memoryIndexArrayIncrement⟩,
  ⟨``Taclet.memoryFieldIncrementAssignment, _, @faithful_memoryFieldIncrementAssignment⟩,
  ⟨``Taclet.memoryIndexArrayIncrementAssignment, _, @faithful_memoryIndexArrayIncrementAssignment⟩ ]

example : faithfulCtors.length = 46 := by decide +kernel


theorem rows_covered :
    tacletReadAnns.all (fun row => (valueReads row).isEmpty ||
      (!(ctorsOf row.keyName).isEmpty &&
        (ctorsOf row.keyName).all ((faithfulCtors.map (·.ctor)).contains ·))) = true := by
  decide +kernel

theorem rows_accounting :
    tacletReadAnns.length = 131 ∧
    (tacletReadAnns.filter fun row => !(valueReads row).isEmpty).length = 105 ∧
    (tacletReadAnns.filter fun row => (valueReads row).any (·.domain == .storage)).length = 75 ∧
    (tacletReadAnns.filter fun row => (valueReads row).any (·.domain == .memory)).length = 30 ∧
    (tacletReadAnns.filter fun row => (valueReads row).any (·.sort != .fixed .stValue)).length
      = 97 := by
  decide +kernel

example :
    (tacletReadAnns.filter fun row =>
      !(valueReads row).isEmpty &&
      (valueReads row).all (·.sort == .fixed .stValue)).length = 8 := by
  decide +kernel


example :
    (tacletReadAnns.filter fun row => (valueReads row).isEmpty).length = 26 := by
  decide +kernel


end SortFaithfulness
end Solidity
