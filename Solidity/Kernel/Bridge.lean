import Solidity.Kernel.Taclet
import Solidity.Calculus.Rules

/-!
# The bridge to the rule table

Each `Taclet` constructor names the solkey taclet it is (`Taclet.origin`,
a `KeyTaclet` of `Calculus/KeyTaclets.lean`), and the rule of the old table
that transcribes it (`Taclet.rule`, a `RuleName` of `Calculus/Rules.lean`).
`Taclet.origin_claimed` checks the two against each other: the old rule's
recorded origin claims the constructor's taclet.  A family (`binopAssignment
op`) keeps its `RuleName` and takes its origin from it.

Where the old table has box/diamond twins, the rule follows the modality.
`ifElseSplit` is the one constructor without a rule: the old table splits a
branch in the sequent, not by a rule (`RuleShapes` excuses the taclet). -/

namespace Solidity
namespace Kernel

open Semantics Rules

variable {C : Contract} {m : Modality}

/-- The rule of the old table a derivation's last step is. -/
def Taclet.rule {Γ Γ' : Ctx} {s : Stmt C Γ Γ'} {pr : Premise C Γ Γ'} : Taclet C m s pr → Option RuleName
  | .storageFieldRead_unfold_rightFst .. => some .storageFieldReadUnfoldRightFst
  | .storageIndexRead_unfold_rightFst .. => some .storageIndexReadUnfoldRightFst
  | .storageIndexRead_unfold_rightSndIndex .. => some .storageIndexReadUnfoldRightSndIndex
  | .storageFieldRead_unfold_rightSndResult .. => some .storageFieldReadUnfoldRightSndResult
  | .storageIndexRead_unfold_rightSndResult .. => some .storageIndexReadUnfoldRightSndResult
  | .storageFieldWrite_unfold_leftFst .. => some .storageFieldWriteUnfoldLeftFst
  | .storageFieldWriteStorageRef_unfold_leftFst .. => some .storageFieldWriteRefUnfoldLeftFst
  | .storageIndexWrite_unfold_leftFst .. => some .storageIndexWriteUnfoldLeftFst
  | .storageIndexWriteStorageRef_unfold_leftFst .. => some .storageIndexWriteRefUnfoldLeftFst
  | .storageIndexWriteNonSimpleIndexCapture .. => some .storageIndexWriteUnfoldLeftSndIndex
  | .storageIndexWriteStorageRefNonSimpleIndexCapture .. => some .storageIndexWriteRefUnfoldLeftSndIndex
  | .storageRootWriteValueRhsCapture .. => some .storageRootWriteUnfoldSource
  | .fieldWriteValueRhsCapture .. => some .storageFieldWriteUnfoldSource
  | .indexWriteValueRhsCapture .. => some .storageIndexWriteUnfoldSource
  | .storageFieldDelete_unfold_leftFst .. => some .storageFieldDeleteUnfoldLeftFst
  | .storageIndexDelete_unfold_leftFst .. => some .storageIndexDeleteUnfoldLeftFst
  | .storageIndexDeleteNonSimpleIndexCapture .. => some .storageIndexDeleteNonSimpleIndexCapture
  | .localValueDeclInitDrop .. => some .localValueDeclInitDrop
  | .valueDeclSkip .. => some .valueDeclSkip
  | .localValueAssign .. => some .localValueAssign
  | .storageRootReadSelect .. => some .storageRootReadSelect
  | .storageFieldReadFind .. => some .storageFieldReadFind
  | .storageIndexReadMappingFind .. => some .storageIndexReadMappingFind
  | .storageIndexReadArrayFind .. => some (match m with | .box => .storageIndexReadArrayFindBox | .diamond => .storageIndexReadArrayFindDiamond)
  | .storageRootWriteStore .. => some .storageRootWriteStore
  | .storageRootWriteCopySource .. => some .storageRootWriteCopySource
  | .storageFieldReadStoreRoot .. => some .storageFieldReadStoreRoot
  | .storageIndexReadMappingStoreRoot .. => some .storageIndexReadMappingStoreRoot
  | .storageIndexReadArrayStoreRoot .. => some (match m with | .box => .storageIndexReadArrayStoreRootBox | .diamond => .storageIndexReadArrayStoreRootDiamond)
  | .storageFieldWriteSave .. => some .storageFieldWriteSave
  | .storageFieldWriteCopySource .. => some .storageFieldWriteCopySource
  | .storageIndexWriteMappingSave .. => some .storageIndexWriteMappingSave
  | .storageIndexWriteArraySave .. => some (match m with | .box => .storageIndexWriteArraySaveBox | .diamond => .storageIndexWriteArraySaveDiamond)
  | .storageIndexWriteMappingCopySource .. => some .storageIndexWriteMappingCopySource
  | .storageIndexWriteArrayCopySource .. => some (match m with | .box => .storageIndexWriteArrayCopySourceBox | .diamond => .storageIndexWriteArrayCopySourceDiamond)
  | .storageLocalRootRebind .. => some .storageLocalRootRebind
  | .storageFieldReadBindLocalRoot .. => some .storageFieldReadBindLocalRoot
  | .storageIndexReadMappingBindLocalRoot .. => some .storageIndexReadMappingBindLocalRoot
  | .storageIndexReadArrayBindLocalRoot .. => some (match m with | .box => .storageIndexReadArrayBindLocalRootBox | .diamond => .storageIndexReadArrayBindLocalRootDiamond)
  | .storageLocalDeclInitDrop .. => some .storageLocalDeclInitDrop
  | .storageRootDelete .. => some .storageRootDelete
  | .storageFieldDelete .. => some .storageFieldDelete
  | .storageIndexDelete .. => some .storageIndexDelete
  | .binopAssignment op .. => some (.binopAssignment op)
  | .binopUnfoldLeft op .. => some (.binopUnfoldLeft op)
  | .binopUnfoldRight op .. => some (.binopUnfoldRight op)
  | .logicalAndShortCircuitRhs .. => some .logicalAndShortCircuitRhs
  | .logicalOrShortCircuitRhs .. => some .logicalOrShortCircuitRhs
  | .unopAssignment op .. => some (.unopAssignment op)
  | .unopCapture op .. => some (.unopCapture op)
  | .ifElseSplit .. => none
  | .requireSimple .. => some .requireSimple
  | .assertSimple .. => some .assertSimple
  | .revertBox .. => some .revertBox
  | .revertDiamond .. => some .revertDiamond

/-- The solkey taclet a derivation's last step is. -/
def Taclet.origin {Γ Γ' : Ctx} {s : Stmt C Γ Γ'} {pr : Premise C Γ Γ'} : Taclet C m s pr → KeyOrigin
  | .storageFieldRead_unfold_rightFst .. => .taclet .storageFieldRead_unfold_rightFst
  | .storageIndexRead_unfold_rightFst .. => .taclet .storageIndexRead_unfold_rightFst
  | .storageIndexRead_unfold_rightSndIndex .. => .taclet .storageIndexRead_unfold_rightSndIndex
  | .storageFieldRead_unfold_rightSndResult .. => .taclet .storageFieldRead_unfold_rightSndResult
  | .storageIndexRead_unfold_rightSndResult .. => .taclet .storageIndexRead_unfold_rightSndResult
  | .storageFieldWrite_unfold_leftFst .. => .taclet .storageFieldWrite_unfold_leftFst
  | .storageFieldWriteStorageRef_unfold_leftFst .. => .taclet .storageFieldWriteStorageRef_unfold_leftFst
  | .storageIndexWrite_unfold_leftFst .. => .taclet .storageIndexWrite_unfold_leftFst
  | .storageIndexWriteStorageRef_unfold_leftFst .. => .taclet .storageIndexWriteStorageRef_unfold_leftFst
  | .storageIndexWriteNonSimpleIndexCapture .. => .taclet .storageIndexWriteNonSimpleIndexCapture
  | .storageIndexWriteStorageRefNonSimpleIndexCapture .. => .taclet .storageIndexWriteStorageRefNonSimpleIndexCapture
  | .storageRootWriteValueRhsCapture .. => .taclet .storageRootWriteValueRhsCapture
  | .fieldWriteValueRhsCapture .. => .taclet .fieldWriteValueRhsCapture
  | .indexWriteValueRhsCapture .. => .taclet .indexWriteValueRhsCapture
  | .storageFieldDelete_unfold_leftFst .. => .taclet .storageFieldDelete_unfold_leftFst
  | .storageIndexDelete_unfold_leftFst .. => .taclet .storageIndexDelete_unfold_leftFst
  | .storageIndexDeleteNonSimpleIndexCapture .. => .taclet .storageIndexDeleteNonSimpleIndexCapture
  | .localValueDeclInitDrop .. => .taclet .localValueDeclInitDrop
  | .valueDeclSkip .. => .taclet .valueDeclSkip
  | .localValueAssign .. => .taclet .localValueAssign
  | .storageRootReadSelect .. => .taclet .storageRootReadSelect
  | .storageFieldReadFind .. => .taclet .storageFieldReadFind
  | .storageIndexReadMappingFind .. => .taclet .storageIndexReadMappingFind
  | .storageIndexReadArrayFind .. => .taclet .storageIndexReadArrayFind
  | .storageRootWriteStore .. => .taclet .storageRootWriteStore
  | .storageRootWriteCopySource .. => .taclet .storageRootWriteCopySource
  | .storageFieldReadStoreRoot .. => .taclet .storageFieldReadStoreRoot
  | .storageIndexReadMappingStoreRoot .. => .taclet .storageIndexReadMappingStoreRoot
  | .storageIndexReadArrayStoreRoot .. => .taclet .storageIndexReadArrayStoreRoot
  | .storageFieldWriteSave .. => .taclet .storageFieldWriteSave
  | .storageFieldWriteCopySource .. => .taclet .storageFieldWriteCopySource
  | .storageIndexWriteMappingSave .. => .taclet .storageIndexWriteMappingSave
  | .storageIndexWriteArraySave .. => .taclet .storageIndexWriteArraySave
  | .storageIndexWriteMappingCopySource .. => .taclet .storageIndexWriteMappingCopySource
  | .storageIndexWriteArrayCopySource .. => .taclet .storageIndexWriteArrayCopySource
  | .storageLocalRootRebind .. => .taclet .storageLocalRootRebind
  | .storageFieldReadBindLocalRoot .. => .taclet .storageFieldReadBindLocalRoot
  | .storageIndexReadMappingBindLocalRoot .. => .taclet .storageIndexReadMappingBindLocalRoot
  | .storageIndexReadArrayBindLocalRoot .. => .taclet .storageIndexReadArrayBindLocalRoot
  | .storageLocalDeclInitDrop .. => .taclet .storageLocalDeclInitDrop
  | .storageRootDelete .. => .taclet .storageRootDelete
  | .storageFieldDelete .. => .taclet .storageFieldDelete
  | .storageIndexDelete .. => .taclet .storageIndexDelete
  | .binopAssignment op .. => (ruleEffect (.binopAssignment op)).origin
  | .binopUnfoldLeft op .. => (ruleEffect (.binopUnfoldLeft op)).origin
  | .binopUnfoldRight op .. => (ruleEffect (.binopUnfoldRight op)).origin
  | .logicalAndShortCircuitRhs .. => .taclet .logicalAndShortCircuitRhs
  | .logicalOrShortCircuitRhs .. => .taclet .logicalOrShortCircuitRhs
  | .unopAssignment op .. => (ruleEffect (.unopAssignment op)).origin
  | .unopCapture op .. => (ruleEffect (.unopCapture op)).origin
  | .ifElseSplit .. => .taclet .ifElseSplit
  | .requireSimple .. => .taclet .requireSimple
  | .assertSimple .. => .taclet .assertSimple
  | .revertBox .. => .taclet .revertBox
  | .revertDiamond .. => .taclet .revertDiamond

/-- **The names agree**: the old rule a step bridges to records the step's
taclet as (one of) its origins.  `alice.age = 10;` is
`storageFieldWriteSave`, whose old rule `storageFieldWriteSave` has that
origin. -/
theorem Taclet.origin_claimed {Γ Γ' : Ctx} {s : Stmt C Γ Γ'} {pr : Premise C Γ Γ'}
    (d : Taclet C m s pr) {r : RuleName} (h : d.rule = some r) :
    ∀ t ∈ d.origin.taclets, t ∈ (ruleEffect r).origin.taclets := by
  cases d <;> (try cases m) <;> simp only [Taclet.rule, Option.some.injEq, reduceCtorEq] at h <;> subst h <;>
    simp only [Taclet.origin] <;> first | exact fun _ h => h | decide

/-- The one step without a rule is the branch split. -/
theorem Taclet.rule_none {Γ Γ' : Ctx} {s : Stmt C Γ Γ'} {pr : Premise C Γ Γ'}
    (d : Taclet C m s pr) (h : d.rule = none) : d.origin = .taclet .ifElseSplit := by
  cases d <;> (try cases m) <;> simp_all [Taclet.rule, Taclet.origin]

end Kernel
end Solidity
