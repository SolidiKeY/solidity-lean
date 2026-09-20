import Solidity.Calculus.Coverage

/-!
# Concrete residue witnesses and a covered negative control

Instantiates the coverage dichotomy of `Calculus/Coverage.lean` on concrete,
`stmtWt`-well-typed statements:

* **Witness A** — `v = net(a);`: a stack variable bound from the `net`
  ledger read.  `wtExpr` admits exactly the call shape
  `net(addr)` at a numeric type (StateTyping.lean), yet no rule of the calculus
  matches a `mkCall` right-hand side outside the memory-copy cells, so
  the statement is `ResidueShape` (`assignCallRhs`), claimed by no
  rule under either modality, and so stuck in the rewrite calculus.

* **Witness B** — `Person memory p = people[i];`: a memory declaration
  initialized from a storage *index* read.  The `storageToMemoryDecl*`
  rules cover storage roots and storage *fields* only, so the index
  shape is residue (`memoryDeclBadInit`).

* **Negative control** — `people[k] = carol;`: a memory value written
  through a storage mapping index.  Covered by
  `memoryToStorageIndexMappingCopyRoot` — this statement *was* residue
  before the 2026-09-08 gap fix split `memoryToStorageSaveIndex` into
  the mapping/array `CopyRoot` rules and taught
  `assignSimpleCandidate`'s storage-index memory-rhs branch to
  discriminate `arrayTyB`/`mappingTyB`.
-/

namespace Solidity
namespace Counterexamples
namespace CoverageResidue

open Rules
open Coverage

def personMapTy : Ty :=
  Ty.ref (RefTy.mapping Ty.uint StandardExample.personTy)

/-- Binding context: value locals `v a i k` and the memory struct
`carol`. -/
def gamma : Semantics.Ctx :=
  [("v", Semantics.BTy.stack Ty.uint),
   ("a", Semantics.BTy.stack Ty.uint),
   ("i", Semantics.BTy.stack Ty.uint),
   ("k", Semantics.BTy.stack Ty.uint),
   ("carol", Semantics.BTy.mem StandardExample.personTy)]

/-- Storage layout: the global mapping `people : mapping(uint => Person)`. -/
def layout : Semantics.Layout :=
  ⟨[("people", personMapTy)]⟩

def vPlace : PlaceExpr :=
  PlaceExpr.var Kind.stack Ty.uint (Field.primitive "v" Ty.uint)

def aExpr : WrappedExpr :=
  WrappedExpr.var Kind.stack Ty.uint (Field.primitive "a" Ty.uint)

def iExpr : WrappedExpr :=
  WrappedExpr.var Kind.stack Ty.uint (Field.primitive "i" Ty.uint)

def kExpr : WrappedExpr :=
  WrappedExpr.var Kind.stack Ty.uint (Field.primitive "k" Ty.uint)

def peopleExpr : WrappedExpr :=
  WrappedExpr.var Kind.storage personMapTy
    (Field.identity "people"
      (RefTy.mapping Ty.uint StandardExample.personTy)
      (some StorageOrigin.global))

def carolExpr : WrappedExpr :=
  WrappedExpr.var Kind.memory StandardExample.personTy
    (Field.identity "carol" StandardExample.personRef)

/-! ## Witness A: `v = net(a);` -/

def netCallAssign : Stmt :=
  Stmt.assign vPlace
    (Typed.WrappedExpr.mkCall Kind.stack Ty.uint "net" [aExpr])

/-- (i) The statement typechecks. -/
theorem netCallAssign_wt :
    Semantics.stmtWt gamma layout netCallAssign = some gamma := by
  decide

/-- (ii) It has a residue shape — established through the decidable
Boolean mirror. -/
theorem netCallAssign_residue : ResidueShape netCallAssign :=
  residueShape_iff_residueShapeB.mpr (by decide)

/-- (iii) No rule of the calculus claims it, in either modality. -/
theorem netCallAssign_not_covered_box :
    ¬ Rules.ruleApplies .box netCallAssign :=
  residue_not_covered netCallAssign_residue

theorem netCallAssign_not_covered_diamond :
    ¬ Rules.ruleApplies .diamond netCallAssign :=
  residue_not_covered netCallAssign_residue

/-- (iv) The rewrite calculus is stuck on it: no rule step exists, under
any block modality (there is no catch-all tier). -/
theorem netCallAssign_no_step (sm : SolidityModality) :
    ¬ ∃ cond rhs, RuleStep sm netCallAssign cond rhs :=
  fun ⟨_, _, h⟩ =>
    let ⟨_, hm⟩ := RuleStep.ruleApplies_of_ruleStep h
    residue_not_covered netCallAssign_residue hm

/-- The dichotomy lands on the residue side. -/
example : Rules.ruleApplies .box netCallAssign ∨
    ResidueShape netCallAssign :=
  coverage_residue .box netCallAssign_wt

/-! ## Witness B: `Person memory p = people[i];` -/

def memoryDeclFromIndex : Stmt :=
  Stmt.memoryDecl StandardExample.personTy "p"
    (some (WrappedExpr.index Kind.storage StandardExample.personTy
      peopleExpr iExpr))

/-- (i) The statement typechecks (binding `p` as a memory local). -/
theorem memoryDeclFromIndex_wt :
    (Semantics.stmtWt gamma layout memoryDeclFromIndex).isSome = true := by
  decide

/-- (ii) It has a residue shape: a storage-*index* initializer is
outside the `storageToMemoryDecl*` family (roots and fields only). -/
theorem memoryDeclFromIndex_residue : ResidueShape memoryDeclFromIndex :=
  residueShape_iff_residueShapeB.mpr (by decide)

/-- (iii) No rule of the calculus claims it, in either modality. -/
theorem memoryDeclFromIndex_not_covered_box :
    ¬ Rules.ruleApplies .box memoryDeclFromIndex :=
  residue_not_covered memoryDeclFromIndex_residue

theorem memoryDeclFromIndex_not_covered_diamond :
    ¬ Rules.ruleApplies .diamond memoryDeclFromIndex :=
  residue_not_covered memoryDeclFromIndex_residue

/-- (iv) The rewrite calculus is stuck on it. -/
theorem memoryDeclFromIndex_no_step (sm : SolidityModality) :
    ¬ ∃ cond rhs, RuleStep sm memoryDeclFromIndex cond rhs :=
  fun ⟨_, _, h⟩ =>
    let ⟨_, hm⟩ := RuleStep.ruleApplies_of_ruleStep h
    residue_not_covered memoryDeclFromIndex_residue hm

example : Rules.ruleApplies .box memoryDeclFromIndex ∨
    ResidueShape memoryDeclFromIndex := by
  obtain ⟨Γ', hwt⟩ := Option.isSome_iff_exists.mp memoryDeclFromIndex_wt
  exact coverage_residue .box hwt

/-! ## Negative control: `people[k] = carol;` is covered

Residue before the 2026-09-08 gap fix (`memoryToStorageSaveIndex` split
into the mapping/array `CopyRoot` rules); now claimed by
`memoryToStorageIndexMappingCopyRoot`. -/

def mappingWrite : Stmt :=
  Stmt.assign
    (PlaceExpr.index Kind.storage StandardExample.personTy peopleExpr kExpr)
    carolExpr

theorem mappingWrite_wt :
    Semantics.stmtWt gamma layout mappingWrite = some gamma := by
  decide

/-- The dispatch function names the covering rule … -/
theorem mappingWrite_candidate :
    UniquenessAux.candidate .box mappingWrite =
      some .memoryToStorageIndexMappingCopyRoot := by
  decide

/-- … and `candidate_applies` turns that into coverage. -/
theorem mappingWrite_covered : Rules.ruleApplies .box mappingWrite := by
  obtain ⟨h1, h2, h3⟩ :=
    candidate_applies (by decide) mappingWrite_candidate
  exact ⟨.memoryToStorageIndexMappingCopyRoot, h1, h2, h3⟩

/-- Consequently it is *not* residue. -/
theorem mappingWrite_not_residue : ¬ ResidueShape mappingWrite :=
  fun h => residue_not_covered h mappingWrite_covered

end CoverageResidue
end Counterexamples
end Solidity
