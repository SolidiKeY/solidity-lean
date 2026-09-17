import Solidity.Update.Theory
import Solidity.RuleSoundness
import Solidity.DecEq

/-!
# The mapping side conditions of the write and the delete are necessary

Three theorems about storage writes carry a side condition shaped like
"there is no mapping here", and after the copy family was folded into the
leaf of a write it is worth asking which of them the fold made redundant.
None of them: each refutation below drops exactly one and exhibits a
closed witness where the conclusion fails.

- **M1** — `mergeFree` in `StValue.selectSt_delValue`. A delete does not
  push through a selector on a `merge`, because the two sides dispatch on
  different trees: `delValue` reads the *new* side's shape (`base` of a
  `merge` is `base` of its right argument) and `selectSt` reads the *old*
  side's. The witness is sharper than the lemma's docstring, which blames
  the disagreement on mappings alone: here neither side is a mapping, and
  it is the array collapse that separates them.
- **M2** — `svalHasMapping cur` in `Theory.denote_save`, and with it
  `Update.theorySave_eq_theoryWrite`. This one is the fold's own content
  rather than residue: upstream's `save` keeps the location's mapping
  members through its leaf, `Semantics.SVal.save` overwrites them, and
  where the location holds a mapping the two terms denote different
  storages. The interpreter is stuck on exactly those programs
  (`tyHasMapping`, solc ≥ 0.7 rejects them), which is why the collapse is
  still enough for every write the rule table states.
- **M3** — `tyHasMapping rhs.ty` in the `*UnfoldRight*` soundness
  theorems whose right-hand-side path is not simple. The rule's residual
  resolves that path before it copies; the interpreter's mapping guard
  fires *ahead* of the resolution. When the path reverts, the two sides
  halt differently — `.stuck` against `.revert` — and `ResultsAgree`
  fails. Where the path is a `SimpleExpression` the resolution cannot
  revert, which is what `RuleSoundness.resolveS_simple_err_stuck` says
  and why `storageFieldReadUnfoldRightSndResult_sound` needs no such
  hypothesis.
-/

namespace Solidity
namespace Counterexamples
namespace MappingSideConditions

open Semantics Theory Theory.StValue Rules RuleSoundness

/-! ## M1 — `mergeFree` in `selectSt_delValue` -/

/-- The old side of the leaf: an array chain that still answers a field
selector, which is what makes the two dispatches disagree. -/
def oldSide : StValue :=
  StValue.storeSt (StValue.sval (SVal.array [])) (Seg.field "x")
    (StValue.sval (SVal.struct [("g", SVal.int 1)]))

/-- The new side: an ordinary struct leaf. -/
def newSide : StValue := StValue.sval (SVal.struct [("x", SVal.int 3)])

def m1 : StValue := StValue.merge oldSide newSide

/-- The two hypotheses that survive are satisfied: the term is neither a
mapping nor an array. -/
theorem m1_hyps : isMapping m1 = false ∧ isArray m1 = false := by
  exact ⟨rfl, rfl⟩

/-- …and `mergeFree`, the one dropped, is exactly what fails. -/
theorem m1_mergeFree : mergeFree m1 = false := rfl

/-- **M1.** Without `mergeFree`, `selectSt_delValue` is false: the delete
reaches the field through the old side on the left and keeps the whole
`merge` on the right. -/
theorem m1_refutes :
    selectSt (delValue m1) (Seg.field "x") ≠
      delValue (selectSt m1 (Seg.field "x")) := by
  decide

/-! ## M2 — `svalHasMapping cur` in `denote_save` -/

/-- A `Wallet` behind one field: `stash` is the mapping member a struct
written over `w` must keep. -/
def m2Root : SVal :=
  SVal.struct
    [("w", SVal.struct [("owner", SVal.int 1),
                        ("stash", SVal.map [] (SVal.int 0))])]

/-- The written value: a `Wallet` whose `stash` says something else.  A
copy source is a struct of the same type, so it carries the member; what
the leaf decides is whose value survives. -/
def m2New : SVal :=
  SVal.struct [("owner", SVal.int 2),
               ("stash", SVal.map [(1, SVal.int 7)] (SVal.int 0))]

def m2Path : List Seg := [Seg.field "w"]

/-- The value the write lands on. -/
def m2Cur : SVal :=
  SVal.struct [("owner", SVal.int 1), ("stash", SVal.map [] (SVal.int 0))]

/-- The location's current value is what carries the mapping, so the
dropped hypothesis is exactly the one that fails. -/
theorem m2_hyp :
    StValue.find (StValue.sval m2Root) m2Path = StValue.sval m2Cur ∧
      svalHasMapping m2Cur = true :=
  ⟨rfl, rfl⟩

/-- **M2.** Without it, `denote_save` is false: upstream's term keeps the
location's `stash` and the interpreter's write takes the source's. -/
theorem m2_refutes :
    denoteSt (StValue.save (StValue.sval m2Root) m2Path (StValue.sval m2New)) ≠
      m2Root.save m2Path m2New := by
  rw [StValue.save,
    denote_write_of
      (t := StValue.merge
        (StValue.asStruct (StValue.find (StValue.sval m2Root) m2Path))
        (StValue.sval m2New))
      (w := mergeKeepMaps m2Cur m2New)
      (by simp [m2Root, m2Path, m2New, m2Cur, StValue.find, StValue.selectSt,
        svalSelect, lookupBy, StValue.asStruct, denoteSt, mergeDen])]
  simp [m2Root, m2New, m2Cur, m2Path, SVal.save, mergeKeepMaps, mergeFields,
    mergeMember, lookupBy, setBy, bind, Except.bind]


/-! ## M3 — `tyHasMapping rhs.ty` in the capture template -/

/-- `people = []`, so nothing about the witness turns on what is stored. -/
def m3Store : State := { State.exampleStore with env := [] }

/-- `wallet.stash = people[1 / 0].stash`: a mapping-typed right-hand side
behind a *pure* path that reverts.  The target is a storage place that
resolves, the source is pure, and both are what
`captureAssignStorageRhs_sound` asks for. -/
def m3Lhs : PlaceExpr := ⟨sexpr!{ wallet.stash }, by rfl⟩
def m3Rhs : WrappedExpr := sexpr!{ people[1 / 0].stash }
def m3Prog : Stmt := Stmt.assign m3Lhs m3Rhs

/-- Value first: the interpreter's mapping guard fires before it resolves
anything, so the assignment is **stuck**. -/
theorem m3_original : execStmt m3Store m3Prog = .error .stuck := by
  native_decide

/-- Path first: the capture residual resolves `people[1 / 0]` and
**reverts**. -/
theorem m3_residual :
    execBlock m3Store
      [Stmt.storagePlaceAlias m3Rhs.ty valueAliasName m3Rhs,
        Stmt.assign m3Lhs (aliasExpr Kind.storage m3Rhs.ty valueAliasName)] =
      .error .revert := by
  native_decide

/-- Every other hypothesis of `captureAssignStorageRhs_sound` holds here:
the target resolves purely, the source is pure and of storage kind, and
`evalValue` reads it the way the bridge says. -/
theorem m3_hyps :
    pureExpr m3Lhs.expr = true ∧ pureExpr m3Rhs = true ∧
      m3Rhs.kind = Kind.storage ∧ tyHasMapping m3Rhs.ty = true :=
  ⟨rfl, rfl, rfl, by native_decide⟩

/-- **M3.** Drop the hypothesis and the capture template is unsound: the
two sides halt differently.  What replaces it in
`captureAssignStorageRhs_sound` is the weaker `hsafe`, which this witness
also fails — `resolveS` reverts here — and which a simple path
discharges outright (`resolveS_simple_err_stuck`). -/
theorem m3_refutes :
    ¬ ResultsAgree aliasNames (execStmt m3Store m3Prog)
        (execBlock m3Store
          [Stmt.storagePlaceAlias m3Rhs.ty valueAliasName m3Rhs,
            Stmt.assign m3Lhs (aliasExpr Kind.storage m3Rhs.ty valueAliasName)]) := by
  rw [m3_original, m3_residual]
  intro h
  exact Halt.noConfusion (h : Halt.stuck = Halt.revert)

end MappingSideConditions
end Counterexamples
end Solidity
