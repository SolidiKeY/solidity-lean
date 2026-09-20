import Solidity.Calculus.RuleSoundness
import Solidity.Semantics.DecEq

/-!
# The mapping side conditions of the storage copy are necessary

Two soundness theorems about the storage-copy capture rules carry a
hypothesis `tyHasMapping rhs.ty = false`, and each refutation below drops it
and exhibits a closed witness where the conclusion fails.  The hypothesis is
what the AST guarantees — `TypedStmt.Assign.mk` cannot be built for a
storage-to-storage copy of a mapping-carrying type, and `stmtTypingOk`
states the same — so the witnesses are untyped `Stmt.assign` terms no front
end produces; the point is that the calculus does need the guard the front
end gives it.

- **M4** — `tyHasMapping rhs.ty` in `storageIndexReadUnfoldRightSndResult_sound`,
  whose path *and* index are simple. The field rule's discharge
  (`resolveS_simple_err_stuck`) does not carry over: resolving an index
  *evaluates* the index expression, and a storage-kind variable is read
  out of the store, which reverts on an out-of-bounds alias — an alias
  `resolveS` builds without a bounds check. So the guard's halt and the
  resolution's halt come apart on a simple index too.
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

open Semantics Rules RuleSoundness

/-! ## M4 — `tyHasMapping rhs.ty` on a simple index -/

/-- `LedgerUse[]`: an element type that carries a mapping through `Ledger`. -/
def m4ElemTy : Ty := Ty.ref (RefTy.struct "LedgerUse")
def m4ArrTy : Ty := Ty.ref (RefTy.array m4ElemTy)

/-- `ledgerUses[age]`: a simple path and a simple index. -/
def m4Rhs : WrappedExpr :=
  WrappedExpr.index Kind.storage m4ElemTy
    (WrappedExpr.var Kind.storage m4ArrTy ⟨"ledgerUses", m4ArrTy, some StorageOrigin.global⟩)
    (WrappedExpr.var Kind.storage Ty.uint ⟨"age", Ty.uint, some StorageOrigin.global⟩)

def m4LedgerTy : Ty := Ty.ref (RefTy.struct "Ledger")

/-- `ledgerUse.ledger`: the rule wants a non-simple target. -/
def m4Lhs : PlaceExpr :=
  ⟨WrappedExpr.field Kind.storage m4LedgerTy
      (WrappedExpr.var Kind.storage m4ElemTy ⟨"ledgerUse", m4ElemTy, some StorageOrigin.global⟩)
      ⟨"ledger", m4LedgerTy, none⟩,
    by native_decide⟩

/-- `age` aliased to `values[9]` with `values` empty — the binding a
`storagePlaceAlias` capture of `values[9]` leaves, since `resolveS` builds a
path without consulting the array's length. -/
def m4Store : State :=
  { State.testSuiteStore with
      storage := ("ledgerUse", defaultForRef (RefTy.struct "LedgerUse")) :: State.testSuiteStore.storage,
      env := [("age", Binding.spath "values" [Seg.at 9])] }

def m4Prog : Stmt := Stmt.assign m4Lhs m4Rhs

/-- The residual of `storageIndexReadUnfoldRightSndResult`. -/
def m4Residual : Block :=
  [Stmt.storagePlaceAlias m4Rhs.ty valueAliasName m4Rhs,
    Stmt.assign m4Lhs (aliasExpr Kind.storage m4Rhs.ty valueAliasName)]

/-- Value first: the mapping guard fires before anything is read, so the
assignment is **stuck**. -/
theorem m4_original : execStmt m4Store m4Prog = .error .stuck := by
  native_decide

/-- Path first: the residual resolves `ledgerUses[age]`, reads `age` through
its alias, and **reverts**. -/
theorem m4_residual : execBlock m4Store m4Residual = .error .revert := by
  native_decide

/-- Every other hypothesis of the theorem holds: the rule's condition (a
simple path and a simple index), a pure target that resolves, and the
right-hand side of storage kind; only `tyHasMapping` fails. -/
theorem m4_hyps :
    (ruleEffect .storageIndexReadUnfoldRightSndResult).cond m4Prog ∧
      pureExpr m4Lhs.expr = true ∧ m4Rhs.kind = Kind.storage ∧
      (match resolveLoc m4Store m4Lhs.expr with
       | .ok _ => true
       | .error _ => false) = true ∧
      tyHasMapping m4Rhs.ty = true := by
  exact ⟨⟨rfl, rfl, rfl, rfl⟩, rfl, rfl, by native_decide, by native_decide⟩

/-- **M4.** Drop the hypothesis and the theorem is false: the two sides halt
differently, exactly as in M3, with no impure subexpression anywhere. -/
theorem m4_refutes :
    ¬ ResultsAgree aliasNames (execStmt m4Store m4Prog) (execBlock m4Store m4Residual) := by
  rw [m4_original, m4_residual]
  intro h
  exact Halt.noConfusion (h : Halt.stuck = Halt.revert)


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
