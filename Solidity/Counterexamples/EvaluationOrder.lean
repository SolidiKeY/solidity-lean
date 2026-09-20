import Solidity.Calculus.RuleSoundness
import Solidity.Semantics.DecEq

/-!
# Evaluation order: the `*WriteUnfoldLeft*` rules, before and after the fix

The interpreter evaluates an assignment's right-hand side *before* resolving
its target (solc order, `Semantics.execAssignNested`).  Before
`Rules.freezeRhs`, `storageFieldWriteUnfoldLeftFst` and
`storageIndexWriteUnfoldLeftSndIndex` captured the *target path* (resp. the
index) into a scratch alias first and only then ran the assignment.  When the
path is impure and interferes with the right-hand side, the two disagree:

* `people[i++].age = i` with `i = 0`: the original reads `i = 0` and then
  writes it at index `0`; the pre-fix residual increments `i` while capturing
  the path and then writes `i = 1` at index `0`.
* `values[i++] = i`: the same, through the index capture.

This file now records **both** directions.

*The refutations* are kept, spelled out against the pre-fix residual literally
rather than computed from `ruleEffect`, so they stay true as the
historical record of what was wrong.

*The positive results* instantiate the general soundness theorems at the same
two programs: with `Rules.freezeRhs` binding the value into `rv` ahead of the
capture, rule and interpreter agree — on exactly the programs that used to be
excluded by the `hev`/`hstable`/`pureExpr index` side conditions.

`Counterexamples/ErrorOrder.lean` carries the companion result: the freeze is
needed even when the path is *pure*, because the two sides otherwise fail with
different `Halt`s.
-/
namespace Solidity
namespace Counterexamples
namespace EvaluationOrder

open Rules RuleSoundness Semantics

/-- The captured index alias `idx`, as the pre-fix residual used it. -/
abbrev idxExprCE (ty : Ty) : WrappedExpr :=
  Rules.aliasExpr Kind.stack ty Rules.indexAliasName

/-- `people = [default Person]`, `values = [0]`, stack `i = 0`.  (The
calculus store's arrays are empty, on which both sides would revert on the
bounds check and agree.) -/
def store : State :=
  { State.exampleStore with
      storage :=
        setBy "values" (SVal.array [SVal.int 0] [])
          (setBy "people"
            (SVal.array [defaultForRef (RefTy.struct "Person")] [])
            State.exampleStore.storage),
      env := [("i", Binding.val (Value.int 0))] }

/-- Agreement forces equal storages (or the same abort). -/
theorem ResultsAgree.map_storage {ns : List Name} {a b : Res State}
    (h : ResultsAgree ns a b) :
    a.map State.storage = b.map State.storage := by
  match a, b, h with
  | .error e₁, .error e₂, h =>
      have h' : e₁ = e₂ := h
      subst h'
      rfl
  | .ok s₁, .ok s₂, h =>
      have h' : EnvAgreeExcept ns s₁ s₂ := h
      simp only [Except.map, h'.storage]
  | .error _, .ok _, h => exact (h : False).elim
  | .ok _, .error _, h => exact (h : False).elim

/-! ## `people[i++].age = i` vs `storageFieldWriteUnfoldLeftFst` -/

def fieldWrite : Stmt := sstmt!{ people[i++].age = i }

theorem fieldWrite_cond :
    (ruleEffect .storageFieldWriteUnfoldLeftFst).cond fieldWrite := by
  change _ = true ∧ _ = true ∧ ¬ (_ = true)
  decide

/-- The rule's residual: capture the path `people[i++]` into `sp`, then
`sp.age = i`. -/
def fieldWriteResidual : Block :=
  (ruleEffect .storageFieldWriteUnfoldLeftFst).block fieldWrite
    fieldWrite_cond

/-- The original writes the *old* `i`: `people[0].age = 0`. -/
theorem fieldWrite_original :
    (execStmt store fieldWrite).map
        (fun s => s.findStorage "people" [Seg.at 0, Seg.field "age"]) =
      .ok (.ok (SVal.int 0)) := by
  native_decide

/-- With the freeze in place the residual writes the *old* `i`, as the
interpreter does: `people[0].age = 0`. -/
theorem fieldWrite_residual :
    (execBlock store fieldWriteResidual).map
        (fun s => s.findStorage "people" [Seg.at 0, Seg.field "age"]) =
      .ok (.ok (SVal.int 0)) := by
  native_decide

/-- **`people[i++].age = i` is in scope now.**  Not a `native_decide` check on
one store but the general theorem instantiated here: the rule agrees with the
interpreter on this program, which the old `hev`/`hstable` hypotheses excluded. -/
theorem fieldWrite_agrees :
    ResultsAgree aliasNames
      (execStmt store fieldWrite) (execBlock store fieldWriteResidual) :=
  storageFieldWriteUnfoldLeftFst_sound store _ _ _ _ fieldWrite_cond
    (by decide) (by decide)

/-! ### The pre-fix residual, kept as the historical refutation

Spelled out literally: capture the path `people[i++]` into `sp`, then
`sp@Person.age = i`, with no `rv` freeze. -/

def fieldWritePreFixResidual : Block :=
  [ captureStoragePath (sexpr!{ people[i++] }),
    sstmt!{ sp@Person.age = i } ]

/-- The pre-fix residual writes the *incremented* `i`: `people[0].age = 1`. -/
theorem fieldWrite_preFix_residual :
    (execBlock store fieldWritePreFixResidual).map
        (fun s => s.findStorage "people" [Seg.at 0, Seg.field "age"]) =
      .ok (.ok (SVal.int 1)) := by
  native_decide

theorem fieldWrite_preFix_storage_ne :
    (execStmt store fieldWrite).map State.storage ≠
      (execBlock store fieldWritePreFixResidual).map State.storage := by
  native_decide

/-- **The pre-fix `storageFieldWriteUnfoldLeftFst` was not sound on
`people[i++].age = i`.** -/
theorem fieldWrite_preFix_not_sound :
    ¬ ResultsAgree aliasNames
        (execStmt store fieldWrite)
        (execBlock store fieldWritePreFixResidual) :=
  fun h => fieldWrite_preFix_storage_ne (ResultsAgree.map_storage h)

/-! ## `values[i++] = i` vs `storageIndexWriteUnfoldLeftSndIndex` -/

def indexWrite : Stmt := sstmt!{ values[i++] = i }

theorem indexWrite_cond :
    (ruleEffect .storageIndexWriteUnfoldLeftSndIndex).cond indexWrite := by
  change _ = true ∧ _ = true ∧ _ = true ∧ ¬ (_ = true)
  decide

def indexWriteResidual : Block :=
  (ruleEffect .storageIndexWriteUnfoldLeftSndIndex).block indexWrite
    indexWrite_cond

theorem indexWrite_original :
    (execStmt store indexWrite).map
        (fun s => s.findStorage "values" [Seg.at 0]) =
      .ok (.ok (SVal.int 0)) := by
  native_decide

/-- With the freeze the residual writes the *old* `i`, as the interpreter
does: `values[0] = 0`. -/
theorem indexWrite_residual :
    (execBlock store indexWriteResidual).map
        (fun s => s.findStorage "values" [Seg.at 0]) =
      .ok (.ok (SVal.int 0)) := by
  native_decide

/-- **`values[i++] = i` is in scope now**, by the general theorem — the
program the old `pureExpr index` hypothesis excluded. -/
theorem indexWrite_agrees :
    ResultsAgree aliasNames
      (execStmt store indexWrite) (execBlock store indexWriteResidual) :=
  storageIndexWriteUnfoldLeftSndIndex_sound store _ _ _ _ indexWrite_cond
    (by decide) (by decide)

/-! ### The pre-fix residual, kept as the historical refutation -/

def indexWritePreFixResidual : Block :=
  [ captureIndex (sexpr!{ i++ }),
    Stmt.assign
      (PlaceExpr.index Kind.storage Ty.uint (sexpr!{ values })
        (idxExprCE Ty.uint))
      (sexpr!{ i }) ]

/-- The pre-fix residual writes the *incremented* `i`: `values[0] = 1`. -/
theorem indexWrite_preFix_residual :
    (execBlock store indexWritePreFixResidual).map
        (fun s => s.findStorage "values" [Seg.at 0]) =
      .ok (.ok (SVal.int 1)) := by
  native_decide

theorem indexWrite_preFix_storage_ne :
    (execStmt store indexWrite).map State.storage ≠
      (execBlock store indexWritePreFixResidual).map State.storage := by
  native_decide

/-- **The pre-fix `storageIndexWriteUnfoldLeftSndIndex` was not sound on
`values[i++] = i`.** -/
theorem indexWrite_preFix_not_sound :
    ¬ ResultsAgree aliasNames
        (execStmt store indexWrite)
        (execBlock store indexWritePreFixResidual) :=
  fun h => indexWrite_preFix_storage_ne (ResultsAgree.map_storage h)

end EvaluationOrder
end Counterexamples
end Solidity
