import tests.h62.item2.«audit-calculus».ExprDagCensus

/-! Executed audit-tool controls. These check serialization, not compiler
correctness or a general injectivity theorem. No failed theorem is declared. -/
open Lean H62.AuditCalculus.ExprDagCensus in
run_cmd do
  let p := mkConst (Name.mkSimple "True")
  let sort := mkSort .zero
  let requireDifferent := fun (a b : Expr) => do
    if (expressionDag a).compress == (expressionDag b).compress then
      throwError "distinct constructor/field control collapsed"
  requireDifferent (.forallE (Name.mkSimple "x") sort (.bvar 0) .default)
    (.forallE (Name.mkSimple "y") sort (.bvar 0) .default)
  requireDifferent (.forallE (Name.mkSimple "x") sort (.bvar 0) .default)
    (.forallE (Name.mkSimple "x") sort (.bvar 0) .implicit)
  requireDifferent (.letE (Name.mkSimple "x") sort p p false)
    (.letE (Name.mkSimple "x") sort p p true)
  requireDifferent (mkConst (.num (Name.mkSimple "n") 0))
    (mkConst (.str (Name.mkSimple "n") "0"))
  requireDifferent (mkSort (.param (Name.mkSimple "u")))
    (mkSort (.param (Name.mkSimple "v")))
  requireDifferent (.mdata (KVMap.empty.insert (Name.mkSimple "tag") true) p)
    (.mdata (KVMap.empty.insert (Name.mkSimple "tag") false) p)
  requireDifferent (.proj (Name.mkSimple "S") 0 p) (.proj (Name.mkSimple "S") 1 p)
  requireDifferent (.lit (.natVal 7)) (.lit (.natVal 8))
  requireDifferent (.lit (.strVal "a")) (.lit (.strVal "b"))
  requireDifferent (.bvar 0) (.bvar 1)
  let repeated := mkApp2 (mkConst (Name.mkSimple "And")) p p
  let copied := mkApp2 (mkConst (Name.mkSimple "And"))
    (mkConst (Name.mkSimple "True")) (mkConst (Name.mkSimple "True"))
  unless (expressionDag repeated).compress == (expressionDag copied).compress do
    throwError "sharing changes structural representation"
  logInfo "H62_EXPR_DAG_CONTROLS 11 passed"
