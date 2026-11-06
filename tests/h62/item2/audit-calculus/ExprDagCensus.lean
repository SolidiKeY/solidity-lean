import tests.h62.item2.«audit-calculus».KernelCensus

/-! Optional lossless structural DAG export. ExprStructMap preserves binder
names and annotations; ExprMap's alpha equivalence would be insufficient.
This tooling never reduces, rewrites or edits the frozen theorem types. -/
namespace H62.AuditCalculus.ExprDagCensus
open Lean Meta Elab Command

private structure Encoder where
  seen : ExprStructMap Nat := {}
  nodes : Array Json := #[]

private def visit (e : Expr) : StateM Encoder Nat := do
  if let some id := (← get).seen.get? ⟨e⟩ then
    return id
  let row ← match e with
    | .app f a => do
        let fi ← visit f
        let ai ← visit a
        pure <| Json.arr #[toJson "app", toJson fi, toJson ai]
    | .lam n d b bi => do
        let di ← visit d
        let bid ← visit b
        pure <| Json.arr #[toJson "lam", toJson (reprStr n), toJson di, toJson bid, toJson (reprStr bi)]
    | .forallE n d b bi => do
        let di ← visit d
        let bid ← visit b
        pure <| Json.arr #[toJson "forall", toJson (reprStr n), toJson di, toJson bid, toJson (reprStr bi)]
    | .letE n t v b nondep => do
        let ti ← visit t
        let vi ← visit v
        let bid ← visit b
        pure <| Json.arr #[toJson "let", toJson (reprStr n), toJson ti, toJson vi, toJson bid, toJson nondep]
    | .mdata md b => do
        let bid ← visit b
        pure <| Json.arr #[toJson "mdata", toJson (reprStr md), toJson bid]
    | .proj n i b => do
        let bid ← visit b
        pure <| Json.arr #[toJson "proj", toJson (reprStr n), toJson i, toJson bid]
    | _ => pure <| Json.arr #[toJson "leaf", toJson (reprStr e)]
  let id := (← get).nodes.size
  modify fun state => { seen := state.seen.insert ⟨e⟩ id, nodes := state.nodes.push row }
  return id

/-- Full constructor/field representation with backward edges for shared
subexpressions. Leaf reprs retain names, levels, literals and variable indices. -/
def expressionDag (e : Expr) : Json :=
  let (root, state) := (visit e).run {}
  Json.mkObj [("root", toJson root), ("nodes", Json.arr state.nodes)]

private def leadingDomains : Expr → Array Expr
  | .forallE _ d b _ => #[d] ++ leadingDomains b
  | _ => #[]

private def theoremRecord (name : Name) (info : ConstantInfo) : MetaM Json := do
  if info.type.hasMVar || info.type.hasFVar then
    throwError "constant type contains unresolved/free variables"
  let (root, state) := (visit info.type).run {}
  let domains := leadingDomains info.type
  let binders ← forallTelescope info.type fun xs _ => do
    unless xs.size == domains.size do
      throwError "nonreducing telescope/domain count mismatch"
    xs.mapIdxM fun i x => do
      let decl ← x.fvarId!.getDecl
      let some domain := state.seen.get? ⟨domains[i]!⟩
        | throwError "domain absent from exact expression graph"
      return Json.mkObj [
        ("name", toJson decl.userName.toString),
        ("type", toJson "exact domain node in full expression DAG"),
        ("domain_node", toJson domain),
        ("is_prop", toJson (← isProp (← inferType x))),
        ("binder_info", toJson (reprStr decl.binderInfo))]
  return Json.mkObj [
    ("name", toJson name.toString),
    ("user_name", toJson ((privateToUserName? name).getD name).toString),
    ("is_private", toJson (isPrivateName name)),
    ("is_internal_detail", toJson name.isInternalDetail),
    ("level_params", toJson (info.levelParams.map Name.toString)),
    ("type_pretty", toJson "see full exact structural DAG and frozen source signature"),
    ("type_expression_format", toJson "expr-dag-v1"),
    ("type_expression", Json.mkObj [("root", toJson root), ("nodes", Json.arr state.nodes)]),
    ("binders", Json.arr binders),
    ("joint_witness", toJson "pending"),
    ("premise_role", toJson "requires semantic review: global vs per-input")]

elab "#audit_module_dag_chunk " module:str " from " offset:num " count " limit:num : command => do
  let moduleName := module.getString.toName
  let first := offset.getNat
  let count := limit.getNat
  unless count > 0 do throwError "chunk count must be positive"
  let env ← getEnv
  let mut names : Array Name := #[]
  for (name, info) in env.constants.toList do
    if let .thmInfo _ := info then
      if let some idx := env.getModuleIdxFor? name then
        if env.header.moduleNames[idx.toNat]! == moduleName then names := names.push name
  names := names.qsort (fun a b => a.toString < b.toString)
  let total := names.size
  unless first < total || (first == 0 && total == 0) do throwError "chunk offset outside module"
  let selected := (names.toList.drop first).take count
  let records ← liftTermElabM do
    selected.toArray.mapM fun name => do theoremRecord name (← getConstInfo name)
  logInfo m!"H62_KERNEL_CENSUS_CHUNK {Json.mkObj [
    ("module", toJson module.getString), ("offset", toJson first),
    ("limit", toJson count), ("total", toJson total),
    ("theorems", Json.arr records)] |>.compress}"

end H62.AuditCalculus.ExprDagCensus
