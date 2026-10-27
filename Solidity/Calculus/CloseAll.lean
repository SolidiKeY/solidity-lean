import Solidity.Calculus.Budget

/-!
# Ground instances after opening a leaf's binders

KeY's `allLeft` applies a universal premise to a ground term. Unlike the
scoped pre-pass in `AllLeft`, this fallback runs after the closer opens its
state and value binders: a later loop counter is then an ordinary local
term, so no term is moved into an older scope. Every instance is a checked
application of the original proof. Range/guard arguments are proved before
being supplied; a failed argument leaves the implication available.

The search has fixed declaration, candidate, application and binder budgets.
Each guard attempt has its own bounded heartbeats and runtime exceptions are
caught. This is term selection for `allLeft`, not quantifier elimination.
-/
namespace Solidity.Close.All

open Lean Meta Elab Tactic

/-- The numeric domains exposed by the scoped closer. -/
private def numeric (e : Expr) : Bool := e.isConstOf ``Int || e.isConstOf ``Nat

/-- Bound reduction as well as node counts, and roll back a failed step. -/
private def bounded (limit : Nat) (action : TacticM α) : TacticM (Option α) := do
  Budget.bounded limit action

/-- Prove one guard locally; failure restores the tactic and metavariable state. -/
private def guardProof (ty : Expr) : TacticM (Option Expr) := do
  let saved ← saveState
  let goals ← getGoals
  let proof ← mkFreshExprSyntheticOpaqueMVar ty
  let ok ← tryCatchRuntimeEx (Budget.within 1000 do
      setGoals [proof.mvarId!]
      Term.withoutErrToSorry <| withoutRecover <| evalTactic (← `(tactic| first | assumption | rfl | omega))
      return (← getUnsolvedGoals).isEmpty) (fun _ => pure false)
  if ok then
    let result ← instantiateMVars proof
    setGoals goals
    return some result
  saved.restore
  return none

/-- Supply at most eight propositional arguments, stopping at an unproved one. -/
private def guards (proof : Expr) : TacticM Expr := do
  let mut pf := proof
  for _ in [0:8] do
    let ty ← whnfR (← inferType pf)
    let .forallE _ dom _ _ := ty | return pf
    unless ← isProp dom do return pf
    let some arg ← guardProof dom | return pf
    pf := mkApp pf arg
  return pf

/-- Add a bounded collection of numeric instances. Original quantifiers can
be hidden once they have supplied an instance, just as `allLeftHide` does. -/
private def addInstances (replay : Bool) : TacticM (Array (TSyntax `tactic)) := withMainContext do
  let g ← getMainGoal
  let mut candidates : Array Expr := #[]
  let mut witnesses : Array Expr := #[]
  let mut locals : Array Expr := #[]
  -- the goal's own numeric locals (a quantified goal's opened variable)
  let mut own : Array Expr := #[]
  let target ← instantiateMVars (← g.getType)
  let mut todo : Array Expr := #[← g.getType]
  let mut pending : Array (Expr × Nat) := #[]
  let mut known : Array Expr := #[]
  let mut scanned := 0
  for d in ← getLCtx do
    if scanned == 256 then break
    scanned := scanned + 1
    if d.isImplementationDetail then continue
    let some (ty, proposition) ← bounded 1000 (do
      let ty ← whnfR (← instantiateMVars d.type)
      return (ty, ← isProp ty)) | break
    known := known.push ty
    todo := todo.push ty
    if numeric ty && locals.size < 8 then locals := locals.push d.toExpr
    if numeric ty && own.size < 4 && (target.find? (· == d.toExpr)).isSome then
      own := own.push d.toExpr
    if ty.isForall && pending.size < 32 && proposition then
      if numeric ty.bindingDomain! then pending := pending.push (d.toExpr, 0)
  -- An anonymised loop counter is the value projection of a typed local,
  -- rather than a free Int variable. Prioritise those projections.
  let mut nodes := 0
  let mut seen : Std.HashSet Expr := {}
  while !todo.isEmpty && nodes < 4096 && (candidates.size < 8 || witnesses.size < 4) do
    let e := todo.back!
    todo := todo.pop
    nodes := nodes + 1
    if seen.contains e then continue
    seen := seen.insert e
    -- A captured key identifies its witness even when it is a negative
    -- literal, rather than a numeric local or a value projection.
    if e.isAppOfArity ``Eq 3 && numeric (e.getArg! 0) then
      let left := e.getArg! 1
      let right := e.getArg! 2
      let hint := if left.hasLooseBVars && !right.hasLooseBVars then some right
        else if right.hasLooseBVars && !left.hasLooseBVars then some left else none
      if let some hint := hint then
        if !hint.hasMVar && witnesses.size < 4 && !witnesses.contains hint then
          witnesses := witnesses.push hint
    let projection := e.isAppOfArity ``Subtype.val 3 || match e with
      | .proj ``Subtype 0 _ => true
      | _ => false
    if candidates.size < 8 && projection && !e.hasLooseBVars && !e.hasMVar && !candidates.contains e then
      let some numericType ← bounded 1000 (do return numeric (← whnfR (← inferType e))) | break
      if numericType then candidates := candidates.push e
    match e with
    | .app f a => todo := (todo.push f).push a
    | .lam _ t body _ | .forallE _ t body _ => todo := (todo.push t).push body
    | .letE _ t v body _ => todo := ((todo.push t).push v).push body
    | .mdata _ body | .proj _ _ body => todo := todo.push body
    | _ => pure ()
  -- Keep the existing candidate cap; equality witnesses take priority.
  let mut selected : Array Expr := #[]
  for e in witnesses ++ candidates do
    if selected.size < 8 && !selected.contains e then selected := selected.push e
  candidates := selected
  for e in locals do
    if candidates.size < 8 && !candidates.contains e then candidates := candidates.push e
  -- the instances the goal asks for, past the cap: at most four more
  for e in own do
    if !candidates.contains e then candidates := candidates.push e
  if candidates.isEmpty || pending.isEmpty then throwError "sol_close_all: no numeric instances"
  let mut goal := g
  let mut cursor := 0
  let mut applications := 0
  let mut added := 0
  let mut hidden : Array FVarId := #[]
  let mut steps : Array (TSyntax `tactic) := #[]
  let mut stopped := false
  while cursor < pending.size && applications < 64 && !stopped do
    let (pf, depth) := pending[cursor]!
    cursor := cursor + 1
    if depth == 8 then continue
    let some ty ← bounded 1000 (do whnfR (← inferType pf)) | break
    let .forallE _ dom _ _ := ty | continue
    for term in candidates do
      if applications == 64 then break
      applications := applications + 1
      let attempt ← bounded 1000 do
        let termTy ← inferType term
        if termTy != dom then return none
        let inst ← guards (mkApp pf term)
        return some (inst, ← whnfR (← inferType inst))
      let some attempt := attempt | stopped := true; break
      let some (inst, instanceTy) := attempt | continue
      if known.contains instanceTy then continue
      let noted ← bounded 1000 do
        let name ← goal.withContext do return (← getLCtx).getUnusedName `allLeft
        let step ← if replay then do
            let term ← goal.withContext <| PrettyPrinter.delab inst
            pure (some (← `(tactic| have $(mkIdent name):ident := $term)))
          else pure none
        let (_, next) ← goal.note name inst
        return (next, step)
      let some (next, step) := noted | stopped := true; break
      if let some step := step then steps := steps.push step
      goal := next
      known := known.push instanceTy
      added := added + 1
      if pf.isFVar && !hidden.contains pf.fvarId! then hidden := hidden.push pf.fvarId!
      if instanceTy.isForall && numeric instanceTy.bindingDomain! then
        pending := pending.push (inst, depth + 1)
  if added == 0 then throwError "sol_close_all: no new instances"
  for h in hidden do
    let cleared ← bounded 1000 do
      let name ← goal.withContext do return (← h.getDecl).userName
      return (name, ← goal.tryClear h)
    let some (name, next) := cleared | break
    if next != goal && replay then steps := steps.push (← `(tactic| clear $(mkIdent name):ident))
    goal := next
  replaceMainGoal [goal]
  return steps

private def runInstances (replay : Bool) : TacticM (Array (TSyntax `tactic)) := do
  let some steps ← bounded 10000 (addInstances replay)
    | throwError "sol_close_all: bounded instance search stopped; original goal retained"
  return steps

elab "sol_close_all" : tactic => do
  discard <| runInstances false

/-- Display the checked proof applications for replay without instance search. -/
elab "sol_close_all?" : tactic => do
  evalTactic (← `(tactic| expose_names))
  let steps ← runInstances true
  Lean.Meta.Tactic.TryThis.addSuggestion (← getRef)
    (← `(tactic| (expose_names; $steps;*)))

end Solidity.Close.All
