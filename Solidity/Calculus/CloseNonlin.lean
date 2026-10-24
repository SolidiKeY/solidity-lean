import Solidity.Calculus.Budget

/-!
# Nonlinear integer facts: `sol_close_nonlin`

The final arithmetic fallback instantiates SolKey's `multiply_2_inEq0`,
`multiply_inEq0`, `square_nonneg` and `add_non_neg_square`. Literal bounds
retain their tightest endpoints; relevant symbolic comparisons can also be
multiplied. Sign-guarded monotonicity handles either sign of the factor.
Squares of factors and pairwise atom differences supply bounds without
literal premises, for example `2*x*y <= x*x + y*y`.

Term choice is Lean-only and incomplete. At most four atoms, eight factors,
twelve comparisons and 128 facts are used. Expression and declaration scans
have explicit budgets; each reduction/elaboration step and the whole search
have heartbeat recovery with state rollback. Only products of two nonliteral
integers trigger it. `sol_close_nonlin?` prints explicit checked applications
for replay without repeating term selection.
-/

namespace Solidity.Close

/-- solkey's `multiply_2_inEq0`: `(b - a) * (d - c) >= 0`. -/
theorem multiply_2_inEq0 {a b c d : Int} (hcd : c ≤ d) (hab : a ≤ b) :
    a * c ≥ -b * d + b * c + a * d := by
  have h : 0 ≤ (b - a) * (d - c) := Int.mul_nonneg (by omega) (by omega)
  rw [Int.sub_mul, Int.mul_sub, Int.mul_sub] at h
  rw [Int.neg_mul]
  omega

/-- A strict bound as KeY's `<`, `a + 1 <= b`. -/
theorem add_one_le_of_lt' {a b : Int} (h : a < b) : a + 1 ≤ b := h

/-- SolKey's `square_nonneg` and `add_non_neg_square`. -/
theorem square_nonneg (x : Int) : 0 ≤ x * x := by
  by_cases h : 0 ≤ x
  · exact Int.mul_nonneg h h
  · exact Int.mul_nonneg_of_nonpos_of_nonpos (by omega) (by omega)

/-- SolKey's sign-guarded `multiply_inEq0`. -/
theorem multiply_inEq0 {a b : Int} (hab : a ≤ b) (c : Int) :
    if 0 ≤ c then a * c ≤ b * c else b * c ≤ a * c := by
  split <;> rename_i hc
  · exact Int.mul_le_mul_of_nonneg_right hab hc
  · exact Int.mul_le_mul_of_nonpos_right hab (by omega)

open Lean Meta Elab Tactic

/-- At most this many atoms in the factors of products are bounded. -/
def maxAtoms : Nat := 4

/-- An integer literal, read off `OfNat`, `Int.ofNat`, `Neg`. -/
partial def intLit? (e : Expr) : MetaM (Option Int) := do
  let e := e.consumeMData
  if let some n ← getIntValue? e then return some n
  if let some n ← getNatValue? e then return some n
  if e.isAppOfArity ``Neg.neg 3 then
    return (← intLit? e.appArg!).map (- ·)
  return none

/-- Whether `e` is an `Int` product `a * b`, returning its factors. -/
def intMul? (e : Expr) : Option (Expr × Expr) :=
  if e.isAppOfArity ``HMul.hMul 6 && (e.getArg! 0).isConstOf ``Int then
    some (e.getArg! 4, e.getArg! 5)
  else none

/-- A premise `x <= c`, `c <= x`, `x < c` or `c < x` of the atom `x` and
a literal `c`: the bound, `true` for an upper one, and the proof as a `<=`. -/
def boundOf (x : Expr) (h : LocalDecl) : MetaM (Option (Int × Bool × Expr)) := do
  let ty ← instantiateMVars h.type
  let ty := ty.consumeMData
  let le := ty.isAppOfArity ``LE.le 4
  let lt := ty.isAppOfArity ``LT.lt 4
  unless (le || lt) && (ty.getArg! 0).isConstOf ``Int do return none
  let l := (ty.getArg! 2).consumeMData
  let r := (ty.getArg! 3).consumeMData
  let pf := if lt then mkApp3 (mkConst ``add_one_le_of_lt') l r h.toExpr else h.toExpr
  if l == x then
    if let some c ← intLit? r then return some (if lt then c - 1 else c, true, pf)
  if r == x then
    if let some c ← intLit? l then return some (if lt then c + 1 else c, false, pf)
  return none

/-- One reduction/elaboration step, with rollback on errors or runtime limits. -/
private def nonlinBounded (limit : Nat) (action : TacticM α) : TacticM (Option α) := do
  Budget.bounded limit action

/-- Inspect at most 8192 expression nodes and 16 distinct products. -/
private def productTerms (roots : Array Expr) (completeRequired : Bool := false) :
    TacticM (Array (Expr × Expr)) := do
  let mut todo := roots
  let mut seen : Std.HashSet Expr := {}
  let mut result := #[]
  let mut nodes := 0
  let mut complete := true
  while !todo.isEmpty && nodes < 8192 && result.size < 16 do
    let e := todo.back!.consumeMData
    todo := todo.pop
    nodes := nodes + 1
    if seen.contains e then continue
    seen := seen.insert e
    if let some (a, b) := intMul? e then
      if !e.hasLooseBVars && !e.hasMVar then
        let some nonlinear ← nonlinBounded 1000 do
          return (← intLit? a).isNone && (← intLit? b).isNone
          | complete := false; break
        if nonlinear then result := result.push (a, b)
    match e with
    | .app f a => todo := (todo.push f).push a
    | .lam _ t b _ | .forallE _ t b _ => todo := (todo.push t).push b
    | .letE _ t v b _ => todo := ((todo.push t).push v).push b
    | .mdata _ b | .proj _ _ b => todo := todo.push b
    | _ => pure ()
  if completeRequired && (!complete || !todo.isEmpty) then
    throwError "sol_close_nonlin: comparison linearity scan incomplete"
  return result

/-- Arithmetic leaves of factors, using a bounded traversal. -/
private def factorAtoms (roots : Array Expr) : TacticM (Array Expr) := do
  let mut todo := roots
  let mut result := #[]
  let mut nodes := 0
  while !todo.isEmpty && nodes < 1024 do
    let e := todo.back!.consumeMData
    todo := todo.pop
    nodes := nodes + 1
    let some literal ← nonlinBounded 1000 (do return (← intLit? e).isSome) | break
    if literal then continue
    if [``HAdd.hAdd, ``HSub.hSub, ``HMul.hMul].any (e.isAppOfArity · 6) then
      todo := (todo.push (e.getArg! 4)).push (e.getArg! 5)
    else if e.isAppOfArity ``Neg.neg 3 then todo := todo.push e.appArg!
    else if !result.contains e then result := result.push e
    if result.size > maxAtoms then throwError "sol_close_nonlin: more than {maxAtoms} atoms"
  if !todo.isEmpty then throwError "sol_close_nonlin: factor traversal budget"
  return result

/-- A relevant comparison, including symbolic bounds, as a proved `<=`.
Strict premises use KeY's integer successor form. -/
private def symbolicBound (xs : Array Expr) (h : LocalDecl) : TacticM (Option Expr) := do
  let ty := (← instantiateMVars h.type).consumeMData
  let le := ty.isAppOfArity ``LE.le 4
  let lt := ty.isAppOfArity ``LT.lt 4
  unless (le || lt) && (ty.getArg! 0).isConstOf ``Int do return none
  let l := ty.getArg! 2
  let r := ty.getArg! 3
  unless xs.any (fun x => (l.find? (· == x)).isSome || (r.find? (· == x)).isSome) do return none
  -- Literal coefficients are linear; only nonlinear products are excluded.
  unless (← productTerms #[l, r] true).isEmpty do return none
  return some (if lt then mkApp3 (mkConst ``add_one_le_of_lt') l r h.toExpr else h.toExpr)

/-- Produce at most 128 checked facts: literal and symbolic bound products,
squares (including differences), and sign-guarded monotonicity. -/
private def nonlinearFacts : TacticM (Array Expr) := withMainContext do
  let mut hyps : Array LocalDecl := #[]
  let target ← instantiateMVars (← getMainTarget)
  let mut roots : Array Expr := #[]
  let mut scanned := 0
  for d in ← getLCtx do
    if scanned == 256 then break
    scanned := scanned + 1
    if d.isImplementationDetail then continue
    let some ty ← nonlinBounded 1000 (instantiateMVars d.type) | break
    hyps := hyps.push d
    roots := roots.push ty
  let targetProducts ← productTerms #[target]
  -- Unrelated premises must not use the product/factor budgets before the
  -- goal. Premise products seed the search only when the goal has none.
  let prods ← if targetProducts.isEmpty then productTerms roots.reverse else pure targetProducts
  if prods.isEmpty then throwError "sol_close_nonlin: no product of two non-literal integers"
  let mut factors : Array Expr := #[]
  for (a, b) in prods do
    for e in [a, b] do
      if !factors.contains e && factors.size < 8 then factors := factors.push e
  let xs ← factorAtoms factors
  let mut bounds : Array Expr := #[]
  for x in xs do
    let mut lo : Option (Int × Expr) := none
    let mut hi : Option (Int × Expr) := none
    for d in hyps do
      let some result ← nonlinBounded 1000 (boundOf x d) | break
      let some (c, upper, pf) := result | continue
      if upper then
        if hi.all (fun (c', _) => c < c') then hi := some (c, pf)
      else if lo.all (fun (c', _) => c > c') then lo := some (c, pf)
    if let some (_, pf) := lo then bounds := bounds.push pf
    if let some (_, pf) := hi then bounds := bounds.push pf
  for d in hyps do
    if bounds.size == 12 then break
    let some result ← nonlinBounded 1000 (symbolicBound xs d) | break
    if let some pf := result then
      if !bounds.contains pf then bounds := bounds.push pf
  let mut facts : Array Expr := #[]
  for i in [:bounds.size] do
    for j in [i:bounds.size] do
      let some pf ← nonlinBounded 1000 (mkAppM ``multiply_2_inEq0 #[bounds[i]!, bounds[j]!]) | break
      facts := facts.push pf
  let mut squareTerms := factors
  for x in xs do
    if !squareTerms.contains x then squareTerms := squareTerms.push x
  for x in squareTerms do
    if facts.size == 128 then break
    let some pf ← nonlinBounded 1000 (mkAppM ``square_nonneg #[x]) | break
    facts := facts.push pf
  for i in [:xs.size] do
    for j in [i+1:xs.size] do
      if facts.size == 128 then break
      let difference := mkApp2 (mkConst ``Int.sub) xs[i]! xs[j]!
      let some pf ← nonlinBounded 1000 (mkAppM ``square_nonneg #[difference]) | break
      facts := facts.push pf
  for bound in bounds do
    for factor in factors do
      if facts.size == 128 then break
      let some pf ← nonlinBounded 1000 (mkAppM ``multiply_inEq0 #[bound, factor]) | break
      facts := facts.push pf
  if facts.isEmpty then throwError "sol_close_nonlin: no bounded instances"
  return facts

private def addNonlinear (replay : Bool) : TacticM (Array (TSyntax `tactic)) := withMainContext do
  let facts ← nonlinearFacts
  let mut goal ← getMainGoal
  let mut steps := #[]
  let mut added := 0
  for pf in facts do
    let some result ← nonlinBounded 1000 do
      let name ← goal.withContext do return (← getLCtx).getUnusedName `nonlin
      let term ← if replay then goal.withContext (PrettyPrinter.delab pf)
        else pure (⟨Syntax.missing⟩ : TSyntax `term)
      let (_, next) ← goal.note name pf
      return (name, term, next) | break
    let (name, term, next) := result
    if replay then steps := steps.push (← `(tactic| have $(mkIdent name):ident := $term))
    goal := next
    added := added + 1
  if added == 0 then throwError "sol_close_nonlin: no fact could be elaborated within budget"
  replaceMainGoal [goal]
  return steps

private def runNonlinear (replay : Bool) : TacticM (Array (TSyntax `tactic)) := do
  let some steps ← nonlinBounded 20000 (addNonlinear replay)
    | throwError "sol_close_nonlin: bounded search stopped; original goal retained"
  return steps

elab "sol_close_nonlin" : tactic => discard <| runNonlinear false

/-- Explicit checked instances for replay without repeated selection. -/
elab "sol_close_nonlin?" : tactic => do
  evalTactic (← `(tactic| expose_names))
  let steps ← runNonlinear true
  Lean.Meta.Tactic.TryThis.addSuggestion (← getRef) (← `(tactic| (expose_names; $steps;*)))

end Solidity.Close
