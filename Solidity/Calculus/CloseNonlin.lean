import Lean

/-!
# Products of bounded integers: `sol_close_nonlin`

`sol_close`'s arithmetic (`omega`, `grind`) reads a product of two
variables as an atom: `grind`'s ring normaliser equates `n * (n + 1)` with
`(n - 1) * n + 2 * n`, but nothing bounds `n * n`, so a range check of
`n * (n + 1)` under `n <= 1000` stays open.  solkey's integer rules close
it by `multiply_2_inEq0` (`intSimplificationRules.key`, heuristics
`inEqSimp_nonLin_multiply`): from `c <= d` and `a <= b`, the product of
the two differences is nonnegative, `a * c >= -b * d + b * c + a * d`.

`sol_close_nonlin` adds those instances, and only where the goal or a
premise has a product of two non-literal integers (else it fails, and
costs nothing): for each atom of such a product's factors, its tightest
literal bounds among the premises (`c <= x`, `x <= c`, `<` as `+ 1 <=`),
and `multiply_2_inEq0` of every pair of those bound facts, the same fact
twice included (`0 <= n` with itself is `n * n >= 0`).  At most
`maxAtoms` atoms are read, so at most `(2k)(2k+1)/2` facts are added.  It
runs last in `sol_close`, after every other alternative failed, so a leaf
that closed before does not pay for it.
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

/-- The atoms of an integer term: its maximal subterms that are not `+`,
`-`, `*`, negation or a literal. -/
partial def atoms (e : Expr) (acc : Array Expr) : MetaM (Array Expr) := do
  let e := e.consumeMData
  if (← intLit? e).isSome then return acc
  for op in [``HAdd.hAdd, ``HSub.hSub, ``HMul.hMul] do
    if e.isAppOfArity op 6 then
      return ← atoms (e.getArg! 5) (← atoms (e.getArg! 4) acc)
  if e.isAppOfArity ``Neg.neg 3 then return ← atoms e.appArg! acc
  return if acc.contains e then acc else acc.push e

/-- The products of two non-literal integers in `e`. -/
partial def products (e : Expr) (acc : Array (Expr × Expr)) : MetaM (Array (Expr × Expr)) := do
  match e with
  | .app f a =>
    let mut acc := acc
    if let some (x, y) := intMul? e then
      if (← intLit? x).isNone && (← intLit? y).isNone then acc := acc.push (x, y)
    products a (← products f acc)
  | .lam _ t b _ | .forallE _ t b _ => products b (← products t acc)
  | .letE _ t v b _ => products b (← products v (← products t acc))
  | .mdata _ b | .proj _ _ b => products b acc
  | _ => return acc

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

/-- `sol_close_nonlin`: `multiply_2_inEq0` of the tightest literal bounds
of the atoms of the goal's products (module docstring). -/
elab "sol_close_nonlin" : tactic => withMainContext do
  let g ← getMainGoal
  let lctx ← getLCtx
  let hyps := lctx.decls.toList.filterMap id |>.filter (!·.isImplementationDetail)
  let mut prods : Array (Expr × Expr) := #[]
  for t in (← instantiateMVars (← g.getType)) :: (← hyps.mapM fun d => instantiateMVars d.type) do
    prods ← products t prods
  if prods.isEmpty then throwError "sol_close_nonlin: no product of two non-literal integers"
  let mut xs : Array Expr := #[]
  for (a, b) in prods do xs ← atoms b (← atoms a xs)
  if xs.size > maxAtoms then throwError "sol_close_nonlin: more than {maxAtoms} atoms"
  -- the tightest literal bounds of each atom
  let mut facts : Array Expr := #[]
  for x in xs do
    let mut lo : Option (Int × Expr) := none
    let mut hi : Option (Int × Expr) := none
    for d in hyps do
      let some (c, upper, pf) ← boundOf x d | continue
      if upper then
        if hi.all (fun (c', _) => c < c') then hi := some (c, pf)
      else
        if lo.all (fun (c', _) => c > c') then lo := some (c, pf)
    if let some (_, pf) := lo then facts := facts.push pf
    if let some (_, pf) := hi then facts := facts.push pf
  if facts.isEmpty then throwError "sol_close_nonlin: no literal bound of a product's atom"
  let mut hs : Array Hypothesis := #[]
  for i in [:facts.size] do
    for j in [i:facts.size] do
      let pf ← mkAppM ``multiply_2_inEq0 #[facts[i]!, facts[j]!]
      hs := hs.push { userName := `nonlin, type := ← inferType pf, value := pf }
  let (_, g') ← g.assertHypotheses hs
  replaceMainGoal [g']

end Solidity.Close
