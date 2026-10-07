import Solidity.Calculus.Core.Taclet

/-!
# The rule a scoped statement fires, by name

`Completeness.lean`'s dispatcher names the rule it fires because it builds
the derivation.  On scoped syntax the strategy is a function
(`Core.Stmt.step`, `Calculus/Core/Step.lean`) and the rule table a relation
over it (`Taclet.toStep`, `LeanTaclet.toStep`: a rule's premise is the
step's, so at most one premise per statement, `Rule.premise_unique`); what
the tools (`#step`, `sol_derive?`, the proof tree) need on top is the
rule's *name*.

`ruleOf?` finds it: the constructor whose conclusion matches the statement
and the modality (a hole's statement, a `match` unification does not
invert, by the hole and the part read off the statement: `holeCandidates`),
and every side condition holding by evaluation; its premise is then `Stmt.step`'s
(`Rule.toStep`), which `ruleOf?` checks.  Under `Rule.premise_unique`, the
first constructor found is the rule.
-/

namespace Solidity.Core

open Lean Meta Elab

/-- The holes the statement `s` may be the statement of, each with the part
it is filled with (`h.fill x` is `s`), read off `s`: a local assigned a read
is `SHole.local`'s with the read's path, a copy `SHole.copy`'s with the path
copied, and so on.  A hole's statement is a `match` on the hole and the
part, which unification does not invert; read off, it need not be. -/
def holeCandidates (s : Expr) : MetaM (List (Expr × Expr)) := do
  let s ← whnfD s
  let args := s.getAppArgs
  let C := (← whnfR (← inferType s)).getArg! 0
  -- every hole constructor takes the contract, the context and one type
  -- implicitly, then its parts
  let app (c : Lean.Name) (xs : Array Expr) (part : Expr) : MetaM (List (Expr × Expr)) := do
    try return [(← mkAppOptM c (#[some C, none, none] ++ xs.map some), part)] catch _ => return []
  let at? (e : Expr) (c : Lean.Name) : MetaM (Option Expr) := do
    let e ← whnfD e
    return if e.isAppOf c then some e.appArg! else none
  let last := args.back!
  match s.getAppFn.constName? with
  | some ``Solidity.Core.Stmt.assignLocal =>
    let i := args[args.size - 2]!
    let r ← whnfD last
    let mut out ← app ``Solidity.Core.VHole.local #[i] last
    if r.isAppOf ``Solidity.Core.Val.read then
      out := out ++ (← app ``Solidity.Core.SHole.local #[i] (← mkAppM ``Solidity.Core.SPath.loc #[r.appArg!]))
    if r.isAppOf ``Solidity.Core.Val.readMem then
      out := out ++ (← app ``Solidity.Core.MHole.local #[i] r.appArg!)
    return out
  | some ``Solidity.Core.Stmt.rebind =>
    let some p ← at? last ``Solidity.Core.ARhs.path | return []
    app ``Solidity.Core.SHole.rebind #[args[args.size - 2]!] p
  | some ``Solidity.Core.Stmt.rebindMem =>
    let some p ← at? last ``Solidity.Core.MRhs.alias | return []
    let some l ← at? p ``Solidity.Core.MPath.loc | return []
    app ``Solidity.Core.MHole.rebind #[args[args.size - 2]!] l
  | some ``Solidity.Core.Stmt.assign =>
    let l := args[args.size - 2]!
    let r ← whnfD last
    if r.isAppOf ``Solidity.Core.Src.copy then
      return ← app ``Solidity.Core.SHole.copy #[l, r.appArg!] (r.getArg! (r.getAppNumArgs - 2))
    let some v ← at? r ``Solidity.Core.Src.val | return []
    app ``Solidity.Core.VHole.store #[l] v
  | some ``Solidity.Core.Stmt.assignMem =>
    let l := args[args.size - 2]!
    let r ← whnfD last
    if r.isAppOf ``Solidity.Core.MSrc.val then
      return ← app ``Solidity.Core.VHole.mem #[l] r.appArg!
    let some p ← at? r ``Solidity.Core.MSrc.ref | return []
    let mut out ← app ``Solidity.Core.NewLhs.mem #[l] p
    if let some ml ← at? p ``Solidity.Core.MPath.loc then
      out := out ++ (← app ``Solidity.Core.MHole.write #[l] ml)
    return out
  | some ``Solidity.Core.Stmt.assignFromMem =>
    app ``Solidity.Core.NewLhs.store #[args[args.size - 2]!] last
  | _ => return []

/-- The `fill` of the holes. -/
def fillFns : List Lean.Name :=
  [``Solidity.Core.SHole.fill, ``Solidity.Core.MHole.fill, ``Solidity.Core.VHole.fill,
    ``Solidity.Core.NewLhs.fill]

/-- The statement `f` (a constructor's `\find`, its schema variables
metavariables) is `s`: a hole's statement by its hole and its part, one of
the candidates read off `s`; any other by unification. -/
def matchFind (f s : Expr) (cands : List (Expr × Expr)) : MetaM Bool := do
  let f ← instantiateMVars f
  unless fillFns.any f.isAppOf do return ← isDefEq f s
  let h := f.getArg! (f.getAppNumArgs - 2)
  for (c, part) in cands do
    let st ← saveState
    if ← isDefEq h c <&&> isDefEq f.appArg! part then return true
    st.restore
  return false

/-- **The rule `Stmt.step` fires on `s` under `m`**, its fresh names at `k`
(`s : Core.Stmt C Γ Γ'`): the constructor of `Core.Taclet` or
`Core.LeanTaclet` it is, and its premise, which is `Stmt.step`'s. -/
def ruleOf? (k m s : Expr) : MetaM (Option (Lean.Name × Expr)) := do
  let sTy ← whnfR (← inferType s)
  unless sTy.isAppOfArity ``Solidity.Core.Stmt 3 do throwError "not a scoped statement: {s}"
  let C := sTy.getArg! 0
  let cands ← holeCandidates s
  for J in [``Solidity.Core.Taclet, ``Solidity.Core.LeanTaclet] do
    let some (.inductInfo ii) := (← getEnv).find? J | continue
    for c in ii.ctors do
      let st ← saveState
      let r ← withNewMCtxDepth do
        let (xs, _, ty) ← forallMetaTelescopeReducing (← inferType (← mkConstWithFreshMVarLevels c))
        let args := ty.getAppArgs
        unless args.size == 7 do return none
        unless ← isDefEq args[0]! C <&&> isDefEq args[1]! k <&&> isDefEq args[2]! m do return none
        unless ← matchFind args[5]! s cands do return none
        -- every side condition holds by evaluation
        for x in xs do
          let t ← whnfR (← instantiateMVars (← inferType x))
          let t := if t.isAppOfArity ``autoParam 2 then t.getArg! 0 else t
          if let some (_, a, b) := t.eq? then
            unless ← isDefEq a b do return none
        let p ← instantiateMVars args[6]!
        if p.hasMVar then return none
        return some (c, p)
      match r with
      | some (c, p) =>
        -- the premise is the step's (`Rule.toStep`)
        let step ← whnfD (← mkAppM ``Solidity.Core.Stmt.step #[k, m, s])
        unless ← isDefEq step (← mkAppM ``Option.some #[p]) do
          throwError "ruleOf?: `{c}` does not leave `Stmt.step`'s premise"
        return some (c, p)
      | none => st.restore
  return none

/-- `#rule_of m s`: the rule `Stmt.step` fires on the scoped statement `s`
under the modality `m`, by name. -/
elab "#rule_of " m:term:max s:term : command => Command.liftTermElabM do
  let m ← Term.elabTermEnsuringType m (mkConst ``Modality)
  let s ← Term.elabTerm s none
  Term.synthesizeSyntheticMVarsNoPostponing
  let s ← instantiateMVars s
  match ← ruleOf? (mkNatLit 1) (← instantiateMVars m) s with
  | some (c, _) => logInfo m!"{c}"
  | none => throwError "no rule fires on {s}"

end Solidity.Core
