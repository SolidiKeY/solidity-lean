import Solidity.Calculus.Taclet

/-!
# The rule a scoped statement fires, by name

Master's dispatcher (`Calculus/Completeness.lean` at `ad728b16`) named the
rule it fired because it built the derivation.  On scoped syntax the strategy is a function
(`Stmt.step`, `Calculus/Step.lean`) and the rule table a relation
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

namespace Solidity

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
  | some ``Solidity.Stmt.assignLocal =>
    let i := args[args.size - 2]!
    let r ← whnfD last
    let mut out ← app ``Solidity.VHole.local #[i] last
    if r.isAppOf ``Solidity.Val.read then
      out := out ++ (← app ``Solidity.SHole.local #[i] (← mkAppM ``Solidity.SPath.loc #[r.appArg!]))
    if r.isAppOf ``Solidity.Val.readMem then
      out := out ++ (← app ``Solidity.MHole.local #[i] r.appArg!)
    return out
  | some ``Solidity.Stmt.rebind =>
    let some p ← at? last ``Solidity.ARhs.path | return []
    app ``Solidity.SHole.rebind #[args[args.size - 2]!] p
  | some ``Solidity.Stmt.rebindMem =>
    let some p ← at? last ``Solidity.MRhs.alias | return []
    let some l ← at? p ``Solidity.MPath.loc | return []
    app ``Solidity.MHole.rebind #[args[args.size - 2]!] l
  | some ``Solidity.Stmt.assign =>
    let l := args[args.size - 2]!
    let r ← whnfD last
    if r.isAppOf ``Solidity.Src.copy then
      return ← app ``Solidity.SHole.copy #[l, r.appArg!] (r.getArg! (r.getAppNumArgs - 2))
    let some v ← at? r ``Solidity.Src.val | return []
    app ``Solidity.VHole.store #[l] v
  | some ``Solidity.Stmt.assignMem =>
    let l := args[args.size - 2]!
    let r ← whnfD last
    if r.isAppOf ``Solidity.MSrc.val then
      return ← app ``Solidity.VHole.mem #[l] r.appArg!
    let some p ← at? r ``Solidity.MSrc.ref | return []
    let mut out ← app ``Solidity.NewLhs.mem #[l] p
    if let some ml ← at? p ``Solidity.MPath.loc then
      out := out ++ (← app ``Solidity.MHole.write #[l] ml)
    return out
  | some ``Solidity.Stmt.assignFromMem =>
    app ``Solidity.NewLhs.store #[args[args.size - 2]!] last
  | _ => return []

/-- The `fill` of the holes. -/
def fillFns : List Lean.Name :=
  [``Solidity.SHole.fill, ``Solidity.MHole.fill, ``Solidity.VHole.fill,
    ``Solidity.NewLhs.fill]

/-- The statement `f` (a constructor's `\find`, its schema variables
metavariables) is `s`: a hole's statement by its hole and its part, one of
the candidates read off `s`; any other by unification. -/
def matchFind (f s : Expr) (cands : List (Expr × Expr)) : MetaM Bool := do
  let f ← instantiateMVars f
  if f.isAppOf ``Solidity.Stmt.loop && s.isAppOf ``Solidity.Stmt.loop then
    let fa ← instantiateMVars (f.getArg! (f.getAppNumArgs - 3))
    if fa.isAppOf ``Solidity.LoopUnwind.before then
      let sa ← whnfD (s.getArg! (s.getAppNumArgs - 3))
      let mode ← if sa.isAppOf ``Solidity.LoopAnn.auto then
        pure (mkConst ``Solidity.LoopUnwind.automatic)
      else if sa.isAppOf ``Solidity.LoopAnn.unwind then do
        let n ← whnfD sa.appArg!
        let pred ← match n with
          | .lit (.natVal (n + 1)) => pure (mkNatLit n)
          | _ =>
            if n.isAppOf ``Nat.succ then pure n.appArg! else return false
        mkAppM ``Solidity.LoopUnwind.bounded #[pred]
      else return false
      unless ← isDefEq fa.appArg! mode do return false
      return ← isDefEq f s
  if f.isAppOf ``Solidity.ReceiverValue.statement then
    let value ← if s.isAppOf ``Solidity.Stmt.callReceiverPush then
      mkAppM ``Solidity.ReceiverValue.deferred
        #[s.getArg! (s.getAppNumArgs - 2), s.appArg!]
    else if s.isAppOf ``Solidity.Stmt.callReceiver then
      let op ← whnfD s.appArg!
      unless op.isAppOf ``Solidity.ReceiverOp.push do return false
      let arg ← whnfD (op.getArg! (op.getAppNumArgs - 2))
      unless arg.isAppOf ``Option.some do return false
      mkAppM ``Solidity.ReceiverValue.pure #[arg.appArg!]
    else return false
    unless ← isDefEq f.appArg! value do return false
    return ← isDefEq f s
  unless fillFns.any f.isAppOf do
    -- A primitive path has only a location constructor, but unification
    -- cannot invert its reader while that path is still a metavariable.
    -- Seed that typed path from the concrete read, then check the whole find.
    if f.isAppOf ``Solidity.Stmt.push && s.isAppOf ``Solidity.Stmt.push then
      let farg ← instantiateMVars (f.getArg! (f.getAppNumArgs - 2))
      let sarg ← instantiateMVars (s.getArg! (s.getAppNumArgs - 2))
      if farg.isAppOf ``Option.some && sarg.isAppOf ``Option.some then
        let fv ← instantiateMVars farg.appArg!
        let sv ← instantiateMVars sarg.appArg!
        if fv.isAppOf ``Solidity.Src.val && sv.isAppOf ``Solidity.Src.val then
          let fe ← instantiateMVars fv.appArg!
          let se ← instantiateMVars sv.appArg!
          if fe.isAppOfArity ``Solidity.SPath.primitiveRead 4 &&
              se.isAppOfArity ``Solidity.Val.read 4 then
            unless ← isDefEq fe.appArg! (← mkAppM ``Solidity.SPath.loc #[se.appArg!]) do
              return false
    return ← isDefEq f s
  let h := f.getArg! (f.getAppNumArgs - 2)
  for (c, part) in cands do
    let st ← saveState
    if ← isDefEq h c <&&> isDefEq f.appArg! part then return true
    st.restore
  return false

/-- The conclusion of a constructor's type, under its binders. -/
private def conclusionOf : Expr → Expr
  | .forallE _ _ b _ => conclusionOf b
  | e => e

/-- The head constructors that `matchFind` needs to have a chance on `s`:
`s`'s own (whnf), and the holes of its candidates. -/
structure FindHeads where
  stmt : Option Lean.Name
  holes : List Lean.Name
  noCands : Bool

/-- `FindHeads` of the statement `s` and its hole candidates `cands`. -/
def FindHeads.of (s : Expr) (cands : List (Expr × Expr)) : MetaM FindHeads := do
  let env ← getEnv
  let ctor? (e : Expr) : Option Lean.Name := e.getAppFn.constName?.filter env.isConstructor
  return { stmt := ctor? (← whnfD s), holes := cands.filterMap (fun (c, _) => ctor? c),
           noCands := cands.isEmpty }

/-- Whether the constructor `c` may match a statement of heads `hs`, read off
its type with no unification: a `\find` whose head is a statement
constructor other than the statement's, or a hole constructor none of the
candidates has, does not; anything else may.  A cheap filter in front of
`ruleOf?`'s unification, which tried every constructor of the table at
every statement. -/
def mayFind (c : Lean.Name) (hs : FindHeads) : MetaM Bool := do
  let env ← getEnv
  let some info := env.find? c | return true
  let concl := conclusionOf info.type
  let args := concl.getAppArgs
  unless args.size == 7 do return true
  let f := args[5]!
  let ctor? (e : Expr) : Option Lean.Name := e.getAppFn.constName?.filter env.isConstructor
  match f.getAppFn.constName? with
  | some n =>
    if fillFns.contains n then
      if hs.noCands then return false
      if f.getAppNumArgs < 2 then return true
      match ctor? (f.getArg! (f.getAppNumArgs - 2)) with
      | some h => return hs.holes.contains h
      | none => return true
    match ctor? f, hs.stmt with
    | some a, some b => return a == b
    | _, _ => return true
  | none => return true

/-- The judgements of the rule table, solkey's first, and how a derivation
of each is a `Rule`. -/
def ruleTables : List (Lean.Name × Lean.Name) :=
  [(``Taclet, ``Rule.key), (``LeanTaclet, ``Rule.lean)]

/-- Every constructor of the rule table, solkey's first. -/
def ruleTableCtors : MetaM (List Lean.Name) := do
  let mut out := []
  for (J, _) in ruleTables do
    let some (.inductInfo ii) := (← getEnv).find? J | continue
    out := out ++ ii.ctors
  return out

/-- The constructor `c` of the rule table at the contract `C`, the fresh
index `k` and the modality `m`, its `\find` matched on the statement `s`
(`matchFind`, over `s`'s hole candidates `cands`): the constructor, its
arguments (metavariables where unification left them) and its premise. -/
def ctorAt? (c : Lean.Name) (C k m s : Expr) (cands : List (Expr × Expr)) :
    MetaM (Option (Expr × Array Expr × Expr)) := do
  let ctor ← mkConstWithFreshMVarLevels c
  let (xs, _, ty) ← forallMetaTelescopeReducing (← inferType ctor)
  let args := ty.getAppArgs
  unless args.size == 7 do return none
  unless ← isDefEq args[0]! C <&&> isDefEq args[1]! k <&&> isDefEq args[2]! m do return none
  unless ← matchFind args[5]! s cands do return none
  return some (ctor, xs, args[6]!)

/-- A local's type among the arguments `xs` that only a side condition's
proof mentions (a rule's `MRhs.mapFree` under a pushed local, as in
`memoryIndexWriteCaptureAllComplexRecv`): no unification sets it, and any
type will do there, so `uint`; whether there was one. -/
def defaultLocalTys (xs : Array Expr) : MetaM Bool := do
  let mut defaulted := false
  for x in xs do
    if (← instantiateMVars x).isMVar then
      if (← whnfR (← instantiateMVars (← inferType x))).isConstOf ``LTy then
        x.mvarId!.assign (mkApp (mkConst ``LTy.val) (mkConst ``PrimTy.uint))
        defaulted := true
  return defaulted

/-- **The rule `Stmt.step` fires on `s` under `m`**, its fresh names at `k`
(`s : Stmt C Γ Γ'`): the constructor of `Taclet` or
`LeanTaclet` it is, and its premise, which is `Stmt.step`'s. -/
def ruleOf? (k m s : Expr) : MetaM (Option (Lean.Name × Expr)) := do
  let sTy ← whnfR (← inferType s)
  unless sTy.isAppOfArity ``Solidity.Stmt 3 do throwError "not a scoped statement: {s}"
  let C := sTy.getArg! 0
  let cands ← holeCandidates s
  let hs ← FindHeads.of s cands
  for c in ← ruleTableCtors do
    unless ← mayFind c hs do continue
    let st ← saveState
    let r ← withNewMCtxDepth do
      let some (_, xs, p) ← ctorAt? c C k m s cands | return none
      -- every side condition holds by evaluation
      for x in xs do
        let t := (← whnfR (← instantiateMVars (← inferType x))).unAutoParam
        if let some (_, a, b) := t.eq? then
          -- a call's summary by the kernel (`summary_cond`), within its bound
          let a ← if a.isAppOf ``CallRet.summary? then
              pure ((← kernelSummary? a).getD a) else pure a
          unless ← isDefEq a b do return none
      discard <| defaultLocalTys xs
      let p ← instantiateMVars p
      if p.hasMVar then return none
      return some (c, p)
    match r with
    | some (c, p) =>
      -- the premise is the step's (`Rule.toStep`)
      let stepE ← mkAppM ``Solidity.Stmt.step #[k, m, s]
      -- a call's step runs its callee's summary: by the kernel, within
      -- the bound of `summary_cond` (`fewNodes`)
      let ok ← if s.isAppOf ``Stmt.call && !p.hasMVar && !stepE.hasMVar &&
          fewNodes stepE summaryNodes && fewNodes p summaryNodes then
          pure (Kernel.isDefEqGuarded (← getEnv) (← getLCtx) stepE p)
        else isDefEq (← whnfD stepE) p
      unless ok do
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

end Solidity
