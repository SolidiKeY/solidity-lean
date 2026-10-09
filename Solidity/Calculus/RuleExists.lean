import Solidity.Calculus.Completeness

/-!
# Every statement has a rule, and the strategy fires only rules

`Taclet.toStep` (`Calculus/Taclet.lean`) says each rule's premise is the
one the strategy (`Stmt.step`) computes.  This module proves the converse:
for every statement, under either modality, the premise `Stmt.step` leaves
is a rule's (`Stmt.rule_exists`); so the strategy fires nothing the rule
table does not have (`Rule.ofStep`).  Master's dispatcher built the
derivation with the premise; the scoped one is a function to `Premise`
(total, decision 76), so here the derivation is found after the fact.

The proof is one lemma per statement constructor (`Stmt.<c>.ruleExists`),
each its own declaration.  It takes `Stmt.step` apart where it is blocked: on
a part of the statement (a path, a value, a location: `cases` on it), or on
a computed test (`b.isSimple`, `args.capture`, `body.frame`: `cases` on its
value, which stays in scope as a hypothesis), until the step is a premise `P`;
there the rule is the constructor of `Taclet` or `LeanTaclet`
whose `\find` is the statement (a hole's statement read off it,
`holeCandidates`), whose premise is `P`, and whose side conditions hold, by
evaluation, by a hypothesis the splits left, or by `simp_all`.  A branch
the step never reaches (`shortStep` on an operator that does not short
circuit) is ruled out by the hypotheses of its branch (`!`).

The search runs once, under `#derive_ruleExists?`, which offers a
`#replay_ruleExists` table: for each statement constructor, the rules of
its leaves in order.  The file keeps the table; the replay takes the same
splits (no search: they are read off the blocked step) and tries only the
named rule at each leaf.
-/

namespace Solidity

open Lean Meta Elab Tactic

variable {C : Contract}

namespace RuleExists

/-- What the step is blocked on: a local to take apart, or a computed value
to take apart in place. -/
inductive Blocker where
  | fvar (x : Expr)
  | gen (d : Expr)

/-- A value worth splitting where it stands: of an inductive type that is
not a proposition or a `Decidable`, computed by a function. -/
def generalizable (d : Expr) : MetaM Bool := do
  if d.hasLooseBVars || d.isFVar then return false
  let .const f _ := d.getAppFn | return false
  let env ← getEnv
  if env.isConstructor f || (← isMatcher f) || isAuxRecursor env f then return false
  if let some (.recInfo _) := env.find? f then return false
  let ty ← whnfR (← inferType d)
  if ← isProp ty then return false
  let .const T _ := ty.getAppFn | return false
  if T == ``Decidable then return false
  return match (← getEnv).find? T with
    | some (.inductInfo _) => true
    | _ => false

/-- The syntax families a split may take apart: finitely deep, each case
telling the rules apart.  A value computed from anything else (a block's
frame, a call's arguments) is split in place instead. -/
def partFamilies : List Lean.Name :=
  [``SPath, ``Loc, ``MPath, ``MLoc, ``Val, ``Simple, ``Src, ``MSrc, ``ARhs, ``MRhs, ``OpLoc,
    ``IndexTy, ``ArrTy, ``SHole, ``MHole, ``VHole, ``NewLhs, ``CallRet, ``LoopAnn, ``BinOp, ``UnOp,
    ``IncDec, ``PrimTy, ``Ty, ``RefTy, ``Modality, ``Option, ``Nat, ``Bool, ``Prod, ``Sigma]

mutual

/-- The blocked point of the blocked term `e` (in `whnf`), and `e` rebuilt
(definitionally) so that the blocked point is a subterm of it: a matcher
unfolded to its recursor, the recursor's major premise the term that
blocks it, followed down while it is itself blocked.  With `gen`, a value a
function computes is split in place when it is a test (a `Bool`) or when
what it is blocked on is not a part of the statement's syntax. -/
partial def blockerOf (e : Expr) (gen : Bool := true) : MetaM (Option (Expr × Blocker)) := do
  let .const n ls := e.getAppFn | return none
  if ← isMatcher n then
    let v ← instantiateValueLevelParams (← getConstInfo n) ls
    return ← blockerOf (← whnfCore (v.beta e.getAppArgs)) gen
  let some (.recInfo r) := (← getEnv).find? n | return none
  let i := r.getMajorIdx
  unless i < e.getAppNumArgs do return none
  let a := (← instantiateMVars (e.getArg! i)).consumeMData
  let some (a', s) ← majorOf a gen | return none
  return some (mkAppN e.getAppFn (e.getAppArgs.set! i a'), s)

/-- The major premise `a` of a blocked recursor: a local, a value computed by a
function (split in place, see `blockerOf`), or a blocked term followed down. -/
partial def majorOf (a : Expr) (gen : Bool) : MetaM (Option (Expr × Blocker)) := do
  if a.isFVar then return some (a, .fvar a)
  if gen && (← generalizable a) then
    if (← whnfR (← inferType a)).isConstOf ``Bool then return some (a, .gen a)
    let deep ← blockerOf (← whnfD a) false
    let isPart ← match deep with
      | some (_, .fvar x) => do
        let t ← whnfR (← inferType x)
        pure (partFamilies.any t.isAppOf)
      | _ => pure false
    unless isPart do return some (a, .gen a)
  let w ← whnfD a
  if w.isFVar then return some (w, .fvar w)
  blockerOf w gen

end

/-- `∃ p, e = p ∧ R p`, read back: `e`, and the rule `R` at `p`. -/
def parseTarget (t : Expr) : MetaM (Option (Expr × Expr)) := do
  let t ← instantiateMVars t
  unless t.isAppOfArity ``Exists 2 do return none
  let .lam _ _ body _ := t.appArg! | return none
  unless body.isAppOfArity ``And 2 do return none
  let eq := body.getArg! 0
  unless eq.isAppOfArity ``Eq 3 do return none
  return some (eq.getArg! 1, body)

/-- The target with the step `e` replaced by the definitionally equal `e'`. -/
def replaceStep (t e' : Expr) : MetaM Expr := do
  let t ← instantiateMVars t
  let .lam n ty body bi := t.appArg! | throwError "rule_exists: not an existential"
  let eq := body.getArg! 0
  let eq' := mkApp3 eq.appFn!.appFn!.appFn! (eq.getArg! 0) e' (eq.getArg! 2)
  let body' := mkApp2 body.appFn!.appFn! eq' (body.getArg! 1)
  return mkApp t.appFn! (.lam n ty body' bi)

/-- The side conditions a rule's constructor asks, proved: by evaluation, by
a hypothesis, or by `simp_all` over the side predicates. -/
def proveSide (t : Expr) : TacticM (Option Expr) := do
  let t := if t.isAppOfArity ``autoParam 2 then t.getArg! 0 else t
  if let some (_, a, b) := t.eq? then
    if ← withNewMCtxDepth (isDefEq a b) then
      if ← isDefEq a b then return some (← mkEqRefl a)
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    if ← withNewMCtxDepth (isDefEq d.type t) then
      if ← isDefEq d.type t then return some d.toExpr
  if t.hasExprMVar then return none
  let g ← mkFreshExprMVar t
  let s ← saveState
  -- `done` would log the goals it leaves: test them instead
  let closes (tac : TacticM Unit) : TacticM Bool := do
    try
      let gs ← Tactic.run g.mvarId! tac
      return gs.isEmpty
    catch _ => return false
  if ← closes (evalTactic (← `(tactic| decide))) then return some (← instantiateMVars g)
  s.restore
  if ← closes (evalTactic (← `(tactic|
      simp_all only [SPath.isSimple, Val.isSimple, MPath.isSimple, Loc.isTarget, Loc.isRoot,
        MLoc.isTarget, MPath.isBindable, Val.notTernary, SHole.isTarget, MHole.isTarget,
        VHole.isTarget, SPath.elemMapping, SPath.elemPrim, Ty.elemIsMapping, Ty.elemIsPrim,
        Ty.isMapping, Ty.isPrimitive, Bool.not_eq_true, Bool.false_eq_true, Bool.true_eq_false,
        Option.isSome, Option.isNone, Args.firstNonSimple, Option.map_none, Option.map_some,
        reduceCtorEq]))) then
    return some (← instantiateMVars g)
  s.restore
  return none

/-- How a constructor fares on a leaf: it closes it, or it matches the
statement and the premise but a side condition `d = b` (`d : Bool`) is
neither true nor false there, or it does not apply. -/
inductive Try where
  | closed (r : Expr)
  | undecided (d : Expr)
  | no

/-- Close the rule goal `R` (`Rule C k m s P`) with the constructor `c` of
`J` (`Taclet`, or `LeanTaclet`), wrapped by `wrap` (`Rule`'s constructor
`key`, or `lean`). -/
def tryCtor (R : Expr) (c wrap : Lean.Name) (cands : List (Expr × Expr)) : TacticM Try := do
  let st ← saveState
  let r ← (do
    let ty ← whnfR R
    let cE ← mkConstWithFreshMVarLevels c
    let (xs, _, cty) ← forallMetaTelescopeReducing (← inferType cE)
    let args := cty.getAppArgs
    unless args.size == 7 do return Try.no
    unless ← isDefEq args[0]! (ty.getArg! 0) <&&> isDefEq args[1]! (ty.getArg! 1)
      <&&> isDefEq args[2]! (ty.getArg! 2) do return .no
    unless ← matchFind args[5]! (ty.getArg! 5) cands do return .no
    unless ← isDefEq args[6]! (ty.getArg! 6) do return .no
    for x in xs do
      let x ← instantiateMVars x
      unless x.isMVar do continue
      let t ← instantiateMVars (← inferType x)
      if ← isProp t then
        let some pf ← proveSide t | do
          let t' := if t.isAppOfArity ``autoParam 2 then t.getArg! 0 else t
          if let some (ty, d, _) := t'.eq? then
            if ty.isConstOf ``Bool && !d.hasExprMVar && !d.isFVar then
              let v ← whnfD d
              unless v.isConstOf ``Bool.true || v.isConstOf ``Bool.false do return .undecided d
          return .no
        unless ← isDefEq x pf do return .no
      else if (← whnfR t).isConstOf ``LTy then
        x.mvarId!.assign (mkApp (mkConst ``LTy.val) (mkConst ``PrimTy.uint))
      else return .no
    let d ← instantiateMVars (mkAppN cE xs)
    if d.hasExprMVar then return .no
    let r ← mkAppOptM wrap #[none, none, none, none, none, none, none, d]
    unless ← isDefEq (← inferType r) R do return .no
    return .closed (← instantiateMVars r))
  match r with
  | .closed _ => pure ()
  | _ => st.restore
  return r

/-- The judgements of the rule table, and how a derivation of each is a
`Rule`. -/
def tables : List (Lean.Name × Lean.Name) :=
  [(``Taclet, ``Rule.key), (``LeanTaclet, ``Rule.lean)]

/-- The rule of a leaf `Rule C k m s P`: the constructor named `c?` (the
replay), or the first that closes it (the search); its name.  Otherwise
the side condition the first matching constructor could not decide, with
that constructor's name. -/
def leaf (R : Expr) (c? : Option Lean.Name) :
    TacticM (Option (Lean.Name × Expr) × List (Lean.Name × Expr)) := do
  let ty ← whnfR R
  let s := ty.getArg! 5
  let cands ← holeCandidates s
  let hs ← FindHeads.of s cands
  let mut und := #[]
  for (J, wrap) in tables do
    let some (.inductInfo ii) := (← getEnv).find? J | continue
    for c in ii.ctors do
      if let some c' := c? then
        unless c == c' do continue
      else unless ← mayFind c hs do continue
      match ← tryCtor R c wrap cands with
      | .closed r => return (some (c, r), [])
      | .undecided d => und := und.push (c, d)
      | .no => pure ()
  return (none, und.toList)

/-- A step of a plan: the rule of a leaf, or a split of the leaf's
statement on its first part of the type named (the rules tell apart what
the step does not: a mapping's entry from an array's, `IndexTy`). -/
inductive Tok where
  | rule (c : Lean.Name)
  | split (T : Lean.Name)
  /-- a split on the side condition the rule `c` cannot decide (an
  array's element a mapping or not, `SPath.elemMapping`) -/
  | side (c : Lean.Name)
  /-- a leaf ruled out by a hypothesis that computes to `false = true` (a
  carried proof the split contradicts) -/
  | absurd
  deriving BEq, Inhabited

/-- The parts a leaf is split on, in the order the search tries them. -/
def leafHeads : List Lean.Name :=
  [``IndexTy, ``ArrTy, ``Option, ``SPath, ``MPath, ``Val, ``Loc, ``MLoc, ``Src, ``MSrc, ``OpLoc,
    ``Ty, ``RefTy]

/-- The first local of the statement `s` whose type is the family `T`. -/
def partOf (s : Expr) (T : Lean.Name) : MetaM (Option FVarId) := do
  for fv in (collectFVars {} (← instantiateMVars s)).fvarIds do
    let t ← whnfR (← instantiateMVars (← fv.getType))
    if t.isAppOf T then return some fv
  return none

/-- Close `g` by a hypothesis `a = b` whose sides compute to different
constructors (`hs : (mfield (loc l) f h).recvSimple = true`); whether it did. -/
def closeAbsurd (g : MVarId) : MetaM Bool := g.withContext do
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let some (ty, a, b) := (← instantiateMVars d.type).eq? | continue
    let a' ← whnfD a
    let b' ← whnfD b
    let some ca := a'.getAppFn.constName? | continue
    let some cb := b'.getAppFn.constName? | continue
    unless (← getEnv).isConstructor ca && (← getEnv).isConstructor cb && ca != cb do continue
    let h ← mkExpectedTypeHint d.toExpr (← mkEq a' b')
    let _ := ty
    g.assign (← mkNoConfusion (← g.getType) h)
    return true
  return false

/-- Whether `e` (in `whnf`) is a premise built: a constructor of `Premise`
at its head. -/
def isPremise (e : Expr) : MetaM Bool := do
  let .const c _ := e.getAppFn | return false
  return match (← getEnv).find? c with
    | some (.ctorInfo ci) => ci.induct == ``Premise
    | _ => false

/-- The rule `R` of the leaf of the goal `g`, its step the premise `P`. -/
def ruleGoal (g : MVarId) : MetaM (Expr × Expr × Expr) := do
  let some (e, _) ← parseTarget (← g.getType) | throwError "rule_exists: not `∃ p, step = p ∧ …`"
  let P ← whnfD e
  let t ← instantiateMVars (← g.getType)
  let .lam _ _ body _ := t.appArg! | throwError "rule_exists: not an existential"
  return ((body.getArg! 1).instantiate1 P, P, t)

mutual

/-- Prove the main goal `∃ p, e = p ∧ Rule C k m s p`: split the
step where it is blocked until it computes, then each leaf by its rule,
following `plan` (the replay) or searching (`plan` is `none`).  Returns the
plan of the goal, and what is left of the one given. -/
partial def go (plan : Option (List Tok)) (depth : Nat := 0) :
    TacticM (Array Tok × Option (List Tok)) := do
  let g ← getMainGoal
  g.withContext do
  let some (e, _) ← parseTarget (← g.getType) | throwError "rule_exists: not `∃ p, step = p ∧ …`"
  let e' ← whnfD e
  -- each leaf in a heartbeat budget of its own (its search tries rules)
  if ← isPremise e' then return ← withCurrHeartbeats (atLeaf plan depth)
  let some (e'', s) ← blockerOf e' | throwError "rule_exists: the step is blocked on nothing to split{indentExpr e'}"
  let g ← g.replaceTargetDefEq (← replaceStep (← g.getType) e'')
  let gs ← match s with
    | .fvar x => do
      let gs ← g.cases x.fvarId!
      pure (gs.map (·.mvarId)).toList
    | .gen d => do
      let (fvs, g) ← g.generalize #[{ expr := d, xName? := `x, hName? := `hx }]
      let gs ← g.cases fvs[0]!
      pure (gs.map (·.mvarId)).toList
  goals gs plan depth

/-- `go` on each of `gs`, the plan threaded through. -/
partial def goals (gs : List MVarId) (plan : Option (List Tok)) (depth : Nat) :
    TacticM (Array Tok × Option (List Tok)) := do
  let mut out := #[]
  let mut plan := plan
  for g in gs do
    setGoals [g]
    let (cs, rest) ← withCurrHeartbeats (go plan depth)
    out := out ++ cs
    plan := rest
  setGoals []
  return (out, plan)

/-- A leaf, its step the premise `P`: the rule the plan names, a split it names,
or, searching, the first rule that closes it, else a split of the side
condition a rule leaves undecided, or of the statement's parts, after which
every case has one. -/
partial def atLeaf (plan : Option (List Tok)) (depth : Nat) : TacticM (Array Tok × Option (List Tok)) := do
  let g ← getMainGoal
  let (R, P, t) ← ruleGoal g
  let close (c? : Option Lean.Name) : TacticM (Option Lean.Name × List (Lean.Name × Expr)) :=
    g.withContext do
      let (some (c, r), und) ← leaf R c? | return (none, (← leaf R c?).2)
      let pf ← mkAppOptM ``Exists.intro #[none, t.appArg!, P,
        ← mkAppM ``And.intro #[← mkEqRefl P, r]]
      unless ← isDefEq (← inferType pf) (← g.getType) do return (none, [])
      g.assign pf
      replaceMainGoal []
      return (some c, und)
  let split (T : Lean.Name) : TacticM (Option (List MVarId)) := g.withContext do
    let some fv ← partOf (R.getArg! 5) T | return none
    let gs ← g.cases fv
    return some (gs.map (·.mvarId)).toList
  let sideSplit (d : Expr) : TacticM (List MVarId) := g.withContext do
    let (fvs, g') ← g.generalize #[{ expr := d, xName? := `x, hName? := `hx }]
    let gs ← g'.cases fvs[0]!
    return (gs.map (·.mvarId)).toList
  match plan with
  | some (.absurd :: rest) =>
    unless ← closeAbsurd g do throwError "rule_exists: no hypothesis rules out{indentExpr R}"
    replaceMainGoal []
    return (#[.absurd], some rest)
  | some (.rule c :: rest) =>
    let (some _, _) ← close (some c) | throwError "rule_exists: `{c}` does not close{indentExpr R}"
    return (#[.rule c], some rest)
  | some (.split T :: rest) =>
    let some gs ← split T | throwError "rule_exists: no `{T}` to split{indentExpr R}"
    let (cs, rest) ← goals gs (some rest) (depth + 1)
    return (#[.split T] ++ cs, rest)
  | some (.side c :: rest) =>
    let (_, (_, d) :: _) ← g.withContext (leaf R (some c)) |
      throwError "rule_exists: `{c}` leaves no side condition to split{indentExpr R}"
    let (cs, rest) ← goals (← sideSplit d) (some rest) (depth + 1)
    return (#[.side c] ++ cs, rest)
  | some [] => throwError "rule_exists: the plan ended{indentExpr R}"
  | none =>
    let (c?, und) ← close none
    if let some c := c? then return (#[.rule c], none)
    if ← closeAbsurd g then
      replaceMainGoal []
      return (#[.absurd], none)
    let mut notes : Array MessageData := #[]
    if depth < 3 then
      for (c, d) in und do
        let st ← saveState
        try
          let (cs, _) ← goals (← sideSplit d) none (depth + 1)
          return (#[.side c] ++ cs, none)
        catch e =>
          notes := notes.push m!"split on {d} ({c}): {e.toMessageData}"
          st.restore
      for T in leafHeads do
        let st ← saveState
        try
          let some gs ← split T | continue
          let (cs, _) ← goals gs none (depth + 1)
          return (#[.split T] ++ cs, none)
        catch e =>
          notes := notes.push m!"split on {T}: {e.toMessageData}"
          st.restore
    throwError "rule_exists: no rule of the table leaves the step's premise{indentExpr R}\n\
      {MessageData.joinSep notes.toList "\n"}"

end

/-! ## Plans as text -/

/-- A token of a plan as the table writes it: `storageRootDelete` (a
`Taclet`), `lean.whileUnwind` (a `LeanTaclet`), `/IndexTy` (a split, the
family under `Solidity`). -/
def Tok.text : Tok → String
  | .rule c => ruleText c
  | .split T =>
    "/" ++ if (`Solidity).isPrefixOf T then (T.replacePrefix `Solidity .anonymous).toString
      else "_root_." ++ T.toString
  | .side c => "?" ++ ruleText c
  | .absurd => "!"
where
  ruleText (c : Lean.Name) : String :=
    if (``Taclet).isPrefixOf c then (c.replacePrefix ``Taclet .anonymous).toString
    else "lean." ++ (c.replacePrefix ``LeanTaclet .anonymous).toString

/-- A plan as text: its tokens, a run of one written once after its length
(`3*storageIndexDeleteNonSimpleIndexCapture`). -/
def planText (ts : Array Tok) : String :=
  let runs := ts.foldl (init := ([] : List (Nat × String))) fun
    | (n, q) :: rs, t => if t.text == q then (n + 1, q) :: rs else (1, t.text) :: (n, q) :: rs
    | [], t => [(1, t.text)]
  " ".intercalate (runs.reverse.map fun (n, t) => if n == 1 then t else s!"{n}*{t}")

/-- A token read back. -/
def Tok.ofText (w : String) : Tok :=
  let rule (w : String) : Lean.Name :=
    if w.startsWith "lean." then ``LeanTaclet ++ (w.drop 5).toName else ``Taclet ++ w.toName
  if w == "!" then .absurd
  else if w.startsWith "/_root_." then .split (w.drop 8).toName
  else if w.startsWith "/" then .split (`Solidity ++ (w.drop 1).toName)
  else if w.startsWith "?" then .side (rule (w.drop 1))
  else .rule (rule w)

/-- A plan read back from its text. -/
def planOfText (s : String) : List Tok :=
  (s.splitOn " ").filter (· ≠ "") |>.flatMap fun w =>
    match w.splitOn "*" with
    | [n, t] => List.replicate n.toNat! (Tok.ofText t)
    | _ => [Tok.ofText w]

/-! ## The lemmas -/

/-- `Stmt.<c>.ruleExists`'s statement: for the constructor `c`'s statement
`s`, every `k` and `m`, `∃ p, s.step k m = p ∧ Rule C k m s p`. -/
def lemmaType (c : Lean.Name) : MetaM Expr := do
  forallTelescope (← getConstInfo c).type fun xs body => do
    let s := mkAppN (mkConst c) xs
    let C := body.getArg! 0
    withLocalDeclD `k (mkConst ``Nat) fun k => withLocalDeclD `m (mkConst ``Modality) fun m => do
      let pTy := mkApp3 (mkConst ``Premise) C (body.getArg! 1) (body.getArg! 2)
      let ex ← withLocalDeclD `p pTy fun p => do
        let eq ← mkEq (← mkAppM ``Stmt.step #[k, m, s]) p
        let r ← mkAppOptM ``Rule #[C, k, m, none, none, s, p]
        mkAppM ``Exists #[← mkLambdaFVars #[p] (mkAnd eq r)]
      mkForallFVars (xs ++ #[k, m]) ex

/-- Add `c.ruleExists` (`c` a constructor of `Stmt`), proved by `go plan`
in its own heartbeat budget; its plan.  A failure is logged; `strict` then
throws. -/
def addLemma (c : Lean.Name) (plan : Option (List Tok)) (strict : Bool := true) :
    Command.CommandElabM (Option (Array Tok)) :=
  Command.liftTermElabM <| withCurrHeartbeats do
    let ty ← lemmaType c
    let mvar ← mkFreshExprMVar ty
    let r ← tryCatchRuntimeEx (do
        let out ← IO.mkRef #[]
        let gs ← Term.withoutErrToSorry <| Tactic.run mvar.mvarId! do
          let (_, g) ← (← getMainGoal).intros
          setGoals [g]
          let (ts, rest) ← go plan
          if let some (_ :: _) := rest then throwError "rule_exists: the plan has more leaves than the proof"
          out.set ts
        let ok := gs.isEmpty && !(← instantiateMVars mvar).hasSorry
        if ok then return some (← out.get) else return none)
      (fun ex => do logError m!"{c}: {((← ex.toMessageData.toString).take 1500)}"; pure none)
    let some ts := r | if strict then throwError "no proof that `{c}`'s step is a rule's" else pure none
    addDecl (Declaration.thmDecl
      { name := c ++ `ruleExists, levelParams := [], type := ty, value := ← instantiateMVars mvar })
    return some ts

/-- The constructors of `Stmt` without a `ruleExists` lemma. -/
def missing : Command.CommandElabM (Array Lean.Name) := do
  let some (.inductInfo ii) := (← getEnv).find? ``Stmt | throwError "no `Stmt`"
  let env ← getEnv
  return ii.ctors.toArray.filter fun c => !env.contains (c ++ `ruleExists)

/-- `#derive_ruleExists?` searches `Stmt.<c>.ruleExists` for every
constructor of `Stmt` without one, and offers the `#replay_ruleExists`
table of the plans it found.  Run it once, after a rule or an arm changes;
the file keeps the table. -/
elab tk:"#derive_ruleExists?" cs:(ppSpace ident)* : command => do
  let t0 ← IO.monoMsNow
  let mut rows : Array String := #[]
  let only := cs.map fun c => ``Stmt ++ c.getId
  for c in ← missing do
    unless only.isEmpty || only.contains c do continue
    let some ts ← addLemma c none (strict := false) | pure ()
    rows := rows.push s!"\n  {c.replacePrefix ``Stmt .anonymous} \"{planText ts}\""
  let text := "#replay_ruleExists" ++ String.join rows.toList
  Command.liftTermElabM do
    logInfoAt tk m!"searched in {(← IO.monoMsNow) - t0} ms"
    Lean.Meta.Tactic.TryThis.addSuggestion tk { suggestion := .string text }

/-- `#replay_ruleExists  c₁ "plan₁" …` proves `Stmt.cᵢ.ruleExists` by the
plan `#derive_ruleExists?` found, and fails if a constructor of `Stmt` is
then left without its lemma. -/
syntax (name := replayRuleExists) "#replay_ruleExists" (ppLine ident ppSpace str)* : command

elab_rules : command
  | `(#replay_ruleExists $[$cs $ps]*) => do
    for c in cs, p in ps do
      discard <| addLemma (``Stmt ++ c.getId) (some (planOfText p.getString))
    let left ← missing
    unless left.isEmpty do
      throwError "#replay_ruleExists: no lemma for {left.toList}; run `#derive_ruleExists?`"

/-- Close `∃ p, s.step k m = p ∧ Rule C k m s p` for the case of
`cases s` it is, by its constructor's lemma. -/
elab "apply_ruleExists" : tactic => do
  let n := ``Stmt ++ (← getMainTag) ++ `ruleExists
  evalTactic (← `(tactic| exact $(mkIdent n) ..))

end RuleExists

open RuleExists

/-! ## The lemmas, one per statement constructor

The table `#derive_ruleExists?` offers: for each constructor, the rule of
each leaf of its step in order (`lean.` a rule solkey does not have), a
split of the leaf's statement on a part (`/IndexTy`: a mapping's entry or
an array's), a split on a side condition a rule cannot decide
(`?storageIndexReadArrayBindLocalRoot`: the array's element a mapping or
not), a leaf ruled out by a contradicted hypothesis (`!`). -/

#replay_ruleExists
  assign "storageRootWriteStore 3*storageRootWriteValueRhsCapture ternaryToIf 7*ternaryCaptureCond 3*storageRootWriteValueRhsCapture 2*storageRootWriteCopySource storageFieldRead_unfold_rightFst storageFieldReadStoreRoot storageIndexRead_unfold_rightFst /IndexTy storageIndexReadMappingStoreRoot storageIndexReadArrayStoreRoot 7*storageIndexRead_unfold_rightSndIndex 4*storageFieldWrite_unfold_leftFst ternaryToIf 7*ternaryCaptureCond 3*storageFieldWrite_unfold_leftFst storageFieldWriteSave 3*fieldWriteValueRhsCapture ternaryToIf 7*ternaryCaptureCond 3*fieldWriteValueRhsCapture storageFieldWriteStorageRef_unfold_leftFst 2*storageFieldWriteCopySource storageFieldRead_unfold_rightFst storageFieldRead_unfold_rightSndResult storageIndexRead_unfold_rightFst storageIndexRead_unfold_rightSndResult 7*storageIndexRead_unfold_rightSndIndex 4*storageIndexWriteCaptureAllComplexRecv ternaryToIf 7*ternaryCaptureCond 3*storageIndexWriteCaptureAllComplexRecv /IndexTy storageIndexWriteMappingSave storageIndexWriteArraySave 3*indexWriteValueRhsCapture ternaryToIf 7*ternaryCaptureCond 3*indexWriteValueRhsCapture 4*storageIndexWriteCaptureAllNonSimpleIndex ternaryToIf 7*ternaryCaptureCond 7*storageIndexWriteCaptureAllNonSimpleIndex ternaryToIf 7*ternaryCaptureCond 7*storageIndexWriteCaptureAllNonSimpleIndex ternaryToIf 7*ternaryCaptureCond 7*storageIndexWriteCaptureAllNonSimpleIndex ternaryToIf 7*ternaryCaptureCond 7*storageIndexWriteCaptureAllNonSimpleIndex ternaryToIf 7*ternaryCaptureCond 7*storageIndexWriteCaptureAllNonSimpleIndex ternaryToIf 7*ternaryCaptureCond 7*storageIndexWriteCaptureAllNonSimpleIndex ternaryToIf 7*ternaryCaptureCond 3*storageIndexWriteCaptureAllNonSimpleIndex storageIndexWriteStorageRefCaptureAllComplexRecv /IndexTy storageIndexWriteMappingCopySource storageIndexWriteArrayCopySource /IndexTy storageIndexWriteMappingCopySource storageIndexWriteArrayCopySource ?storageFieldRead_unfold_rightFst /SPath storageFieldRead_unfold_rightFst /Loc 4*storageFieldRead_unfold_rightFst ?storageFieldRead_unfold_rightSndResult /SPath storageFieldRead_unfold_rightSndResult /Loc 4*storageFieldRead_unfold_rightSndResult ?storageIndexRead_unfold_rightFst /SPath storageIndexRead_unfold_rightFst /Loc 4*storageIndexRead_unfold_rightFst ?storageIndexRead_unfold_rightSndResult /SPath storageIndexRead_unfold_rightSndResult /Loc 4*storageIndexRead_unfold_rightSndResult ?storageIndexRead_unfold_rightSndIndex /SPath storageIndexRead_unfold_rightSndIndex /Loc 4*storageIndexRead_unfold_rightSndIndex ?storageIndexRead_unfold_rightSndIndex /SPath storageIndexRead_unfold_rightSndIndex /Loc 4*storageIndexRead_unfold_rightSndIndex ?storageIndexRead_unfold_rightSndIndex /SPath storageIndexRead_unfold_rightSndIndex /Loc 4*storageIndexRead_unfold_rightSndIndex ?storageIndexRead_unfold_rightSndIndex /SPath storageIndexRead_unfold_rightSndIndex /Loc 4*storageIndexRead_unfold_rightSndIndex ?storageIndexRead_unfold_rightSndIndex /SPath storageIndexRead_unfold_rightSndIndex /Loc 4*storageIndexRead_unfold_rightSndIndex ?storageIndexRead_unfold_rightSndIndex /SPath storageIndexRead_unfold_rightSndIndex /Loc 4*storageIndexRead_unfold_rightSndIndex ?storageIndexRead_unfold_rightSndIndex /SPath storageIndexRead_unfold_rightSndIndex /Loc 4*storageIndexRead_unfold_rightSndIndex 7*storageIndexWriteStorageRefCaptureAllNonSimpleIndex"
  rebind "2*storageLocalRootRebind storageFieldRead_unfold_rightFst storageFieldReadBindLocalRoot storageIndexRead_unfold_rightFst /IndexTy storageIndexReadMappingBindLocalRoot ?storageIndexReadArrayBindLocalRoot storageIndexReadArrayBindLocalRoot storageIndexReadArrayBindLocalRootMappingElement 7*storageIndexRead_unfold_rightSndIndex storageLocalRootPush_unfold_leftFstReceiver ?storageLocalRootPushBind storageLocalRootPushBind storageLocalRootPushBindMappingElement"
  assignLocal "localValueAssign storageRootReadSelect storageFieldRead_unfold_rightFst storageFieldReadFind storageIndexRead_unfold_rightFst /IndexTy storageIndexReadMappingFind storageIndexReadArrayFind 7*storageIndexRead_unfold_rightSndIndex binopAssignment binopUnfoldRight 12*! logicalAndShortCircuitRhs 4*! logicalOrShortCircuitRhs 13*! binopUnfoldRight 12*! logicalAndShortCircuitRhs 4*! logicalOrShortCircuitRhs 13*! binopUnfoldRight 12*! logicalAndShortCircuitRhs 4*! logicalOrShortCircuitRhs 13*! binopUnfoldRight 12*! logicalAndShortCircuitRhs 4*! logicalOrShortCircuitRhs 13*! binopUnfoldRight 12*! logicalAndShortCircuitRhs 4*! logicalOrShortCircuitRhs 13*! binopUnfoldRight 12*! logicalAndShortCircuitRhs 4*! logicalOrShortCircuitRhs 13*! binopUnfoldRight 12*! logicalAndShortCircuitRhs 4*! logicalOrShortCircuitRhs 13*! 7*binopUnfoldLeft unopAssignment 7*unopCapture ternaryToIf 7*ternaryCaptureCond memoryFieldRead memoryFieldRead_unfold_rightFst memoryIndexReadArrayValue 7*memoryIndexRead_unfold_rightSndIndex memoryIndexRead_unfold_rightFst storageLengthRead_unfold_rightFst storageLengthRead memoryLengthRead memoryLengthRead_unfold_rightFst"
  declLocal "valueDeclSkip localValueDeclInitDrop"
  declStorage "storageLocalDeclSkip storageLocalDeclInitDrop"
  opAssign "localOpAssign storageRootOpAssign storageFieldOpAssignUnfoldLeftFst storageFieldOpAssign storageIndexOpAssignUnfoldLeftFst /IndexTy storageIndexMappingOpAssign storageIndexArrayOpAssign memoryFieldOpAssign memoryFieldOpAssignUnfoldLeftFst memoryIndexArrayOpAssign memoryIndexOpAssignUnfoldLeftFst 7*compoundAssignValueRhsCapture"
  incDec "localIncrement storageRootIncrement storageFieldIncrementUnfoldLeftFst storageFieldIncrement storageIndexIncrementUnfoldLeftFst storageIndexIncrement memoryFieldIncrement memoryFieldIncrementUnfoldLeftFst memoryIndexArrayIncrement memoryIndexIncrementUnfoldLeftFst"
  assignIncDec "/OpLoc localAssignIncrement storageRootIncrementAssignment storageFieldIncrementAssignment storageIndexIncrementAssignment /MPath memoryFieldIncrementAssignment ! /ArrTy /MPath memoryIndexArrayIncrementAssignment ! /MPath memoryIndexArrayIncrementAssignment !"
  push "/_root_.Option storagePush_unfold_leftFstReceiver storagePushValue_unfold_leftFstReceiver storagePushLengthSaveReferenceElement storagePushLengthSave storagePushValueSave 7*storagePushValue_unfold_rightSndArgument storagePushValueCopySource"
  pop "storagePop_unfold_leftFstReceiver storagePopSave storagePopSaveMappingElement"
  transfer "lean.transferDiamond transferNoCallbackBox 7*transfer_unfold_rightSndArgument 7*transfer_unfold_leftFstReceiver"
  send "sendNoCallbackDiamond sendNoCallbackBox 7*send_unfold_rightSndArgument 7*send_unfold_leftFstReceiver"
  declMem "memoryReferenceDeclFreshAlloc memoryLocalDeclInitDrop"
  rebindMem "memoryRootRebind memoryFieldReadAliasRoot memoryFieldRead_unfold_rightFst memoryIndexReadArrayMemory 7*memoryIndexRead_unfold_rightSndIndex memoryIndexRead_unfold_rightFst memoryStorageCopyUnfold memoryStorageCopy memoryArrayFreshAlloc"
  assignFromMem "memoryToStorageStoreRoot memoryToStorageField_unfold_leftFst memoryToStorageFieldCopyRoot memoryToStorageIndexCaptureAllComplexRecv /IndexTy memoryToStorageIndexMappingCopyRoot memoryToStorageIndexArrayCopyRoot 7*memoryToStorageIndexCaptureAllNonSimpleIndex"
  assignMem "memoryFieldWrite 3*memoryFieldWriteUnfoldSource ternaryToIf 7*ternaryCaptureCond 3*memoryFieldWriteUnfoldSource memoryFieldWrite_unfold_leftFst 2*memoryFieldWriteCopy memoryFieldRead_unfold_rightFst memoryFieldWriteCopy 7*memoryIndexRead_unfold_rightSndIndex memoryIndexRead_unfold_rightFst memoryFieldWrite_unfold_leftFst memoryIndexWriteArray 3*memoryIndexWriteUnfoldSource ternaryToIf 7*ternaryCaptureCond 3*memoryIndexWriteUnfoldSource 7*memoryIndexWriteCaptureAllNonSimpleIndex memoryIndexWriteCaptureAllComplexRecv 2*memoryIndexWriteCopy memoryFieldRead_unfold_rightFst memoryIndexWriteCopy 7*memoryIndexRead_unfold_rightSndIndex memoryIndexRead_unfold_rightFst 7*memoryIndexWriteMemRefCaptureAllNonSimpleIndex memoryIndexWriteMemRefCaptureAllComplexRecv"
  delete "storageRootDelete storageFieldDelete_unfold_leftFst storageFieldDelete storageIndexDelete_unfold_leftFst /IndexTy storageIndexDelete storageIndexArrayDelete 7*storageIndexDeleteNonSimpleIndexCapture"
  deleteMem "memoryRootDeleteFreshRebind memoryFieldDeletePrimitive memoryFieldDeleteReference memoryFieldDelete_unfold_leftFst memoryIndexDeletePrimitive memoryIndexDeleteReference 7*memoryIndexDeleteNonSimpleIndexCapture memoryIndexDelete_unfold_leftFst"
  assignNew "newArrayCapture"
  ite "ifElseSplit 7*ifElseUnfold"
  require "requireSimple 7*requireConditionCapture"
  assert "assertSimple 7*assertConditionCapture"
  revert "revertDiamond revertBox"
  call "internalCallExpand lean.functionCallArgCapture internalCallExpand lean.functionCallArgCapture functionBodyExpand lean.functionCallArgCapture internalCallExpand lean.functionCallArgCapture"
  tryCall "lean.tryCallDiamond tryCallNoCallbackBox"
  loop "lean.loopExit lean.whileUnwind lean.whileClose lean.whileNoVariantDiamond lean.whileInvariantDiamond lean.whileInvariantBox"
  block "blockEmpty"

/-- **Every statement has a rule, and it is the strategy's**: under either
modality, some rule of the table (`Taclet`, or `LeanTaclet`) rewrites the
statement to the premise `Stmt.step` leaves. -/
theorem Stmt.rule_exists (k : Nat) (m : Modality) {Γ Γ' : Ctx} (s : Stmt C Γ Γ') :
    Rule C k m s (s.step k m) := by
  obtain ⟨p, h, d⟩ : ∃ p, s.step k m = p ∧ Rule C k m s p := by cases s <;> apply_ruleExists
  rw [h]; exact d

/-- **The strategy fires only rules**: a premise `Stmt.step` leaves is a
rule's (the converse of `Rule.toStep`). -/
theorem Rule.ofStep {k : Nat} {m : Modality} {Γ Γ' : Ctx} {s : Stmt C Γ Γ'} {p : Premise C Γ Γ'}
    (h : s.step k m = p) : Rule C k m s p :=
  h ▸ Stmt.rule_exists k m s

/-- A rule exactly when the strategy's: `Rule.toStep` and `Rule.ofStep`. -/
theorem Rule.iff_step {k : Nat} {m : Modality} {Γ Γ' : Ctx} {s : Stmt C Γ Γ'} {p : Premise C Γ Γ'} :
    Rule C k m s p ↔ s.step k m = p :=
  ⟨Rule.toStep, Rule.ofStep⟩

end Solidity

