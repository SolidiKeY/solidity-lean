import Solidity.Calculus.UpdateRules
import Solidity.Calculus.WalkSyntax
import Solidity.Calculus.Rewrite

/-!
# Today's steps after the program, on a scoped goal

Under `open scoped Solidity.Scoped` the lines that finish a goal keep
today's text (`Calculus/Rewrite.lean`): `refine merge rfl ?_` and
`refine Proves.mergeStorage ?_` (`sequentialToParallel`), `refine simplify
?_`, `refine Proves.eqDSplit ?_ ?_ ?_`, `exact Proves.definedWritten`,
`exact Proves.definedLit`, `exact Proves.eqRefl`, `exact Proves.eqDClose`,
`sol_apply_upd`, and `rw [r]`/`sol_rw [r, …]`.  On a scoped goal
(`Proves`) each is the scoped rule of `Calculus/Proves.lean` or
`Calculus/UpdateRules.lean`; on today's goal, today's.

The scoped context has what today's does not show: hidden binders (a
declaration's local) and scope ends (an update that only pops).  So a merge
line takes the scope ends under the last update into it first, then merges
the last update with the one before it past the hidden binders between them
(`Proves.merge`'s `bs`): one line, one merge of updates that print.

What a step computes (the merged update, the goal with an update applied, a
rewritten update) is computed by the compiled code and quoted back
(`Upd.quote`, `Fml.quote`), so that the next line, and the printer, see its
terms; the kernel checks it (`rfl`).
-/

namespace Solidity

open Lean Elab Tactic Meta

/-! ## Computing and quoting -/

/-- The contract's name of a scoped goal. -/
def Walk.contractName (C : Expr) : MetaM Lean.Name := do
  let some n := (← whnfR C).constName? | throwError "not a named contract: {C}"
  return n

/-- `e : Option T`, computed by the compiled code, each value quoted back by
`quote` (`Upd.quote`, `Fml.quote`: its explicit arguments the contract's
name and the value). -/
unsafe def Walk.evalQuoteOptImpl (C : Expr) (quote : Lean.Name) (e : Expr) : MetaM (Option Expr) := do
  let c := quoteConstName (← Walk.contractName C)
  let T := (← whnf (← inferType e)).appArg!
  let qf ← withLocalDeclD `x T fun x => do mkLambdaFVars #[x] (← mkAppM quote #[c, x])
  let ty := mkApp (mkConst ``Option [levelZero]) (mkConst ``Expr)
  evalExpr (Option Expr) ty (← mkAppM ``Option.map #[qf, e])

@[implemented_by Walk.evalQuoteOptImpl]
opaque Walk.evalQuoteOpt (C : Expr) (quote : Lean.Name) (e : Expr) : MetaM (Option Expr)

/-- The parts of a scoped sequent `Proves C R Γ₀ H φ`. -/
def Walk.provesParts (ty : Expr) : MetaM (Expr × Expr × Expr) := do
  let ty ← instantiateMVars ty
  unless ty.isAppOfArity ``Proves 6 do throwError "not a scoped sequent"
  return (ty.getArg! 0, ty.getArg! 4, ty.getArg! 5)

/-- The top update of a context, `H.upd m V`: `(H, m, V)`. -/
def Walk.updTop? (H : Expr) : MetaM (Option (Expr × Expr × Expr)) := do
  let H ← whnf H
  unless H.isAppOfArity ``Hyps.upd 7 do return none
  return some (H.getArg! 4, H.getArg! 5, H.getArg! 6)

/-! ## `sequentialToParallel` -/

/-- The update below the top one, past the hidden binders between: the
binders (top first) and the update. -/
def Walk.below (H₁ : Expr) : MetaM (Option (Array Expr × Expr)) := do
  let mut bsRev : Array Expr := #[]
  let mut cur ← whnf H₁
  while cur.isAppOfArity ``Hyps.bind 7 do
    let tr ← mkAppM ``Prod.mk #[cur.getArg! 4, ← mkAppM ``Prod.mk #[cur.getArg! 5, cur.getArg! 6]]
    bsRev := bsRev.push tr
    cur ← whnf (cur.getArg! 3)
  unless cur.isAppOfArity ``Hyps.upd 7 do return none
  return some (bsRev, cur.getArg! 6)

/-- One `Proves.merge` on the main goal: the top update with the update
below the hidden binders under it.  Fails where there is none. -/
def Walk.mergeOnce : TacticM Unit := withMainContext do
  let (C, H, _) ← Walk.provesParts (← getMainTarget)
  let some (H₁, _, V) ← Walk.updTop? H | throwError "merge: no update at the top of the context"
  let some (bsRev, U) ← Walk.below H₁ | throwError "merge: no update before the last one"
  let elemTy ← mkAppM ``Prod #[mkConst ``Modality, ← mkAppM ``Prod #[mkConst ``Var, mkConst ``LTy]]
  let bs ← mkListLit elemTy bsRev.reverse.toList
  let some U' ← Walk.evalQuoteOpt C ``Upd.quote (← mkAppM ``Upd.liftBinds? #[bs, U])
    | throwError "merge: the update before the binders cannot move under them"
  let some W ← Walk.evalQuoteOpt C ``Upd.quote (← mkAppM ``Upd.seqPar #[U', V])
    | throwError "merge: the last update reads a global part the one before it writes"
  let bsS ← Term.exprToSyntax bs
  let U'S ← Term.exprToSyntax U'
  let WS ← Term.exprToSyntax W
  evalTactic (← `(tactic|
    refine Solidity.Proves.merge (bs := $bsS) (U' := $U'S) (W := $WS) rfl rfl ?_))

/-- `core_merge`: the scope ends under the last update merged into it,
silently, then one merge (`Proves.merge`, past the hidden binders). -/
elab "core_merge" : tactic => withMainContext do
  for _ in [0:64] do
    let (_, H, _) ← withMainContext do Walk.provesParts (← getMainTarget)
    let some (H₁, _, V) ← Walk.updTop? H | break
    let some (bsRev, U) ← Walk.below H₁ | break
    -- a scope end at the top, or below the binders, is merged silently
    unless (← Walk.popsOnly V) && bsRev.isEmpty || (← Walk.popsOnly U) do break
    Walk.mergeOnce
  Walk.mergeOnce

/-! ## The steps that finish a goal -/

/-- `core_simplify`: `Proves.simplify'`, the simplified update computed. -/
elab "core_simplify" : tactic => withMainContext do
  let (C, H, _) ← Walk.provesParts (← getMainTarget)
  let some (_, _, U) ← Walk.updTop? H | throwError "simplify: no update at the top of the context"
  let some U₂ ← Walk.evalQuoteOpt C ``Upd.quote (← mkAppM ``Option.some #[
      ← mkAppM ``Upd.simp #[mkNatLit 0, U]]) | throwError "simplify: internal error"
  let U₂S ← Term.exprToSyntax U₂
  evalTactic (← `(tactic| refine Solidity.Proves.simplify' (U₂ := $U₂S) rfl ?_))

/-- `core_apply_upd`: `Proves.applyOnRigidBox`, the goal with the last
update applied computed. -/
elab "core_apply_upd" : tactic => withMainContext do
  let (C, H, φ) ← Walk.provesParts (← getMainTarget)
  let some (_, _, W) ← Walk.updTop? H | throwError "sol_apply_upd: no update at the top of the context"
  let some φ' ← Walk.evalQuoteOpt C ``Fml.quote (← mkAppM ``Fml.substU #[W, φ])
    | throwError "sol_apply_upd: the goal reads a global part the update writes, or is not \
        first-order"
  let φ'S ← Term.exprToSyntax φ'
  evalTactic (← `(tactic| refine Solidity.Proves.applyOnRigidBox (φ' := $φ'S) rfl ?_))

/-! ## Rewriting with a term taclet or the Theory's laws -/

/-- The closed value terms among the subterms of `e`, outermost first, each
with its erasure: a term a rewrite may replace (`Tm.rwC`, `Tm.sideC`). -/
partial def Walk.closedVals (e : Expr) (acc : Array (Expr × Expr) := #[]) :
    MetaM (Array (Expr × Expr)) := do
  let mut acc := acc
  let isTm ← do
    if e.hasLooseBVars || e.hasMVar || acc.any (·.1 == e) then pure false
    else
      let e' ← whnfR e
      pure (e'.getAppFn.constName?.map (·.getPrefix == ``Tm) |>.getD false)
  if isTm then
    let ty ← try some <$> (whnf (← inferType e)) catch _ => pure none
    if let some ty := ty then
      if ty.isAppOfArity ``Tm 3 && (← whnf (ty.getArg! 2)).isConstOf ``Srt.val then
        let closed ← whnfD (← mkAppM ``Option.isSome #[← mkAppM ``Tm.toNil? #[e]])
        if closed.isConstOf ``Bool.true then
          let nil ← mkListLit (mkConst ``Var) []
          let er ← Meta.reduce (← mkAppM ``Tm.erase #[nil, e]) (skipTypes := true)
          acc := acc.push (e, er)
  for a in e.getAppArgs do acc ← Walk.closedVals a acc
  return acc

/-- The sides of the goal's equations (`Fml.eq`), through `¬`, `∧`, `→`. -/
partial def Walk.eqSides (φ : Expr) : MetaM (Array Expr) := do
  let φ ← whnf φ
  if φ.isAppOfArity ``Fml.eq 4 then return #[φ.getArg! 2, φ.getArg! 3]
  if φ.isAppOfArity ``Fml.not 3 then return ← Walk.eqSides (φ.getArg! 2)
  if φ.isAppOfArity ``Fml.and 4 || φ.isAppOfArity ``Fml.imp 4 then
    return (← Walk.eqSides (φ.getArg! 2)) ++ (← Walk.eqSides (φ.getArg! 3))
  return #[]

/-- Rewrite the main goal by `q = (t, t')`: in the sides of its equations
(`Proves.rewrite'`, `hq : Term.Theq t t'`) when one is `t`, else in the last
box update's right-hand sides (`Proves.updRw'`) when `t'` cannot halt. -/
def Walk.rwWith (C q hq : Expr) (inGoal : Bool) : TacticM Unit := withMainContext do
  let (_, H, φ) ← Walk.provesParts (← getMainTarget)
  let qS ← Term.exprToSyntax q
  let hqS ← Term.exprToSyntax hq
  if inGoal then
    let some φ' ← Walk.evalQuoteOpt C ``Fml.quote (← mkAppM ``Option.some #[← mkAppM ``Fml.rwEqC #[q, φ]])
      | throwError "rw: internal error"
    let φ'S ← Term.exprToSyntax φ'
    evalTactic (← `(tactic| refine Solidity.Proves.rewrite' ($qS) ($hqS) (φ' := $φ'S) rfl ?_))
  else
    let some (_, _, U) ← Walk.updTop? H | throwError "rw: no update at the top of the context"
    let some U₂ ← Walk.evalQuoteOpt C ``Upd.quote (← mkAppM ``Option.some #[← mkAppM ``Upd.rwC #[q, U]])
      | throwError "rw: internal error"
    let U₂S ← Term.exprToSyntax U₂
    evalTactic (← `(tactic|
      refine Solidity.Proves.updRw' ($qS)
        (Solidity.Term.EvalRefines.of_theq ($hqS) (by first | rfl | decide)) (U₂ := $U₂S) rfl ?_))

/-- The places a rewrite of the main goal may reach: the sides of its
equations, then the last box update's right-hand sides; each closed value
term with its erasure, and whether it is in the goal. -/
def Walk.rwCandidates : TacticM (Array (Expr × Expr × Bool)) := withMainContext do
  let (_, H, φ) ← Walk.provesParts (← getMainTarget)
  let mut out : Array (Expr × Expr × Bool) := #[]
  for side in ← Walk.eqSides φ do
    for (t, er) in ← Walk.closedVals side do
      if t == side then out := out.push (t, er, true)
  if let some (_, m, U) ← Walk.updTop? H then
    if (← whnf m).isConstOf ``Modality.box then
      for (t, er) in ← Walk.closedVals U do out := out.push (t, er, false)
  return out

/-- `rw [r]` with a term taclet or a Theory equation `r` on a scoped goal:
its left side matched against each place a rewrite may reach, in turn. -/
def Walk.rwTaclet (h : Lean.Term) (symm : Bool) : TacticM Unit := withMainContext do
  let (C, _, _) ← Walk.provesParts (← getMainTarget)
  for (_, er, inGoal) in ← Walk.rwCandidates do
    let saved ← saveState
    try
      let h' ← qualifyTaclet h
      let pf ← match h' with
        | `($id:ident) => elabTerm (← `(@$id)) none (mayPostpone := true)
        | _ => elabTerm h' none (mayPostpone := true)
      let (args, _, _) ← forallMetaTelescope (← instantiateMVars (← inferType pf))
      let pf ← asTaclet (mkAppN pf args)
      let pf ← if symm then mkAppM ``TermTaclet.symm #[pf] else pure pf
      let_expr TermTaclet _ lhs rhs ← (← whnfR (← instantiateMVars (← inferType pf)))
        | throwError "rw: {h} is not a term taclet or a Theory equation"
      unless ← isDefEq lhs er do throwError "no match"
      for a in args do
        let g := a.mvarId!
        if !(← g.isAssigned) && (← isProp (← g.getType)) then solRwSide h g
      Term.synthesizeSyntheticMVarsNoPostponing
      let pf ← instantiateMVars pf
      let rhs ← instantiateMVars rhs
      if pf.hasExprMVar || rhs.hasExprMVar then throwError "rw: could not instantiate {pf}"
      if !inGoal then
        let lit := (← whnfR rhs).isAppOf ``Tm.app0 || (← whnfR rhs).isAppOf ``Term.lit
        unless lit do throwError "not a literal"
      let q ← mkAppM ``Prod.mk #[er, rhs]
      Walk.rwWith C q (← mkAppM ``TermTaclet.sound #[pf]) inGoal
      return
    catch _ => saved.restore
  throwError "rw: {h} rewrites nothing in the sequent"

/-- `sol_rw [l₁, …]` with Theory laws on a scoped goal: each read of a closed
term they turn into a term rewritten (`theoryRewrite`), until none is. -/
def Walk.rwTheory (thms : SimpTheorems) (names : Array Lean.Term) : TacticM Unit := do
  let mut rounds := 0
  let mut progress := true
  while progress && rounds < 32 do
    progress := false
    let (C, _, _) ← withMainContext do Walk.provesParts (← getMainTarget)
    for (_, er, inGoal) in ← Walk.rwCandidates do
      unless er.isAppOfArity ``Surface.Tm.app2 7 &&
          ((er.getArg! 4).isConstOf ``Op2.find || (er.getArg! 4).isConstOf ``Op2.len) do continue
      let some (u', pf) ← withMainContext (theoryRewrite thms C er) | continue
      let saved ← saveState
      try
        if !inGoal then
          unless (← whnfR u').isAppOf ``Surface.Tm.app0 do throwError "not a literal"
        Walk.rwWith C (← mkAppM ``Prod.mk #[er, u']) pf inGoal
        progress := true
        break
      catch _ => saved.restore
    if progress then rounds := rounds + 1
  if rounds == 0 then
    throwError "sol_rw: no term of the sequent is rewritten to a term by {names}"

/-- `core_rw [r, …]`: `sol_rw`'s rules on a scoped goal, in order (a term
taclet or Theory equation by `Walk.rwTaclet`, a run of Theory laws by
`Walk.rwTheory`).  It fails on a goal that is not a scoped sequent. -/
def Walk.rwRules (rs : Array Syntax) : TacticM Unit := do
  unless (← instantiateMVars (← getMainTarget)).isAppOf ``Proves do
    throwError "core_rw: not a scoped sequent"
  let mut thms : SimpTheorems := {}
  let mut names : Array Lean.Term := #[]
  for r in rs do
    let h : Lean.Term := ⟨r[1]⟩
    let symm := !r[0].isNone
    let isTheq ← withMainContext do
      unless h.raw.isIdent do return true
      if (← getEnv).contains (``TermTaclet ++ h.raw.getId) then return true
      let some n ← (try some <$> realizeGlobalConstNoOverloadWithInfo h
          catch _ => pure none) | return true
      forallTelescope (← getConstInfo n).type fun _ ty => do
        let ty ← whnfR ty
        return ty.isAppOf ``Solidity.Term.Theq || ty.isAppOf ``Solidity.TermTaclet
    if isTheq then
      unless names.isEmpty do
        Walk.rwTheory thms names
        thms := {}; names := #[]
      withRef r <| Walk.rwTaclet h symm
    else
      let n ← realizeGlobalConstNoOverloadWithInfo h
      thms ← match (← getConstInfo n) with
        | .defnInfo _ => thms.addDeclToUnfold n
        | _ => thms.addConst n (inv := symm)
      names := names.push h
  unless names.isEmpty do Walk.rwTheory thms names

/-- `core_rw [r, …]`: `rw`/`sol_rw` on a scoped goal. -/
syntax "core_rw " "[" Lean.Parser.Tactic.rwRule,+ "]" : tactic

elab_rules : tactic
  | `(tactic| core_rw [$rs,*]) => Walk.rwRules (rs.getElems.map (·.raw))

/-! ## Today's lines, read on a scoped goal -/

namespace Scoped

scoped macro_rules
  | `(tactic| refine merge rfl ?_) =>
    `(tactic| first | core_merge | refine Solidity.NFml.Proves.merge rfl ?_)
  | `(tactic| refine Proves.merge rfl ?_) =>
    `(tactic| first | core_merge | refine Solidity.NFml.Proves.merge rfl ?_)
  | `(tactic| refine mergeStorage ?_) =>
    `(tactic| first | core_merge | refine Solidity.NFml.Proves.mergeStorage ?_)
  | `(tactic| refine Proves.mergeStorage ?_) =>
    `(tactic| first | core_merge | refine Solidity.NFml.Proves.mergeStorage ?_)
  | `(tactic| refine simplify ?_) =>
    `(tactic| first | core_simplify | refine Solidity.NFml.Proves.simplify ?_)
  | `(tactic| refine Proves.simplify ?_) =>
    `(tactic| first | core_simplify | refine Solidity.NFml.Proves.simplify ?_)
  | `(tactic| refine Proves.eqDSplit ?_ ?_ ?_) =>
    `(tactic| first | refine Solidity.Proves.eqDSplit ?_ ?_ ?_ | refine Solidity.NFml.Proves.eqDSplit ?_ ?_ ?_)
  | `(tactic| exact Proves.definedWritten) =>
    `(tactic| first | exact Solidity.Proves.definedWritten | exact Solidity.NFml.Proves.definedWritten)
  | `(tactic| exact Proves.definedLit) =>
    `(tactic| first | exact Solidity.Proves.definedLit | exact Solidity.NFml.Proves.definedLit)
  | `(tactic| exact Proves.eqRefl) =>
    `(tactic| first | exact Solidity.Proves.eqRefl | exact Solidity.NFml.Proves.eqRefl)
  | `(tactic| exact Proves.eqClose) =>
    `(tactic| first | exact Solidity.Proves.eqClose | exact Solidity.NFml.Proves.eqClose)
  | `(tactic| exact Proves.eqDClose) =>
    `(tactic| first | exact Solidity.Proves.eqDClose | exact Solidity.NFml.Proves.eqDClose)
  | `(tactic| sol_apply_upd) => `(tactic| core_apply_upd)
  | `(tactic| sol_rw [$rs,*]) => `(tactic| core_rw [$rs,*])
  | `(tactic| rw [$rs,*]) => `(tactic| core_rw [$rs,*])

end Scoped

end Solidity
