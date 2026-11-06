import Solidity.Calculus.Symex
import Solidity.Calculus.CloseScoped
import Solidity.Calculus.CallFunctionTransform
import Solidity.Calculus.CallFunctionAffine

/-! # Default checked call-family leaf closure
Only the closer changes. The intrinsic calculus and single-rule walk stay
unchanged. Named leaves use exact operational laws; failed attempts restore
all state and leave ordinary handling available under its existing budgets.
-/
namespace Solidity.CloseCallSharing
open Lean Elab Tactic Meta

open Solidity.Quote

/-- Quote an accepted leaf with its semantic head retained. Quotation is
untrusted computation; replacement still requires kernel definitional equality. -/
def qUpdate {C : Contract} (Γ Δ : Ctx) (m : Modality) (U : Upd C Γ Δ)
    (φ : Fml C Δ) (qφ : Expr) : QM Expr := by
  cases h : CallFunctionTransform.classify? U with
  | none => exact do
      sctor ``Fml.upd #[← qCtx Γ, ← qCtx Δ, toExpr m, ← qUpd Γ Δ U, qφ]
  | some w =>
    cases w with
    | «local» target out => exact do
      match CallFunctionEmit.emit? m target out φ with
      | none => sctor ``Fml.upd #[← qCtx Γ, ← qCtx Γ, toExpr m, ← qUpd Γ Γ (Upd.nil.snoc (.local target (.val out))), qφ]
      | some e =>
        return mkAppN (mkConst ``CallFunctionLeaf.leaf) #[← contract, ← qCtx Γ,
          toExpr m, toExpr CallFunctionEmit.tableName, toExpr CallFunctionEmit.inputName,
          toExpr CallFunctionEmit.resultName,
          ← qTm (.val .uint :: Γ) (.val .uint) e.plan.base, toExpr e.plan.level,
          ← qIdx Γ (.val .uint) target, ← qIdx Γ (.val .uint) e.plan.input, qφ]

partial def qTransform {C : Contract} (Γ : Ctx) (φ : Fml C Γ) : QM Expr := do
  let Γe ← qCtx Γ
  match φ with
  | .tt => sctor ``Fml.tt #[Γe]
  | @Fml.eq _ _ p a b => sctor ``Fml.eq #[Γe, toExpr p, ← qTm Γ (.val p) a, ← qTm Γ (.val p) b]
  | @Fml.wellFormed _ _ s => sctor ``Fml.wellFormed #[Γe, ← qTm Γ .st s]
  | .not φ => sctor ``Fml.not #[Γe, ← qTransform Γ φ]
  | .and φ ψ => sctor ``Fml.and #[Γe, ← qTransform Γ φ, ← qTransform Γ ψ]
  | .imp φ ψ => sctor ``Fml.imp #[Γe, ← qTransform Γ φ, ← qTransform Γ ψ]
  | @Fml.upd _ _ Γ' m U φ =>
    qUpdate Γ Γ' m U (CallFunctionTransform.transform φ) (← qTransform Γ' φ)
  | @Fml.modal _ _ Γ₁ Γ₀ m P κ φ =>
    sctor ``Fml.modal #[Γe, ← qCtx Γ₁, ← qCtx Γ₀, toExpr m, ← qProg Γ Γ₁ P, ← qFrames Γ₁ Γ₀ κ,
      ← qTransform Γ₀ φ]
  | .havoc φ => sctor ``Fml.havoc #[Γe, ← qTransform Γ φ]
  | .all x p φ => sctor ``Fml.all #[Γe, toExpr x, toExpr p, ← qTransform (.val p :: Γ) φ]
  | .bind m x t φ => sctor ``Fml.bind #[Γe, toExpr m, toExpr x, qLTy t, ← qTransform (t :: Γ) φ]
  | .anon xs φ => do sctor ``Fml.anon #[Γe, ← qIdxList Γ xs, ← qTransform Γ φ]
  | .allocAll x A φ => sctor ``Fml.allocAll #[Γe, toExpr x, toExpr A, ← qTransform (.mem A :: Γ) φ]
  | .grow φ => sctor ``Fml.grow #[Γe, ← qTransform Γ φ]

def quoteTransform {C : Contract} (c : Expr) {Γ : Ctx} (φ : Fml C Γ) : Expr × Bool :=
  (Lean.ShareCommon.shareCommon ((qTransform Γ φ).go c),
    decide ((CallFunctionTransform.transform φ).tmSize < φ.tmSize))

/-- Apply the exact intrinsic equivalence and normalize its actual result.
Refusal keeps the old formula and is reported as unchanged. -/
private def shareCore (g : MVarId) : TacticM MVarId := do
  let some (C, φ) ← Symex.validGoal? g | throwError "sol_share_calls: expected closed validity"
  let before ← instantiateMVars (← g.getType)
  let ψ := mkApp3 (mkConst ``CallFunctionTransform.transform) C (ctxE []) φ
  let after := mkApp2 (mkConst ``Fml.Valid) C ψ
  let next ← mkFreshExprSyntheticOpaqueMVar after (← g.getTag)
  let eqv := mkApp2 (mkConst ``CallFunctionTransform.valid_iff) C φ
  -- Avoid eager `apply` unification through the entire producer. The final
  -- generated proof still has the same explicit kernel-checked type.
  g.assign (mkAppN (mkConst ``Iff.mp) #[after, before, eqv, next])
  if φ.hasFVar || φ.hasMVar then throwError "sol_share_calls: formula is not closed"
  let some contractName := C.constName? | throwError "sol_share_calls: expected a named contract"
  let (quoted, shrunk) ← unsafe evalExpr (Expr × Bool)
    (mkApp2 (mkConst ``Prod [0, 0]) (mkConst ``Expr) (mkConst ``Bool))
    (mkAppN (mkConst ``quoteTransform) #[C, quoteConstName contractName, ctxE [], ← Symex.evaluable φ])
  unless shrunk do throwError "sol_share_calls: no smaller checked call leaf"
  let quoted := Symex.restoreMarks φ quoted
  let result ← next.mvarId!.replaceTargetDefEq (mkApp2 (mkConst ``Fml.Valid) C quoted)
  return result

/-- Failure restores the goal and all assignments, including runtime errors. -/
def share (g : MVarId) : TacticM MVarId := do
  let saved ← saveState
  tryCatchRuntimeEx (shareCore g) fun ex => do
    saved.restore
    throw ex

elab "sol_share_calls" : tactic => do
  replaceMainGoal [← share (← getMainGoal)]

/-- Consume the actual typed affine base, checking its profile internally.
Unsupported shapes fail; no future coefficient or validity fact is assumed. -/
private def affineStepCore (g : MVarId) : TacticM MVarId := g.withContext do
  let before ← instantiateMVars (← g.getType)
  let_expr holds C Γ σ φ := before | throwError "sol_call_affine: expected holds"
  unless φ.isAppOfArity ``CallFunctionLeaf.leaf 11 do
    throwError "sol_call_affine: expected a named shared leaf"
  let args := φ.getAppArgs
  let a ← mkFreshExprMVar (mkConst ``CallFunctionTable.Key)
  let b ← mkFreshExprMVar (mkConst ``CallFunctionTable.Key)
  let pattern := mkAppN (mkConst ``CallFunctionAffine.term) #[C, Γ, a, b]
  unless ← withTransparency .all <| isDefEq pattern args[6]! do
    throwError "sol_call_affine: unsupported base"
  let a ← instantiateMVars a
  let b ← instantiateMVars b
  if a.hasMVar || b.hasMVar then throwError "sol_call_affine: incomplete coefficients"
  let profile ← mkAppM ``LE.le #[toExpr (1 : Int), ← mkAppM ``Subtype.val #[a]]
  -- mkDecideProof only constructs an expected-proposition hint. Validate it
  -- synchronously now, so a false profile refuses before reporting closure.
  let ha ← Derive.kernelLemma profile (← mkDecideProof profile)
  let eqv ← mkAppM ``CallFunctionAffine.holds_shared_affine_cases
    #[args[2]!, args[3]!, args[4]!, args[5]!, a, b, ha, args[7]!, args[8]!, args[9]!, args[10]!, σ]
  let eqvType ← inferType eqv
  let after := eqvType.appArg!
  let next ← mkFreshExprSyntheticOpaqueMVar after (← g.getTag)
  g.assign (mkAppN (mkConst ``Iff.mpr) #[before, after, eqv, next])
  return next.mvarId!

/-- Explicit local consumption also restores on unsupported profiles. -/
def affineStep (g : MVarId) : TacticM MVarId := do
  let saved ← saveState
  tryCatchRuntimeEx (affineStepCore g) fun ex => do
    saved.restore
    throw ex

elab "sol_call_affine" : tactic => do
  replaceMainGoal [← affineStep (← getMainGoal)]

/-- Keep the existing Boolean observations as hypotheses and derive their
propositional comparisons with a kernel theorem, never an assumed bound. -/
def comparisonFacts (g : MVarId) : MetaM MVarId := g.withContext do
  let declarations := (← getLCtx).foldl (fun acc d => acc.push d) #[]
  let mut g := g
  for d in declarations do
    let_expr Eq _ lhs rhs := d.type | continue
    unless lhs.isAppOf ``decide && rhs.isConstOf ``Bool.true do continue
    let fact ← mkAppM ``of_decide_eq_true #[mkFVar d.fvarId]
    let g' ← g.assert `callComparison (← inferType fact) fact
    let (_, g') ← g'.intro1
    g := g'
  return g

/-- Prefix-only fallback: the ordinary peeler may have no interval for a
landed value. Its same checked-return solver can use actual local facts here;
this route never introduces a bound or changes the opaque shared leaf. -/
private def settlePrefix (gs : List MVarId) (hs : List FVarId)
    (bounds : CloseJ.Bounds) (prems : Array FVarId) :
    TacticM (Option (MVarId × CloseJ.Bounds)) := do
  let some main := gs.getLast? | throwError "call sharing: no prefix goal"
  for originalSide in gs.dropLast do
    let side ← comparisonFacts originalSide
    let facts ← side.withContext do
      (← getLCtx).foldlM (init := #[]) fun keep d => do
        let t ← instantiateMVars d.type
        let eqSort ← if t.isAppOfArity ``Eq 3 then whnf (t.getArg! 0) else pure t
        let arithmetic := t.isAppOf ``LE.le || t.isAppOf ``LT.lt || t.isAppOf ``Int.le || t.isAppOf ``Int.lt ||
          (t.isAppOfArity ``Eq 3 && (eqSort.isConstOf ``Bool || eqSort.isConstOf ``Int))
        return if arithmetic then keep.push d.fvarId else keep
    unless (← CloseJ.closeSide side bounds facts) ||
        (← CloseJ.closeArith side bounds facts) do
      throwError "call sharing: prefix value not shown to return\n{MessageData.ofGoal side}"
  CloseJ.settle [main] hs bounds prems

/-- Continue only binder/premise/update prefix heads, retaining each actual
rest as an opaque formula while evaluating that one update. This deliberately
stops at the exact generalized leaf rather than unfolding its table clauses. -/
private partial def peelPrefix (g : MVarId) (bounds : CloseJ.Bounds)
    (prems : Array FVarId) (leaf : FVarId) : TacticM (Option MVarId) := g.withContext do
  let t ← instantiateMVars (← g.getType)
  unless t.isAppOfArity ``Solidity.holds 4 do
    throwError "call sharing: unsupported prefix target"
  if t.appArg! == mkFVar leaf then return some g
  let φ ← whnf t.appArg!
  let rest? :=
    if φ.isAppOfArity ``Fml.upd 6 || φ.isAppOfArity ``Fml.bind 6 then some (φ.getArg! 5)
    else if φ.isAppOfArity ``Fml.all 5 then some (φ.getArg! 4)
    else if φ.isAppOfArity ``Fml.imp 4 then some (φ.getArg! 3)
    else none
  let some rest := rest? | throwError "call sharing: unsupported prefix head"
  let ty ← withLocalDeclD `ψ (← inferType rest) fun ψ => do
    withLocalDeclD `hψ (← mkEq rest ψ) fun h => do
      mkForallFVars #[ψ, h] (mkApp t.appFn! (mkAppN φ.getAppFn (φ.getAppArgs.pop.push ψ)))
  let next ← mkFreshExprSyntheticOpaqueMVar ty (← g.getTag)
  g.assign (mkApp2 next rest (← mkEqRefl rest))
  let (fs, next) ← next.mvarId!.introNP 2
  let gs ← CloseJ.runOn next (← `(tactic| simp only [close_rw_s]))
  let [next] := gs | if gs.isEmpty then return none else
    throwError "call sharing: prefix normalization split"
  let (gs, hs, ps) ← CloseJ.introFront next
  let prems := prems ++ ps.toArray
  let some (next, bounds) ← settlePrefix gs hs bounds prems | return none
  let next ← next.withContext do
    let target ← instantiateMVars (← next.getType)
    unless target.isAppOfArity ``Solidity.holds 4 && target.appArg! == mkFVar fs[0]! do
      throwError "call sharing: prefix did not reach its actual rest"
    next.replaceTargetEq (mkApp target.appFn! rest)
      (← mkCongrArg target.appFn! (← mkEqSymm (mkFVar fs[1]!)))
  peelPrefix next bounds prems leaf

/-- One actual named family leaf, reached through its original state prefix.
A refused profile restores the entire input goal. -/
private def closeCore : TacticM Unit := do
  let incoming ← getMainGoal
  let incomingType ← instantiateMVars (← incoming.getType)
  let first ← if (incomingType.find? (fun e => e.isAppOfArity ``CallFunctionLeaf.leaf 11)).isSome then
      pure incoming
    else share incoming
  replaceMainGoal [first]
  let ty ← instantiateMVars (← first.getType)
  let some leaf := ty.find? (fun e => e.isAppOfArity ``CallFunctionLeaf.leaf 11)
    | throwError "sol_close_call_shared: no named leaf"
  let callLeafName ← mkFreshUserName `callLeaf
  let callLeafFact ← mkFreshUserName `hCallLeaf
  let (fs, next) ← first.generalize #[{ expr := leaf, xName? := callLeafName, hName? := callLeafFact }]
  let leafName ← next.withContext <| fs[0]!.getUserName
  replaceMainGoal [next]
  evalTactic (← `(tactic| (apply CloseS.valid_of_holds; intro σ)))
  -- Prefix transport keeps the complete table leaf opaque and stops only
  -- at its exact generalized variable, before expanding definitions.
  let some next ← peelPrefix (← getMainGoal) ({} : CloseJ.Bounds) #[] fs[0]!
    | do replaceMainGoal []; return
  replaceMainGoal [next]
  evalTactic (← `(tactic| (
    subst $(mkIdent leafName)
    all_goals sol_call_affine
    all_goals simp only [CallFunctionAffine.coefficients, close_rw_s]
    all_goals split
    all_goals (try simp only [close_rw_s] at *))))
  let goals ← getGoals
  setGoals (← goals.mapM fun g => do comparisonFacts g)
  evalTactic (← `(tactic| all_goals (first | (apply decide_eq_true_eq.mpr; omega) | omega)))
  unless (← getGoals).isEmpty do throwError "sol_close_call_shared: unfinished leaf"

/-- Optional explicit consumer, with the existing closer's proof budget. -/
def close : TacticM Unit := do
  let saved ← saveState
  tryCatchRuntimeEx (Budget.within CloseJ.budget <|
      Term.withoutErrToSorry <| withoutRecover closeCore) fun ex => do
    saved.restore
    throw ex

@[tactic Solidity.tacticSol_close_call_shared]
def evalSolCloseCallShared : Tactic := fun _ => close

/-- Both routes retain earlier anon/small-split/alias paths. Only a named
leaf or one update with more than the existing whole-operation limit enters
sharing, before generic per-operation expansion. Guards are disjoint per
invocation; recursive splits create new goals and may begin another pass. -/
private def routed (joined : Bool) : TacticM Unit := withMainContext do
  let ty ← instantiateMVars (← getMainTarget)
  unless ty.isAppOf ``Fml.Valid do throwUnsupportedSyntax
  let hasJoins := CloseJ.countJoins ty 0 1 != 0
  unless hasJoins == joined do throwUnsupportedSyntax
  let named := (ty.find? (fun e => e.isAppOfArity ``CallFunctionLeaf.leaf 11)).isSome
  unless named || CloseJ.countShare ty (CloseJ.shareWholeMax+1) > CloseJ.shareWholeMax do
    throwUnsupportedSyntax
  close

@[tactic Solidity.tacticSol_close_call_shared_plain]
def evalSolCloseCallSharedPlain : Tactic := fun _ => routed false

@[tactic Solidity.tacticSol_close_call_shared_joined]
def evalSolCloseCallSharedJoined : Tactic := fun _ => routed true

end Solidity.CloseCallSharing
