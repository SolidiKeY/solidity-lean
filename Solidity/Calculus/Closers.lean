import Solidity.Calculus.ProvesDerive
import Solidity.Calculus.WalkSyntax
import Solidity.Calculus.DecideComplete
import Solidity.Calculus.UpdRuleScoped

/-!
# The closers on a scoped leaf

After `sol_symex` on a scoped goal (`Fml.Valid ψ`, `⊨ᶠ dl!{ … }`), or `sol_leaf`
on a leaf `sol_prove` left, a leaf is closed on its scoped form:
`sol_close`, `sol_close_mt` and `sol_spec_close` read it through
`sol_close_unwrap` (`CloseS.valid_of_holds`, `Calculus/CloseScoped.lean`),
`holds` on the typed state.  `sol_close_eval` on the bare leaf `Fml.Valid ψ`, before its
state is introduced, takes the same first step here.  `sol_upd` and `sol_merge`
rewrite the scoped formula itself (M6c, W7 `w7-rewrites`): `Calculus/UpdRuleScoped.lean`'s
rules, the leaf staying scoped.  `sol_prove?` runs the scoped `sol_prove`
and the scoped leaf search after it.
-/

namespace Solidity

open Lean Elab Tactic

/-- `sol_close_eval` on a bare scoped leaf `Fml.Valid ψ`: the leaf as `holds`
reads it (`sol_close_unwrap`), its state introduced, then the scoped step
(`Calculus/CloseScoped.lean`). -/
@[tactic Solidity.tacticSol_close_eval]
def evalSolCloseEvalCore : Tactic := fun _ => withMainContext do
  let some _ ← Symex.validGoal? (← getMainGoal) | throwUnsupportedSyntax
  evalTactic (← `(tactic| (sol_close_unwrap; intro σ; sol_close_eval)))

/-- `sol_merge`: every stack of updates merged into one and what is dead
dropped. -/
syntax "sol_merge" : tactic

/-- `sol_upd r`: the update rule `r` at the first update where it fits. -/
syntax "sol_upd " term : tactic

open Meta in
/-- `sol_merge` on a scoped goal: every stack of updates merged and cleaned
on the scoped formula itself (`Fml.simpUpdsS`, `Fml.Valid.of_simpUpdsS`). -/
@[tactic Solidity.tacticSol_merge]
def evalSolMergeCore : Tactic := fun _ => withMainContext do
  let g ← getMainGoal
  let some (C, _) ← Symex.validGoal? g | throwUnsupportedSyntax
  Symex.reporting g do
    replaceMainGoal [← Symex.applyValid "sol_merge" g (mkApp (mkConst ``Fml.Valid.of_simpUpdsS) C)]

open Meta in
/-- `sol_upd r` on a scoped goal: the update rule `r` (`UpdRuleNameS`) at
the first update where it fits, on the scoped formula itself
(`Fml.updAtS`, `Fml.Valid.of_updAtSD`). -/
@[tactic Solidity.tacticSol_upd_]
def evalSolUpdCore : Tactic := fun stx => withMainContext do
  let g ← getMainGoal
  let some (C, _) ← Symex.validGoal? g | throwUnsupportedSyntax
  Symex.reporting g do
    let r ← Term.elabTermEnsuringType stx[1] (mkConst ``UpdRuleNameS)
    Term.synthesizeSyntheticMVarsNoPostponing
    let r ← instantiateMVars r
    replaceMainGoal [← Symex.applyValid "sol_upd" g (mkApp2 (mkConst ``Fml.Valid.of_updAtSD) C r)
      (some m!"rule {stx[1]} does not apply here")]

/-! ## `sol_prove?` on a scoped goal

The scoped `sol_prove` (`Fml.Valid φ` and `⊢ φ`, `Calculus/ProvesDerive.lean`),
then each leaf it leaves (a scoped sequent, `sol_leaf` its first line),
closed by the first of the scoped leaf tactics (`Derive.searchLeaf`,
`Derive.leafTacs`, its bounds read on the scoped leaf, `Seq.goalFits`); the
replay suggested (`Derive.replayLines`). -/

open Meta in
/-- `sol_prove?` on a scoped goal. -/
@[tactic Solidity.tacticSol_prove?]
def evalSolProveQCore : Tactic := fun stx => withMainContext do
  let g ← getMainGoal
  unless ← Walk.isCoreGoal g do throwUnsupportedSyntax
  let rest := (← getUnsolvedGoals).erase g
  let h0 ← IO.getNumHeartbeats
  setGoals [g]
  evalTactic (← `(tactic| sol_prove))
  let steps := Derive.replaySteps (← instantiateMVars (.mvar g))
  let leaves ← getUnsolvedGoals
  let mut hb : Nat := (← IO.getNumHeartbeats) - h0
  let mut found : List (Lean.Name × Array String) := []
  let mut open_ : List MVarId := []
  for l in leaves do
    let name ← l.getTag
    match ← Derive.searchLeaf l Seq.goalFits with
    | some (t, h) =>
      found := found ++ [(name, t)]
      hb := hb + h
    | none =>
      open_ := open_ ++ [l]
      found := found ++ [(name, #[r"sorry"])]
  if let some l := open_.head? then
    logInfo m!"sol_prove?: no tactic closes {← l.getTag}:{indentExpr (← l.getType)}"
  else unless ← Derive.replayFits hb do
    logWarning m!"sol_prove?: the replay needs about {hb / 1000} heartbeats in one \
      declaration, past `maxHeartbeats`"
  setGoals (open_ ++ rest)
  ProofTree.suggest stx[0] (Derive.replayLines found steps)

/-! ## `sol_auto` on a scoped goal

`sol_prove?` without the replay: the walk, then the leaf search on each leaf
(`Derive.searchLeaf`), all in one tactic.  Each try runs with heartbeats of
its own, and nothing follows it in the declaration, so a derivation's leaves
are each bounded, not their sum: what a replay of one `case` per leaf cannot
give, since every tactic after a long one fails the declaration's check. -/

open Meta in
/-- `sol_auto` on a scoped goal. -/
@[tactic Solidity.tacticSol_auto]
def evalSolAuto : Tactic := fun stx => withMainContext do
  let `(tactic| sol_auto $[(steps := $n:num)]?) := stx | throwUnsupportedSyntax
  let g ← getMainGoal
  unless ← Walk.isCoreGoal g do throwUnsupportedSyntax
  let rest := (← getUnsolvedGoals).erase g
  setGoals [g]
  evalTactic (← `(tactic| sol_prove $[(steps := $n)]?))
  for l in ← getUnsolvedGoals do
    -- the leaf's bounds read in its own heartbeats too, not only its tries
    withCurrHeartbeats do
      if (← Derive.searchLeaf l Seq.goalFits).isNone then
        throwError "sol_auto: no tactic closes {← l.getTag}:{indentExpr (← l.getType)}"
  setGoals rest

/-- `sol_auto_theorem n : φ`: the theorem `n`, proved by `sol_auto`, the
walk and each leaf elaborated with heartbeats of their own, and the
declaration added after them. An optional `:= by` supplies the proof of each
normalized leaf. It uses the derivation-only walk and emits checked `leafN`
auxiliary theorems, separating normalization from closing without changing
any heartbeat limit. A tactic cannot give that: whatever the
elaborator runs after it is checked against the declaration's heartbeats
since its start.  Each step is bounded as any proof's is; their number
grows with the leaves.  The kernel checks the whole proof, as always. -/
syntax (name := solAutoTheorem) "sol_auto_theorem " ident " : " term
  (" := " "by " tacticSeq)? : command

open Lean Elab Command Term Meta in
@[command_elab solAutoTheorem]
def elabSolAutoTheorem : CommandElab := fun stx => do
  let leaf? ← match stx with
    | `(command| sol_auto_theorem $_:ident : $_:term := by $ts:tacticSeq) => pure (some ts)
    | _ => pure none
  let n := stx[1].getId
  let declName := (← getCurrNamespace) ++ n
  liftTermElabM do
    -- Every auxiliary is a checked theorem, with the same limit as the root.
    let addProof (name : Lean.Name) (type value : Expr) : TermElabM Unit := do
      addDecl <| .thmDecl { name, levelParams := [], type, value }
    let type ← withCurrHeartbeats do
      let t ← elabType stx[3]
      synthesizeSyntheticMVarsNoPostponing
      instantiateMVars t
    let g ← mkFreshExprSyntheticOpaqueMVar type
    let leaves ← withCurrHeartbeats do
      let walk ← if leaf?.isSome then `(tactic| sol_derive) else `(tactic| sol_prove)
      Tactic.run g.mvarId! (Tactic.evalTactic walk)
    let mut idx := 0
    for l in leaves do
      match leaf? with
      | none =>
        withCurrHeartbeats do
          let closed ← Tactic.run l do
            if (← Derive.searchLeaf l Seq.goalFits).isNone then
              throwError "sol_auto_theorem: no tactic closes {← l.getTag}:{indentExpr (← l.getType)}"
          unless closed.isEmpty do throwError "sol_auto_theorem: a leaf is left open"
      | some ts =>
        -- Freeze the exact normalized leaf before spending its proof budget.
        let normalized ← withCurrHeartbeats do
          Tactic.run l (Tactic.evalTactic (← `(tactic| first
            | exact Proves.assumeInv
            | (refine Proves.openInv ?_; sol_leaf)
            | sol_leaf)))
        for n in normalized do
          idx := idx + 1
          let auxType ← instantiateMVars (← n.getType)
          if auxType.hasFVar || auxType.hasMVar then
            throwError "sol_auto_theorem: an auxiliary leaf is not closed"
          let aux ← mkFreshExprSyntheticOpaqueMVar auxType (← n.getTag)
          withCurrHeartbeats do
            let closed ← Tactic.run aux.mvarId! (Tactic.evalTactic (← `(tactic| ($ts:tacticSeq))))
            unless closed.isEmpty do throwError "sol_auto_theorem: an auxiliary leaf is left open"
          let auxValue ← instantiateMVars aux
          if auxValue.hasMVar then throwError "sol_auto_theorem: an auxiliary proof is not closed"
          let auxName := declName ++ Lean.Name.mkSimple s!"leaf{idx}"
          withCurrHeartbeats do addProof auxName auxType auxValue
          n.assign (mkConst auxName)
    withCurrHeartbeats do
      let value ← instantiateMVars g
      if value.hasMVar then throwError "sol_auto_theorem: the proof is not closed"
      addProof declName type value

/-! ## A scoped formula refuted at a state

`¬ ⊨ᶠ dl!{ … }` by one typed state where the run panics, or fails under the
diamond: the typed run's outcome read by the kernel (`decide +kernel` on
`TRes.isPanic`/`TRes.isFail`), as today's refutations read it by `rfl`.  A
run exhausted (a push at the bound) is no failure: both modalities accept
it (decision 15). -/

/-- The typed outcome is a panic. -/
def TRes.isPanic {α : Type} : TRes α → Bool
  | .error .panic => true
  | _ => false

/-- The typed outcome is one the diamond refuses: a revert, a panic, a
divergence. -/
def TRes.isFail {α : Type} : TRes α → Bool
  | .error .exhausted => false
  | .error _ => true
  | .ok _ => false

/-- No modality holds of a run that panics. -/
theorem _root_.Solidity.Modality.afterRunTR_not_panic {α : Type} {m : Modality} {p : α → Prop}
    {r : TRes α} (h : m.afterRunTR p r) (hp : r.isPanic = true) : False := by
  cases r with
  | ok _ => cases hp
  | error e => cases e <;> first | exact h.2 rfl | cases hp

/-- The diamond does not hold of a run that fails. -/
theorem _root_.Solidity.Modality.afterRunTR_diamond_fail {α : Type} {p : α → Prop}
    {r : TRes α} (h : Modality.diamond.afterRunTR p r) (hp : r.isFail = true) : False := by
  cases r with
  | ok _ => cases hp
  | error e =>
    cases e with
    | exhausted => cases hp
    | _ => exact absurd h.1 nofun

end Solidity
