import Solidity.Calculus.Closers
import Solidity.Tools.Counterexample

/-! # Literal signed intervals under the sequential closer
The actual bound producer supplies the interval proof; wrong bounds have
inhabited countermodels. Existing proof and Boolean-case budgets stay fixed.
-/
namespace Solidity.Examples.Tactics.JoinSigned
open Lean Meta Elab Command Term Tactic
local instance : InContract := ⟨StandardExample⟩
open scoped Solidity.Scoped

/-- Use the actual interval producer's stored proof, not a parallel proof. -/
elab "literal_interval " h:ident a:ident : tactic => withMainContext do
  let h ← getFVarId h
  let a ← getFVarId a
  let some (g, bs) ← CloseJ.addInterval (← getMainGoal) h {}
    | throwError "unexpectedly closed before interval"
  let some (_, _, bound) := bs.get? a | throwError "missing certified literal interval"
  g.withContext do g.assign (mkFVar bound)
  replaceMainGoal []

/-- The first conditional's actual certified range, including negative literals. -/
theorem firstInterval (c : Bool) (a : PrimTy.int.Denote)
    (h : (bif c then some (CloseS.intOf (-6)) else some (CloseS.intOf (-7))) = some a) :
    -7 ≤ a.val ∧ a.val ≤ -6 := by
  literal_interval h a

/-- The corresponding ordinary unsigned path still produces its exact interval. -/
theorem unsignedInterval (c : Bool) (a : PrimTy.uint.Denote)
    (h : (bif c then some (CloseS.uintOf 6) else some (CloseS.uintOf 7)) = some a) :
    6 ≤ a.val ∧ a.val ≤ 7 := by
  literal_interval h a

/-- Compose two actual interval certificates in evaluation order. -/
elab "composed_interval " h₁:ident h₂:ident b:ident : tactic => withMainContext do
  let h₁ ← getFVarId h₁
  let h₂ ← getFVarId h₂
  let b ← getFVarId b
  let some (g₁, bs₁) ← CloseJ.addInterval (← getMainGoal) h₁ {}
    | throwError "unexpected first interval closure"
  let some (g₂, bs₂) ← CloseJ.addInterval g₁ h₂ bs₁
    | throwError "unexpected second interval closure"
  let some (_, _, bound) := bs₂.get? b | do
    g₂.withContext do
      for d in (← getLCtx) do
        if d.userName.toString.startsWith "hjoin" then
          logInfo m!"COMPOSED_FACT {d.type}; VALUES={CloseJ.valuesOf (mkFVar b) d.type}"
    throwError "missing composed interval"
  g₂.withContext do g₂.assign (mkFVar bound)
  replaceMainGoal []

private def checked (n : Int) : Option PrimTy.int.Denote :=
  if -Semantics.intBound ≤ n ∧ n < Semantics.intBound then some (CloseS.intOf n) else none

/-- The second dependent join carries the certified final range. -/
theorem secondInterval (c d : Bool) (a b : PrimTy.int.Denote)
    (h₁ : (bif c then some (CloseS.intOf (-6)) else some (CloseS.intOf (-7))) = some a)
    (h₂ : (bif d then checked (a.val - 1) else checked (a.val - 2)) = some b) :
    -9 ≤ b.val ∧ b.val ≤ -7 := by
  simp only [checked] at h₂
  composed_interval h₁ h₂ b

/-- Exact previously failing forced sequential fixture. -/
theorem sequential : ⊨ᶠ dl!{ ∀ bool c; ∀ bool d; { x := -5 }
    { x := (c ? x + -1 : x + -2) }
    { x := (d ? x + -1 : x + -2) } x >= -9 } := by
  sol_close_join_steps

/-- Both final endpoints are retained by the forced sequential closer. -/
theorem finalInterval : ⊨ᶠ dl!{ ∀ int x; ∀ bool c; ∀ bool d; { x := -5 }
    { x := (c ? x + -1 : x + -2) }
    { x := (d ? x + -1 : x + -2) } (x >= -9 ∧ x <= -7) } := by
  sol_close_join_steps

/-- Without postcondition parentheses, the upper bound observes the original
unconstrained x outside the updates. That different claim is refuted. -/
theorem misScopedCombination : ¬ (⊨ᶠ dl!{ ∀ int x; ∀ bool c; ∀ bool d; { x := -5 }
    { x := (c ? x + -1 : x + -2) }
    { x := (d ? x + -1 : x + -2) } x >= -9 ∧ x <= -7 }) := by
  sol_refute

/-- Both false conditions return -9, rejecting the tempting tighter lower bound. -/
theorem wrongBound : ¬ (⊨ᶠ dl!{ ∀ bool c; ∀ bool d; { x := -5 }
    { x := (c ? x + -1 : x + -2) }
    { x := (d ? x + -1 : x + -2) } x >= -8 }) := by
  sol_refute

private def underflow : Tm StandardExample [] (.val .int) :=
  .app2 (.binop .add rfl) (.app0 (.lit (CloseS.intOf (-57896044618658097711785492504343953926634992332820282019728792003956564819968))))
    (.app0 (.lit (CloseS.intOf (-1))))
/-- Signed word underflow remains a real partial operation. -/
theorem signedUnderflow : underflow.eval (State.init StandardExample) = none := by
  decide +kernel

/-- Exercise the literal route at the existing case cap, including irrelevant locals.
Seven used Booleans must refuse this bounded optimization, not refute the formula. -/
elab "#literal_interval_cap " n:num : command => liftTermElabM do
  let total := n.getNat
  let used := if total == 26 then 6 else total
  unless used == 6 || used == 7 do throwError "control supports six or seven used Booleans"
  let names := (List.range total).map fun i => "c" ++ toString i
  let rhs := (names.take used).foldr
    (fun c rest => "(bif " ++ c ++ " then some (CloseS.intOf (-6)) else " ++ rest ++ ")")
    "some (CloseS.intOf (-7))"
  let text := "∀ (x : PrimTy.int.Denote) (" ++ String.intercalate " " names ++
    " : Bool), " ++ rhs ++ " = some x → -7 ≤ x.val ∧ x.val ≤ -6"
  let .ok stx := Parser.runParserCategory (← getEnv) `term text | throwError "cap parser"
  let ty ← Term.elabTerm stx none
  let root ← mkFreshExprSyntheticOpaqueMVar ty
  let start ← IO.monoNanosNow
  let hb ← IO.getNumHeartbeats
  discard <| Tactic.run root.mvarId! (Budget.within CloseJ.budget <| Tactic.withoutRecover do
    let (fs, g) ← root.mvarId!.introN (total + 2)
    setGoals [g]
    let some (g, bounds) ← CloseJ.addInterval g fs[total+1]! {}
      | throwError "unexpected cap closure"
    setGoals [g]
    if used == 7 then
      if (bounds.get? fs[0]!).isSome then throwError "exceeded existing literal case cap"
      logInfo "LITERAL_CAP seven: refused=true; global_refutation=false; limit=64"
      return
    let some (lo, hi, fact) := bounds.get? fs[0]! | throwError "six-case literal interval refused"
    unless lo == -7 && hi == -6 do throwError "wrong literal interval"
    g.assign (mkFVar fact)
    let proof ← instantiateMVars root
    let ty ← instantiateMVars ty
    if proof.hasMVar || proof.hasFVar || proof.hasSorry || ty.hasMVar then throwError "incomplete cap proof"
    let name := (← getCurrNamespace) ++ (if total == 26 then `literalSixIrrelevant else `literalSix)
    addDecl (.thmDecl { name := name, levelParams := [], type := ty, value := proof })
    logInfo m!"LITERAL_CAP six: kernel_checked=true; irrelevant={total-used}; limit=64; ns={(← IO.monoNanosNow)-start}; raw_heartbeats={(← IO.getNumHeartbeats)-hb}")

#literal_interval_cap 6
#literal_interval_cap 7
#literal_interval_cap 26

/-- A bound proof from another local context cannot close a target-only comparison. -/
elab "#stale_target_interval" : command => liftTermElabM do
  let ty ← Term.elabTerm (← `(term| ∀ a : PrimTy.uint.Denote, a.val ≤ 4)) none
  let root ← mkFreshExprSyntheticOpaqueMVar ty
  discard <| Tactic.run root.mvarId! (Tactic.withoutRecover do
    let (a, g) ← root.mvarId!.intro1
    let bounds ← g.withContext do
      let p ← CloseJ.intervalP (mkFVar a) (toExpr (0 : Int)) (toExpr (4 : Int))
      let stale ← withLocalDeclD `stale p fun h => pure h.fvarId!
      pure (({} : CloseJ.Bounds).insert a (0, 4, stale))
    if ← CloseJ.closeArith g bounds #[] then throwError "used a stale target interval"
    if ← g.isAssigned then throwError "assigned unsupported target"
    logInfo "STALE_TARGET refused=true; global_refutation_requires_countermodel=true")

#stale_target_interval

/-- An inhabited witness proves that the stale target's universal claim is false. -/
theorem staleTargetCountermodel : ¬ (∀ a : PrimTy.uint.Denote, a.val ≤ 4) := by
  intro h
  have bad : (uintOfNat 5).val ≤ 4 := h (uintOfNat 5)
  change (5 : Int) ≤ 4 at bad
  omega

end Solidity.Examples.Tactics.JoinSigned
