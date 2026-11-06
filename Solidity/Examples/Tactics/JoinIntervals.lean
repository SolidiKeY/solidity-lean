import Solidity.Calculus.Closers
import Solidity.Tools.Counterexample
/-! # Certified interval hull and fixed Boolean-case controls
Refusal logs are metadata, paired with inhabited kernel countermodels.
Positive certificates are installed only after complete proof checking. -/
namespace Solidity.Examples.Tactics.JoinIntervals
open Lean Elab Command Meta Tactic
open Solidity CloseJ
private abbrev U := PrimTy.uint.Denote

-- Metadata refusal controls are paired below with genuine countermodels.
elab "#join_interval_control " mode:ident : command => liftTermElabM do
  let mixed := mode.getId == `mixed
  let wrong := mode.getId == `wrong
  let missing := mode.getId == `missing || mode.getId == `stale
  let tyStx ← if mixed then `(term|
      ∀ (a b x : U) (c d : Bool),
        (1 ≤ a.val ∧ a.val ≤ 2) → (3 ≤ b.val ∧ b.val ≤ 4) →
        (bif c then some a else bif d then some b else some (uintOfNat 0)) = some x →
        0 ≤ x.val ∧ x.val ≤ 4)
    else if missing then `(term|
      ∀ (a b x : U) (c : Bool), (1 ≤ a.val ∧ a.val ≤ 2) →
        (bif c then some a else some b) = some x → x.val ≤ 4)
    else if wrong then `(term|
      ∀ (a b x : U) (c : Bool),
        (1 ≤ a.val ∧ a.val ≤ 3) → (2 ≤ b.val ∧ b.val ≤ 4) →
        (bif c then some a else some b) = some x → x.val ≤ 3)
    else `(term|
      ∀ (a b x : U) (c : Bool),
        (1 ≤ a.val ∧ a.val ≤ 2) → (3 ≤ b.val ∧ b.val ≤ 4) →
        (bif c then some a else some b) = some x → 1 ≤ x.val ∧ x.val ≤ 4)
  let ty ← Term.elabTerm tyStx none
  let g ← mkFreshExprSyntheticOpaqueMVar ty
  discard <| Tactic.run g.mvarId! (Tactic.withoutRecover do
    let (fs, g₁) ← g.mvarId!.introN (if mixed then 8 else if missing then 6 else 7)
    setGoals [g₁]
    let ha := fs[if mixed then 5 else 4]!
    let hx := fs[if mixed then 7 else if missing then 5 else 6]!
    let mut bounds : Bounds := ({} : Bounds).insert fs[0]! (1, if wrong then 3 else 2, ha)
    if mode.getId == `stale then
      let hbTy ← g₁.withContext <| intervalP (mkFVar fs[1]!) (toExpr (3 : Int)) (toExpr (4 : Int))
      let stale ← g₁.withContext <| withLocalDeclD `stale hbTy fun h => pure h.fvarId!
      bounds := bounds.insert fs[1]! (3, 4, stale)
    else if !missing then
      bounds := bounds.insert fs[1]! (if wrong then 2 else 3, 4, fs[if mixed then 6 else 5]!)
    let some (g₂, bounds') ← Solidity.CloseJ.addInterval g₁ hx bounds
      | throwError "control unexpectedly closed during interval inference"
    setGoals [g₂]
    if missing then
      if (bounds'.get? fs[2]!).isSome then throwError "invented interval for unavailable base"
      logInfo m!"HULL_REFUSED {mode.getId}: no_interval=true"
      return
    let some (lo, hi, hBound) := bounds'.get? fs[2]! | do
      let ty ← g₂.withContext <| hx.getType
      let (_, gd) ← assertH g₂ `diagnosticFact ty (mkFVar hx)
      let [gd] ← runOn gd (← `(tactic| sol_close_join_fact $(mkIdent `diagnosticFact))) | throwError "normalization shape"
      gd.withContext do
        let some hd := (← getLCtx).findFromUserName? `diagnosticFact | throwError "missing fact"
        let vs := valuesOf (mkFVar fs[2]!) hd.type
        logInfo m!"HULL_DEBUG {mode.getId}: normalized={hd.type}; values={vs}; affine={vs.map affine}"
        for v in vs do
          let key := if v.isAppOfArity ``Subtype.val 3 && v.appArg!.isFVar then some v.appArg!.fvarId! else none
          logInfo m!"HULL_SHAPE: raw={repr v}; key={repr key}; fsA={repr fs[0]!}; fsB={repr fs[1]!}; mapA={(bounds.get? fs[0]!).isSome}; mapB={(bounds.get? fs[1]!).isSome}"

      throwError "no certified hull"
    unless lo == (if mixed then 0 else 1) && hi == 4 do throwError "incorrect hull endpoints"
    if wrong then
      let e ← g₂.withContext <| omegaIn #[hBound] (← g₂.getType)
      if e.isSome then throwError "proved false upper bound"
      logInfo "HULL_REFUSED wrong: false_result_not_proved=true"
      return
    g₂.assign (mkFVar hBound)
    let proof ← instantiateMVars g
    if proof.hasSorry || proof.hasMVar then throwError "incomplete hull proof"
    let name := (← getCurrNamespace) ++ mode.getId.appendAfter "_closed"
    addDecl <| .thmDecl { name := name, levelParams := [], type := (← instantiateMVars ty), value := proof }
    logInfo m!"HULL_CONTROL {mode.getId}: kernel_checked=true")

#join_interval_control bounded
#join_interval_control mixed
#join_interval_control missing
#join_interval_control stale
#join_interval_control wrong

-- Exercise the original 64-case cap without raising a proof budget.
elab "#join_interval_cap " n:num : command => liftTermElabM do
  let total := n.getNat
  let n := if total == 26 then 6 else total
  unless n == 6 || n == 7 do throwError "control supports six or seven Booleans"
  let names := (List.range total).map fun i => "c" ++ toString i
  let rhs := (names.take n).foldr (fun c rest => "(bif " ++ c ++ " then some a else " ++ rest ++ ")") "some b"
  let text := "∀ (a b x : U) (" ++ String.intercalate " " names ++ " : Bool), " ++
    "(1 ≤ a.val ∧ a.val ≤ 2) → (3 ≤ b.val ∧ b.val ≤ 4) → " ++
    rhs ++ " = some x → 1 ≤ x.val ∧ x.val ≤ 4"
  let .ok stx := Parser.runParserCategory (← getEnv) `term text | throwError "control parser"
  let ty ← Term.elabTerm stx none
  let root ← mkFreshExprSyntheticOpaqueMVar ty
  discard <| Tactic.run root.mvarId! (Budget.within CloseJ.budget <| Tactic.withoutRecover do
    let (fs, g) ← root.mvarId!.introN (total + 6)
    setGoals [g]
    let bounds : Bounds := (({} : Bounds).insert fs[0]! (1, 2, fs[total+3]!)).insert fs[1]! (3, 4, fs[total+4]!)
    let some (g', bounds') ← Solidity.CloseJ.addInterval g fs[total+5]! bounds
      | throwError "cap control unexpectedly closed"
    setGoals [g']
    if n == 7 then
      if (bounds'.get? fs[2]!).isSome then throwError "exceeded original 64-case cap"
      logInfo "HULL_CAP seven: refused=true; original_limit=64"
      return
    let some (lo, hi, hb) := bounds'.get? fs[2]! | throwError "six-case positive refused"
    unless lo == 1 && hi == 4 do throwError "six-case wrong hull"
    g'.assign (mkFVar hb)
    let proof ← instantiateMVars root
    let ty ← instantiateMVars ty
    if proof.hasMVar || proof.hasSorry || ty.hasMVar then throwError "incomplete cap certificate"
    addDecl <| .thmDecl { name := (← getCurrNamespace) ++ (if total == 26 then `sixIrrelevantClosed else `sixClosed), levelParams := [], type := ty, value := proof }
    logInfo m!"HULL_CAP six: kernel_checked=true; irrelevant_bools={total-n}; original_limit=64")

#join_interval_cap 6
#join_interval_cap 7
#join_interval_cap 26

/-- A missing upper bound cannot be supplied by the value's Solidity type. -/
theorem missingBoundCountermodel : ¬ (∀ (a b x : U) (c : Bool),
    (1 ≤ a.val ∧ a.val ≤ 2) → (bif c then some a else some b) = some x → x.val ≤ 4) := by
  intro h
  have bad : (uintOfNat 5).val ≤ 4 := h (uintOfNat 1) (uintOfNat 5) (uintOfNat 5) false (by decide +kernel) rfl
  change (5 : Int) ≤ 4 at bad
  omega

/-- Overlapping valid intervals do not justify a narrower result interval. -/
theorem wrongBoundCountermodel : ¬ (∀ (a b x : U) (c : Bool),
    (1 ≤ a.val ∧ a.val ≤ 3) → (2 ≤ b.val ∧ b.val ≤ 4) →
    (bif c then some a else some b) = some x → x.val ≤ 3) := by
  intro h
  have bad : (uintOfNat 4).val ≤ 3 := h (uintOfNat 1) (uintOfNat 4) (uintOfNat 4) false (by decide +kernel) (by decide +kernel) rfl
  change (4 : Int) ≤ 3 at bad
  omega

open scoped Solidity.Scoped
local instance : InContract := ⟨StandardExample⟩

/-- A selected checked overflow stays observable under the diamond. -/
theorem selectedOverflow : ¬ (⊨ᶠ dl!{ ⟨ uint x = a; uint y = 0;
    if (b == 1) { x = x + 1; } else { x = y + 1; };
    if (c == 1) { y = x + 1; } else { y = y + 1; }; ⟩ y >= 0 }) := by
  sol_refute

/-- Selecting division by zero still prevents a returning execution. -/
theorem selectedDivision : ¬ (⊨ᶠ dl!{ ⟨ uint x = 0; uint y = 0;
    if (b == 1) { x = 1 / 0; } else { x = 1; };
    if (c == 1) { y = x + 1; } else { y = y + 1; }; ⟩ y >= 0 }) := by
  sol_refute

/-- An untaken failing RHS is not eagerly evaluated. -/
theorem untakenDivision : ⊨ᶠ dl!{ b == 1 → ⟨ uint x = 0; uint y = 0;
    if (b == 1) { x = 1; } else { x = 1 / 0; };
    if (c == 1) { y = x + 1; } else { y = x + 1; }; ⟩ y == 2 } := by
  sol_prove
-- A stale bound must not prevent proving an impossible Boolean side case.
elab "#join_stale_case_control" : command => liftTermElabM do
  let ty ← Term.elabTerm (← `(term| ∀ (a : PrimTy.uint.Denote),
    a.val = 1 → decide (a.val = 1) = false →
    (none : Option PrimTy.uint.Denote).isSome = true)) none
  let root ← mkFreshExprSyntheticOpaqueMVar ty
  discard <| Tactic.run root.mvarId! (Tactic.withoutRecover do
    let (fs, g) ← root.mvarId!.introN 3
    setGoals [g]
    let boundTy ← g.withContext do CloseJ.intervalP (mkFVar fs[0]!) (toExpr (0 : Int)) (toExpr (2 : Int))
    let stale ← g.withContext do withLocalDeclD `stale boundTy fun h => pure h.fvarId!
    let bounds : CloseJ.Bounds := ({} : CloseJ.Bounds).insert fs[0]! (0, 2, stale)
    unless ← Solidity.CloseJ.closeSide g bounds #[fs[1]!,fs[2]!] do
      throwError "stale bound blocked actual case contradiction"
    setGoals [])
  let proof ← instantiateMVars root
  let ty ← instantiateMVars ty
  if proof.hasMVar || proof.hasSorry || ty.hasMVar then throwError "incomplete stale-case proof"
  addDecl <| .thmDecl { name := (← getCurrNamespace) ++ `staleDecisionClosed, levelParams := [], type := ty, value := proof }
  logInfo "STALE_DECISION_CONTROL: kernel_checked=true"

#join_stale_case_control

/-- Without the matching premise, a false Boolean decision can select a failing value. -/
theorem caseWithoutPremiseCountermodel : ¬ (∀ (a : PrimTy.uint.Denote),
    decide (a.val = 1) = false → (none : Option PrimTy.uint.Denote).isSome = true) := by
  intro h
  have bad : false = true := h (uintOfNat 2) (by decide +kernel)
  cases bad

end Solidity.Examples.Tactics.JoinIntervals
