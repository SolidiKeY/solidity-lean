import Solidity.Frontend.Testing

/-! Validation-driver integrity controls. These test the kernel boundary, not
compiler or EVM behavior. The original PublicGetters source observations and
aggregate roster remain in scripts/public-getters.test.mjs. -/
namespace Solidity.Tests.GetterKernelSharing
open Lean Meta Elab Command Tactic

private def Empty : Contract := contract!{}

run_elab do
  let C := mkConst ``Empty
  let R := mkConst ``RuleSet.all
  let Γ := ctxE []
  let H := mkApp2 (mkConst ``Hyps.nil) C Γ
  let φ := mkApp2 (mkConst ``Fml.tt) C Γ
  let ty := mkAppN (mkConst ``Proves) #[C, R, Γ, Γ, H, φ]
  let propose (share : Bool) : TermElabM Expr := do
    let g ← mkFreshExprSyntheticOpaqueMVar ty
    let leaves ← Seq.prove g.mvarId! C R Γ H φ (some 1) (oneCheck := 1) (shareCheck := share)
    unless leaves.isEmpty do throwError "true control left an open leaf"
    let proof ← instantiateMVars g
    if proof.hasMVar || proof.hasFVar || proof.hasSorry then
      throwError "certificate is not a closed proof"
    return proof
  let shared ← propose true
  let certificate := shared.find? fun e =>
    e.isAppOfArity ``id 2 && (e.getArg! 0).isAppOfArity ``Eq 3 &&
      ((e.getArg! 0).getArg! 1).isAppOf ``Seq.residueWithin
  let some certificate := certificate
    | throwError "shared residue certificate was not retained"
  let exactType := certificate.getArg! 0
  unless exactType.isAppOfArity ``Eq 3 && (exactType.getArg! 1).isAppOf ``Seq.residueWithin do
    throwError "certificate lost the original residue equality"
  let leafTy := mkApp (mkConst ``Seq.SLeaf) C
  let listTy := mkApp (mkConst ``List [0]) leafTy
  let resultTy := mkApp (mkConst ``Option [0]) listTy
  let expectedRhs := mkApp2 (mkConst ``Option.some [0]) listTy (mkApp (mkConst ``List.nil [0]) leafTy)
  let expectedLhs := mkAppN (mkConst ``Seq.residueWithin) #[C, toExpr (1 : Nat), R, Γ, H, φ]
  let expectedEq := mkApp3 (mkConst ``Eq [1]) resultTy expectedLhs expectedRhs
  unless exactType == expectedEq do throwError "original residue equality changed"
  let validName := `Solidity.Tests.GetterKernelSharing.sharedAccepted
  withOptions (Elab.async.set · false) <|
    addDecl <| .thmDecl { name := validName, levelParams := [], type := ty, value := shared }
  let some stored := (← getEnv).find? validName | throwError "accepted theorem disappeared"
  let some storedProof := stored.value? | throwError "accepted proof disappeared"
  unless (storedProof.find? fun e => e.isAppOfArity ``id 2 && e.getArg! 0 == exactType).isSome do
    throwError "final theorem lost its exact equality checkpoint"
  let invalid := shared.replace fun e =>
    if e != certificate then none else
      let type := e.getArg! 0
      let resTy := type.getArg! 0
      let noneValue := mkApp (mkConst ``Option.none [0]) (resTy.getArg! 0)
      some (mkApp2 (mkConst ``id [0]) type (mkApp2 (mkConst ``Eq.refl [1]) resTy noneValue))
  if invalid == shared then throwError "malformed proposal control did not change the value"
  let rejectedName := `Solidity.Tests.GetterKernelSharing.malformedRejected
  if (← getEnv).contains rejectedName then throwError "malformed control name already exists"
  let saved ← Term.saveState
  let context ← readThe Core.Context
  let deadline := context.initHeartbeats + context.maxHeartbeats
  let accepted ← try
      withOptions (Elab.async.set · false) <|
        addDecl <| .thmDecl { name := rejectedName, levelParams := [], type := ty, value := invalid }
      pure true
    catch _ => pure false
  if accepted then throwError "kernel accepted the malformed residue proposal"
  saved.restore
  if (← getEnv).contains rejectedName then throwError "rejected declaration survived rollback"
  let now ← IO.getNumHeartbeats
  let remaining := if context.maxHeartbeats == 0 then 0 else deadline - now
  if context.maxHeartbeats != 0 && remaining == 0 then throwError "original control budget exhausted"
  withTheReader Core.Context
      (fun c => { c with initHeartbeats := now, maxHeartbeats := remaining }) do
    let checked ← propose false
    if (checked.find? fun e => e.isAppOfArity ``id 2 && e.getArg! 0 == exactType).isSome then
      throwError "ordinary checked policy unexpectedly deferred a certificate"
    let checkedName := `Solidity.Tests.GetterKernelSharing.checkedFallback
    withOptions (Elab.async.set · false) <|
      addDecl <| .thmDecl { name := checkedName, levelParams := [], type := ty, value := checked }
    for name in [validName, checkedName] do
      let axioms ← collectAxioms name
      unless axioms.all ([``propext, ``Classical.choice, ``Quot.sound].contains ·) do
        throwError "nonstandard axioms in {name}: {axioms}"
      logInfo m!"{name}: kernel checked, axioms={axioms}"
    logInfo "malformed residue rejected; state restored; checked fallback passed within original deadline"
run_elab do
  let C := mkConst ``Empty
  let Γ := ctxE []
  let φ := mkApp2 (mkConst ``Fml.tt) C Γ
  let ty := mkApp2 (mkConst ``Fml.Valid) C φ
  let propose (share : Bool) : TermElabM Expr := do
    let g ← mkFreshExprSyntheticOpaqueMVar ty
    let closed ← withOptions (·.setBool `sol.prove.sharedResidues share) <|
      Decide.closeScoped g.mvarId! C φ
    unless closed do throwError "true closer control left an open goal"
    let proof ← instantiateMVars g
    if proof.hasMVar || proof.hasFVar || proof.hasSorry then
      throwError "certificate is not a closed proof"
    return proof
  let shared ← propose true
  let certificate := shared.find? fun e =>
    e.isAppOfArity ``id 2 && (e.getArg! 0).isAppOfArity ``Eq 3 &&
      ((e.getArg! 0).getArg! 1).isAppOf ``Seq.checkCore
  let some certificate := certificate
    | throwError "shared scoped closer certificate was not retained"
  let exactType := certificate.getArg! 0
  unless exactType.isAppOfArity ``Eq 3 && (exactType.getArg! 1).isAppOf ``Seq.checkCore do
    throwError "certificate lost the original scoped closer equality"
  let resultTy := mkApp (mkConst ``Option [0]) (mkConst ``Bool)
  let expectedRhs := mkApp2 (mkConst ``Option.some [0]) (mkConst ``Bool) (mkConst ``Bool.true)
  let expectedLhs := mkApp2 (mkConst ``Seq.checkCore) C φ
  let expectedEq := mkApp3 (mkConst ``Eq [1]) resultTy expectedLhs expectedRhs
  unless exactType == expectedEq do throwError "original closer equality changed"
  let validName := `Solidity.Tests.GetterKernelSharing.scopedAccepted
  withOptions (Elab.async.set · false) <|
    addDecl <| .thmDecl { name := validName, levelParams := [], type := ty, value := shared }
  let some stored := (← getEnv).find? validName | throwError "accepted theorem disappeared"
  let some storedProof := stored.value? | throwError "accepted proof disappeared"
  unless (storedProof.find? fun e => e.isAppOfArity ``id 2 && e.getArg! 0 == exactType).isSome do
    throwError "final theorem lost its exact equality checkpoint"
  let invalid := shared.replace fun e =>
    if e != certificate then none else
      let type := e.getArg! 0
      let resTy := type.getArg! 0
      let noneValue := mkApp (mkConst ``Option.none [0]) (resTy.getArg! 0)
      some (mkApp2 (mkConst ``id [0]) type (mkApp2 (mkConst ``Eq.refl [1]) resTy noneValue))
  if invalid == shared then throwError "malformed proposal control did not change the value"
  let rejectedName := `Solidity.Tests.GetterKernelSharing.scopedMalformedRejected
  if (← getEnv).contains rejectedName then throwError "malformed control name already exists"
  let saved ← Term.saveState
  let context ← readThe Core.Context
  let deadline := context.initHeartbeats + context.maxHeartbeats
  let accepted ← try
      withOptions (Elab.async.set · false) <|
        addDecl <| .thmDecl { name := rejectedName, levelParams := [], type := ty, value := invalid }
      pure true
    catch _ => pure false
  if accepted then throwError "kernel accepted the malformed scoped closer proposal"
  saved.restore
  if (← getEnv).contains rejectedName then throwError "rejected declaration survived rollback"
  let now ← IO.getNumHeartbeats
  let remaining := if context.maxHeartbeats == 0 then 0 else deadline - now
  if context.maxHeartbeats != 0 && remaining == 0 then throwError "original control budget exhausted"
  withTheReader Core.Context
      (fun c => { c with initHeartbeats := now, maxHeartbeats := remaining }) do
    let checked ← propose false
    if (checked.find? fun e => e.isAppOfArity ``id 2 && e.getArg! 0 == exactType).isSome then
      throwError "ordinary checked policy unexpectedly deferred a certificate"
    let checkedName := `Solidity.Tests.GetterKernelSharing.scopedCheckedFallback
    withOptions (Elab.async.set · false) <|
      addDecl <| .thmDecl { name := checkedName, levelParams := [], type := ty, value := checked }
    for name in [validName, checkedName] do
      let axioms ← collectAxioms name
      unless axioms.all ([``propext, ``Classical.choice, ``Quot.sound].contains ·) do
        throwError "nonstandard axioms in {name}: {axioms}"
      logInfo m!"{name}: kernel checked, axioms={axioms}"
    logInfo "malformed scoped closer rejected; state restored; checked fallback passed within original deadline"


run_elab do
  let C := mkConst ``Empty
  let Γ := ctxE []
  for shared in [false, true] do
    let falseFormula := mkApp2 (mkConst ``Fml.ff) C Γ
    let g ← mkFreshExprSyntheticOpaqueMVar (mkApp2 (mkConst ``Fml.Valid) C falseFormula)
    let closed ← withOptions (·.setBool `sol.prove.sharedResidues shared) <|
      Decide.closeScoped g.mvarId! C falseFormula
    if closed || (← g.mvarId!.isAssigned) then throwError "false closer control was proved"
    -- Positive-polarity havoc is explicitly outside Fml.toLS's fragment.
    let unread := mkApp3 (mkConst ``Fml.havoc) C Γ (mkApp2 (mkConst ``Fml.tt) C Γ)
    let unsupported ← mkFreshExprSyntheticOpaqueMVar (mkApp2 (mkConst ``Fml.Valid) C unread)
    let refused ← try
        let _ ← withOptions (·.setBool `sol.prove.sharedResidues shared) <|
          Decide.closeScoped unsupported.mvarId! C unread
        pure false
      catch e => do
        let message ← e.toMessageData.toString
        pure (message.startsWith "sol_decide: the leaf is outside the fragment")
    unless refused && !(← unsupported.mvarId!.isAssigned) do
      throwError "closer fragment refusal changed"
  logInfo "closer false observation and fragment refusal unchanged in both policies"

local instance : InContract := ⟨Empty⟩

private def stageCount : CoreM Nat := do
  return ((← getEnv).constants.toList.filter fun (name, _) =>
    name.toString.startsWith "prefix_memory_stage").length

-- Staged controls create auxiliary declarations; check synchronously so Lean
-- does not restrict their names to an asynchronous theorem namespace.
set_option Elab.async false in
theorem prefixStagesChecked : ProvesC (C := Empty) .tt false [] .nil
    cdl!{ ∀ uint x; x == 0 → x == 1 → false } := by
  apply ProvesC.allIntro
  apply ProvesC.intro
  apply ProvesC.intro
  run_tac do
    let before ← stageCount
    withOptions (·.setBool `sol.prove.sharedResidues false) <| Budget.within 16384 do
      CallbackWalk.closePrefixFalse (← getMainGoal) 8 (some 0)
    unless before < (← stageCount) do
      throwError "staged prefix control fell back instead of checking its stages"
    replaceMainGoal []
#print axioms prefixStagesChecked

set_option Elab.async false in
theorem prefixStagesShared : ProvesC (C := Empty) .tt false [] .nil
    cdl!{ ∀ uint x; x == 0 → x == 1 → false } := by
  apply ProvesC.allIntro
  apply ProvesC.intro
  apply ProvesC.intro
  run_tac do
    let before ← stageCount
    withOptions (·.setBool `sol.prove.sharedResidues true) <| Budget.within 16384 do
      CallbackWalk.closePrefixFalse (← getMainGoal) 8 (some 0)
    unless before < (← stageCount) do
      throwError "staged prefix control fell back instead of checking its stages"
    replaceMainGoal []
#print axioms prefixStagesShared

run_elab do
  let C := mkConst ``Empty
  let Γ := ctxE []
  let H := mkApp2 (mkConst ``Hyps.nil) C Γ
  let c := mkApp2 (mkConst ``Fml.ff) C Γ
  let atom := mkAppN (mkConst ``Seq.refuteS) #[C, Γ, H, c]
  let truth := mkConst ``Bool.true
  let type ← mkEq atom truth
  let malformed := mkApp2 (mkConst ``id [0]) type (← mkEqRefl (mkConst ``Bool.false))
  let proof := mkAppN (mkConst ``Eq.trans [1])
    #[mkConst ``Bool, atom, truth, truth, malformed, ← mkEqRefl truth]
  let saved ← Term.saveState
  let context ← readThe Core.Context
  let deadline := context.initHeartbeats + context.maxHeartbeats
  let accepted ← try
      let _ ← Derive.kernelLemma type proof
      pure true
    catch _ => pure false
  if accepted then throwError "immediate atom gate accepted a corrupted intermediate equality"
  saved.restore
  let now ← IO.getNumHeartbeats
  let remaining := if context.maxHeartbeats == 0 then 0 else deadline - now
  if context.maxHeartbeats != 0 && remaining == 0 then throwError "atom control exhausted original budget"
  let checked ← withTheReader Core.Context
      (fun context => { context with initHeartbeats := now, maxHeartbeats := remaining }) do
    let checked ← Decide.trueLemma atom
    let _ ← Derive.kernelLemma type checked
    return checked
  let axioms ← collectAxioms checked.constName!
  unless axioms.all ([``propext,``Classical.choice,``Quot.sound].contains ·) do
    throwError "nonstandard atom fallback axioms"
  logInfo "immediate original atom gate rejected corrupted intermediate; bounded original-checker fallback passed"


run_elab do
  let rec fullTree : Nat → Expr
    | 0 => mkConst ``Bool.true
    | n + 1 => let child := fullTree n; mkApp child child
  let below := mkApp (fullTree 12) (fullTree 11)
  unless below.sizeWithoutSharing == 12287 do throwError "policy control size changed"
  if Frontend.testingShares below then throwError "small goal unexpectedly shared"
  unless Frontend.testingShares (mkMData {} below) do
    throwError "large goal did not select shared checking"
  if Frontend.testingShares (mkConst ``Bool.true) then throwError "atom unexpectedly shared"
  logInfo "testing strategy threshold controls passed: 12287 original, 12288 shared"



-- Reconstruct the production staged proof with its actual private lemmas.
-- Corrupt one exact reduction/terminal equality and require a kernel type
-- mismatch at the final original atom, rather than an auxiliary cache hit.
run_elab do
  Budget.within 16384 do
    let named (suffix : String) : MetaM Expr := do
      let candidates := (← getEnv).constants.toList.filter fun (name, _) =>
        name.toString.endsWith (".Solidity.CallbackWalk." ++ suffix)
      let [(name, _)] := candidates | throwError "expected one production stage lemma: {suffix}"
      return mkConst name
    let C := mkConst ``Empty
    let Γ := ctxE []
    let H := mkApp2 (mkConst ``Hyps.nil) C Γ
    let c := mkApp2 (mkConst ``Fml.ff) C Γ
    let hc := mkAppN (mkConst ``Hyps.pre) #[C, Γ, Γ, H, c]
    let ψ := mkAppN (mkConst ``Hyps.wrap) #[C, Γ, Γ, hc, c]
    let atom := mkAppN (mkConst ``Seq.refuteS) #[C, Γ, H, c]
    let truth := mkConst ``Bool.true
    let lfTy := mkApp (mkConst ``Decide.LFml) C
    let reduce := mkApp2 (← named "prefixReduction") C ψ
    let someL ← withTransparency .all <| whnf reduce
    unless someL.isAppOfArity ``Option.some 2 do throwError "tiny atom did not reduce"
    let l := someL.getArg! 1
    let form := mkApp2 (← named "prefixForm") C l
    let r ← withTransparency .all <| whnf form
    let mut previous := r
    let mut forms : Array Expr := #[]
    let mut stages : Array Expr := #[]
    for i in [:4] do
      let stage := mkAppN (← named "memoryStage") #[C, toExpr i, previous]
      let next ← withTransparency .all <| whnf stage
      stages := stages.push (mkApp2 (mkConst ``id [0]) (← mkEq stage next) (← mkEqRefl next))
      forms := forms.push next
      previous := next
    let terminal := mkApp2 (mkConst ``Decide.LFml.closeMem.closeTwice) C previous
    let annotate (type value : Expr) : Expr := mkApp2 (mkConst ``id [0]) type value
    let boolProof (b : Expr) : MetaM Expr := do
      return annotate (← mkEq b truth) (← mkEqRefl truth)
    let build (badReduction badTerminal : Bool) : MetaM Expr := do
      let reduceValue ← mkEqRefl (if badReduction then mkApp (mkConst ``Option.none [0]) lfTy else someL)
      let hReduce := annotate (← mkEq reduce someL) reduceValue
      let hForm := annotate (← mkEq form r) (← mkEqRefl r)
      let terminalValue ← mkEqRefl (if badTerminal then mkConst ``Bool.false else truth)
      let hTerminal := annotate (← mkEq terminal truth) terminalValue
      let hMemory := mkAppN (← named "memoryStages_checked")
        (#[C, r] ++ forms ++ stages ++ #[hTerminal])
      let hClose := mkAppN (← named "prefixClose_mem") #[C, ψ, r, hMemory]
      let hGuard ← boolProof (mkApp2 (mkConst ``Decide.LFml.refuteOk) C r)
      let hCheck := mkAppN (← named "prefixDecision_parts") #[C, ψ, r, hGuard, hClose]
      let hCore := mkAppN (← named "refuteCore_reduced") #[C, ψ, l, r, hReduce, hForm, hCheck]
      let hModal ← boolProof (mkApp3 (mkConst ``Fml.modalFree) C Γ ψ)
      return mkAppN (← named "refuteS_parts") #[C, Γ, H, c, hModal, hCore]
    let type ← mkEq atom truth
    for badReduction in [true, false] do
      let badName := if badReduction then `badAtomReduction else `badAtomTerminal
      if (← getEnv).contains badName then throwError "bad atom name already exists"
      let checkpoint ← saveState
      let proof ← build badReduction (!badReduction)
      let rejected ← try
          withOptions (Elab.async.set · false) <|
            addDecl <| .thmDecl { name := badName, levelParams := [], type, value := proof }
          pure false
        catch e => do
          let message ← e.toMessageData.toString
          unless (message.splitOn "type mismatch").length > 1 do throw e
          pure true
      checkpoint.restore
      unless rejected && !(← getEnv).contains badName do
        throwError "malformed production atom checkpoint escaped"
    let name := `Solidity.Tests.GetterKernelSharing.checkedStagedAtom
    withOptions (Elab.async.set · false) <|
      addDecl <| .thmDecl { name, levelParams := [], type, value := ← build false false }
    unless (← collectAxioms name).all ([``propext, ``Classical.choice, ``Quot.sound].contains ·) do
      throwError "staged atom uses nonstandard axioms"
    -- The original checker fallback is also checked within this same budget.
    let name := `Solidity.Tests.GetterKernelSharing.stagedAtomOriginalFallback
    withOptions (Elab.async.set · false) <|
      addDecl <| .thmDecl { name, levelParams := [], type, value := ← mkEqRefl truth }
    unless (← collectAxioms name).all ([``propext, ``Classical.choice, ``Quot.sound].contains ·) do
      throwError "original atom fallback uses nonstandard axioms"
    logInfo "production reduction/closeTwice corruption rejected at original atom; checked staged atom and original-budget fallback passed"
#print axioms checkedStagedAtom
#print axioms stagedAtomOriginalFallback
end Solidity.Tests.GetterKernelSharing
