import Solidity.Tools.LatexSolkey
import Solidity.Calculus.Elementary

/-! Checked refinement of strategy macro steps. This layer changes the actual
Fml pair, not the printed rule tag. It records a semantic proof of every new
pair and refuses to use a proof whose left side differs from the current line. -/
namespace Solidity.Elementary
open Lean Elab Command Meta
open Solidity.Latex

structure PendingCapture where
  phase : Nat
  kind : Nat := 0
  source : Expr := default
  it : Expr
  recv : Expr
  index : Expr
  receiverName : Expr
  indexName : Expr
  deriving Inhabited

partial def normalizeSpine (f : Expr) : MetaM Expr := do
  if Chain.isPost f then return f
  let e ← withTransparency .all (whnf (← instantiateMVars f))
  if e.isAppOf ``Fml.upd || e.isAppOf ``Fml.bind || e.isAppOf ``Fml.all then
    let a := e.getAppArgs
    return mkAppN e.getAppFn (a.set! (a.size - 1) (← normalizeSpine a.back!))
  return e

/-- Obtain the exact successor from a semantic proof, unifying its complete
before formula (including scopes and updates) with the current formula. -/
def successor (before proof : Expr) : MetaM Expr := do
  let ty ← whnfR (← inferType proof)
  unless ty.isAppOf ``Fml.Leads do throwError "expected Fml.Leads proof"
  let a := ty.getAppArgs
  unless ← isDefEq a[2]! before do throwError "elementary proof has a different before formula"
  return ← normalizeSpine a[3]!

/-- Lift a single modal transformation through the enclosing formula spine. -/
partial def inSpine (f : Expr → MetaM (Option Expr)) (before : Expr) : MetaM (Option Expr) := do
  let e ← whnfR before
  let a := e.getAppArgs
  if e.isAppOf ``Fml.modal then return ← f e
  if e.isAppOf ``Fml.upd then
    if let some h ← inSpine f a.back! then
      let h ← mkAppM ``underUpdate #[a[3]!, a[4]!, h]
      let _ ← successor before h
      return some h
  if e.isAppOf ``Fml.bind then
    if let some h ← inSpine f a.back! then
      let h ← mkAppM ``underBind #[a[2]!, a[3]!, a[4]!, h]
      let _ ← successor before h
      return some h
  if e.isAppOf ``Fml.all then
    if let some h ← inSpine f a.back! then
      let h ← mkAppM ``underAll #[a[2]!, a[3]!, h]
      let _ ← successor before h
      return some h
  if e.isAppOf ``Fml.imp then
    if let some h ← inSpine f a.back! then
      return some (← mkAppM ``underImp #[a[a.size - 2]!, h])
  if e.isAppOf ``Fml.and then
    -- Match the strategy's first active branch, even when `f` does not
    -- recognize its modal head; never jump ahead into the other branch.
    let left := a[a.size - 2]!
    let active ← Chain.runChain left
    if !active.lines.isEmpty || active.modalStop then
      if let some h ← inSpine f left then
        return some (← mkAppM ``underAndLeft #[a.back!, h])
    else if let some h ← inSpine f a.back! then
      return some (← mkAppM ``underAndRight #[left, h])
  if e.isAppOf ``Fml.havoc then
    if let some h ← inSpine f a.back! then
      return some (← mkAppM ``underHavoc #[h])
  if e.isAppOf ``Fml.anon then
    if let some h ← inSpine f a.back! then
      return some (← mkAppM ``underAnon #[a[a.size - 2]!, h])
  return none

/-- Count state-write elements without unfolding contract metadata or RHSs. -/
partial def stateWriteCounts (update : Expr) : MetaM (Nat × Nat) := do
  let e ← withTransparency .all (whnf (← instantiateMVars update))
  let a := e.getAppArgs
  if e.isAppOf ``Upd.nil then return (0, 0)
  if e.isAppOf ``Upd.snoc then
    let (st, mem) ← stateWriteCounts a[a.size - 2]!
    let element ← withTransparency .all (whnf a.back!)
    return (st + if element.isAppOf ``UpdElem.storage then 1 else 0,
            mem + if element.isAppOf ``UpdElem.memory then 1 else 0)
  if e.isAppOf ``Upd.decl then return ← stateWriteCounts a[a.size - 3]!
  if e.isAppOf ``Upd.pop || e.isAppOf ``Upd.drop then
    return ← stateWriteCounts a[a.size - 2]!
  throwError "unknown update constructor while counting storage writes: {e.getAppFn}"

/-- Refine a planned endpoint through the intrinsic raw merge and dropSh.
Both intermediate Fmls receive their own semantic proofs. This includes the
unchanged enclosing updates and hidden binders in their before formulas. -/
partial def rawStorageRefinement (before goal : Expr) : MetaM (Option (Expr × Expr)) := do
  let e ← withTransparency .all (whnf (← instantiateMVars before))
  let a := e.getAppArgs
  if e.isAppOf ``Fml.upd then
    let child ← withTransparency .all (whnf a.back!)
    let mut rawProofs : Array Expr := #[]
    if child.isAppOf ``Fml.bind then
      let bindings := child.getAppArgs
      let body ← withTransparency .all (whnf bindings.back!)
      if body.isAppOf ``Fml.upd then
        let b := body.getAppArgs
        if ← isDefEq a[3]! b[3]! then
          let absorbed ← mkAppM ``absorbForRaw #[b[4]!, bindings[3]!]
          let absorbed ← withTransparency .all (whnf absorbed)
          if absorbed.isAppOf ``Option.some then
            let V := absorbed.getAppArgs.back!
            let merged ← mkAppM ``Upd.mergeK? #[a[4]!, V]
            let merged ← withTransparency .all (whnf merged)
            if merged.isAppOf ``Option.some then
              let h ← mkAppM ``rawSingleAbsorbLeads #[a[3]!, bindings[2]!, a[4]!, bindings[3]!, b[4]!, V, merged.getAppArgs.back!, b.back!, ← mkEqRefl absorbed, ← mkEqRefl merged]
              rawProofs := rawProofs.push h
    let absorbed ← mkAppM ``Fml.absorbBinds #[a.back!]
    let child ← withTransparency .all (whnf absorbed)
    if child.isAppOf ``Fml.upd then
      let b := child.getAppArgs
      if ← isDefEq a[3]! b[3]! then
        let result ← mkAppM ``Upd.mergeK? #[a[4]!, b[4]!]
        let value ← withTransparency .all (whnf result)
        if value.isAppOf ``Option.some then
          let h ← mkAppM ``rawAbsorbAllLeads #[a[3]!, a[4]!, a.back!, b[4]!, value.getAppArgs.back!, b.back!, ← mkEqRefl child, ← mkEqRefl value]
          rawProofs := rawProofs.push h
    for h₁ in rawProofs do
      let intermediate ← successor before h₁
      let raw ← withTransparency .all (whnf intermediate)
      let args := raw.getAppArgs
      let W := args[4]!
      let h₂ ← mkAppM ``dropStateLeads #[args[3]!, W, args.back!]
      let after ← successor intermediate h₂
      if ← isDefEq after goal then
        let dropped := (← withTransparency .all (whnf after)).getAppArgs[4]!
        let oldCounts ← stateWriteCounts W
        let newCounts ← stateWriteCounts dropped
        if oldCounts.1 == newCounts.1 + 1 && oldCounts.2 == newCounts.2 then
          return some (h₁, h₂)
  let g ← withTransparency .all (whnf (← instantiateMVars goal))
  if e.isAppOf ``Fml.upd then
    let child ← withTransparency .all (whnf a.back!)
    if child.isAppOf ``Fml.bind && g.isAppOf ``Fml.bind then
      let b := child.getAppArgs
      let z := g.getAppArgs
      if (← isDefEq b[2]! z[2]!) && (← isDefEq b[3]! z[3]!) && (← isDefEq b[4]! z[4]!) then
        let allowed ← mkAppM ``liftAllowedForRaw #[a[4]!, b[4]!]
        let allowed ← withTransparency .all (whnf allowed)
        if allowed.isAppOf ``Bool.true then
          let lifted ← mkAppM ``liftForRaw #[a[4]!, b[4]!]
          let lifted ← withTransparency .all (whnf lifted)
          if lifted.isAppOf ``Option.some then
            let U := lifted.getAppArgs.back!
            let inner ← mkAppM ``Fml.upd #[a[3]!, U, b.back!]
            if let some (h₁, h₂) ← rawStorageRefinement inner z.back! then
              let intermediate ← successor inner h₁
              let h₁ ← mkAppM ``rawUnderLiftLeads #[a[3]!, b[2]!, a[4]!, b[4]!, U, b[3]!, b.back!, intermediate, ← mkEqRefl lifted, ← mkEqRefl allowed, h₁]
              let intermediate ← successor before h₁
              let h₂ ← mkAppM ``underBind #[b[2]!, b[3]!, b[4]!, h₂]
              unless ← isDefEq (← successor intermediate h₂) goal do
                throwError "lifted raw storage refinement changed its endpoint"
              return some (h₁, h₂)
  if e.getAppFn != g.getAppFn then return none
  let b := g.getAppArgs
  if a.size != b.size || a.isEmpty then return none
  if e.isAppOf ``Fml.and && (← isDefEq a.back! b.back!) then
    if let some (h₁, h₂) ← rawStorageRefinement a[a.size - 2]! b[b.size - 2]! then
      let h₁ ← mkAppM ``underAndLeft #[a.back!, h₁]
      let intermediate ← successor before h₁
      let h₂ ← mkAppM ``underAndLeft #[a.back!, h₂]
      unless ← isDefEq (← successor intermediate h₂) goal do
        throwError "storage refinement changed its enclosing left branch"
      return some (h₁, h₂)
  unless ← isDefEq (mkAppN e.getAppFn a.pop) (mkAppN g.getAppFn b.pop) do return none
  if e.isAppOf ``Fml.upd || e.isAppOf ``Fml.bind || e.isAppOf ``Fml.all ||
      e.isAppOf ``Fml.imp || e.isAppOf ``Fml.and ||
      e.isAppOf ``Fml.havoc || e.isAppOf ``Fml.anon then
    if let some (h₁, h₂) ← rawStorageRefinement a.back! b.back! then
      let liftOne : Expr → MetaM Expr := fun h => do
        if e.isAppOf ``Fml.upd then return ← mkAppM ``underUpdate #[a[3]!, a[4]!, h]
        if e.isAppOf ``Fml.bind then return ← mkAppM ``underBind #[a[2]!, a[3]!, a[4]!, h]
        if e.isAppOf ``Fml.imp then return ← mkAppM ``underImp #[a[a.size - 2]!, h]
        if e.isAppOf ``Fml.and then return ← mkAppM ``underAndRight #[a[a.size - 2]!, h]
        if e.isAppOf ``Fml.havoc then return ← mkAppM ``underHavoc #[h]
        if e.isAppOf ``Fml.anon then return ← mkAppM ``underAnon #[a[a.size - 2]!, h]
        mkAppM ``underAll #[a[2]!, a[3]!, h]
      let h₁ ← liftOne h₁
      let intermediate ← successor before h₁
      let h₂ ← liftOne h₂
      unless ← isDefEq (← successor intermediate h₂) goal do
        throwError "storage refinement changed its planned enclosing formula"
      return some (h₁, h₂)
  return none

/-- Count update nodes in the actual formula syntax, without unfolding the
contract or looking inside program metadata/postcondition variables. -/
partial def updateNodes (f : Expr) : MetaM Nat := do
  let e ← normalizeSpine f
  let a := e.getAppArgs
  if e.isAppOf ``Fml.upd then return 1 + (← updateNodes a.back!)
  if e.isAppOf ``Fml.bind || e.isAppOf ``Fml.all || e.isAppOf ``Fml.havoc || e.isAppOf ``Fml.anon then
    return ← updateNodes a.back!
  if e.isAppOf ``Fml.and || e.isAppOf ``Fml.imp then
    return (← updateNodes a[a.size - 2]!) + (← updateNodes a.back!)
  return 0

partial def mergeApplications (rw : Expr) : Array Expr :=
  if rw.isAppOf ``FmlRw.mergePast || rw.isAppOf ``FmlRw.stateMerge then #[rw]
  else rw.getAppArgs.foldl (fun acc arg => acc ++ mergeApplications arg) #[]

def printedUpdateNodes (tex : String) : Nat :=
  ((tex.splitOn "\\{").drop 1).countP fun part =>
    decide ((((part.splitOn "\\}").headD "").splitOn "\\upd").length > 1)

/-- Evaluate one supplied rewrite through the supported quote/splice API.
The evaluator only discovers the candidate; PastStep.leads then constructs
its equality proof and the complete trace is checked by the kernel. -/
def candidateFor (before rw : Expr) : MetaM (Option Chain.RwCand) := do
  let { C, Γ, name := nm, sp, fml, modality := mode } ← Chain.prepare before
  let fmlTy := mkApp2 (mkConst ``Fml) C Γ
  let fn ← whnf (mkAppN (mkConst ``FmlRw.apply) #[C, rw, Γ])
  let list ← mkListLit (← mkArrow fmlTy (mkApp (mkConst ``Option [0]) fmlTy)) [fn]
  let ty := mkApp (mkConst ``List [0]) (mkApp (mkConst ``Option [0])
    (mkApp2 (mkConst ``Prod [0, 0]) (mkConst ``Expr) (mkConst ``Expr)))
  let eval (φ : Expr) : MetaM (Option (Expr × Expr)) := do
    let rows ← unsafe Chain.evalQuoted (List (Option (Expr × Expr))) ty
      (mkAppN (mkConst ``Fml.rwResultsQ) #[C, quoteConstName nm, Γ, φ, list])
    return rows.headD none
  match mode with
  | none =>
    let some (f, key) ← eval fml | return none
    return some { rw, fml := Chain.unpunch sp f, keys := #[key] }
  | some m =>
    let some (fd, kd) ← eval (fml.replaceFVar m (mkConst ``Modality.diamond)) | return none
    let some (fb, kb) ← eval (fml.replaceFVar m (mkConst ``Modality.box)) | return none
    let some joined := Chain.mergeModality m fd fb | return none
    return some { rw, fml := Chain.unpunch sp joined, keys := #[kd, kb] }

def replaceMerge (rw old replacement : Expr) : Expr :=
  rw.replace fun e => if e == old then some replacement else none

/-- Expand the same successful long merge into its own one-pair operations.
Keeping its reorder mode and positions avoids a greedy plan that can strand
heap-dependent reference updates in two unmergeable blocks. -/
def elementaryMerges (first : Expr) (maxPairs : Nat := 400) : TermElabM (Array Step × Expr × Expr × Nat) := do
  if (first.find? (·.isAppOf ``Fml.modal)).isSome then
    throwError "program is still open before elementary update composition"
  let mut current := first
  let mut proof ← mkAppM ``Fml.Leads.self #[first]
  let mut steps : Array Step := #[]
  let mut administrative := 0
  -- Probe for completion before charging another plan to the budget.
  for used in [:maxPairs + 1] do
    let (_, candidates, _) ← Chain.scopedRwCands current (.table `sequentialToParallel) (past := true)
    let mut chosenPlan : Option Chain.RwCand := none
    for candidate in candidates do
      let calls := mergeApplications candidate.rw
      if calls.size != 1 then continue
      let oldCount ← updateNodes current
      let newCount ← updateNodes candidate.fml
      if newCount < oldCount then
        chosenPlan := some candidate
        break
    let some plan := chosenPlan | return (steps, proof, current, administrative)
    if used == maxPairs then
      throwError "elementary update composition exceeded {maxPairs} plans"
    let call := (mergeApplications plan.rw)[0]!
    let (C, _) ← Chain.lineType current
    let mut rewrites : Array Expr := #[]
    if call.isAppOf ``FmlRw.mergePast then
      let args := call.getAppArgs
      let k ← Chain.kernelNat args[1]!
      let n ← Chain.kernelNat args[2]!
      let mut chosenMode : Option Bool := none
      for mode in [false, true] do
        let replacement := mkApp4 (mkConst ``mergeRunMode) C (toExpr mode) (toExpr k) (toExpr n)
        if let some result ← candidateFor current (replaceMerge plan.rw call replacement) then
          if ← isDefEq result.fml plan.fml then
            chosenMode := some mode
            break
      let some mode := chosenMode | throwError "long merge has no uniform verified reorder mode"
      for offset in (List.range (n + 1)).reverse do
        let replacement := mkApp3 (mkConst ``mergePairMode) C (toExpr mode) (toExpr (k + offset))
        rewrites := rewrites.push (replaceMerge plan.rw call replacement)
    else
      rewrites := #[plan.rw]
    for rw in rewrites do
      let some candidate ← candidateFor current rw | throwError "a planned elementary update pair does not apply"
      let beforeCount ← updateNodes current
      let afterCount ← updateNodes candidate.fml
      unless afterCount + 1 == beforeCount do
        throwError "one planned native merge contracted more than one update pair"
      if let some (rawProof, shadowProof) ← rawStorageRefinement current candidate.fml then
        let intermediate ← successor current rawProof
        let checkedAfter ← successor intermediate shadowProof
        unless ← isDefEq checkedAfter candidate.fml do
          throwError "storage-shadow proof changed the planned endpoint"
        -- Keep the quoted candidate's constructor representation. A raw
        -- dropSh application is definitionally equal but can hide update
        -- slots from the subsequent read-rule discriminator.
        let after := candidate.fml
        let beforeTex ← exprLatex current { backend := .macros, width := 100 }
        let rawTex ← exprLatex intermediate { backend := .macros, width := 100 }
        let afterTex ← exprLatex after { backend := .macros, width := 100 }
        unless printedUpdateNodes rawTex + 1 == printedUpdateNodes beforeTex &&
            printedUpdateNodes afterTex == printedUpdateNodes rawTex do
          throwError "intrinsic storage refinement changed the wrong update blocks"
        steps := steps.push { rule := "sequentialToParallel2", line := intermediate }
        steps := steps.push { rule := "shadowedStorageUpdate", line := after }
        proof ← mkAppM ``Fml.Leads.comp #[proof, rawProof]
        proof ← mkAppM ``Fml.Leads.comp #[proof, shadowProof]
        current := after
        continue
      let step : Chain.PastStep := { name := "sequentialToParallel2", fml := candidate.fml, keys := candidate.keys, rw }
      let h ← step.leads current
      let after ← successor current h
      let beforeTex ← exprLatex current { backend := .macros, width := 100 }
      let afterTex ← exprLatex after { backend := .macros, width := 100 }
      if beforeTex != afterTex then
        unless printedUpdateNodes afterTex + 1 == printedUpdateNodes beforeTex do
          throwError "one native merge changed the printed formula by more than one update pair"
        steps := steps.push { rule := step.name, line := after, rw? := some step.rw }
      else
        -- Only byte-identical rendered formulas are omitted. Every native
        -- scope bookkeeping pair remains in the composed kernel proof.
        administrative := administrative + 1
      proof ← mkAppM ``Fml.Leads.comp #[proof, h]
      current := after
    unless ← isDefEq current plan.fml do
      throwError "elementary pairs did not reach the original merge endpoint"
  throwError "elementary update composition exceeded {maxPairs} plans"

/-- One indexed-value capture at a time, interleaved with ordinary execution
of the introduced declarations. Remaining strategy rules are left unchanged
and therefore still require the before/after audit. -/
def elementaryTrace (first : Expr) (maxSteps : Nat := 800) : TermElabM (Array Step × Expr) := do
  let mut current := first
  let mut proof ← mkAppM ``Fml.Leads.self #[first]
  let mut steps : Array Step := #[]
  let mut pending : Array PendingCapture := #[]
  for _ in [:maxSteps] do
    let run ← withCurrHeartbeats (Chain.runChain current)
    let some next := run.lines.head? | break
    let label := ((← Chain.labelOfFocus? next.focus).map (·.1.toString)).getD ""
    let mut applied := false
    for j in [:pending.size] do
      let p := pending[j]!
      let saved ← saveState
      try
        let some h ← inSpine (fun modal => do
          let a := modal.getAppArgs
          let P ← whnfR a[5]!
          unless P.isAppOf ``Prog.cons do return none
          let sa ← whnfR P.getAppArgs[P.getAppArgs.size - 2]!
          unless sa.isAppOf ``Stmt.assign || sa.isAppOf ``Stmt.assignMem do return none
          let ω := P.getAppArgs.back!
          let hm ← if p.kind == 3 then mkAppM ``MPath.mapFree #[p.recv] else pure p.recv
          let args := if p.kind == 4 then #[a[4]!, p.recv, p.source, p.index, p.it, p.receiverName, ω, a[6]!, a[7]!]
            else if p.kind == 1 || p.kind == 2 then #[a[4]!, p.recv, p.index, p.it, p.receiverName, ω, a[6]!, a[7]!]
            else if p.phase == 1 then #[a[4]!, p.it, p.recv, p.index, p.receiverName, ω, a[6]!, a[7]!]
            else if p.kind == 3 then #[a[4]!, p.it, hm, p.index, p.indexName, ω, a[6]!, a[7]!]
            else #[a[4]!, p.it, p.index, p.indexName, ω, a[6]!, a[7]!]
          let h ← mkAppM (if p.kind == 4 then ``memoryRefFieldReceiverLeads else if p.kind == 2 then ``memoryFieldReceiverLeads else if p.kind == 1 then ``fieldReceiverLeads else if p.kind == 3 then (if p.phase == 1 then ``memoryReceiverLeads else ``memoryIndexLeads) else if p.phase == 1 then ``receiverLeads else ``indexLeads) args
          let _ ← successor modal h
          return some h) current | throwError "capture not at current focus"
        let after ← successor current h
        let checkedComposition ← mkAppM ``Fml.Leads.comp #[proof, h]
        current := after
        proof := checkedComposition
        steps := steps.push { rule := if p.kind == 4 then "captureMemoryRefReceiver" else if p.kind == 3 then (if p.phase == 1 then "captureMemoryReceiver" else "captureMemoryIndex") else if p.kind == 2 then "captureMemoryFieldReceiver" else if p.kind == 1 then "captureStorageFieldReceiver" else if p.phase == 1 then "captureStorageReceiver" else "captureStorageIndex", line := current }
        if (p.kind == 0 || p.kind == 3) && p.phase == 1 then pending := pending.set! j { p with phase := 2 }
        else pending := pending.extract 0 j ++ pending.extract (j + 1) pending.size
        applied := true
        break
      catch _ => saved.restore
    if applied then continue
    if label == "storageIndexWriteCaptureAllComplexRecv" || label == "storageIndexWriteCaptureAllNonSimpleIndex" || label == "storageFieldWrite_unfold_leftFst" || label == "memoryFieldWrite_unfold_leftFst" || label == "memoryIndexWriteCaptureAllComplexRecv" || label == "memoryIndexWriteCaptureAllNonSimpleIndex" then
      unless pending.isEmpty do throwError "a pending elementary capture failed at the next write"
      let origin ← IO.mkRef (none : Option PendingCapture)
      let some h ← inSpine (fun modal => do
        let a := modal.getAppArgs
        let P ← whnfR a[5]!
        let s ← whnfR P.getAppArgs[P.getAppArgs.size - 2]!
        let sa := s.getAppArgs
        let loc ← whnfR sa[sa.size - 2]!
        let rhs ← whnfR sa.back!
        unless (loc.isAppOf ``Loc.index || loc.isAppOf ``Loc.field || loc.isAppOf ``MLoc.field || loc.isAppOf ``MLoc.index) && (rhs.isAppOf ``Src.val || rhs.isAppOf ``MSrc.val || rhs.isAppOf ``MSrc.ref) do return none
        let la := loc.getAppArgs
        let kind := if loc.isAppOf ``MLoc.field && rhs.isAppOf ``MSrc.ref then 4 else if loc.isAppOf ``MLoc.index then 3 else if loc.isAppOf ``MLoc.field then 2 else if loc.isAppOf ``Loc.field then 1 else 0
        let it := if kind == 1 || kind == 2 || kind == 4 then la.back! else la[la.size - 3]!
        let b := if kind == 1 || kind == 2 || kind == 4 then la[la.size - 3]! else la[la.size - 2]!
        let i := if kind == 1 || kind == 2 || kind == 4 then la[la.size - 2]! else la.back!
        let e := rhs.getAppArgs.back!
        let k := toExpr next.fresh
        let x ← mkAppM (if kind == 4 then ``fmv else ``fse) #[k]
        let receiverName ← mkAppM (if kind >= 2 then ``fmv else ``fsp) #[if kind == 4 then toExpr (next.fresh + 1) else k]
        let indexName ← mkAppM ``fie #[k]
        origin.set (some { phase := 1, kind := kind, source := e, it := it, recv := b, index := i, receiverName := receiverName, indexName := indexName })
        let h ← if kind == 4 then
          mkAppM ``memoryReferenceLeads #[a[4]!, loc, e, x, P.getAppArgs.back!, a[6]!, a[7]!]
        else do
          let hole ← mkAppM (if kind >= 2 then ``VHole.mem else ``VHole.store) #[loc]
          mkAppM ``captureValue #[a[4]!, hole, e, x, P.getAppArgs.back!, a[6]!, a[7]!]
        let _ ← successor modal h
        return some h) current | throwError "could not refine indexed-value capture"
      let after ← successor current h
      let checkedComposition ← mkAppM ``Fml.Leads.comp #[proof, h]
      current := after
      proof := checkedComposition
      let captureKind := (← origin.get).get!.kind
      steps := steps.push { rule := if captureKind == 4 then "captureMemoryReference" else if captureKind == 3 then "captureMemoryValue" else if captureKind == 2 then "captureMemoryFieldValue" else if captureKind == 1 then "captureStorageFieldValue" else "captureValue", line := current }
      pending := pending.push (← origin.get).get!
    else
      let h ← mkAppM ``Fml.Steps.sound #[← Chain.stepsProof run.splice current [next]]
      let _ ← successor current h
      proof ← mkAppM ``Fml.Leads.comp #[proof, h]
      current := next.fml
      steps := steps.push { rule := label, line := current }
  unless pending.isEmpty do throwError "unfinished elementary captures: {pending.size}"
  let remaining ← withCurrHeartbeats (Chain.runChain current)
  if !remaining.lines.isEmpty then
    throwError "elementary program trace exceeded {maxSteps} steps"
  if remaining.modalStop then
    throwError "{Chain.modalStopNote remaining}"
  return (steps, proof)
end Solidity.Elementary
