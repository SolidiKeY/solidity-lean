import Solidity.TestSuite.MemoryLoopReplay.Discover09
open scoped Solidity.Scoped
-- A real fully discovered checkpoint is not yet an assembled proof.
resume_memory_replay Solkey.TestSuite.returnLeavesNestedLoops.problem
example : Solidity.Proves Solkey.TestSuite .all [] .nil .tt := by
  fail_if_success finish_memory_replay
  exact .closeTrue rfl

-- Nonempty residual leaves have no replay rule in this helper.
resume_memory_replay Solkey.TestSuite.returnLeavesNestedLoops.problem
run_elab do
  let some j ← Solidity.Seq.MemoryReplay.job.get | throwError "missing test checkpoint"
  let hints := j.hints.set! 0 {j.hints[0]! with residual := true}
  let rejected ← Lean.tryCatchRuntimeEx (do
    let _ ← Solidity.Seq.MemoryReplay.expected {j with hints} 0
    pure false) (fun _ => pure true)
  unless rejected do throwError "residual-leaf proposal incorrectly accepted"
  Solidity.Seq.MemoryReplay.job.set none


open Lean Meta Solidity Solidity.Seq Solidity.Seq.MemoryReplay

-- Only genuine kernel type mismatches count as negative proof controls.
-- Heartbeat, memory, recursion or interruption errors propagate as failures.
private def kernelTypingRefusal (action : MetaM Unit) : MetaM Bool := withOptions (fun o => o.setBool `pp.raw true) do
  try
    action
    return false
  catch e =>
    let text ← e.toMessageData.toString
    if text.startsWith "(kernel)" && (text.splitOn "type mismatch").length>1 then return true
    throw e

run_elab do
  let z := toExpr (0 : Nat)
  let o := toExpr (1 : Nat)
  let cs : Array LayerCandidate := #[
    ⟨mkConst ``True, mkConst ``True.intro⟩,
    ⟨← mkEq z z, ← mkEqRefl z⟩,
    ⟨← mkEq o o, ← mkEqRefl o⟩]
  let ps ← checkLayerConjunction cs
  unless ps.size==3 do throwError "wrong component count"
  for i in [0:3] do
    let _ ← Derive.kernelLemma cs[i]!.type ps[i]!
    pure ()
  for i in [0:3] do
    let saved ← getEnv
    let bad := cs.set! i ⟨mkConst ``False,mkConst ``True.intro⟩
    let rejected ← kernelTypingRefusal do
      let _ ← checkLayerConjunction bad
      pure ()
    setEnv saved
    unless rejected do throwError "false batch component {i} accepted"
  requireKernelChecking false
  let rejected ← Lean.tryCatchRuntimeEx
    (do requireKernelChecking true; pure false) (fun _ => pure true)
  unless rejected do throwError "disabled-kernel preflight accepted"
  logInfo "checked distinct components, false first/middle/last, and preflight refusal"

-- A wrong reached fresh literal must fail the production save transaction.
resume_memory_replay Solkey.TestSuite.returnLeavesNestedLoops.problem
run_elab do
  let some base ← job.get | throwError "missing checkpoint"
  let originalInputs ← base.inputs.get
  let hints := base.hints.map fun h => {h with fresh := h.fresh+1}
  let mut selected := false
  -- Recorded by the actual default-budget discovery: the first literalized node.
  for id in [973] do
    unless selected do
      let env ← getEnv
      pendingLayers.set #[]
      let initial := hints[id]!.children.foldl (fun xs child => xs.set! child none) originalInputs
      let inputs ← IO.mkRef initial
      let j := {base with hints,inputs}
      let _ ← discover j id
      let candidates ← pendingLayers.get
      let used := candidates.any fun q => (q.2.value.find? fun e =>
        e.isAppOf ``Solidity.Seq.memoryReplayModalConsAt && e.getAppNumArgs==22 && e.getAppArgs[19]! == toExpr hints[id]!.fresh).isSome
      if used then
        selected := true
        job.set (some j)
        let count := (snapshots.getState (← getEnv)).size
        let rejected ← kernelTypingRefusal saveCheckpoint
        unless rejected do throwError "wrong reached fresh literal accepted"
        unless (snapshots.getState (← getEnv)).size==count do
          throwError "failed save appended checkpoint"
        unless (← job.get).isNone && (← pendingLayers.get).isEmpty do
          throwError "failed save retained candidate state"
      setEnv env
      pendingLayers.set #[]
      aliasCache.set {}
      job.set none
  unless selected do throwError "fresh refusal never reached literalized step"
  logInfo "wrong reached fresh literal rejected; production save rolled back"


-- The same terminal result must NOT hide incorrect quoted inputs.
private def rejectFlatHint (formula : Bool) : MetaM Unit := do
  let some base ← job.get | throwError "missing tiny job"
  unless base.hints.size==1 do throwError "not a one-node control"
  let h := base.hints[0]!
  unless h.n>0 do throwError "unused zero-depth hint"
  let wrong := if formula then
      {h with formula := Fml.quote (C := Solkey.TestSuite) base.C (.not (.not (.tt : Fml Solkey.TestSuite [])))}
    else {h with inputK := h.inputK+1}
  let j := {base with hints := base.hints.set! 0 wrong}
  let children ← discover j 0
  unless children.isEmpty && (← pendingLayers.get).size==1 do
    throwError "tampered hint did not reach a pending kernel equation"
  job.set (some {j with pending := []})
  let count := (snapshots.getState (← getEnv)).size
  let rejected ← kernelTypingRefusal saveCheckpoint
  unless rejected do throwError "wrong flat hint accepted"
  unless (snapshots.getState (← getEnv)).size==count do throwError "failed save published checkpoint"
  unless (← job.get).isNone && (← pendingLayers.get).isEmpty do throwError "failed save retained candidate"
  logInfo "wrong same-result quoted input rejected by production kernel/save transaction"

prepare_memory_replay (.tt : Solidity.Fml Solkey.TestSuite [])
run_elab rejectFlatHint true
prepare_memory_replay (.tt : Solidity.Fml Solkey.TestSuite [])
run_elab rejectFlatHint false

-- Untampered quotation traverses the same save/resume/assembly path.
prepare_memory_replay (.tt : Solidity.Fml Solkey.TestSuite [])
discover_memory_replay
save_memory_replay
resume_memory_replay (.tt : Solidity.Fml Solkey.TestSuite [])
assemble_memory_replay
save_memory_replay
resume_memory_replay (.tt : Solidity.Fml Solkey.TestSuite [])
example : Solidity.Proves Solkey.TestSuite .all [] .nil .tt := by
  finish_memory_replay


private def largeCondition : Nat → Fml Solkey.TestSuite []
  | 0 => .tt
  | n+1 => .and (largeCondition n) (largeCondition n)
example : (largeCondition 9).tmSize = 1023 := rfl
example : (Hyps.nil (C := Solkey.TestSuite) (Γ₀ := [])).rigid (largeCondition 9) = none := rfl
example : memoryReplayRigidNil Solkey.TestSuite (largeCondition 9) = none := rfl

private def largeUpdate : Nat → Upd Solkey.TestSuite [] []
  | 0 => .nil
  | n+1 => .snoc (largeUpdate n) (.storage (.app0 .storage))
private theorem largeUpdate_size (n : Nat) : (largeUpdate n).tmSize = 2*n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change (largeUpdate n).tmSize + 2 = 2*(n+1)
      rw [ih]
      omega
example : (largeUpdate 257).tmSize = 514 := by rw [largeUpdate_size]
private theorem oversizedUpdateRefused {C : Contract} {Γ Δ : Ctx} (H : Hyps C [] Γ)
    (U : Upd C Γ Δ) (c : Fml C Δ) (h : decide (U.tmSize ≤ Hyps.rigidSize) = false) :
    (H.upd .box U).rigid c = none := by
  change (cond (decide (c.tmSize ≤ Hyps.rigidSize) && decide (U.tmSize ≤ Hyps.rigidSize)) _ none) = none
  rw [h, Bool.and_false]
  rfl
example : ((Hyps.nil (C := Solkey.TestSuite) (Γ₀ := [])).upd .box (largeUpdate 257)).rigid .tt = none :=
  oversizedUpdateRefused .nil (largeUpdate 257) .tt (by rw [largeUpdate_size]; rfl)

run_elab do
  let C := mkConst ``Solkey.TestSuite
  let Γ := mkApp (mkConst ``List.nil [0]) (mkConst ``LTy)
  let H ← Lean.Elab.Term.elabTerm
    (← `(((Solidity.Hyps.nil (C := Solkey.TestSuite) (Γ₀ := [])).upd .box (largeUpdate 257)))) none
  let H ← instantiateMVars H
  let env ← getEnv
  let rejected ← kernelTypingRefusal do
    let _ ← checkedRigidFunction C Γ H
    pure ()
  setEnv env
  unless rejected do throwError "oversized update accepted by function certificate"
  let unsupported ← Lean.Elab.Term.elabTerm
    (← `((Solidity.Hyps.nil (C := Solkey.TestSuite) (Γ₀ := [])).havoc)) none
  let unsupported ← instantiateMVars unsupported
  let rejected ← try
    let _ ← checkedRigidFunction C Γ unsupported
    pure false
   catch e =>
    let text ← e.toMessageData.toString
    if text.startsWith "memory replay: unsupported rigid function prefix" then pure true else throw e
  unless rejected do throwError "unsupported rigid function accepted"
  logInfo "original condition/update caps and named unsupported-prefix refusal preserved"


private def rejectSelectedGuard (index : Nat) (corruptResult : Bool := false) : MetaM Unit := do
  let some base ← job.get | throwError "missing original checkpoint"
  let mut selected := none
  for offset in [:base.hints.size] do
    let id := base.hints.size-1-offset
    if selected.isNone && base.hints[id]!.guards.size>index then selected := some id
  let some id := selected | throwError "guard control never reached requested branch"
  let h := base.hints[id]!
  if index==1 then
    unless h.guards.size==2 && !h.guards[0]! do throwError "second guard lacks original false prefix"
  let wrong ← if corruptResult then do
      unless (h.guardHints[0]?.join).isSome do throwError "corrupt-second control did not enter paired path"
      let some (q,core) := h.guardHints[index]?.join | throwError "missing original quoted result"
      let nilCtx := mkApp (mkConst ``List.nil [0]) (mkConst ``LTy)
      let bad := mkAppN (mkConst ``Fml.not) #[base.C,nilCtx,q]
      pure {h with guardHints := h.guardHints.set! index (some (bad,core))}
    else pure {h with guards := h.guards.set! index (!h.guards[index]!)}
  let inputs ← IO.mkRef (h.children.foldl (fun xs child => xs.set! child none) (← base.inputs.get))
  let j := {base with hints := base.hints.set! id wrong, inputs, pending := [id]}
  job.set (some j)
  let count := (snapshots.getState (← getEnv)).size
  let rejected ← kernelTypingRefusal discoverNext
  unless rejected do throwError "wrong selected split guard {index} accepted"
  unless (snapshots.getState (← getEnv)).size==count do throwError "failed discovery published checkpoint"
  unless (← job.get).isNone && (← pendingLayers.get).isEmpty do throwError "failed discovery retained state"
  logInfo m!"selected split guard {index} rejected by original evaluator/kernel; production discovery rolled back"

resume_memory_replay Solkey.TestSuite.returnLeavesNestedLoops.problem
run_elab rejectSelectedGuard 0
resume_memory_replay Solkey.TestSuite.returnLeavesNestedLoops.problem
run_elab rejectSelectedGuard 1

run_elab do
  let C := mkConst ``Solkey.TestSuite
  let nilCtx := mkApp (mkConst ``List.nil [0]) (mkConst ``LTy)
  let wrong := Fml.quote (C := Solkey.TestSuite) C (.tt : Fml Solkey.TestSuite [.val .uint])
  let env ← getEnv
  let rejected ← kernelTypingRefusal do
    let _ ← defineChecked (mkApp2 (mkConst ``Fml) C nilCtx) wrong
    pure ()
  setEnv env
  aliasCache.set {}
  unless rejected do throwError "foreign-context quotation accepted"
  logInfo "foreign-context quotation rejected by actual typed data declaration"


-- A true first projection cannot mask a false SECOND component of the pair.
resume_memory_replay Solkey.TestSuite.returnLeavesNestedLoops.problem
run_elab rejectSelectedGuard 1 true

-- Missing proposal metadata uses the original evaluator path, with the
-- same original guard observations and a kernel-checked layer equation.
resume_memory_replay Solkey.TestSuite.returnLeavesNestedLoops.problem
run_elab do
  let some base ← job.get | throwError "missing original checkpoint"
  let mut selected := none
  for offset in [:base.hints.size] do
    let id := base.hints.size-1-offset
    if selected.isNone && base.hints[id]!.guards.size==2 then selected := some id
  let some id := selected | throwError "missing actual two-guard split"
  let h := base.hints[id]!
  unless !h.guards[0]! && (h.guardHints[0]?.join).isSome && (h.guardHints[1]?.join).isSome do
    throwError "fallback control lacks original second hint"
  let wrong := {h with guardHints := h.guardHints.set! 1 none}
  let inputs ← IO.mkRef (h.children.foldl (fun xs child => xs.set! child none) (← base.inputs.get))
  let env ← getEnv
  let count := (snapshots.getState env).size
  let before := (← finePerf.get)["rigidPairKernel"]?.getD 0
  job.set (some {base with hints := base.hints.set! id wrong, inputs, pending := [id]})
  discoverNext
  unless (← pendingLayers.get).size==1 do throwError "fallback failed to produce layer"
  let some current ← job.get | throwError "fallback lost job"
  flushLayers current
  let some checked := (← inputs.get)[id]! | throwError "fallback lost input"
  unless checked.layer.isSome do throwError "fallback layer was not kernel checked"
  unless (← finePerf.get)["rigidPairKernel"]?.getD 0 == before do throwError "missing hint incorrectly used paired path"
  unless (snapshots.getState (← getEnv)).size==count do throwError "diagnostic unexpectedly published checkpoint"
  setEnv env
  aliasCache.set {}
  job.set none
  pendingLayers.set #[]
  logInfo "missing second hint used original checked evaluator; same observations and no paired certificate"
