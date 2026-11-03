import Solidity.Calculus.MemoryLoopReplay
import Solidity.TestSuite.ScopedProblems

/-! Kernel admission, collision and rollback controls for fallback sibling certificates.
The fixed replay timing roster is unchanged. -/

open Lean Meta Solidity Solidity.Seq Solidity.Seq.MemoryReplay

private def typedRefusal (action : MetaM Unit) : MetaM Bool :=
  withOptions (fun o => o.setBool `pp.raw true) do
    try
      action
      return false
    catch e =>
      let text ← e.toMessageData.toString
      if text.startsWith "(kernel)" && (text.splitOn "type mismatch").length>1 then return true
      throw e

run_elab do
  let C := mkConst ``Solkey.TestSuite
  let Γ := mkApp (mkConst ``List.nil [0]) (mkConst ``LTy)
  let H := mkApp2 (mkConst ``Hyps.nil) C Γ
  let yes := mkApp2 (mkConst ``Fml.tt) C Γ
  let no := mkApp2 (mkConst ``Fml.ff) C Γ
  let originalNames ← getDeclNGen
  let originalFresh ← getNGen
  let first ← checkedFallbackPair C Γ H yes no false true
  unless first.size==2 do throwError "wrong fallback certificate size"
  for (proof,condition,result) in [(first[0]!,yes,false),(first[1]!,no,true)] do
    let type ← ofExceptKernelException (Kernel.check (← getEnv) {} proof)
    let expected := knownEq (mkConst ``Bool)
      (mkAppN (mkConst ``refuteLanded) #[C,Γ,H,condition]) (toExpr result)
    unless type==expected do throwError "changed original guard equation"
  let names ← getDeclNGen
  let fresh ← getNGen
  unless names.namePrefix==originalNames.namePrefix && names.idx==originalNames.idx &&
      names.parentIdxs==originalNames.parentIdxs &&
      fresh.namePrefix==originalFresh.namePrefix && fresh.idx==originalFresh.idx do
    throwError "fallback certificate consumed an original fresh name"
  let base := (← getEnv).mainModule ++ `_memoryReplayFallbackCertificate
  unless (← getEnv).contains (Name.num base 0) do throwError "missing checked certificate"
  for (a,b) in [(true,true),(false,false)] do
    let rejected ← typedRefusal do
      let _ ← checkedFallbackPair C Γ H yes no a b
      pure ()
    unless rejected do throwError "false fallback component accepted"
    if (← getEnv).contains (Name.num base 1) then
      throwError "failed fallback admission leaked a declaration"
  let second ← checkedFallbackPair C Γ H yes no false true
  unless second.size==2 && (← getEnv).contains (Name.num base 1) do
    throwError "collision-safe subsequent certificate missing"
  let savedDispatch ← getEnv
  let inputs ← IO.mkRef #[none]
  let hint : Hint := ⟨0,none,false,#[],0,#[false,true],#[none,none],yes,0⟩
  let j : Job := ⟨yes,C,mkConst ``RuleSet.all,mkConst ``Bool,#[hint],inputs,[],0⟩
  let pair ← checkedRigidPair j 0 Γ H yes no
  unless pair.size==2 do throwError "both-missing-hint dispatch did not batch"
  let _ ← checkedGuard j 0 0 Γ H yes false pair[0]?
  let _ ← checkedGuard j 0 1 Γ H no true pair[1]?
  setEnv savedDispatch
  for hints in [#[],#[none,some (no,false)],#[none,none,none]] do
    let j := {j with hints := #[{hint with guardHints := hints}]}
    let pair ← checkedRigidPair j 0 Γ H yes no
    unless pair.isEmpty do throwError "unexpected fallback batching outside two absent hints"
  if (← getEnv).contains (Name.num base 2) then
    throwError "unselected fallback dispatch leaked a declaration"
  let rejected ← tryCatchRuntimeEx
    (do
      requireKernelChecking true
      pure false)
    (fun e => do
      let text ← e.toMessageData.toString
      if text=="memory replay requires kernel checking" then return true
      throw e)
  unless rejected do throwError "disabled-kernel fallback admission accepted"
  if (← getEnv).contains (Name.num base 2) then
    throwError "disabled-kernel admission leaked a declaration"
  logInfo "checked fallback truth values, both false components, names, collision, rollback, dispatch and kernel preflight"
