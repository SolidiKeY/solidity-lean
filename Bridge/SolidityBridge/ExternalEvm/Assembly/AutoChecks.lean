import SolidityBridge.ExternalEvm.Assembly.Automatic
import SolidityBridge.ExternalEvm.Assembly.StackLoopChecks
import SolidityBridge.ExternalEvm.Assembly.CompositionChecks

namespace Solidity.Evm.External.Assembly.AutomaticChecks

#guard (assembleAtoms ComposedBranch.code 5 (ComposedBranch.initial (.ofNat 1) [])).isSome
#guard (certifyAtoms ComposedBranch.image (ComposedBranch.initial (.ofNat 0) [])).isSome

/-- The semantic certificate is constructed by executable finite checking,
not by a hand-written per-instruction proof for this example. -/
def branchCertificate : DecodedCode (ComposedBranch.initial (.ofNat 1) []) ComposedBranch.image :=
  ((certifyCode ComposedBranch.image (ComposedBranch.initial (.ofNat 1) [])).get
    (by
      rw [certifyCode.eq_def]
      dsimp only [ComposedBranch.code, List.length_cons, List.length_nil, collectFin, bind, Option.bind]
      simp only [Fin.getElem_fin, List.getElem_cons_zero]
      simp only [certifySite.eq_def]
      decide +kernel)).down

example : MacroRefinement ComposedBranch.image (ComposedBranch.initial (.ofNat 1) []) :=
  branchCertificate.refinement

private def corrupted : EvmYul.EVM.State :=
  {(ComposedBranch.initial (.ofNat 1) []) with
    executionEnv := {(ComposedBranch.initial (.ofNat 1) []).executionEnv with code := ⟨#[0x00]⟩}}
#guard (certifyAtoms ComposedBranch.image corrupted).isNone
#guard (assembleAtoms ComposedBranch.code 5 corrupted).isNone
#guard (assembleAtoms [.jump 1] 0 corrupted).isNone
#guard (assembleAtoms [.sload] 0 corrupted).isNone

#guard (assembleChecked ComposedBranch.code 5 (ComposedBranch.initial (.ofNat 1) [])).isSome
#guard (assembleChecked StackLoop.code 0 (StackLoop.initial [.ofNat 1, .ofNat 0])).isSome


def loopCertificate : DecodedCode (StackLoop.initial []) StackLoop.image :=
  ((certifyCode StackLoop.image (StackLoop.initial [])).get (by
      rw [certifyCode.eq_def]
      dsimp only [StackLoop.code, List.length_cons, List.length_nil, collectFin, bind, Option.bind]
      simp only [Fin.getElem_fin, List.getElem_cons_zero]
      simp only [certifySite.eq_def]
      simp only [certifyCode.eq_def, List.length_nil, collectFin, bind, Option.bind]
      simp only [assembleChild]
      decide +kernel)).down

/-- A nonconstant, multi-turn source loop now uses the automatically
constructed certificate rather than a caller's routing proof. -/
example : ∃ n t, fetchedSteps n (StackLoop.initial [.ofNat 1, .ofNat 2, .ofNat 0, .ofNat 9]) = .ok t ∧
    t.pc.toNat = 72 ∧ words t.stack = [w[9]] := by
  let m := {Machine.init with stack := [w[1], w[2], w[0], w[9]]}
  have source : run StackLoop.code m = .ok {Machine.init with stack := [w[9]]} 0 := by
    have hl : (Instr.loop [] []).step m = .ok {Machine.init with stack := [w[9]]} 0 :=
      loopRun_of_iterN (n := 3) rfl
    change ((Instr.loop [] []).step m).bind (fun m k => exec [] k m) = _
    rw [hl]
    rfl
  have entry : Boundary StackLoop.image (StackLoop.initial []) 0 m
      (StackLoop.initial [.ofNat 1, .ofNat 2, .ofNat 0, .ofNat 9]) :=
    ⟨by decide, rfl, rfl, rfl, rfl⟩
  obtain ⟨n, t, ht, he⟩ := certified_run_simulation StackLoop.image (StackLoop.initial [])
    loopCertificate m _ _ entry source
  exact ⟨n, t, ht, (Option.some.inj he.pc).symm, he.stack.symm⟩

private def nested : List Instr := [.loop [.push w[0]] [.loop [] []], .push w[9]]
private def nestedFrame : EvmYul.EVM.State :=
  {(default : EvmYul.EVM.State) with
    pc := .ofNat 0
    executionEnv := {(default : EvmYul.ExecutionEnv .EVM) with
      code := ⟨((emit nested 0).getD []).toArray⟩}}
#guard (assembleChecked nested 0 nestedFrame).isSome
#guard (assembleChecked nested 1 nestedFrame).isNone
#guard (assembleChecked [.loop [.jump 1] []] 0 nestedFrame).isNone

end Solidity.Evm.External.Assembly.AutomaticChecks
