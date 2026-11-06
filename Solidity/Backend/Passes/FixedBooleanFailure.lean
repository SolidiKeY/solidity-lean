import Solidity.Backend.Passes.FixedBooleanControls
import Solidity.Backend.Passes.RevertWitness

/-! The SAME runtime selector reaches an out-of-bounds observation only on
the short independent array, after its earlier captured increment succeeds. -/
namespace Solidity.Backend.Passes.FixedBooleanSequence
open Evm Evm.Memory Evm.Compiler
open Controls.Fixture
open ReferenceControls (Γb state branchThenRead)

private abbrev selected : Idx Captured (.mem (.array (.prim .uint))) :=
  .there (.there (.there .here))
def captureStage : Memory.CompiledProg 1 receiver.frag capturePrefix :=
  (Memory.compileProg 1 _ capturePrefix).get (by decide +kernel)
def badObserve : Prog C Captured Final :=
  .cons (.declLocal .uint (.user "bad-observed")
    (some (.readMem (.index .dyn (.var selected rfl) (.simple (.lit 1 rfl)))))) .nil
def badStage : Memory.CompiledProg 1 captureStage.frag badObserve :=
  (Memory.compileProg 1 _ badObserve).get (by decide +kernel)

private theorem capture_some (b : Bool) :
    (capturePrefix.run (middle b).st).toOption.isSome = true := by cases b <;> decide +kernel
noncomputable def afterCapture (b : Bool) : Solidity.Out C (middle b).st.H Captured :=
  (capturePrefix.run (middle b).st).toOption.get (capture_some b)
private theorem source_get {Γ Δ : Ctx} {τ : State C Γ} {P : Prog C Γ Δ}
    {o : Solidity.Out C τ.H Δ} (hx : some o = (P.run τ).toOption) : P.run τ = .ok o := by
  cases hs : P.run τ with
  | ok value => rw [hs] at hx; exact congrArg Except.ok (Option.some.inj hx).symm
  | error e => rw [hs] at hx; cases hx

theorem capture_source (b : Bool) : capturePrefix.run (middle b).st = .ok (afterCapture b) :=
  source_get (Option.some_get (capture_some b))

theorem actual_source_failure : badObserve.run (afterCapture true).st = .error .revert := by with_unfolding_all rfl

/-- Both actual successful maps precede all saved tails. The failing Input
uses the capture's selected map and its actual typed state; no post-failure
machine or map is posited. -/
theorem reached_failure {base : Nat → Fin W}
    (hp : MappedOutput (.memory population) 1 128 initialBase initial initialMachine σ populatedTarget base) :
    ∃ (mb nb : Nat → Fin W) (mid next : Machine), ∀ tail,
      run receiver.code {(runtimeInput true) with stack := tail} = .ok {mid with stack := tail} 0 ∧
      MappedOutput (.memory receiver) 1 128 base (state true)
        {(runtimeInput true) with stack := tail} (middle true).st {mid with stack := tail} mb ∧
      (Compilation.memory captureStage).Input 1 128 mb (middle true).st {mid with stack := tail} ∧
      run captureStage.code {mid with stack := tail} = .ok {next with stack := tail} 0 ∧
      MappedOutput (.memory captureStage) 1 128 mb (middle true).st
        {mid with stack := tail} (afterCapture true).st {next with stack := tail} nb ∧
      (Compilation.memory badStage).Input 1 128 nb (afterCapture true).st {next with stack := tail} ∧
      badObserve.run (afterCapture true).st = .error .revert ∧
      run badStage.code {next with stack := tail} = .revert ∧
      run (receiver.code ++ (captureStage.code ++ badStage.code))
        {(runtimeInput true) with stack := tail} = .revert := by
  have empty : (runtimeInput true).stack = [] := by
    simpa only [runtimeInput,writeMachine] using populated_stack
  have link : MappedBoundaryLink (.memory receiver) (.memory captureStage)
      1 128 base (state true) (runtimeInput true) :=
    memory_nonallocating_mapped_link _ _ (by decide +kernel) (by decide +kernel)
  obtain ⟨mb,nb,mid,next,_,_,_,hall⟩ :=
    compilation_pair_shared (.memory receiver) (.memory captureStage)
      (runtime_input hp true) empty link (by decide +kernel) (by decide +kernel)
      (middle_source true) (capture_source true)
  refine ⟨mb,nb,mid,next,?_⟩
  intro tail
  obtain ⟨hi,hm,hir,hn,_,ma,md⟩ := hall tail
  have ma' : MappedOutput (.memory receiver) 1 128 base (state true)
      {(runtimeInput true) with stack := tail} (middle true).st {mid with stack := tail} mb := by
    simpa only [receiver.cert.pushes_zero,Nat.add_zero] using ma
  have md' : MappedOutput (.memory captureStage) 1 128 mb (middle true).st
      {mid with stack := tail} (afterCapture true).st {next with stack := tail} nb := by
    simpa only [receiver.cert.pushes_zero,captureStage.cert.pushes_zero,Nat.add_zero] using md
  have hir' : (Compilation.memory captureStage).Input 1 128 mb (middle true).st {mid with stack := tail} := by
    simpa only [receiver.cert.pushes_zero,Nat.add_zero] using hir
  have lastLink : MappedBoundaryLink (.memory captureStage) (.memory badStage)
      1 128 mb (middle true).st {mid with stack := tail} :=
    memory_nonallocating_mapped_link captureStage badStage
    (by decide +kernel) (by decide +kernel)
  have lastInput : (Compilation.memory badStage).Input 1 128 nb (afterCapture true).st {next with stack := tail} := by
    simpa only [captureStage.cert.pushes_zero,Nat.add_zero] using
      lastLink (afterCapture true) {next with stack := tail} nb (capture_source true) hn md'
  have failed : run badStage.code {next with stack := tail} = .revert :=
    (compilation_revert_iff (.memory badStage) lastInput (by decide +kernel)).mpr (.inl actual_source_failure)
  exact ⟨hm,ma',hir',hn,md',lastInput,actual_source_failure,failed,
    by
      have h1 : run receiver.code {(runtimeInput true) with stack := tail} = .ok {mid with stack := tail} 0 := hm
      have h2 : run captureStage.code {mid with stack := tail} = .ok {next with stack := tail} 0 := hn
      rw [run_append_ok h1,run_append_ok h2]
      exact failed⟩

private def vector (out : Evm.Out) : Option (List Nat) :=
  match out with
  | .ok m _ => (m.stack ++ addresses.map m.mem).mapM fun w =>
      match w with | .val v => some v.val | .slot _ => none
  | _ => none

theorem actual_capture_prefix_vector :
    vector (run (receiver.code ++ captureStage.code)
      {(runtimeInput true) with stack := [w[77],w[88]]}) =
      some [77,88,261,99,259,256,259,4,1,4,0,2,7,9,1,5] := by decide +kernel

theorem opposite_branch_success :
    vector (run (receiver.code ++ (captureStage.code ++ badStage.code))
      {(runtimeInput false) with stack := [w[77],w[88]]}) =
      some [77,88,261,99,259,256,256,7,0,7,9,2,8,9,1,4] := by decide +kernel

theorem failure_not_divergence_or_panic :
    badObserve.run (afterCapture true).st ≠ .error .diverge ∧
    badObserve.run (afterCapture true).st ≠ .error .panic := by
  rw [actual_source_failure]
  constructor <;> intro h <;> cases h

end Solidity.Backend.Passes.FixedBooleanSequence
