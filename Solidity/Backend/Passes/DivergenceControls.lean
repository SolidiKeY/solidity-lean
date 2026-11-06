import Solidity.Backend.Passes.Spin
import Solidity.Backend.Passes.DivergenceWitness
import Solidity.Backend.Passes.TripleFailures

/-! Immediate and reached intrinsic loop divergence, including real memory
allocation/capture-to-core boundaries. No malformed target code is used. -/
namespace Solidity.Backend.Passes.DivergenceControls
open Solidity.Evm Solidity.Evm.Compiler Solidity.Evm.Memory
open Solidity.Backend.Passes.Controls.Fixture
open Solidity.Backend.Passes.AllocatingControls
open Solidity.Backend.Passes.TripleControls

def initialSpin := Spin.checked (C := C) 1 (Frag.init [])
def middleSpin := Spin.checked (C := C) 1 allocationStage.frag
def lastSpin := Spin.checked (C := C) 1 captureStage.frag

theorem initial_input : initialSpin.Input 1 7 initialBase (State.init C) initialMachine :=
  ⟨initial_repr7.1.core, by decide +kernel⟩

/-- The suffix is not reached, so no represented entry for it is required. -/
theorem immediate (tail : List Word) :
    run (initialSpin.code ++ (allocationStage.code ++ captureStage.code))
      {initialMachine with stack := tail} = .fault :=
  run_append_fault (Spin.fault_all_tails initial_input tail)

theorem middle_link (tail : List Word) :
    MappedBoundaryLink (.memory allocationStage) middleSpin 1 7 initialBase
      (State.init C) {initialMachine with stack := tail} :=
  Spin.memory_link allocationStage

/-- Real memory output supplies the reached core Input; after the loop,
the third memory Input is unreachable, not silently inferred from core Rep. -/
theorem middle (tail : List Word) :
    run (allocationStage.code ++ (middleSpin.code ++ captureStage.code))
      {initialMachine with stack := tail} = .fault := by
  have de : ReachedMappedLink (.memory allocationStage) middleSpin (.memory captureStage)
      1 7 initialBase (State.init C) {initialMachine with stack := tail} := by
    intro o mid mb _ _ _
    exact Spin.unreachable_link (.memory captureStage) mb o.st mid
  exact (compilation_triple_fault_iff (.memory allocationStage) middleSpin (.memory captureStage)
    (compilation_input_stack (.memory allocationStage) prefix_input7 tail)
    (middle_link tail) de rfl rfl rfl).mpr
      (.inr ⟨_, ReachabilityControls.fresh_state_reaches_fixture, .inl (Spin.diverges σ)⟩)

theorem last_link (tail : List Word) :
    ReachedMappedLink (.memory allocationStage) (.memory captureStage) lastSpin
      1 7 initialBase (State.init C) {initialMachine with stack := tail} := by
  intro o mid mb _ _ _
  exact Spin.memory_link captureStage

theorem third (tail : List Word) :
    run (allocationStage.code ++ (captureStage.code ++ lastSpin.code))
      {initialMachine with stack := tail} = .fault := by
  have ad : MappedBoundaryLink (.memory allocationStage) (.memory captureStage)
      1 7 initialBase (State.init C) {initialMachine with stack := tail} :=
    memory_nonallocating_mapped_link _ _ (by decide +kernel) (by decide +kernel)
  exact (compilation_triple_fault_iff (.memory allocationStage) (.memory captureStage) lastSpin
    (compilation_input_stack (.memory allocationStage) prefix_input7 tail)
    ad (last_link tail) rfl rfl rfl).mpr
      (.inr ⟨_, ReachabilityControls.fresh_state_reaches_fixture,
        .inr ⟨_, capture_source, Spin.diverges CaptureControls.afterCapture⟩⟩)

/-- Source executions are independent of target fault. Both associations
retain divergence at their actually reached stages. -/
theorem source_cases :
    ((Spin.program (C := C) (Γ := [])).join
      (ReachabilityControls.populatedBuilder.join captureProg)).run (State.init C) = .error .diverge ∧
    (ReachabilityControls.populatedBuilder.join ((Spin.program (C := C)).join captureProg)).run
      (State.init C) = .error .diverge ∧
    (ReachabilityControls.populatedBuilder.join (captureProg.join (Spin.program (C := C)))).run
      (State.init C) = .error .diverge := by
  refine ⟨(joined_diverge_iff _).mpr (.inl (Spin.diverges _)), ?_, ?_⟩
  · exact (joined_diverge_iff _).mpr (.inr ⟨_, ReachabilityControls.fresh_state_reaches_fixture,
      (joined_diverge_iff _).mpr (.inl (Spin.diverges σ))⟩)
  · exact (joined_diverge_iff _).mpr (.inr ⟨_, ReachabilityControls.fresh_state_reaches_fixture,
      (joined_diverge_iff _).mpr (.inr ⟨_, capture_source, Spin.diverges _⟩)⟩)

/-- Concrete left-associated code and intrinsic sources at every reached
position, in addition to the general association equivalences. -/
theorem left_targets (tail : List Word) :
    run ((initialSpin.code ++ allocationStage.code) ++ captureStage.code)
      {initialMachine with stack := tail} = .fault ∧
    run ((allocationStage.code ++ middleSpin.code) ++ captureStage.code)
      {initialMachine with stack := tail} = .fault ∧
    run ((allocationStage.code ++ captureStage.code) ++ lastSpin.code)
      {initialMachine with stack := tail} = .fault := by
  exact ⟨by simpa only [List.append_assoc] using immediate tail,
    by simpa only [List.append_assoc] using middle tail,
    by simpa only [List.append_assoc] using third tail⟩

theorem left_sources :
    (((Spin.program (C := C) (Γ := [])).join ReachabilityControls.populatedBuilder).join captureProg).run
      (State.init C) = .error .diverge ∧
    ((ReachabilityControls.populatedBuilder.join (Spin.program (C := C))).join captureProg).run
      (State.init C) = .error .diverge ∧
    ((ReachabilityControls.populatedBuilder.join captureProg).join (Spin.program (C := C))).run
      (State.init C) = .error .diverge := by
  simpa only [typed_sequencing_assoc] using source_cases

/-- Revert short-circuits a typed divergent suffix and remains distinct
from fault. No loop Input/success is requested on this unreachable path. -/
theorem revert_before_spin (tail : List Word) :
    run (TripleFailures.first.code ++ initialSpin.code)
      {initialMachine with stack := tail} = .revert ∧
    run (TripleFailures.first.code ++ initialSpin.code)
      {initialMachine with stack := tail} ≠ .fault := by
  have hi : (Compilation.memory TripleFailures.first).Input 1 7 initialBase
      (State.init C) initialMachine :=
    ⟨initial_repr7.1, by decide +kernel, .inl (by decide +kernel)⟩
  have hr : run (TripleFailures.first.code ++ initialSpin.code)
      {initialMachine with stack := tail} = .revert :=
    run_append_revert ((compilation_revert_iff (.memory TripleFailures.first)
      (compilation_input_stack (.memory TripleFailures.first) hi tail) rfl).mpr
        (.inl TripleFailures.first_source))
  exact ⟨hr, by rw [hr]; intro bad; cases bad⟩

/-- Successful physical prefixes have one pair of maps/machines for all
tails. The following fault is obtained anew from its typed loop certificate. -/
theorem shared_prefix_maps : ∃ (mid next : Machine) (mb nb : Nat → Fin W),
    ∀ tail,
    run allocationStage.code {initialMachine with stack := tail} = .ok {mid with stack := tail} 0 ∧
    run captureStage.code {mid with stack := tail} = .ok {next with stack := tail} 0 ∧
    MappedOutput (.memory allocationStage) 1 7 initialBase (State.init C)
      {initialMachine with stack := tail} σ {mid with stack := tail} mb ∧
    MappedOutput (.memory captureStage) 1 7 mb σ {mid with stack := tail}
      CaptureControls.afterCapture {next with stack := tail} nb ∧
    run lastSpin.code {next with stack := tail} = .fault := by
  obtain ⟨mid, mb, hm, sm, hall⟩ := compilation_success_shared_mapped (.memory allocationStage)
    prefix_input7 rfl ReachabilityControls.fresh_state_reaches_fixture
  have ma := (hall []).2
  have ma' : MappedOutput (.memory allocationStage) 1 7 initialBase (State.init C)
      initialMachine σ mid mb := by
    have em : {mid with stack := []} = mid := by cases mid; cases sm; rfl
    simpa only [allocationStage.cert.pushes_zero, Nat.add_zero, em] using ma
  have hi := first_link _ _ _ ReachabilityControls.fresh_state_reaches_fixture hm ma'
  obtain ⟨next, nb, _, _, hnext⟩ :=
    compilation_success_shared_mapped (.memory captureStage) hi rfl capture_source
  refine ⟨mid, next, mb, nb, ?_⟩
  intro tail
  have mta : MappedOutput (.memory allocationStage) 1 7 initialBase (State.init C)
      {initialMachine with stack := tail} σ {mid with stack := tail} mb := by
    simpa only [allocationStage.cert.pushes_zero, Nat.add_zero] using (hall tail).2
  have mtc : MappedOutput (.memory captureStage) 1 7 mb σ {mid with stack := tail}
      CaptureControls.afterCapture {next with stack := tail} nb := by
    simpa only [captureStage.cert.pushes_zero, allocationStage.cert.pushes_zero,
      Nat.add_zero] using (hnext tail).2
  have hloop : lastSpin.Input 1 7 nb CaptureControls.afterCapture {next with stack := tail} :=
    ⟨mtc.1.core, by decide +kernel⟩
  exact ⟨(hall tail).1, (hnext tail).1, mta, mtc,
    (compilation_fault_iff lastSpin hloop rfl).mpr (Spin.diverges _)⟩

/-- A reached diverging third stage retains both actual physical prefix maps. -/
theorem reached_maps : ∃ (o : Solidity.Out C (State.init C).H Γ)
    (mid : Machine) (mb : Nat → Fin W),
    ReachabilityControls.populatedBuilder.run (State.init C) = .ok o ∧
    run allocationStage.code initialMachine = .ok mid 0 ∧
    MappedOutput (.memory allocationStage) 1 7 initialBase (State.init C) initialMachine o.st mid mb ∧
    ∃ (u : Solidity.Out C o.st.H Γ) (next : Machine) (nb : Nat → Fin W),
      captureProg.run o.st = .ok u ∧ run captureStage.code mid = .ok next 0 ∧
      MappedOutput (.memory captureStage) 1 7 mb o.st mid u.st next nb ∧
      (Spin.program (C := C)).run u.st = .error .diverge := by
  have h := (compilation_triple_fault_witness_iff (.memory allocationStage) (.memory captureStage)
    lastSpin prefix_input7 first_link (last_link []) rfl rfl rfl).mp (third [])
  rcases h with hs | ⟨o, mid, mb, hs, hm, ha, hd | ⟨u, next, nb, hu, hn, hd, he⟩⟩
  · rw [ReachabilityControls.fresh_state_reaches_fixture] at hs
    cases hs
  · have ho : o = ⟨σ, ⟨σ.H, rfl⟩⟩ :=
      Except.ok.inj (hs.symm.trans ReachabilityControls.fresh_state_reaches_fixture)
    cases ho
    rw [capture_source] at hd
    cases hd
  · exact ⟨o, mid, mb, hs, hm,
      by simpa only [allocationStage.cert.pushes_zero, Nat.add_zero] using ha,
      u, next, nb, hu, hn,
      by simpa only [allocationStage.cert.pushes_zero, captureStage.cert.pushes_zero, Nat.add_zero] using hd,
      he⟩

private def cell (n : Nat) : Evm.Out → Option Nat
  | .ok m _ => match m.mem n with | .val w => some w.val | _ => none
  | _ => none
private def beforeThird := allocationStage.code ++ captureStage.code
private theorem a4 : cell 4 (run allocationStage.code initialMachine) = some 0 := by decide +kernel
private theorem a2 : cell 2 (run allocationStage.code initialMachine) = some 16 := by decide +kernel
private theorem a3 : cell 3 (run allocationStage.code initialMachine) = some 16 := by decide +kernel
private theorem a1 : cell 1 (run allocationStage.code initialMachine) = some 19 := by decide +kernel
private theorem a17 : cell 17 (run allocationStage.code initialMachine) = some 7 := by decide +kernel
private theorem a18 : cell 18 (run allocationStage.code initialMachine) = some 9 := by decide +kernel
private theorem a20 : cell 20 (run allocationStage.code initialMachine) = some 4 := by decide +kernel
private theorem a0 : cell 0 (run allocationStage.code initialMachine) = some 21 := by decide +kernel
private theorem c4 : cell 4 (run beforeThird initialMachine) = some 7 := by decide +kernel
private theorem c2 : cell 2 (run beforeThird initialMachine) = some 16 := by decide +kernel
private theorem c3 : cell 3 (run beforeThird initialMachine) = some 16 := by decide +kernel
private theorem c1 : cell 1 (run beforeThird initialMachine) = some 19 := by decide +kernel
private theorem c17 : cell 17 (run beforeThird initialMachine) = some 8 := by decide +kernel
private theorem c18 : cell 18 (run beforeThird initialMachine) = some 9 := by decide +kernel
private theorem c20 : cell 20 (run beforeThird initialMachine) = some 4 := by decide +kernel
private theorem c0 : cell 0 (run beforeThird initialMachine) = some 21 := by decide +kernel

theorem ordered_prefixes :
    [4, 2, 3, 1, 17, 18, 20, 0].mapM (fun n => cell n (run allocationStage.code initialMachine)) =
      some [0, 16, 16, 19, 7, 9, 4, 21] ∧
    [4, 2, 3, 1, 17, 18, 20, 0].mapM (fun n => cell n (run beforeThird initialMachine)) =
      some [7, 16, 16, 19, 8, 9, 4, 21] := by
  constructor
  · simp only [List.mapM_cons, List.mapM_nil, a4, a2, a3, a1, a17, a18, a20, a0]
    rfl
  · simp only [List.mapM_cons, List.mapM_nil, c4, c2, c3, c1, c17, c18, c20, c0]
    rfl

end Solidity.Backend.Passes.DivergenceControls
