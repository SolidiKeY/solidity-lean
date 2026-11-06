import Solidity.Backend.Passes.SourceTerminalFailure
import Solidity.Backend.Passes.DivergenceControls

/-! Actual reached ordinary revert and asserting panic after memory effects.
The coarse target boundary is explicitly non-injective on source failures;
there is no ABI-byte field or replacement observation layer here. -/
namespace Solidity.Backend.Passes.RevertControls
open Solidity.Evm Solidity.Evm.Compiler Solidity.Evm.Memory
open Solidity.Backend.Passes.Controls.Fixture
open Solidity.Backend.Passes.AllocatingControls
open Solidity.Backend.Passes.TripleControls

def panicProg : Prog C Γ Γ := .cons (.assert (.simple (.bool false))) .nil
def panicStage : Compilation 1 captureStage.frag panicProg := .core captureStage.frag (by rfl)
theorem panic_recognized : (Compiler.compile 1 captureStage.frag panicProg).isSome = true := rfl

theorem panic_source : panicProg.asserts = true ∧
    panicProg.run CaptureControls.afterCapture = .error .panic := ⟨rfl, rfl⟩

theorem panic_link (tail : List Word) :
    ReachedMappedLink (.memory allocationStage) (.memory captureStage) panicStage
      1 7 initialBase (State.init C) {initialMachine with stack := tail} := by
  intro o mid mb _ _ _ u next nb _ _ ma
  exact ⟨ma.1.core, by simpa only [panicStage, panicProg, Evm.Prog.pushes,
    Evm.Stmt.pushes, Nat.add_zero] using ma.1.core.bound⟩

theorem panic_reached (tail : List Word) :
    run (allocationStage.code ++ (captureStage.code ++ panicStage.code))
      {initialMachine with stack := tail} = .revert := by
  have ad : MappedBoundaryLink (.memory allocationStage) (.memory captureStage)
      1 7 initialBase (State.init C) {initialMachine with stack := tail} :=
    memory_nonallocating_mapped_link _ _ (by decide +kernel) (by decide +kernel)
  exact (compilation_triple_revert_iff (.memory allocationStage) (.memory captureStage) panicStage
    (compilation_input_stack (.memory allocationStage) prefix_input7 tail) ad (panic_link tail)
    rfl rfl rfl).mpr (.inr ⟨_, ReachabilityControls.fresh_state_reaches_fixture,
      .inr ⟨_, capture_source, .inr panic_source⟩⟩)

/-- Immediate failure requires no entry relation or source success for the
skipped allocation/capture suffix. -/
theorem immediate (tail : List Word) :
    TerminalFailure TripleFailures.stop (State.init C) ∧
    run (TripleFailures.first.code ++ (allocationStage.code ++ captureStage.code))
      {initialMachine with stack := tail} = .revert :=
  ⟨.inl TripleFailures.first_source, TripleFailures.first_short_circuit tail⟩

/-- The map used by the reached middle Input is precisely the map selected
by the real allocation output. No third source success/Input is required. -/
theorem middle_witness (tail : List Word) : ∃ (mid : Machine) (mb : Nat → Fin W),
    run allocationStage.code {initialMachine with stack := tail} = .ok mid 0 ∧
    MappedOutput (.memory allocationStage) 1 7 initialBase (State.init C)
      {initialMachine with stack := tail} σ mid mb ∧
    (Compilation.memory TripleFailures.middleBad).Input 1 7 mb σ mid ∧
    TerminalFailure CompileExamples.badRhsRead σ ∧
    run TripleFailures.middleBad.code mid = .revert := by
  have ad : MappedBoundaryLink (.memory allocationStage) (.memory TripleFailures.middleBad)
      1 7 initialBase (State.init C) {initialMachine with stack := tail} :=
    memory_nonallocating_mapped_link _ _ (by decide +kernel) (by decide +kernel)
  have ht : run (allocationStage.code ++ TripleFailures.middleBad.code)
      {initialMachine with stack := tail} = .revert :=
    (compilation_mapped_revert_iff (.memory allocationStage) (.memory TripleFailures.middleBad)
      (compilation_input_stack (.memory allocationStage) prefix_input7 tail) ad rfl rfl).mpr
      (.inr ⟨_, ReachabilityControls.fresh_state_reaches_fixture,
        .inl LinkedControls.right_stage_source_revert⟩)
  have h := (compilation_mapped_revert_witness_iff (.memory allocationStage) (.memory TripleFailures.middleBad)
    (compilation_input_stack (.memory allocationStage) prefix_input7 tail) ad rfl rfl).mp ht
  rcases h with ⟨hs | ⟨_, hs⟩, _⟩ | ⟨o, mid, mb, hs, hm, ma, hi, hf, hr⟩
  · rw [ReachabilityControls.fresh_state_reaches_fixture] at hs
    cases hs
  · rw [ReachabilityControls.fresh_state_reaches_fixture] at hs
    cases hs
  · have ho : o = ⟨σ, ⟨σ.H, rfl⟩⟩ :=
      Except.ok.inj (hs.symm.trans ReachabilityControls.fresh_state_reaches_fixture)
    cases ho
    exact ⟨mid, mb, hm,
      by simpa only [allocationStage.cert.pushes_zero, Nat.add_zero] using ma,
      by simpa only [allocationStage.cert.pushes_zero, Nat.add_zero] using hi, hf, hr⟩

/-- The genuinely reached middle branch also instantiates the TRIPLE
witness law; third source/Input obligations remain absent. -/
theorem middle_triple_witness (tail : List Word) : ∃ (mid : Machine) (mb : Nat → Fin W),
    run allocationStage.code {initialMachine with stack := tail} = .ok mid 0 ∧
    MappedOutput (.memory allocationStage) 1 7 initialBase (State.init C)
      {initialMachine with stack := tail} σ mid mb ∧
    (Compilation.memory TripleFailures.middleBad).Input 1 7 mb σ mid ∧
    TerminalFailure CompileExamples.badRhsRead σ ∧ run TripleFailures.middleBad.code mid = .revert := by
  have ad : MappedBoundaryLink (.memory allocationStage) (.memory TripleFailures.middleBad)
      1 7 initialBase (State.init C) {initialMachine with stack := tail} :=
    memory_nonallocating_mapped_link _ _ (by decide +kernel) (by decide +kernel)
  have de : ReachedMappedLink (.memory allocationStage) (.memory TripleFailures.middleBad)
      (.memory TripleFailures.afterBad) 1 7 initialBase (State.init C) {initialMachine with stack := tail} := by
    intro o mid mb _ _ _
    exact memory_nonallocating_mapped_link _ _ (by decide +kernel) (by decide +kernel)
  have h := (compilation_triple_revert_witness_iff (.memory allocationStage) (.memory TripleFailures.middleBad)
    (.memory TripleFailures.afterBad) (compilation_input_stack (.memory allocationStage) prefix_input7 tail)
    ad de rfl rfl rfl).mp (TripleFailures.second_reached tail)
  rcases h with ⟨hs | ⟨_, hs⟩, _⟩ | ⟨o, mid, mb, hs, hm, ma, hi, hd⟩
  · rw [ReachabilityControls.fresh_state_reaches_fixture] at hs
    cases hs
  · rw [ReachabilityControls.fresh_state_reaches_fixture] at hs
    cases hs
  · have ho : o = ⟨σ, ⟨σ.H, rfl⟩⟩ := Except.ok.inj (hs.symm.trans ReachabilityControls.fresh_state_reaches_fixture)
    cases ho
    rcases hd with ⟨hf, hr⟩ | ⟨u, next, nb, hu, _⟩
    · exact ⟨mid, mb, hm,
        by simpa only [allocationStage.cert.pushes_zero, Nat.add_zero] using ma,
        by simpa only [allocationStage.cert.pushes_zero, Nat.add_zero] using hi, hf, hr⟩
    · rw [LinkedControls.right_stage_source_revert] at hu
      cases hu

/-- Both actual prefix maps, full output relations AND the failing suffix
Input/run are retained. This works for independently supplied physical links. -/
theorem third_witness {R : Prog C Γ Γ} (last : Compilation 1 captureStage.frag R)
    (tail : List Word)
    (link : ReachedMappedLink (.memory allocationStage) (.memory captureStage) last
      1 7 initialBase (State.init C) {initialMachine with stack := tail})
    (hp : Evm.Prog.pays R = false)
    (ht : run (allocationStage.code ++ (captureStage.code ++ last.code))
      {initialMachine with stack := tail} = .revert) :
    ∃ (mid next : Machine) (mb nb : Nat → Fin W),
      run allocationStage.code {initialMachine with stack := tail} = .ok mid 0 ∧
      MappedOutput (.memory allocationStage) 1 7 initialBase (State.init C)
        {initialMachine with stack := tail} σ mid mb ∧
      (Compilation.memory captureStage).Input 1 7 mb σ mid ∧
      run captureStage.code mid = .ok next 0 ∧
      MappedOutput (.memory captureStage) 1 7 mb σ mid CaptureControls.afterCapture next nb ∧
      last.Input 1 7 nb CaptureControls.afterCapture next ∧
      TerminalFailure R CaptureControls.afterCapture ∧ run last.code next = .revert := by
  have ad : MappedBoundaryLink (.memory allocationStage) (.memory captureStage)
      1 7 initialBase (State.init C) {initialMachine with stack := tail} :=
    memory_nonallocating_mapped_link _ _ (by decide +kernel) (by decide +kernel)
  have h := (compilation_triple_revert_witness_iff (.memory allocationStage) (.memory captureStage)
    last (compilation_input_stack (.memory allocationStage) prefix_input7 tail) ad link rfl rfl hp).mp ht
  rcases h with ⟨hs | ⟨_, hs⟩, _⟩ | ⟨o, mid, mb, hs, hm, ma, hi, hd | ⟨u, next, nb, hu, hn, md, he, hf, hr⟩⟩
  · rw [ReachabilityControls.fresh_state_reaches_fixture] at hs
    cases hs
  · rw [ReachabilityControls.fresh_state_reaches_fixture] at hs
    cases hs
  · have ho : o = ⟨σ, ⟨σ.H, rfl⟩⟩ := Except.ok.inj (hs.symm.trans ReachabilityControls.fresh_state_reaches_fixture)
    cases ho
    rcases hd.1 with hd | ⟨_, hd⟩ <;> rw [capture_source] at hd <;> cases hd
  · have ho : o = ⟨σ, ⟨σ.H, rfl⟩⟩ := Except.ok.inj (hs.symm.trans ReachabilityControls.fresh_state_reaches_fixture)
    cases ho
    have hu' : u = ⟨CaptureControls.afterCapture, List.prefix_refl _⟩ := Except.ok.inj (hu.symm.trans capture_source)
    cases hu'
    refine ⟨mid, next, mb, nb, hm, ?_, ?_, hn, ?_, ?_, hf, hr⟩
    · simpa only [allocationStage.cert.pushes_zero, Nat.add_zero] using ma
    · simpa only [allocationStage.cert.pushes_zero, Nat.add_zero] using hi
    · simpa only [allocationStage.cert.pushes_zero, captureStage.cert.pushes_zero, Nat.add_zero] using md
    · simpa only [allocationStage.cert.pushes_zero, captureStage.cert.pushes_zero, Nat.add_zero] using he

/-- Independently inhabited ordinary and asserting-panic suffixes. -/
def ordinary_witness (tail : List Word) :=
  third_witness (.memory TripleFailures.third) tail
    (by intro o mid mb _ _ _; exact memory_nonallocating_mapped_link _ _ (by decide +kernel) (by decide +kernel))
    rfl (TripleFailures.third_reached tail)
def asserting_witness (tail : List Word) :=
  third_witness panicStage tail (panic_link tail) rfl (panic_reached tail)

/-- One pair of actual prefix maps/machines precedes forall tail for
BOTH ordinary and asserting-panic suffixes. Each consumes the same nb. -/
theorem shared_revert_maps : ∃ (mid next : Machine) (mb nb : Nat → Fin W), ∀ tail,
    run allocationStage.code {initialMachine with stack := tail} = .ok {mid with stack := tail} 0 ∧
    run captureStage.code {mid with stack := tail} = .ok {next with stack := tail} 0 ∧
    MappedOutput (.memory allocationStage) 1 7 initialBase (State.init C)
      {initialMachine with stack := tail} σ {mid with stack := tail} mb ∧
    MappedOutput (.memory captureStage) 1 7 mb σ {mid with stack := tail}
      CaptureControls.afterCapture {next with stack := tail} nb ∧
    (Compilation.memory TripleFailures.third).Input 1 7 nb CaptureControls.afterCapture {next with stack := tail} ∧
    panicStage.Input 1 7 nb CaptureControls.afterCapture {next with stack := tail} ∧
    run TripleFailures.third.code {next with stack := tail} = .revert ∧
    run panicStage.code {next with stack := tail} = .revert := by
  obtain ⟨mid, next, mb, nb, hall⟩ := DivergenceControls.shared_prefix_maps
  refine ⟨mid, next, mb, nb, ?_⟩
  intro tail
  obtain ⟨ha, hd, ma, md, _⟩ := hall tail
  have ho : (Compilation.memory TripleFailures.third).Input 1 7 nb
      CaptureControls.afterCapture {next with stack := tail} :=
    ⟨md.1, by decide +kernel, .inl (by decide +kernel)⟩
  have hp : panicStage.Input 1 7 nb CaptureControls.afterCapture {next with stack := tail} :=
    ⟨md.1.core, by decide +kernel⟩
  exact ⟨ha, hd, ma, md, ho, hp,
    (compilation_revert_iff (.memory TripleFailures.third) ho rfl).mpr (.inl TripleFailures.third_source),
    (compilation_revert_iff panicStage hp rfl).mpr (.inr panic_source)⟩

/-- Independent source ordinary-revert versus guarded-panic runs. -/
theorem source_cases :
    (TripleFailures.stop.join (ReachabilityControls.populatedBuilder.join captureProg)).run (State.init C) = .error .revert ∧
    (ReachabilityControls.populatedBuilder.join (CompileExamples.badRhsRead.join captureProg)).run (State.init C) = .error .revert ∧
    (ReachabilityControls.populatedBuilder.join (captureProg.join TripleFailures.badAfterCapture)).run (State.init C) = .error .revert ∧
    (ReachabilityControls.populatedBuilder.join (captureProg.join panicProg)).run (State.init C) = .error .panic := by
  refine ⟨(joined_halt_iff _ _).mpr (.inl TripleFailures.first_source), TripleFailures.joined_sources.1,
    TripleFailures.joined_sources.2, ?_⟩
  exact (joined_halt_iff _ _).mpr (.inr ⟨_, ReachabilityControls.fresh_state_reaches_fixture,
    (joined_halt_iff _ _).mpr (.inr ⟨_, capture_source, panic_source.2⟩)⟩)

theorem left_sources :
    ((TripleFailures.stop.join ReachabilityControls.populatedBuilder).join captureProg).run (State.init C) = .error .revert ∧
    ((ReachabilityControls.populatedBuilder.join CompileExamples.badRhsRead).join captureProg).run (State.init C) = .error .revert ∧
    ((ReachabilityControls.populatedBuilder.join captureProg).join TripleFailures.badAfterCapture).run (State.init C) = .error .revert ∧
    ((ReachabilityControls.populatedBuilder.join captureProg).join panicProg).run (State.init C) = .error .panic := by
  simpa only [typed_sequencing_assoc] using source_cases

theorem left_targets (tail : List Word) :
    run ((TripleFailures.first.code ++ allocationStage.code) ++ captureStage.code) {initialMachine with stack := tail} = .revert ∧
    run ((allocationStage.code ++ TripleFailures.middleBad.code) ++ TripleFailures.afterBad.code) {initialMachine with stack := tail} = .revert ∧
    run ((allocationStage.code ++ captureStage.code) ++ TripleFailures.third.code) {initialMachine with stack := tail} = .revert ∧
    run ((allocationStage.code ++ captureStage.code) ++ panicStage.code) {initialMachine with stack := tail} = .revert := by
  exact ⟨by simpa only [List.append_assoc] using TripleFailures.first_short_circuit tail,
    by simpa only [List.append_assoc] using TripleFailures.second_reached tail,
    by simpa only [List.append_assoc] using TripleFailures.third_reached tail,
    by simpa only [List.append_assoc] using panic_reached tail⟩

private def cell (n : Nat) : Evm.Out → Option Nat
  | .ok m _ => match m.mem n with | .val w => some w.val | _ => none
  | _ => none
private def prefixCode := allocationStage.code ++ captureStage.code

private theorem a4 : cell 4 (run allocationStage.code initialMachine) = some 0 := by decide +kernel
private theorem c4 : cell 4 (run prefixCode initialMachine) = some 7 := by decide +kernel
private theorem a2 : cell 2 (run allocationStage.code initialMachine) = some 16 := by decide +kernel
private theorem c2 : cell 2 (run prefixCode initialMachine) = some 16 := by decide +kernel
private theorem a3 : cell 3 (run allocationStage.code initialMachine) = some 16 := by decide +kernel
private theorem c3 : cell 3 (run prefixCode initialMachine) = some 16 := by decide +kernel
private theorem a1 : cell 1 (run allocationStage.code initialMachine) = some 19 := by decide +kernel
private theorem c1 : cell 1 (run prefixCode initialMachine) = some 19 := by decide +kernel
private theorem a17 : cell 17 (run allocationStage.code initialMachine) = some 7 := by decide +kernel
private theorem c17 : cell 17 (run prefixCode initialMachine) = some 8 := by decide +kernel
private theorem a18 : cell 18 (run allocationStage.code initialMachine) = some 9 := by decide +kernel
private theorem c18 : cell 18 (run prefixCode initialMachine) = some 9 := by decide +kernel
private theorem a20 : cell 20 (run allocationStage.code initialMachine) = some 4 := by decide +kernel
private theorem c20 : cell 20 (run prefixCode initialMachine) = some 4 := by decide +kernel
private theorem a0 : cell 0 (run allocationStage.code initialMachine) = some 21 := by decide +kernel
private theorem c0 : cell 0 (run prefixCode initialMachine) = some 21 := by decide +kernel

/-- ALL original locals/aliases, both array elements, independent value,
and allocator cursor. These exact existing observations are preserved. -/
theorem ordered_prefixes :
    [4,2,3,1,17,18,20,0].mapM (fun n => cell n (run allocationStage.code initialMachine)) =
      some [0,16,16,19,7,9,4,21] ∧
    [4,2,3,1,17,18,20,0].mapM (fun n => cell n (run prefixCode initialMachine)) =
      some [7,16,16,19,8,9,4,21] := by
  constructor
  · simp only [List.mapM_cons, List.mapM_nil, a4, a2, a3, a1, a17, a18, a20, a0]
    rfl
  · simp only [List.mapM_cons, List.mapM_nil, c4, c2, c3, c1, c17, c18, c20, c0]
    rfl

theorem wrong_stage : ¬ TerminalFailure captureProg σ ∧
    ¬ TerminalFailure ReachabilityControls.populatedBuilder (State.init C) := by
  constructor
  · rintro (h | ⟨_, h⟩) <;> rw [capture_source] at h <;> cases h
  · rintro (h | ⟨_, h⟩) <;> rw [ReachabilityControls.fresh_state_reaches_fixture] at h <;> cases h

theorem stale_map (m : Machine) :
    ¬ StateRepr 1 1 7 allocationStage.frag σ initialBase m := TripleControls.stale_map m

theorem skipped_effect : cell 4 (run allocationStage.code initialMachine) = some 0 ∧
    cell 4 (run prefixCode initialMachine) = some 7 ∧
    cell 17 (run prefixCode initialMachine) = some 8 := by
  constructor
  · decide +kernel
  · constructor <;> decide +kernel

private def readZero : Val C Γ .uint :=
  .readMem (.index .dyn (.var (.there .here) rfl) (.simple (.lit 0 rfl)))
def wrongRecapture : Prog C Γ Γ :=
  .cons (.incDec .postInc rfl CaptureControls.location) (.cons (.assignLocal .here readZero) .nil)
def wrongStage : CompiledProg 1 allocationStage.frag wrongRecapture :=
  (compileProg 1 allocationStage.frag wrongRecapture).get (by decide +kernel)

theorem recapture_negative :
    cell 4 (run (allocationStage.code ++ wrongStage.code) initialMachine) = some 8 ∧
    cell 4 (run prefixCode initialMachine) = some 7 := by
  constructor <;> decide +kernel

def recapturedSource : State C Γ :=
  { CaptureControls.afterCapture with env :=
    (CompileExamples.uint 8 (by decide), some CompileExamples.r0, some CompileExamples.r0,
      some CompileExamples.r1, ()) }

theorem recapture_source : wrongRecapture.run σ = .ok ⟨recapturedSource, List.prefix_refl _⟩ := by
  with_unfolding_all rfl

private theorem r4 : cell 4 (run (allocationStage.code ++ wrongStage.code) initialMachine) = some 8 := by decide +kernel
private theorem r2 : cell 2 (run (allocationStage.code ++ wrongStage.code) initialMachine) = some 16 := by decide +kernel
private theorem r3 : cell 3 (run (allocationStage.code ++ wrongStage.code) initialMachine) = some 16 := by decide +kernel
private theorem r1 : cell 1 (run (allocationStage.code ++ wrongStage.code) initialMachine) = some 19 := by decide +kernel
private theorem r17 : cell 17 (run (allocationStage.code ++ wrongStage.code) initialMachine) = some 8 := by decide +kernel
private theorem r18 : cell 18 (run (allocationStage.code ++ wrongStage.code) initialMachine) = some 9 := by decide +kernel
private theorem r20 : cell 20 (run (allocationStage.code ++ wrongStage.code) initialMachine) = some 4 := by decide +kernel
private theorem r0 : cell 0 (run (allocationStage.code ++ wrongStage.code) initialMachine) = some 21 := by decide +kernel

/-- The negative also checks the complete vector, including unchanged cells. -/
theorem recapture_ordered : [4,2,3,1,17,18,20,0].mapM
    (fun n => cell n (run (allocationStage.code ++ wrongStage.code) initialMachine)) =
      some [8,16,16,19,8,9,4,21] := by
  simp only [List.mapM_cons, List.mapM_nil, r4, r2, r3, r1, r17, r18, r20, r0]
  rfl

/-- Neither successful prefix is the failing stage in the actual third-stage
revert/panic runs. This is a target control as well as wrong_stage's source one. -/
theorem prefix_not_reverted (tail : List Word) :
    ∃ next, run prefixCode {initialMachine with stack := tail} = .ok next 0 ∧
      run prefixCode {initialMachine with stack := tail} ≠ .revert := by
  obtain ⟨mid, next, mb, nb, hall⟩ := shared_revert_maps
  have h := hall tail
  have ht : run prefixCode {initialMachine with stack := tail} = .ok {next with stack := tail} 0 := by
    change run (allocationStage.code ++ captureStage.code) _ = _
    rw [run_append_ok h.1]
    exact h.2.1
  exact ⟨_, ht, by rw [ht]; intro bad; cases bad⟩

/-- Coarse revert is non-injective on the actual source failures. Inferring
source failure identity from it is invalid. No ABI-byte theorem is asserted. -/
theorem coarse_not_source_identity (tail : List Word) :
    run (allocationStage.code ++ (captureStage.code ++ panicStage.code))
      {initialMachine with stack := tail} =
    run (allocationStage.code ++ (captureStage.code ++ TripleFailures.third.code))
      {initialMachine with stack := tail} ∧
    panicProg.run CaptureControls.afterCapture ≠
      TripleFailures.badAfterCapture.run CaptureControls.afterCapture := by
  constructor
  · rw [panic_reached tail, TripleFailures.third_reached tail]
  · rw [panic_source.2, TripleFailures.third_source]
    intro h
    cases h

theorem divergence_separate (tail : List Word) :
    run (allocationStage.code ++ (captureStage.code ++ DivergenceControls.lastSpin.code))
      {initialMachine with stack := tail} ≠
    run (allocationStage.code ++ (captureStage.code ++ panicStage.code))
      {initialMachine with stack := tail} := by
  rw [DivergenceControls.third tail, panic_reached tail]
  intro h
  cases h

end Solidity.Backend.Passes.RevertControls
