import Solidity.Backend.Passes.FreshBooleanPrefix
import Solidity.Backend.Passes.SourceTerminalFailure

/-! The fully joined fresh allocating/provisioning prefix reaches the real
captured effect and internal revert. All four successful maps precede tails. -/
namespace Solidity.Backend.Passes.FreshBooleanFailure
open Evm Evm.Memory Evm.Compiler
open Controls.Fixture
open FixedBooleanSequence FreshBooleanPrefix
open ReferenceControls (Γb state initializeBool branchThenRead)

def prefixProgram (b : Bool) : Prog C [] Captured :=
  ReachabilityControls.populatedBuilder.join ((initializeBool b).join (branchThenRead.join capturePrefix))
def wholeProgram (b : Bool) : Prog C [] Final := (prefixProgram b).join badObserve
def prefixCode (b : Bool) : List Instr :=
  population.code ++ ((initializer b).code ++ (receiver.code ++ captureStage.code))
def wholeCode (b : Bool) : List Instr := prefixCode b ++ badStage.code
def rightCode (b : Bool) : List Instr :=
  population.code ++ ((initializer b).code ++ (receiver.code ++ (captureStage.code ++ badStage.code)))

theorem source_prefix (b : Bool) :
    (prefixProgram b).run initial =
      .ok ⟨(afterCapture b).st,sourcePopulation.ext.trans
        ((List.prefix_refl _).trans ((middle b).ext.trans (afterCapture b).ext))⟩ := by
  have body : (branchThenRead.join capturePrefix).run (state b) =
      .ok ⟨(afterCapture b).st,(middle b).ext.trans (afterCapture b).ext⟩ := by
    rw [DeferredSource.join_run]
    simp only [TRun.seq,middle_source,capture_source,Except.map]
  exact (triple_source_success initial population_source (initialized_source b) body).2

theorem source_revert : (wholeProgram true).run initial = .error .revert :=
  (joined_halt_iff initial .revert).mpr (.inr ⟨_,source_prefix true,actual_source_failure⟩)

theorem source_right_revert :
    (ReachabilityControls.populatedBuilder.join ((initializeBool true).join
      (branchThenRead.join (capturePrefix.join badObserve)))).run initial = .error .revert := by
  simpa only [wholeProgram,prefixProgram,typed_sequencing_assoc] using source_revert

theorem capture_link (b : Bool) (base : Nat → Fin W) (m : Machine) :
    MappedBoundaryLink (.memory receiver) (.memory captureStage) 1 128 base (state b) m :=
  memory_nonallocating_mapped_link receiver captureStage (by decide +kernel) (by decide +kernel)

theorem observation_link (b : Bool) (base : Nat → Fin W) (m : Machine) :
    MappedBoundaryLink (.memory captureStage) (.memory badStage) 1 128 base (middle b).st m :=
  memory_nonallocating_mapped_link captureStage badStage (by decide +kernel) (by decide +kernel)

/-- No initial representation premise is assumed here: the real empty-heap
Input and actual allocating run produce every reached Input/map. -/
theorem pipeline_shared :
    ∃ pb : Nat → Fin W, ∀ b : Bool,
    ∃ (ib rb cb : Nat → Fin W) (mid captured : Machine), ∀ tail,
      (Compilation.memory population).Input 1 128 initialBase initial {initialMachine with stack := tail} ∧
      run population.code {initialMachine with stack := tail} = .ok {populatedTarget with stack := tail} 0 ∧
      MappedOutput (.memory population) 1 128 initialBase initial {initialMachine with stack := tail}
        σ {populatedTarget with stack := tail} pb ∧
      MappedBoundaryLink (.memory population) (.memory (provisioner b)) 1 128 initialBase initial
        {initialMachine with stack := tail} ∧
      (Compilation.memory (initializer b)).Input 1 128 pb σ {populatedTarget with stack := tail} ∧
      run (initializer b).code {populatedTarget with stack := tail} = .ok {(runtimeInput b) with stack := tail} 0 ∧
      MappedOutput (.memory (initializer b)) 1 128 pb σ {populatedTarget with stack := tail}
        (state b) {(runtimeInput b) with stack := tail} ib ∧
      MappedBoundaryLink (.memory (initializer b)) (.memory receiver) 1 128 pb σ
        {populatedTarget with stack := tail} ∧
      (Compilation.memory receiver).Input 1 128 ib (state b) {(runtimeInput b) with stack := tail} ∧
      run receiver.code {(runtimeInput b) with stack := tail} = .ok {mid with stack := tail} 0 ∧
      MappedOutput (.memory receiver) 1 128 ib (state b) {(runtimeInput b) with stack := tail}
        (middle b).st {mid with stack := tail} rb ∧
      MappedBoundaryLink (.memory receiver) (.memory captureStage) 1 128 ib (state b)
        {(runtimeInput b) with stack := tail} ∧
      (Compilation.memory captureStage).Input 1 128 rb (middle b).st {mid with stack := tail} ∧
      run captureStage.code {mid with stack := tail} = .ok {captured with stack := tail} 0 ∧
      MappedOutput (.memory captureStage) 1 128 rb (middle b).st {mid with stack := tail}
        (afterCapture b).st {captured with stack := tail} cb ∧
      MappedBoundaryLink (.memory captureStage) (.memory badStage) 1 128 rb (middle b).st
        {mid with stack := tail} ∧
      (Compilation.memory badStage).Input 1 128 cb (afterCapture b).st {captured with stack := tail} ∧
      run (prefixCode b) {initialMachine with stack := tail} = .ok {captured with stack := tail} 0 := by
  obtain ⟨pb,hprovision⟩ := provisioning_shared
  refine ⟨pb,?_⟩
  intro b
  obtain ⟨ib,hp⟩ := hprovision b
  obtain ⟨_,_,_,_,_,_,_,_,hi⟩ := hp []
  have ri : (Compilation.memory receiver).Input 1 128 ib (state b) (runtimeInput b) :=
    (compilation_input_stack_iff (.memory receiver) []).mp hi
  have empty : (runtimeInput b).stack = [] := by
    simpa only [runtimeInput,writeMachine] using populated_stack
  obtain ⟨rb,cb,mid,captured,_,_,_,hall⟩ :=
    compilation_pair_shared (.memory receiver) (.memory captureStage) ri empty
      (capture_link b ib (runtimeInput b)) (by decide +kernel) (by decide +kernel)
      (middle_source b) (capture_source b)
  refine ⟨ib,rb,cb,mid,captured,?_⟩
  intro tail
  obtain ⟨ip,hpop,ma,link1,ii,hinit,mi,link2,ir⟩ := hp tail
  obtain ⟨_,hm,ic,hn,hbody,mr,mc⟩ := hall tail
  have mr' : MappedOutput (.memory receiver) 1 128 ib (state b) {(runtimeInput b) with stack := tail}
      (middle b).st {mid with stack := tail} rb := by
    simpa only [receiver.cert.pushes_zero,Nat.add_zero] using mr
  have mc' : MappedOutput (.memory captureStage) 1 128 rb (middle b).st {mid with stack := tail}
      (afterCapture b).st {captured with stack := tail} cb := by
    simpa only [receiver.cert.pushes_zero,captureStage.cert.pushes_zero,Nat.add_zero] using mc
  have ic' : (Compilation.memory captureStage).Input 1 128 rb (middle b).st {mid with stack := tail} := by
    simpa only [receiver.cert.pushes_zero,Nat.add_zero] using ic
  have hn' : run captureStage.code {mid with stack := tail} = .ok {captured with stack := tail} 0 := hn
  have hm' : run receiver.code {(runtimeInput b) with stack := tail} = .ok {mid with stack := tail} 0 := hm
  have io : (Compilation.memory badStage).Input 1 128 cb (afterCapture b).st {captured with stack := tail} := by
    simpa only [captureStage.cert.pushes_zero,Nat.add_zero] using
      observation_link b rb {mid with stack := tail} (afterCapture b) {captured with stack := tail}
        cb (capture_source b) hn' mc'
  exact ⟨ip,hpop,ma,link1,ii,hinit,mi,link2,ir,hm',mr',
    capture_link b ib {(runtimeInput b) with stack := tail},ic',hn',mc',
    observation_link b rb {mid with stack := tail},io,by
      unfold prefixCode
      rw [run_append_ok hpop,run_append_ok hinit,run_append_ok hm']
      exact hn'⟩

theorem fresh_revert (tail : List Word) :
    (wholeProgram true).run initial = .error .revert ∧
    run (wholeCode true) {initialMachine with stack := tail} = .revert ∧
    run (rightCode true) {initialMachine with stack := tail} = .revert := by
  obtain ⟨pb,hb⟩ := pipeline_shared
  obtain ⟨ib,rb,cb,mid,captured,hall⟩ := hb true
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,hi,hprefix⟩ := hall tail
  have failed : run badStage.code {captured with stack := tail} = .revert :=
    (compilation_revert_iff (.memory badStage) hi (by decide +kernel)).mpr (.inl actual_source_failure)
  have terminal : run (wholeCode true) {initialMachine with stack := tail} = .revert := by
    unfold wholeCode
    rw [run_append_ok hprefix]
    exact failed
  exact ⟨source_revert,terminal,by simpa only [wholeCode,prefixCode,rightCode,List.append_assoc] using terminal⟩


/-- A single inhabited witness exposes all successful Inputs, code runs,
selected maps and physical links AND the actual joined failure. There is
no prefix/agreement premise supplied by the caller. -/
theorem fresh_failure_witness :
    ∃ (pb ib rb cb : Nat → Fin W) (mid captured : Machine),
      (wholeProgram true).run initial = .error .revert ∧ ∀ tail,
      (Compilation.memory population).Input 1 128 initialBase initial {initialMachine with stack := tail} ∧
      run population.code {initialMachine with stack := tail} = .ok {populatedTarget with stack := tail} 0 ∧
      MappedOutput (.memory population) 1 128 initialBase initial {initialMachine with stack := tail}
        σ {populatedTarget with stack := tail} pb ∧
      MappedBoundaryLink (.memory population) (.memory (provisioner true)) 1 128 initialBase initial
        {initialMachine with stack := tail} ∧
      (Compilation.memory (initializer true)).Input 1 128 pb σ {populatedTarget with stack := tail} ∧
      run (initializer true).code {populatedTarget with stack := tail} = .ok {(runtimeInput true) with stack := tail} 0 ∧
      MappedOutput (.memory (initializer true)) 1 128 pb σ {populatedTarget with stack := tail}
        (state true) {(runtimeInput true) with stack := tail} ib ∧
      MappedBoundaryLink (.memory (initializer true)) (.memory receiver) 1 128 pb σ
        {populatedTarget with stack := tail} ∧
      (Compilation.memory receiver).Input 1 128 ib (state true) {(runtimeInput true) with stack := tail} ∧
      run receiver.code {(runtimeInput true) with stack := tail} = .ok {mid with stack := tail} 0 ∧
      MappedOutput (.memory receiver) 1 128 ib (state true) {(runtimeInput true) with stack := tail}
        (middle true).st {mid with stack := tail} rb ∧
      MappedBoundaryLink (.memory receiver) (.memory captureStage) 1 128 ib (state true)
        {(runtimeInput true) with stack := tail} ∧
      (Compilation.memory captureStage).Input 1 128 rb (middle true).st {mid with stack := tail} ∧
      run captureStage.code {mid with stack := tail} = .ok {captured with stack := tail} 0 ∧
      MappedOutput (.memory captureStage) 1 128 rb (middle true).st {mid with stack := tail}
        (afterCapture true).st {captured with stack := tail} cb ∧
      MappedBoundaryLink (.memory captureStage) (.memory badStage) 1 128 rb (middle true).st
        {mid with stack := tail} ∧
      (Compilation.memory badStage).Input 1 128 cb (afterCapture true).st {captured with stack := tail} ∧
      run (prefixCode true) {initialMachine with stack := tail} = .ok {captured with stack := tail} 0 ∧
      badObserve.run (afterCapture true).st = .error .revert ∧
      run badStage.code {captured with stack := tail} = .revert ∧
      run (wholeCode true) {initialMachine with stack := tail} = .revert ∧
      run (rightCode true) {initialMachine with stack := tail} = .revert := by
  obtain ⟨pb,hb⟩ := pipeline_shared
  obtain ⟨ib,rb,cb,mid,captured,hall⟩ := hb true
  refine ⟨pb,ib,rb,cb,mid,captured,source_revert,?_⟩
  intro tail
  obtain ⟨ip,hp,mp,l1,ii,hi,mi,l2,ir,hr,mr,l3,ic,hc,mc,l4,io,hprefix⟩ := hall tail
  have failed : run badStage.code {captured with stack := tail} = .revert :=
    (compilation_revert_iff (.memory badStage) io (by decide +kernel)).mpr (.inl actual_source_failure)
  have terminal : run (wholeCode true) {initialMachine with stack := tail} = .revert := by
    unfold wholeCode
    rw [run_append_ok hprefix]
    exact failed
  exact ⟨ip,hp,mp,l1,ii,hi,mi,l2,ir,hr,mr,l3,ic,hc,mc,l4,io,hprefix,
    actual_source_failure,failed,terminal,by
      simpa only [wholeCode,prefixCode,rightCode,List.append_assoc] using terminal⟩

private theorem opposite_some :
    (badObserve.run (afterCapture false).st).toOption.isSome = true := by decide +kernel
noncomputable def oppositeResult : Solidity.Out C (afterCapture false).st.H Final :=
  (badObserve.run (afterCapture false).st).toOption.get opposite_some

private theorem source_get {Γ Δ : Ctx} {τ : State C Γ} {P : Prog C Γ Δ}
    {o : Solidity.Out C τ.H Δ} (hx : some o = (P.run τ).toOption) : P.run τ = .ok o := by
  cases hs : P.run τ with
  | ok value => rw [hs] at hx; exact congrArg Except.ok (Option.some.inj hx).symm
  | error e => rw [hs] at hx; cases hx

theorem opposite_source : badObserve.run (afterCapture false).st = .ok oppositeResult :=
  source_get (Option.some_get opposite_some)

/-- The opposite Boolean uses the SAME receiver/capture/observation stages.
Its fifth selected map and actual result also precede every saved tail. -/
theorem fresh_opposite_shared :
    ∃ (pb ib rb cb ob : Nat → Fin W) (mid captured out : Machine), ∀ tail,
      (Compilation.memory population).Input 1 128 initialBase initial {initialMachine with stack := tail} ∧
      run population.code {initialMachine with stack := tail} = .ok {populatedTarget with stack := tail} 0 ∧
      MappedOutput (.memory population) 1 128 initialBase initial {initialMachine with stack := tail}
        σ {populatedTarget with stack := tail} pb ∧
      MappedBoundaryLink (.memory population) (.memory (provisioner false)) 1 128 initialBase initial
        {initialMachine with stack := tail} ∧
      (Compilation.memory (initializer false)).Input 1 128 pb σ {populatedTarget with stack := tail} ∧
      run (initializer false).code {populatedTarget with stack := tail} = .ok {(runtimeInput false) with stack := tail} 0 ∧
      MappedOutput (.memory (initializer false)) 1 128 pb σ {populatedTarget with stack := tail}
        (state false) {(runtimeInput false) with stack := tail} ib ∧
      MappedBoundaryLink (.memory (initializer false)) (.memory receiver) 1 128 pb σ
        {populatedTarget with stack := tail} ∧
      (Compilation.memory receiver).Input 1 128 ib (state false) {(runtimeInput false) with stack := tail} ∧
      run receiver.code {(runtimeInput false) with stack := tail} = .ok {mid with stack := tail} 0 ∧
      MappedOutput (.memory receiver) 1 128 ib (state false) {(runtimeInput false) with stack := tail}
        (middle false).st {mid with stack := tail} rb ∧
      MappedBoundaryLink (.memory receiver) (.memory captureStage) 1 128 ib (state false)
        {(runtimeInput false) with stack := tail} ∧
      (Compilation.memory captureStage).Input 1 128 rb (middle false).st {mid with stack := tail} ∧
      run captureStage.code {mid with stack := tail} = .ok {captured with stack := tail} 0 ∧
      MappedOutput (.memory captureStage) 1 128 rb (middle false).st {mid with stack := tail}
        (afterCapture false).st {captured with stack := tail} cb ∧
      MappedBoundaryLink (.memory captureStage) (.memory badStage) 1 128 rb (middle false).st
        {mid with stack := tail} ∧
      (Compilation.memory badStage).Input 1 128 cb (afterCapture false).st {captured with stack := tail} ∧
      run (prefixCode false) {initialMachine with stack := tail} = .ok {captured with stack := tail} 0 ∧
      run badStage.code {captured with stack := tail} = .ok {out with stack := tail} 0 ∧
      MappedOutput (.memory badStage) 1 128 cb (afterCapture false).st {captured with stack := tail}
        oppositeResult.st {out with stack := tail} ob ∧
      run (wholeCode false) {initialMachine with stack := tail} = .ok {out with stack := tail} 0 ∧
      run (rightCode false) {initialMachine with stack := tail} = .ok {out with stack := tail} 0 := by
  obtain ⟨pb,hb⟩ := pipeline_shared
  obtain ⟨ib,rb,cb,mid,captured,hall⟩ := hb false
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,hi,_⟩ := hall []
  obtain ⟨out,ob,_,_,hbad⟩ := compilation_success_shared_mapped (.memory badStage)
    hi (by decide +kernel) opposite_source
  refine ⟨pb,ib,rb,cb,ob,mid,captured,out,?_⟩
  intro tail
  obtain ⟨ip,hp,mp,l1,ii,hi,mi,l2,ir,hm,mr,l3,ic,hc,mc,l4,io,hprefix⟩ := hall tail
  obtain ⟨hr,mo⟩ := hbad tail
  have hr' : run badStage.code {captured with stack := tail} = .ok {out with stack := tail} 0 := hr
  have mo' : MappedOutput (.memory badStage) 1 128 cb (afterCapture false).st {captured with stack := tail}
      oppositeResult.st {out with stack := tail} ob := by
    simpa only [badStage.cert.pushes_zero,Nat.add_zero] using mo
  have terminal : run (wholeCode false) {initialMachine with stack := tail} = .ok {out with stack := tail} 0 := by
    unfold wholeCode
    rw [run_append_ok hprefix]
    exact hr'
  exact ⟨ip,hp,mp,l1,ii,hi,mi,l2,ir,hm,mr,l3,ic,hc,mc,l4,io,hprefix,hr',mo',terminal,by
    simpa only [wholeCode,prefixCode,rightCode,List.append_assoc] using terminal⟩

theorem fresh_opposite_source :
    (wholeProgram false).run initial =
      .ok ⟨oppositeResult.st,
        (sourcePopulation.ext.trans ((List.prefix_refl _).trans
          ((middle false).ext.trans (afterCapture false).ext))).trans oppositeResult.ext⟩ := by
  rw [wholeProgram,DeferredSource.join_run]
  simp only [TRun.seq,source_prefix,opposite_source,Except.map]

/-- Concrete reached cost5 comes only from the real population. All later
zero-cost outputs extend its selected map; allocator growth is composed
from the SAME four mapped outputs, not a substituted initial address map. -/
theorem prefix_resources (b : Bool) :
    ∃ (pb ib rb cb : Nat → Fin W) (mid captured : Machine), ∀ tail,
      MappedOutput (.memory population) 1 128 initialBase initial {initialMachine with stack := tail}
        σ {populatedTarget with stack := tail} pb ∧
      MappedOutput (.memory (initializer b)) 1 128 pb σ {populatedTarget with stack := tail}
        (state b) {(runtimeInput b) with stack := tail} ib ∧
      MappedOutput (.memory receiver) 1 128 ib (state b) {(runtimeInput b) with stack := tail}
        (middle b).st {mid with stack := tail} rb ∧
      MappedOutput (.memory captureStage) 1 128 rb (middle b).st {mid with stack := tail}
        (afterCapture b).st {captured with stack := tail} cb ∧
      BaseExtends σ.H pb cb ∧
      cb CompileExamples.r0.id = pb CompileExamples.r0.id ∧
      cb CompileExamples.r1.id = pb CompileExamples.r1.id ∧
      GrowsAllocator 1 128 5 initial initialBase {initialMachine with stack := tail}
        (afterCapture b).st cb {captured with stack := tail} := by
  obtain ⟨pb,hb⟩ := pipeline_shared
  obtain ⟨ib,rb,cb,mid,captured,hall⟩ := hb b
  refine ⟨pb,ib,rb,cb,mid,captured,?_⟩
  intro tail
  obtain ⟨_,_,mp,_,_,_,mi,_,_,_,mr,_,_,_,mc,_,_,_⟩ := hall tail
  have base : BaseExtends σ.H pb cb :=
    BaseExtends.trans (List.prefix_refl _) mi.2.1 (BaseExtends.trans (middle b).ext mr.2.1 mc.2.1)
  have growth := GrowsAllocator.comp mp.2.2
    (GrowsAllocator.comp mi.2.2 (GrowsAllocator.comp mr.2.2 mc.2.2))
  have cp : population.cert.cost initial = 5 := by decide +kernel
  have ci : (initializer b).cert.cost σ = 0 := by cases b <;> decide +kernel
  have cr : receiver.cert.cost (state b) = 0 := by cases b <;> decide +kernel
  have cc : captureStage.cert.cost (middle b).st = 0 := by cases b <;> decide +kernel
  exact ⟨mp,mi,mr,mc,base,base CompileExamples.r0,base CompileExamples.r1,by
    simpa only [cp,ci,cr,cc,Nat.add_zero] using growth⟩

end Solidity.Backend.Passes.FreshBooleanFailure
