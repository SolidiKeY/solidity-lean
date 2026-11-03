import Solidity.Backend.Passes.RuntimeReturnFailure
import Solidity.Backend.Passes.RuntimeReturnCaptureControls

/-! The actual call first returns seven. Its consumer then uses that returned
value as an array index, which reverts (length two). Capturing this expression
before the call instead succeeds at index zero. No post-revert map is given. -/
namespace Solidity.Backend.Passes.RuntimeReturnFailure.Controls
open Evm Evm.Memory
open Solidity.Backend.InternalFlow.RuntimeFrame
open V3CallProducer.Controls

def operand : Val P Γ .uint :=
  .readMem (.index .dyn (.var (.there .here) rfl) (.simple (.local .here)))
def valueCode : CompiledVal 0 selected.checked.frag operand :=
  ⟨readLocalValueCode 0 (.there .here) (Evm.compileVal 0 (.simple (.local .here))),
    .read (.there .here) rfl (.simple (.local .here)) _ (.core _ rfl)⟩
def suffix := CapturedValueStability.captureStage (.user "captured") operand valueCode
def code : List Instr := (V3CallProducer.plan selected 8 8).code ++ suffix.code
def cells : List Nat := [3,2,1,0,8,9,16,17,18,20,21]
def expected : List Word := [w[7],w[16],w[16],w[20],w[10],w[0],w[2],w[7],w[9],w[1],w[4]]

theorem evaluated : operand.evalT output = .error .revert := by
  first | rfl | with_unfolding_all rfl

theorem early_value : operand.evalT initial = .ok (uint 7 (by decide)) := by
  first | rfl | with_unfolding_all rfl

def instantiated : type_of% (capture_revert selected 8 8 flags positive_member
  ⟨output,List.prefix_refl _⟩ source_success (.user "captured") operand valueCode
  evaluated (by decide)) :=
  capture_revert selected 8 8 flags positive_member
    ⟨output,List.prefix_refl _⟩ source_success (.user "captured") operand valueCode
    evaluated (by decide)

theorem source_failure :
    (Prog.cons call (.cons (.declLocal .uint (.user "captured") (some operand)) .nil)).run
      initial = .error .revert :=
  instantiated.1

/-- Every original caller local, both aliases, both old array elements, the
independent object and protected arena words are observed BEFORE the failure.
The fresh capture local does not yet exist and has no asserted value. -/
theorem reached :
    ∃ (mid : Machine) (addresses : Nat → Fin W),
      StateRepr 1 0 16 selected.checked.frag output addresses mid ∧
      BaseExtends initial.H bases addresses ∧
      GrowsAllocator 0 16 ((V3CallProducer.plan selected 8 8).heapCost initial)
        initial bases machine output addresses mid ∧
      mid.stack = [w[77]] ∧ mid.mem 8 = w[10] ∧
      Footprint.Words 8 10 machine mid ∧
      cells.map mid.mem = expected ∧
      run (V3CallProducer.plan selected 8 8).code machine = .ok mid 0 ∧
      ∀ tail,
        suffix.Input 1 16 addresses output (appendTail mid tail) ∧
        run (V3CallProducer.plan selected 8 8).code (appendTail machine tail) =
          .ok (appendTail mid tail) 0 ∧
        run valueCode.code (appendTail mid tail) = .revert ∧
        run suffix.code (appendTail mid tail) = .revert ∧
        run code (appendTail machine tail) = .revert := by
  obtain ⟨mid,addresses,callRun,represented,stack,extension,growth,cursor,older,tails⟩ :=
    instantiated.2
  have returned := represented.core.vals (.here : Idx Γ (.val .uint))
  have returnedWord : mid.mem 3 = w[7] :=
    Restored.value_unique returned (ReprV.uint_of rfl)
  obtain ⟨after,success,afterStack,observed⟩ :=
    RuntimeReturnCapture.Controls.Fixture.ordered
  have successSuffix :
      run RuntimeReturnCapture.Controls.Fixture.suffix.code mid =
        .ok (writeMachine mid 4 w[7]) 0 := by
    rw [RuntimeReturnCapture.Controls.Fixture.suffix_instructions]
    change Evm.Out.ok (writeMachine mid 4 (mid.mem 3)) 0 = _
    rw [returnedWord]
  have successJoined :
      run RuntimeReturnCapture.Controls.Fixture.code machine =
        .ok (writeMachine mid 4 w[7]) 0 := by
    change run ((V3CallProducer.plan selected 8 8).code ++
      RuntimeReturnCapture.Controls.Fixture.suffix.code) machine = _
    rw [run_append_ok callRun]
    exact successSuffix
  have same : after = writeMachine mid 4 w[7] :=
    (Evm.Out.ok.inj (success.symm.trans successJoined)).1
  rw [same] at observed
  change [mid.mem 3,w[7],mid.mem 2,mid.mem 1,mid.mem 0,mid.mem 8,mid.mem 9,
    mid.mem 16,mid.mem 17,mid.mem 18,mid.mem 20,mid.mem 21] =
      RuntimeReturnCapture.Controls.Fixture.expected at observed
  have firstWord := (List.cons.inj observed).1
  have restWords := (List.cons.inj (List.cons.inj observed).2).2
  refine ⟨mid,addresses,represented,extension,growth,stack,cursor,older,?_,callRun,tails⟩
  change mid.mem 3 :: [mid.mem 2,mid.mem 1,mid.mem 0,mid.mem 8,mid.mem 9,
    mid.mem 16,mid.mem 17,mid.mem 18,mid.mem 20,mid.mem 21] = _
  rw [firstWord,restWords]
  rfl

theorem actual_target_failure : run code machine = .revert := by
  obtain ⟨mid,addresses,represented,extension,growth,stack,cursor,older,observed,actual,tails⟩ :=
    reached
  simpa only [appendTail,List.append_nil] using (tails []).2.2.2.2

/-- This failure is REACHED, not a failure of the call itself. -/
theorem wrong_failure_stage :
    run (V3CallProducer.plan selected 8 8).code machine ≠ .revert := by
  obtain ⟨mid,addresses,represented,extension,growth,stack,cursor,older,observed,actual,tails⟩ :=
    reached
  rw [actual]
  intro impossible
  cases impossible

/-- Moving the consuming capture before the call really succeeds at index0;
it is not the reached index7 failure, nor a whole reversed-call theorem. -/
theorem early_target :
    ∃ word, ReprV .uint (uint 7 (by decide)) word ∧
      run suffix.code machine = .ok (writeMachine machine 4 word) 0 := by
  let earlyCode : CompiledVal 0 F operand :=
    ⟨readLocalValueCode 0 (.there .here) (Evm.compileVal 0 (.simple (.local .here))),
      .read (.there .here) rfl (.simple (.local .here)) _ (.core _ rfl)⟩
  have sameCode : valueCode.code = earlyCode.code := rfl
  obtain ⟨word,repr,actual⟩ := value_success_tail earlyCode initial_repr early_value machine.stack
  have valueRun : run valueCode.code machine = .ok (machine.push word) 0 := by
    rw [sameCode]
    simpa only using actual
  refine ⟨word,repr,?_⟩
  simp only [suffix,CapturedValueStability.captureStage,Evm.Compiler.Compilation.code,List.append_nil]
  rw [run_append_ok valueRun]
  rfl

theorem stale_index :
    operand.evalT output ≠ .ok (uint 7 (by decide)) := by
  rw [evaluated]
  intro impossible
  cases impossible

theorem prefix_tail_negative (tail : List Word) :
    ∃ mid, run (V3CallProducer.plan selected 8 8).code (appendTail machine tail) =
      .ok (appendTail mid tail) 0 ∧
      (appendTail mid tail).stack ≠ w[78] :: tail := by
  obtain ⟨mid,addresses,represented,extension,growth,stack,cursor,older,observed,actual,tails⟩ :=
    reached
  refine ⟨mid,(tails tail).2.1,?_⟩
  simp only [appendTail,stack,List.cons_append,List.nil_append]
  intro same
  exact (by decide : (w[77] : Word) ≠ w[78]) (List.cons.inj same).1

end Solidity.Backend.Passes.RuntimeReturnFailure.Controls
