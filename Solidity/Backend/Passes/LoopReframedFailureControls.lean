import Solidity.Backend.Passes.ReframedFailureWitness
import Solidity.Backend.Passes.ReframedLoops
import Solidity.Backend.Passes.LoopScopeTerminal

/-! DRAFT / UNVALIDATED. Actual typed loop + memory-read guard, with a
wrong-order success control. No intrinsic source or target semantics is replaced.
No full independent Source frontend/admission theorem is claimed. -/
namespace Solidity.Backend.Passes.LoopReframedFailureControls
open Evm Evm.Memory Evm.Compiler
open MemoryCallControls (C A initial base machine)
open LoopScopeControls
open LoopScopeTrace (preparedTarget loopTarget preparation_target loop_target)

def oldValue : Val C LoopScopeControls.Γ .bool :=
  .binop .eqB rfl rfl
    (.readMem (.index .dyn (.var .here rfl) (.simple (.lit 0 rfl))))
    (.simple (.lit 7 rfl))

def demandOld : Prog C LoopScopeControls.Γ LoopScopeControls.Γ :=
  .cons (.require oldValue) .nil

def afterCheck : CompiledProg 1 enclosed.frag demandOld :=
  (Memory.compileProg 1 _ demandOld).get (by decide +kernel)

def beforeCheck : CompiledProg 1 preparation.frag demandOld :=
  (Memory.compileProg 1 _ demandOld).get (by decide +kernel)

private def beforeValue : CompiledVal 1 preparation.frag oldValue :=
  (Memory.compileVal 1 _ oldValue).get (by decide +kernel)

attribute [local irreducible] beforeValue afterCheck beforeCheck LoopScopeControls.preparation
  LoopScopeControls.enclosed LoopScopeControls.prepared LoopScopeControls.loopOut
  LoopScopeTrace.preparedTarget LoopScopeTrace.loopTarget

theorem before_source : demandOld.run prepared.st =
    .ok ⟨prepared.st,List.prefix_refl _⟩ := by with_unfolding_all rfl

theorem after_source : demandOld.run loopOut.st = .error .revert := by
  with_unfolding_all rfl

theorem after_link {selected : Nat → Fin W} {mid : Machine} :
    ReframedLink checked (.memory afterCheck) 1 128 5 selected prepared.st mid :=
  loop_scopes_shrinking_link enclosed afterCheck (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Actual successful preparation and positive-cost loop witnesses, followed
by a failing Input at5. All maps and Cost/ext precede tails. No failure output. -/
theorem reached_prefix_failure :
    ∃ (mb nb : Nat → Fin W) (amount : Nat) (ext : prepared.st.H <+: loopOut.st.H),
      Memory.LoopScopes.Cost enclosed.cert prepared.st ⟨loopOut.st,ext⟩ amount ∧
      prepare.run initial = .ok prepared ∧ wrapped.run prepared.st = .ok loopOut ∧
      demandOld.run loopOut.st = .error .revert ∧ ∀ tail,
      (Compilation.memory preparation).Input 1 128 base initial {machine with stack := tail} ∧
      run preparation.code {machine with stack := tail} = .ok {preparedTarget with stack := tail} 0 ∧
      MappedOutput (.memory preparation) 1 128 base initial {machine with stack := tail}
        prepared.st {preparedTarget with stack := tail} mb ∧
      checked.Input 1 128 mb prepared.st {preparedTarget with stack := tail} ∧
      run enclosed.code {preparedTarget with stack := tail} = .ok {loopTarget with stack := tail} 0 ∧
      MappedOutput checked 1 128 mb prepared.st {preparedTarget with stack := tail}
        loopOut.st {loopTarget with stack := tail} nb ∧
      (Compilation.memory afterCheck).Input 1 5 nb loopOut.st {loopTarget with stack := tail} ∧
      run afterCheck.code {loopTarget with stack := tail} = .revert ∧
      run (preparation.code ++ (enclosed.code ++ afterCheck.code))
        {machine with stack := tail} = .revert ∧
      run ((preparation.code ++ enclosed.code) ++ afterCheck.code)
        {machine with stack := tail} = .revert := by
  obtain ⟨mb,nb,prefixes⟩ := LoopScopeTerminal.prefix_tails
  obtain ⟨hp0,_,ha0,canonicalOutput⟩ := prefixes []
  have loopInput0 : checked.Input 1 128 mb prepared.st {preparedTarget with stack := []} :=
    LoopScopeApplication.into_scope prepared {preparedTarget with stack := []} mb
      prepared_source hp0 ha0
  rcases canonicalOutput with ⟨amount,ext,cost,state,baseExt,growth⟩
  refine ⟨mb,nb,amount,ext,cost,prepared_source,wrapped_source,after_source,?_⟩
  intro tail
  obtain ⟨hp,hl,ha,hb⟩ := prefixes tail
  have loopInput : checked.Input 1 128 mb prepared.st
      {preparedTarget with stack := tail} := compilation_input_stack checked loopInput0 tail
  have step : (Compilation.memory afterCheck).Input
      (1 + Evm.Prog.pushes wrapped) 5 nb loopOut.st {loopTarget with stack := tail} := after_link (selected := mb) (mid := {preparedTarget with stack := tail})
    loopOut {loopTarget with stack := tail} nb wrapped_source hl
    (by simpa only [enclosed.cert.pushes_zero,Nat.add_zero] using hb)
  have input : (Compilation.memory afterCheck).Input 1 5 nb loopOut.st
      {loopTarget with stack := tail} := by
    simpa only [enclosed.cert.pushes_zero,Nat.add_zero] using step
  have failed : run afterCheck.code {loopTarget with stack := tail} = .revert := (compilation_revert_iff (.memory afterCheck) input
    (by decide +kernel)).mpr (.inl after_source)
  have whole : run (preparation.code ++ (enclosed.code ++ afterCheck.code))
      {machine with stack := tail} = .revert := by
    rw [run_append_ok hp,run_append_ok hl]
    exact failed
  exact ⟨compilation_input_stack (.memory preparation) LoopScopeApplication.preparation_input tail,
    hp,ha,loopInput,hl,hb,input,failed,whole,
    by simpa only [List.append_assoc] using whole⟩

theorem joined_source_failure :
    (prepare.join (wrapped.join demandOld)).run initial = .error .revert ∧
    ((prepare.join wrapped).join demandOld).run initial = .error .revert := by
  have whole : (prepare.join (wrapped.join demandOld)).run initial = .error .revert :=
    (joined_halt_iff initial .revert).mpr (.inr ⟨prepared,prepared_source,
      (joined_halt_iff prepared.st .revert).mpr (.inr ⟨loopOut,wrapped_source,after_source⟩)⟩)
  exact ⟨whole,by simpa only [typed_sequencing_assoc] using whole⟩

/-- The same guard passes before alias rebinding, and does not modify the
actual machine. This is a candidate proof, not a precomputed observation oracle. -/
private theorem guard_code : beforeCheck.code = beforeValue.code ++ assertTop := by
  unfold beforeCheck beforeValue
  with_unfolding_all rfl

private theorem before_value : oldValue.evalT prepared.st = .ok true := by
  with_unfolding_all rfl

theorem before_target : run beforeCheck.code preparedTarget = .ok preparedTarget 0 := by
  obtain ⟨mb,_,ha,_⟩ := LoopScopeTerminal.prefix_relations
  have correct : ValOutT .bool (oldValue.evalT prepared.st)
      (run beforeValue.code preparedTarget) preparedTarget :=
    beforeValue.cert.correct ha.1
  rcases correct with ⟨value,word,evaluated,represented,target⟩ | ⟨failed,_⟩
  · have same : value = true := Except.ok.inj (evaluated.symm.trans before_value)
    subst value
    obtain rfl := represented.bool_inv
    rw [guard_code,run_append_skip target]
    rfl
  · rw [before_value] at failed
    cases failed

theorem before_target_tail (tail : List Word) :
    run beforeCheck.code {preparedTarget with stack := tail} =
      .ok {preparedTarget with stack := tail} 0 := by
  have empty : preparedTarget.stack = [] := by decide +kernel
  have h : run beforeCheck.code (appendTail preparedTarget tail) =
      appendOut tail (run beforeCheck.code preparedTarget) := run_tail beforeCheck.code preparedTarget tail
    (by rw [before_target]; intro impossible; cases impossible)
  simpa only [before_target,appendOut,appendTail,empty,List.nil_append] using h

theorem wrong_order_target (tail : List Word) :
    run (preparation.code ++ (beforeCheck.code ++ enclosed.code))
      {machine with stack := tail} = .ok {loopTarget with stack := tail} 0 := by
  obtain ⟨_,_,prefixes⟩ := LoopScopeTerminal.prefix_tails
  obtain ⟨hp,hl,_,_⟩ := prefixes tail
  rw [run_append_ok hp,run_append_ok (before_target_tail tail)]
  exact hl

theorem wrong_order_source :
    (prepare.join (demandOld.join wrapped)).run initial =
      .ok ⟨loopOut.st,prepared.ext.trans loopOut.ext⟩ := by
  have inner : (demandOld.join wrapped).run prepared.st = .ok loopOut := by
    rw [DeferredSource.join_run]
    simp only [TRun.seq,before_source,wrapped_source,Except.map]
  rw [DeferredSource.join_run]
  simp only [TRun.seq,prepared_source,inner,Except.map]

theorem wrong_order_distinct (tail : List Word) :
    run (preparation.code ++ (enclosed.code ++ afterCheck.code))
      {machine with stack := tail} ≠
    run (preparation.code ++ (beforeCheck.code ++ enclosed.code))
      {machine with stack := tail} := by
  obtain ⟨mb,nb,amount,ext,facts⟩ := reached_prefix_failure
  have whole : run (preparation.code ++ (enclosed.code ++ afterCheck.code))
      {machine with stack := tail} = .revert :=
    (facts.2.2.2.2 tail).2.2.2.2.2.2.2.2.1
  rw [whole,wrong_order_target]
  intro impossible
  cases impossible

private def observed (m : Machine) : Option (List Nat) :=
  (m.stack ++ LoopScopeTrace.addresses.map m.mem).mapM fun word =>
    match word with | .val n => some n.val | .slot _ => none

private def observedRun : Evm.Out → Option (List Nat)
  | .ok m 0 => observed m
  | _ => none

/-- ALL original loop observations are retained, including both saved words,
cursor, sentinel, every local/alias, old element, new length and both elements. -/
theorem complete_wrong_order_vector :
    observedRun (run (preparation.code ++ (beforeCheck.code ++ enclosed.code))
      {machine with stack := [w[77],w[88]]}) =
      some [77,88,261,99,256,0,258,258,1,7,2,0,0] := by
  rw [wrong_order_target]
  exact LoopScopeTrace.loop_vector

theorem corrupt_saved_tail :
    observedRun (run (preparation.code ++ (beforeCheck.code ++ enclosed.code))
      {machine with stack := [w[88],w[77]]}) ≠
      some [77,88,261,99,256,0,258,258,1,7,2,0,0] := by
  rw [wrong_order_target]
  decide +kernel


/-- The original code/local bound remains mandatory even for this guard. -/
theorem insufficient_guard_frame {selected : Nat → Fin W}
    {σ : State C LoopScopeControls.Γ} {m : Machine} :
    ¬ (Compilation.memory afterCheck).Input 1 3 selected σ m := by
  intro input
  have room : 1 + frameNeedProg demandOld ≤ 3 := input.2.1
  have need : 1 + frameNeedProg demandOld = 4 := by decide +kernel
  omega

private theorem stale_pointer {target : Machine}
    (pointers : PointerRepr loopOut.st LoopScopeTrace.oldOnly 1 target)
    (observed : (match target.mem 3 with
      | .val value => some value.val | _ => none) = some 258) : False := by
  obtain ⟨ref,henv,hptr⟩ := pointers (.here : Idx LoopScopeControls.Γ (.mem A))
  have ids : (TEnv.get (.here : Idx LoopScopeControls.Γ (.mem A)) loopOut.st.env).map
      (·.id) = some ref.id := congrArg (Option.map (fun ref => ref.id)) henv
  rw [LoopScopeTrace.new_identity] at ids
  have id : ref.id = 1 := (Option.some.inj ids).symm
  have hcell : cellOf 1 (.here : Idx LoopScopeControls.Γ (.mem A)) = 3 := rfl
  rw [hcell, id] at hptr
  rw [hptr] at observed
  change (some 0 : Option Nat) = some 258 at observed
  cases observed

/-- A smaller frame does not make an old-only map represent the new alias. -/
theorem stale_guard_input_refused :
    ¬ (Compilation.memory afterCheck).Input 1 5 LoopScopeTrace.oldOnly
      loopOut.st loopTarget := by
  intro input
  apply stale_pointer input.1.pointers
  decide +kernel

theorem ordinary_revert_separate :
    demandOld.asserts = false ∧
    demandOld.run loopOut.st ≠ .error .panic ∧
    demandOld.run loopOut.st ≠ .error .diverge := by
  refine ⟨rfl,?_,?_⟩
  · rw [after_source]
    intro impossible
    cases impossible
  · rw [after_source]
    intro impossible
    cases impossible

end Solidity.Backend.Passes.LoopReframedFailureControls
