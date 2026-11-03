import Solidity.Backend.Passes.MemoryCompilerSequence
import Solidity.Backend.Passes.ReframedTripleControls
import Solidity.Backend.Passes.LoopScopeTerminal

/-! Real wrong-order failure: moving the existing consumer before allocation
performs TWO writes, then its second-element read reverts on the old length1
array. Prefix observations are retained; no post-failure state is invented. -/
namespace Solidity.Backend.Passes.ReframedTripleWrongOrder
open Evm Evm.Memory Evm.Compiler
open MemoryCallControls (C A initial base machine)
open LoopScopeControls
open LoopScopeTrace (preparedTarget preparation_target finalTarget)

def effects : Prog C LoopScopeControls.Γ LoopScopeControls.Γ :=
  .cons (.assignMem (.index .dyn (.var .here rfl) (.simple (.lit 0 rfl)))
    (.val (.binop .add rfl rfl
      (.readMem (.index .dyn (.var .here rfl) (.simple (.lit 0 rfl)))) (.simple (.lit 9 rfl)))))
  (.cons (.assignMem (.index .dyn (.var (.there (.there .here)) rfl) (.simple (.lit 0 rfl)))
    (.val (.binop .add rfl rfl
      (.readMem (.index .dyn (.var (.there (.there .here)) rfl) (.simple (.lit 0 rfl))))
      (.simple (.lit 1 rfl))))) .nil)

def readLast : Prog C LoopScopeControls.Γ LoopScopeControls.Ω :=
  .cons (.declLocal .uint (.user "observed")
    (some (.readMem (.index .dyn (.var .here rfl) (.simple (.lit 1 rfl)))))) .nil

theorem split_consumer : effects.join readLast = consume := rfl

def effectStage : CompiledProg 1 preparation.frag effects :=
  (Memory.compileProg 1 _ effects).get (by decide +kernel)
def readStage : CompiledProg 1 effectStage.frag readLast :=
  (Memory.compileProg 1 _ readLast).get (by decide +kernel)
def beforeLoop : Prog C LoopScopeControls.Γ LoopScopeControls.Γ :=
  .cons (.block consume) .nil
def blockStage : CompiledProg 1 preparation.frag beforeLoop :=
  (Memory.compileProg 1 _ beforeLoop).get (by decide +kernel)

noncomputable def affected : Solidity.Out C prepared.st.H LoopScopeControls.Γ :=
  (effects.run prepared.st).toOption.get (by decide +kernel)

private theorem source_get {Γ Δ : Ctx} {σ : State C Γ} {P : Prog C Γ Δ}
    {o : Solidity.Out C σ.H Δ} (h : some o = (P.run σ).toOption) : P.run σ = .ok o := by
  cases hs : P.run σ with
  | ok actual => rw [hs] at h; exact congrArg Except.ok (Option.some.inj h).symm
  | error error => rw [hs] at h; cases h

theorem effects_source : effects.run prepared.st = .ok affected :=
  source_get (Option.some_get _)

theorem read_source : readLast.run affected.st = .error .revert := by
  with_unfolding_all rfl

theorem consumer_before_loop_reverts : consume.run prepared.st = .error .revert := by
  rw [← split_consumer]
  exact (joined_halt_iff prepared.st .revert).mpr
    (.inr ⟨affected,effects_source,read_source⟩)

theorem before_loop_source : beforeLoop.run prepared.st = .error .revert := by
  have failed : (Stmt.block consume).run prepared.st = .error .revert := by
    change (consume.run prepared.st).map _ = .error .revert
    rw [consumer_before_loop_reverts]
    rfl
  exact Prog.run_cons_error failed

theorem wrong_source :
    (prepare.join (beforeLoop.join wrapped)).run initial = .error .revert :=
  (joined_halt_iff initial .revert).mpr (.inr ⟨prepared,prepared_source,
    (joined_halt_iff prepared.st .revert).mpr (.inl before_loop_source)⟩)

theorem first_link (entry : Machine) :
    ReframedLink (.memory preparation) (.memory effectStage)
      1 128 64 base initial entry :=
  memory_shrinking_link preparation effectStage (by decide) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

theorem second_link :
    ReachedReframedLink (.memory preparation) (.memory effectStage) (.memory readStage)
      1 128 64 5 base initial machine := by
  intro o mid selected _ _ _
  exact memory_shrinking_link effectStage readStage (by decide) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

private def okMachine : Evm.Out → Option Machine
  | .ok m 0 => some m
  | _ => none
private theorem target_get {result : Evm.Out} {m : Machine}
    (h : some m = okMachine result) : result = .ok m 0 := by
  cases result with
  | ok actual skip =>
    cases skip with
    | zero => exact congrArg (fun m => Evm.Out.ok m 0) (Option.some.inj h).symm
    | succ k => cases h
  | revert => cases h
  | fault => cases h

noncomputable def effectTarget : Machine :=
  (okMachine (run effectStage.code preparedTarget)).get (by decide +kernel)
theorem effects_target : run effectStage.code preparedTarget = .ok effectTarget 0 :=
  target_get (Option.some_get _)

/-- The new generic THREE-frame iff is inhabited by an actual reached
third failure after both nonempty successful effect prefixes. -/
theorem triple_reverts :
    run (preparation.code ++ (effectStage.code ++ readStage.code)) machine = .revert := by
  exact (compilation_reframed_triple_revert_iff
    (.memory preparation) (.memory effectStage) (.memory readStage)
    LoopScopeApplication.preparation_input (first_link machine) second_link
    (by decide +kernel) (by decide +kernel) (by decide +kernel)).mpr
      (.inr ⟨prepared,prepared_source,.inr ⟨affected,effects_source,.inl read_source⟩⟩)

theorem prefix_relations :
    ∃ (mb nb : Nat → Fin W), effectTarget.stack = [] ∧
      MappedOutput (.memory preparation) 1 128 base initial machine
        prepared.st preparedTarget mb ∧
      MappedOutput (.memory effectStage) 1 64 mb prepared.st preparedTarget
        affected.st effectTarget nb ∧
      (Compilation.memory readStage).Input 1 5 nb affected.st effectTarget := by
  obtain ⟨mb,_,ha,_⟩ := LoopScopeTerminal.prefix_relations
  have input := first_link machine prepared preparedTarget mb prepared_source preparation_target ha
  obtain ⟨actual,ht,stack,rep⟩ := compilation_success (.memory effectStage) input
    (by decide +kernel) effects_source
  have same : actual = effectTarget := (Evm.Out.ok.inj (ht.symm.trans effects_target)).1
  subst actual
  obtain ⟨nb,output⟩ := (mapped_output_iff (.memory effectStage) _ _ _ _ _ _ _).mp rep
  have full : MappedOutput (.memory effectStage) 1 64 mb prepared.st preparedTarget
      affected.st effectTarget nb := by
    simpa only [effectStage.cert.pushes_zero,Nat.add_zero] using output
  have link := memory_shrinking_link effectStage readStage
    (base := mb) (σ := prepared.st) (m := preparedTarget) (L := 1)
    (beforeFrame := 64) (afterFrame := 5)
    (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have readInput := link affected effectTarget nb effects_source effects_target
    (by simpa only [effectStage.cert.pushes_zero,Nat.add_zero] using full)
  refine ⟨mb,nb,stack.trans (by decide +kernel),ha,full,?_⟩
  simpa only [effectStage.cert.pushes_zero,Nat.add_zero] using readInput

/-- Maps and all reached non-stack effects precede tails. There is no
post-revert output map, machine, ABI payload or public-resource assertion. -/
theorem effects_before_failure :
    ∃ (mb nb : Nat → Fin W), ∀ tail,
      run preparation.code {machine with stack := tail} =
        .ok {preparedTarget with stack := tail} 0 ∧
      MappedOutput (.memory preparation) 1 128 base initial {machine with stack := tail}
        prepared.st {preparedTarget with stack := tail} mb ∧
      (Compilation.memory effectStage).Input 1 64 mb prepared.st {preparedTarget with stack := tail} ∧
      run effectStage.code {preparedTarget with stack := tail} =
        .ok {effectTarget with stack := tail} 0 ∧
      MappedOutput (.memory effectStage) 1 64 mb prepared.st {preparedTarget with stack := tail}
        affected.st {effectTarget with stack := tail} nb ∧
      (Compilation.memory readStage).Input 1 5 nb affected.st {effectTarget with stack := tail} ∧
      run readStage.code {effectTarget with stack := tail} = .revert ∧
      run (preparation.code ++ (effectStage.code ++ readStage.code))
        {machine with stack := tail} = .revert ∧
      run ((preparation.code ++ effectStage.code) ++ readStage.code)
        {machine with stack := tail} = .revert := by
  obtain ⟨mb,nb,empty,ha,output,readInput⟩ := prefix_relations
  have input := first_link machine prepared preparedTarget mb prepared_source preparation_target ha
  obtain ⟨_,_,preparationTails⟩ := LoopScopeTerminal.prefix_tails
  refine ⟨mb,nb,?_⟩
  intro tail
  have hp := (preparationTails tail).1
  have transported := run_tail effectStage.code preparedTarget tail
    (by rw [effects_target]; intro impossible; cases impossible)
  have he : run effectStage.code {preparedTarget with stack := tail} =
      .ok {effectTarget with stack := tail} 0 := by
    simpa only [effects_target,appendOut,appendTail,empty,
      show preparedTarget.stack = [] by decide +kernel,List.nil_append] using transported
  have ih := compilation_input_stack (.memory readStage) readInput tail
  have failed := (compilation_revert_iff (.memory readStage) ih
    (by decide +kernel)).mpr (.inl read_source)
  have whole : run (preparation.code ++ (effectStage.code ++ readStage.code))
      {machine with stack := tail} = .revert := by
    rw [run_append_ok hp,run_append_ok he]
    exact failed
  exact ⟨hp,mapped_output_stack (.memory preparation) ha tail tail,
    compilation_input_stack (.memory effectStage) input tail,he,
    mapped_output_stack (.memory effectStage) output tail tail,ih,failed,whole,
    by simpa only [List.append_assoc] using whole⟩

private theorem consumer_code :
    ∃ body : CompiledProg 1 preparation.frag consume,
      Memory.compileProg 1 preparation.frag consume = some body ∧
      body.code = effectStage.code ++ readStage.code := by
  have leftAccepted : Memory.compileProg 1 preparation.frag effects = some effectStage :=
    (Option.some_get _).symm
  have rightAccepted : Memory.compileProg 1 effectStage.frag readLast = some readStage :=
    (Option.some_get _).symm
  obtain ⟨body,accepted,_,code⟩ := memory_compile_join effectStage readStage leftAccepted rightAccepted
  exact ⟨body,accepted,code⟩

private theorem block_code :
    ∃ outer : CompiledProg 1 preparation.frag beforeLoop,
      Memory.compileProg 1 preparation.frag beforeLoop = some outer ∧
      outer.code = effectStage.code ++ readStage.code := by
  obtain ⟨body,accepted,code⟩ := consumer_code
  obtain ⟨outer,compiled,sameCode⟩ := memory_compile_single_block body accepted
  exact ⟨outer,compiled,sameCode.trans code⟩

theorem block_code_split : blockStage.code = effectStage.code ++ readStage.code := by
  obtain ⟨outer,compiled,code⟩ := block_code
  have accepted : some blockStage = Memory.compileProg 1 preparation.frag beforeLoop :=
    Option.some_get _
  have same : blockStage = outer := Option.some.inj (accepted.trans compiled)
  exact (congrArg (fun result : CompiledProg 1 preparation.frag beforeLoop => result.code) same).trans code

theorem wrong_order_target (tail : List Word) :
    run (preparation.code ++ (blockStage.code ++ enclosed.code))
      {machine with stack := tail} = .revert := by
  obtain ⟨_,_,all⟩ := effects_before_failure
  have bad := (all tail).2.2.2.2.2.2.2.1
  have stopped := run_append_revert (c₂ := enclosed.code) bad
  simpa only [block_code_split,List.append_assoc] using stopped

private def observed (m : Machine) : Option (List Nat) :=
  (m.stack ++ LoopScopeTrace.addresses.map m.mem).mapM fun word =>
    match word with | .val value => some value.val | .slot _ => none

theorem complete_effect_prefix :
    observed {effectTarget with stack := [w[77],w[88]]} =
      some [77,88,258,99,256,42,256,0,1,17,0,0,0] := by decide +kernel

theorem wrong_order_is_distinct (tail : List Word) :
    run (preparation.code ++ (enclosed.code ++ suffix.code)) {machine with stack := tail} ≠
    run (preparation.code ++ (blockStage.code ++ enclosed.code)) {machine with stack := tail} := by
  have good : run (preparation.code ++ (enclosed.code ++ suffix.code)) {machine with stack := tail} =
      .ok {finalTarget with stack := tail} 0 := LoopScopeTrace.whole_target_tail tail
  rw [good,wrong_order_target]
  intro impossible
  cases impossible

theorem read_refuses_short_frame {selected : Nat → Fin W}
    {σ : State C LoopScopeControls.Γ} {m : Machine} :
    ¬ (Compilation.memory readStage).Input 1 4 selected σ m := by
  intro input
  have capacity := input.2.1
  have need : 1 + frameNeedProg readLast = 5 := by decide +kernel
  omega
end Solidity.Backend.Passes.ReframedTripleWrongOrder
