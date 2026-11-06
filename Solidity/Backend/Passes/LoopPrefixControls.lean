import Solidity.Backend.Passes.LoopScopeTerminal

/-! A reached failing turn keeps prefix effects but never demands unreachable
allocation; a nonallocating infinite loop has inhabited Room after allocation.
All failures are internal terminal observations, not public ABI bytes. -/
namespace Solidity.Backend.Passes.LoopPrefixControls
open Evm Evm.Memory Evm.Compiler
open MemoryCallControls (C A initial base machine)
open LoopScopeControls
open LoopScopeTrace (preparedTarget loopTarget)

def effect : Prog C LoopScopeControls.Γ LoopScopeControls.Γ :=
  .cons (.assignLocal (.there .here) (.simple (.lit 0 rfl))) .nil

def failedBody : Prog C LoopScopeControls.Γ LoopScopeControls.Δ :=
  effect.join (.cons .revert body)
def failing : Prog C LoopScopeControls.Γ LoopScopeControls.Γ :=
  .cons (.loop .auto condition failedBody) .nil
def failureScope : Prog C LoopScopeControls.Γ LoopScopeControls.Γ := .cons (.block failing) .nil

def failureCompiled : LoopScopes.CompiledProg 1 preparation.frag failureScope :=
  (LoopScopes.compileProg 1 failureScope _).get (by decide +kernel)

theorem body_failure (σ : State C LoopScopeControls.Γ) : failedBody.run σ = .error .revert := by
  with_unfolding_all rfl

theorem failed_cost (σ : State C LoopScopeControls.Γ) : allocationCostProg failedBody σ = 0 := by
  with_unfolding_all rfl

theorem loop_failure : failing.run prepared.st = .error .revert := by
  have h : (Stmt.loop .auto condition failedBody).run prepared.st = .error .revert := by
    rw [Stmt.run_loop]
    apply TLoop.run_of_iterN (n := 1)
    simp only [TLoop.iterN,TLoop.step,condition_initial,body_failure,Except.map]
  exact Prog.run_cons_error h

theorem scope_failure : failureScope.run prepared.st = .error .revert := by
  have h : (Stmt.block failing).run prepared.st = .error .revert := by
    change (failing.run prepared.st).map _ = .error .revert
    rw [loop_failure]
    rfl
  exact Prog.run_cons_error h

/-- The body syntactically allocates, but its reached prefix cost is zero:
the allocation is after a real earlier effect and unconditional revert. -/
theorem failed_room (selected : Nat → Fin W) (m : Machine) :
    hasAllocation failedBody = true ∧ LoopScopes.Room failureCompiled.cert 128 prepared.st selected m := by
  refine ⟨by decide +kernel,?_⟩
  apply LoopScopes.room_block
  apply LoopScopes.room_base_singleton
  apply Loops.room_singleton
  apply loopRoom_one_turn condition failedBody prepared.st selected m
  · intro σ o hs
    rw [body_failure] at hs
    cases hs
  · exact .inl (failed_cost prepared.st)

theorem reached_body_failure : ∃ mb, ∀ tail,
    MappedOutput (.memory preparation) 1 128 base initial {machine with stack := tail}
      prepared.st {preparedTarget with stack := tail} mb ∧
    (Compilation.memoryLoopScopes failureCompiled).Input 1 128 mb prepared.st
      {preparedTarget with stack := tail} ∧
    run failureCompiled.code {preparedTarget with stack := tail} = .revert ∧
    run (preparation.code ++ failureCompiled.code) {machine with stack := tail} = .revert := by
  obtain ⟨mb,nb,hp⟩ := LoopScopeTerminal.prefix_tails
  refine ⟨mb,?_⟩
  intro tail
  obtain ⟨ht,_,ha,_⟩ := hp tail
  have hi : (Compilation.memoryLoopScopes failureCompiled).Input 1 128 mb prepared.st
      {preparedTarget with stack := tail} := ⟨ha.1,by decide +kernel,(failed_room _ _).2⟩
  have hf := (compilation_revert_iff (.memoryLoopScopes failureCompiled) hi
    (by decide +kernel)).mpr (.inl scope_failure)
  change run failureCompiled.code {preparedTarget with stack := tail} = .revert at hf
  exact ⟨ha,hi,hf,by rw [run_append_ok ht,hf]⟩

def effectCompiled : CompiledProg 1 preparation.frag effect :=
  (Memory.compileProg 1 _ effect).get (by decide +kernel)
private def okMachine : Evm.Out → Option Machine
  | .ok m 0 => some m | _ => none
noncomputable def afterEffect : Machine :=
  (okMachine (run effectCompiled.code preparedTarget)).get (by decide +kernel)
theorem effect_target : run effectCompiled.code preparedTarget = .ok afterEffect 0 := by
  have h : some afterEffect = okMachine (run effectCompiled.code preparedTarget) := Option.some_get _
  generalize run effectCompiled.code preparedTarget = result at h ⊢
  cases result with
  | ok m skip =>
    cases skip with
    | zero => exact congrArg (fun m => Evm.Out.ok m 0) (Option.some.inj h).symm
    | succ n => cases h
  | revert => cases h
  | fault => cases h

theorem emitted_failure : failureCompiled.code =
    [.loop conditionCompiled.code (effectCompiled.code ++ [.revert] ++ bodyCompiled.code)] := rfl

theorem failing_body_target :
    run (effectCompiled.code ++ [.revert] ++ bodyCompiled.code) preparedTarget = .revert := by
  rw [List.append_assoc,run_append_ok effect_target]
  rfl

/-- The condition really reaches this body on the concrete target machine;
its successful primitive evaluation preserves every non-stack component. -/
theorem condition_target : run conditionCompiled.code preparedTarget =
    .ok (preparedTarget.push (.val (bword true))) 0 := by
  obtain ⟨mb,nb,ha,hb⟩ := LoopScopeTerminal.prefix_relations
  rcases conditionCompiled.cert.correct ha.1 with ⟨v,w,hv,repr,ht⟩ | ⟨hv,ht⟩
  · rw [condition_initial] at hv
    have same : v = true := (Except.ok.inj hv).symm
    subst v
    change w = .val (bword true) at repr
    rw [repr] at ht
    exact ht
  · rw [condition_initial] at hv
    cases hv

theorem actual_failing_turn :
    loopTurn (run conditionCompiled.code)
      (run (effectCompiled.code ++ [.revert] ++ bodyCompiled.code)) preparedTarget = .inr .revert := by
  unfold loopTurn
  rw [condition_target]
  change (if (1 : Nat) = 0 then _ else _) = _
  rw [if_neg (by decide)]
  change (match run (effectCompiled.code ++ [.revert] ++ bodyCompiled.code) preparedTarget with
    | .ok m 0 => (Sum.inl m : Machine ⊕ Evm.Out) | .ok _ (_+1) => .inr .fault | r => .inr r) = .inr .revert
  rw [failing_body_target]

private def words (m : Machine) : Option (List Nat) :=
  (m.stack ++ LoopScopeTrace.addresses.map m.mem).mapM fun w => match w with
    | .val n => some n.val | .slot _ => none

theorem failing_prefix_vector : words {afterEffect with stack := [w[77],w[88]]} =
    some [77,88,258,99,256,0,256,0,1,7,0,0,0] := by decide +kernel

theorem skipped_failure_effect : words {afterEffect with stack := [w[77],w[88]]} ≠
    some [77,88,258,99,256,42,256,0,1,7,0,0,0] := by decide +kernel

def spinCondition : Val C LoopScopeControls.Γ .bool :=
  .binop .eqB rfl rfl (.mlen (.var .here rfl) rfl) (.simple (.lit 2 rfl))
def spin : Prog C LoopScopeControls.Γ LoopScopeControls.Γ :=
  .cons (.loop .auto spinCondition .nil) .nil
def spinScope : Prog C LoopScopeControls.Γ LoopScopeControls.Γ := .cons (.block spin) .nil
def spinCompiled : LoopScopes.CompiledProg 1 enclosed.frag spinScope :=
  (LoopScopes.compileProg 1 spinScope _).get (by decide +kernel)

theorem spin_condition : spinCondition.evalT loopOut.st = .ok true := by with_unfolding_all rfl

/-- No evaluation of an infinite target or source loop is used. Every finite
source iteration remains at the same independently reached state. -/
theorem spin_source : spin.run loopOut.st = .error .diverge := by
  let step := fun o : Solidity.Out C loopOut.st.H LoopScopeControls.Γ =>
    ((Prog.nil : Prog C LoopScopeControls.Γ LoopScopeControls.Γ).run o.st).map fun o' =>
      (⟨o'.st.drop Ext.refl,o.ext.trans o'.ext⟩ : Solidity.Out C loopOut.st.H LoopScopeControls.Γ)
  let start : Solidity.Out C loopOut.st.H LoopScopeControls.Γ := ⟨loopOut.st,List.prefix_refl _⟩
  have hstep : TLoop.step step (fun o => spinCondition.evalT o.st) start = .inl start := by
    unfold TLoop.step
    dsimp only [start]
    rw [spin_condition]
    rfl
  have iter : ∀ n, TLoop.iterN step (fun o => spinCondition.evalT o.st) n start = .inl start := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => rw [TLoop.iterN,hstep]; exact ih
  have hn : ¬ ∃ r n, TLoop.iterN step (fun o => spinCondition.evalT o.st) n start = .inr r := by
    rintro ⟨r,n,h⟩
    rw [iter] at h
    cases h
  have h : (Stmt.loop .auto spinCondition (Prog.nil : Prog C LoopScopeControls.Γ LoopScopeControls.Γ)).run loopOut.st =
      .error .diverge := by
    rw [Stmt.run_loop]
    change TLoop.run step (fun o => spinCondition.evalT o.st) start = .error .diverge
    unfold TLoop.run
    rw [dif_neg hn]
  exact Prog.run_cons_error h

theorem spin_scope_source : spinScope.run loopOut.st = .error .diverge := by
  have h : (Stmt.block spin).run loopOut.st = .error .diverge := by
    change (spin.run loopOut.st).map _ = .error .diverge
    rw [spin_source]
    rfl
  exact Prog.run_cons_error h

theorem reached_divergence : ∃ mb nb, ∀ tail,
    MappedOutput (.memory preparation) 1 128 base initial {machine with stack := tail}
      prepared.st {preparedTarget with stack := tail} mb ∧
    MappedOutput checked 1 128 mb prepared.st {preparedTarget with stack := tail}
      loopOut.st {loopTarget with stack := tail} nb ∧
    (Compilation.memoryLoopScopes spinCompiled).Input 1 128 nb loopOut.st {loopTarget with stack := tail} ∧
    run spinCompiled.code {loopTarget with stack := tail} = .fault ∧
    run (preparation.code ++ (enclosed.code ++ spinCompiled.code)) {machine with stack := tail} = .fault ∧
    run ((preparation.code ++ enclosed.code) ++ spinCompiled.code) {machine with stack := tail} = .fault := by
  obtain ⟨mb,nb,hp⟩ := LoopScopeTerminal.prefix_tails
  refine ⟨mb,nb,?_⟩
  intro tail
  obtain ⟨hpre,hloop,ha,hb⟩ := hp tail
  rcases hb with ⟨amount,ext,cost,state,extension,grows⟩
  have hi : (Compilation.memoryLoopScopes spinCompiled).Input 1 128 nb loopOut.st
      {loopTarget with stack := tail} := ⟨state,by decide +kernel,
        LoopScopes.room_nonallocating spinCompiled.cert (by decide +kernel) _ _ _⟩
  have hf := (compilation_fault_iff (.memoryLoopScopes spinCompiled) hi
    (by decide +kernel)).mpr spin_scope_source
  change run spinCompiled.code {loopTarget with stack := tail} = .fault at hf
  have whole : run (preparation.code ++ (enclosed.code ++ spinCompiled.code))
      {machine with stack := tail} = .fault := by rw [run_append_ok hpre,run_append_ok hloop,hf]
  exact ⟨ha,⟨amount,ext,cost,state,extension,grows⟩,hi,hf,whole,
    by simpa only [List.append_assoc] using whole⟩

theorem distinct_failures :
    failureScope.run prepared.st ≠ .error .diverge ∧
    spinScope.run loopOut.st ≠ .error .revert ∧ spinScope.run loopOut.st ≠ .error .panic := by
  rw [scope_failure,spin_scope_source]
  constructor
  · intro h; cases h
  · constructor
    · intro h; cases h
    · intro h; cases h

end Solidity.Backend.Passes.LoopPrefixControls
