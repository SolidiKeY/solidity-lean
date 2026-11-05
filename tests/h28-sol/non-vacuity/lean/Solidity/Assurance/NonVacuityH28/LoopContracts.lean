import Solidity.Assurance.NonVacuityH28.CheckedFamilies

/-! The scalar clients have an actual reached zero demand/cost. Additional
nonempty loop programs below check a false condition on a live heap, including
a body that would revert if entered. A complementary true-condition loop
actually reaches that revert. No completed successful or allocating loop turn
or positive allocating-loop capacity is claimed; those findings remain open. -/
namespace Solidity.Assurance.NonVacuityH28
open Solidity Semantics
variable (C : Contract)

theorem scalar_loop_demand (σ : State C MemCtx) :
    Evm.Memory.Loops.Demand (loopResult C).cert σ 0 :=
  Evm.Memory.Loops.Demand.head rfl

theorem scalar_loop_cost (σ : State C MemCtx) :
    Evm.Memory.Loops.Cost (loopResult C).cert σ ⟨σ, List.prefix_refl _⟩ 0 :=
  by
    refine .cons (o := ⟨σ, List.prefix_refl _⟩) (o' := ⟨σ, List.prefix_refl _⟩)
      (cost := 0) (rest := 0) rfl ?_ (.nil σ)
    rfl

theorem scalar_scope_demand (σ : State C MemCtx) :
    Evm.Memory.LoopScopes.Demand (scopeResult C).cert σ 0 :=
  .head (.base (Evm.Memory.Loops.Demand.head rfl))

theorem scalar_scope_cost (σ : State C MemCtx) :
    Evm.Memory.LoopScopes.Cost (scopeResult C).cert σ ⟨σ, List.prefix_refl _⟩ 0 :=
  by
    refine .cons (o := ⟨σ, List.prefix_refl _⟩) (o' := ⟨σ, List.prefix_refl _⟩)
      (cost := 0) (rest := 0) rfl ?_ (.nil σ)
    refine .base ?_
    refine .cons (o := ⟨σ, List.prefix_refl _⟩) (o' := ⟨σ, List.prefix_refl _⟩)
      (cost := 0) (rest := 0) rfl ?_ (.nil σ)
    rfl

/-- A real condition check stops before any body turn, for every annotation and body. -/
theorem false_loop_stmt_source {Γ Δ : Ctx} (σ : State C Γ)
    (a : LoopAnn C Γ) (body : Prog C Γ Δ) :
    Stmt.run σ (.loop a (.simple (.bool false)) body) =
      .ok ⟨σ, List.prefix_refl _⟩ := by
  rw [Stmt.run_loop]
  exact TLoop.run_of_iterN (n := 1) rfl

def skippedLoopBody (flag : Bool) : Prog C MemCtx MemCtx :=
  .cons (.require (.simple (.bool flag))) .nil

def skippedLoopProgram (a : LoopAnn C MemCtx) (flag : Bool) : Prog C MemCtx MemCtx :=
  .cons (.loop a (.simple (.bool false)) (skippedLoopBody C flag)) .nil

def skippedLoopResult (a : LoopAnn C MemCtx) (flag : Bool) :
    Evm.Memory.Loops.CompiledProg 1 (liveLayout C) (skippedLoopProgram C a flag) :=
  (Evm.Memory.Loops.compileProg 1 (liveLayout C) (skippedLoopProgram C a flag)).get
    (by cases flag <;> rfl)

def skippedLoopCompiled (a : LoopAnn C MemCtx) (flag : Bool) :
    Evm.Compiler.Compilation 1 (liveLayout C) (skippedLoopProgram C a flag) :=
  .memoryLoops (skippedLoopResult C a flag)

theorem skipped_loop_source (σ : State C MemCtx) (a : LoopAnn C MemCtx) (flag : Bool) :
    Prog.run σ (skippedLoopProgram C a flag) = .ok ⟨σ, List.prefix_refl _⟩ := by
  rw [skippedLoopProgram, Prog.run_cons_ok (false_loop_stmt_source C σ a _)]
  rfl

/-- The skipped body would actually revert if entered. -/
theorem skipped_body_reverts (σ : State C MemCtx) :
    Prog.run σ (skippedLoopBody C false) = .error .revert := rfl

theorem skipped_loop_input (a : LoopAnn C MemCtx) (flag : Bool)
    {σ : State C MemCtx} {base : Nat → Fin Evm.W} {mc : Evm.Machine}
    (h : Evm.Memory.Objects.StateRepr 1 1 128 (liveLayout C) σ base mc) :
    (skippedLoopCompiled C a flag).Input 1 128 base σ mc := by
  refine ⟨h.legacy, ?_, ?_⟩
  · cases flag <;> change 2 ≤ 128 <;> decide +kernel
  · apply Evm.Memory.Loops.room_nonallocating (skippedLoopResult C a flag).cert
    cases flag <;> rfl

theorem skipped_loop_code_nonempty (a : LoopAnn C MemCtx) (flag : Bool) :
    (skippedLoopCompiled C a flag).code ≠ [] := by
  cases flag <;> change [_] ≠ [] <;> exact List.cons_ne_nil _ _

/-- Independent target evaluation: one zero-word condition check, no body step. -/
theorem zero_condition_target (body : List Evm.Instr) (mc : Evm.Machine) :
    Evm.run [.loop [.push (.val (Evm.wmod 0))] body] mc = .ok mc 0 := by
  have ht : Evm.loopRun
      (fun m => Evm.exec [.push (.val (Evm.wmod 0))] 0 m)
      (fun m => Evm.exec body 0 m) mc = .ok mc 0 :=
    Evm.loopRun_of_iterN (n := 1) rfl
  change (Evm.loopRun _ _ mc).bind (fun m k => Evm.exec [] k m) = _
  rw [ht]
  rfl

theorem skipped_loop_target (a : LoopAnn C MemCtx) (flag : Bool) (mc : Evm.Machine) :
    Evm.run (skippedLoopCompiled C a flag).code mc = .ok mc 0 := by
  cases flag <;>
    change Evm.run [.loop [.push (.val (Evm.wmod 0))] _] mc = .ok mc 0 <;>
    exact zero_condition_target _ mc

/-- A reached header prefix and demand exist even though the body is skipped. -/
theorem skipped_loop_demand (a : LoopAnn C MemCtx) (flag : Bool) (σ : State C MemCtx) :
    Evm.Memory.Loops.Demand (skippedLoopResult C a flag).cert σ 0 := by
  cases flag <;> exact Evm.Memory.Loops.Demand.head (.inl ⟨_, .start⟩)

theorem skipped_loop_cost (a : LoopAnn C MemCtx) (flag : Bool) (σ : State C MemCtx) :
    Evm.Memory.Loops.Cost (skippedLoopResult C a flag).cert σ
      ⟨σ, List.prefix_refl _⟩ 0 := by
  cases flag
  all_goals
    refine .cons (o := ⟨σ, List.prefix_refl _⟩) (o' := ⟨σ, List.prefix_refl _⟩)
      (cost := 0) (rest := 0) (false_loop_stmt_source C σ a _) ?_ (.nil σ)
    exact Evm.Memory.LoopPrefix.start

/-- Actual Main.compiler_checked application paired with both independent runs. -/
theorem skipped_loop_checked (a : LoopAnn C MemCtx) (flag : Bool)
    {σ : State C MemCtx} {base : Nat → Fin Evm.W} {mc : Evm.Machine}
    (h : Evm.Memory.Objects.StateRepr 1 1 128 (liveLayout C) σ base mc) :
    SuccessfulChecked C (skippedLoopCompiled C a flag) σ base mc := by
  have hs := skipped_loop_source C σ a flag
  have ht := skipped_loop_target C a flag mc
  have input := skipped_loop_input C a flag h
  obtain ⟨mc', ht', hstack, hrep⟩ := checked_success_after_source
    (skippedLoopCompiled C a flag) input rfl hs
  have heq := ht'.symm.trans ht
  cases heq
  exact ⟨input, ⟨σ, List.prefix_refl _⟩, mc, hs, ht, rfl, hrep⟩

/-- Every contract has a genuinely inhabited checked loop entry with a live pointer. -/
theorem skipped_loop_joint (a : LoopAnn C MemCtx) (flag : Bool) :
    ∃ mc : Evm.Machine, ∃ base : Nat → Fin Evm.W,
      ∃ r : HRef (primitiveOutcome C).st.H (.array (.prim .uint)),
      Evm.run (constructionCompiled C).code memoryMachine = .ok mc 0 ∧
      Evm.Memory.Objects.StateRepr 1 1 128 (liveLayout C) (primitiveOutcome C).st base mc ∧
      TEnv.get .here (primitiveOutcome C).st.env = some r ∧
      mc.mem (Evm.cellOf 1 (.here : Idx MemCtx (.mem (.array (.prim .uint))))) = .val (base r.id) ∧
      128 ≤ (base r.id).val ∧
      SuccessfulChecked C (skippedLoopCompiled C a flag) (primitiveOutcome C).st base mc ∧
      Evm.run (skippedLoopCompiled C a flag).code mc = .ok mc 0 := by
  obtain ⟨mc, base, ht, _, hstate⟩ := construction_joint C
  obtain ⟨r, hr, hp⟩ := hstate.pointers (.here : Idx MemCtx (.mem (.array (.prim .uint))))
  exact ⟨mc, base, r, ht, hstate, hr, hp, hstate.heap.owner.above r,
    skipped_loop_checked C a flag hstate, skipped_loop_target C a flag mc⟩

/-- Jointly inhabited actual loop clients retain a live nonempty array's fields.
The universal annotation/body-flag family establishes zero turns only. -/
theorem skipped_loop_joint_layout (a : LoopAnn C MemCtx) (flag : Bool) :
    ∃ mc : Evm.Machine, ∃ base : Nat → Fin Evm.W,
      ∃ r : HRef (primitiveOutcome C).st.H (.array (.prim .uint)),
      Evm.run (constructionCompiled C).code memoryMachine = .ok mc 0 ∧
      (primitiveOutcome C).st.H.length = 1 ∧
      TEnv.get .here (primitiveOutcome C).st.env = some r ∧
      mc.mem (Evm.cellOf 1 (.here : Idx MemCtx (.mem (.array (.prim .uint))))) = .val (base r.id) ∧
      mc.mem (base r.id).val = .val (Evm.wmod 1) ∧
      mc.mem ((base r.id).val + 1) = .val (Evm.wmod 0) ∧
      SuccessfulChecked C (skippedLoopCompiled C a flag) (primitiveOutcome C).st base mc ∧
      Evm.run (skippedLoopCompiled C a flag).code mc = .ok mc 0 := by
  obtain ⟨mc, base, ht, _, hstate⟩ := construction_joint C
  let r : HRef (primitiveOutcome C).st.H (.array (.prim .uint)) :=
    (TEnv.get .here (primitiveOutcome C).st.env).get (by rfl)
  have hr : TEnv.get .here (primitiveOutcome C).st.env = some r := rfl
  obtain ⟨q, hq, hp⟩ := hstate.pointers (.here : Idx MemCtx (.mem (.array (.prim .uint))))
  have hqr : q = r := Option.some.inj (hq.symm.trans hr)
  rw [hqr] at hp
  have hl := (hstate.heap.arrays .dyn r).length rfl
  have hn : (primitiveOutcome C).st.heap.len r .dyn = 1 := by with_unfolding_all rfl
  rw [hn] at hl
  have hv : (MObj.elems .dyn ((primitiveOutcome C).st.heap.get r))[0]? =
      some (⟨0, rfl⟩ : PrimTy.uint.Denote) := by with_unfolding_all rfl
  obtain ⟨word, hw, hz⟩ := (hstate.heap.arrays .dyn r).elements 0
    (⟨0, rfl⟩ : PrimTy.uint.Denote) hv
  change (0 : Int) = (word.val : Int) at hz
  have hword : word = Evm.wmod 0 := by
    apply Fin.ext
    change word.val = 0
    omega
  rw [hword] at hw
  exact ⟨mc, base, r, ht, by with_unfolding_all rfl, hr, hp, hl, hw,
    skipped_loop_checked C a flag hstate, skipped_loop_target C a flag mc⟩

def enteredRevertProgram (a : LoopAnn C MemCtx) : Prog C MemCtx MemCtx :=
  .cons (.loop a (.simple (.bool true)) (skippedLoopBody C false)) .nil

def enteredRevertResult (a : LoopAnn C MemCtx) :
    Evm.Memory.Loops.CompiledProg 1 (liveLayout C) (enteredRevertProgram C a) :=
  (Evm.Memory.Loops.compileProg 1 (liveLayout C) (enteredRevertProgram C a)).get (by rfl)

def enteredRevertCompiled (a : LoopAnn C MemCtx) :
    Evm.Compiler.Compilation 1 (liveLayout C) (enteredRevertProgram C a) :=
  .memoryLoops (enteredRevertResult C a)

/-- The true condition reaches the nonempty body and observes its real revert. -/
theorem entered_revert_source (a : LoopAnn C MemCtx) (σ : State C MemCtx) :
    Prog.run σ (enteredRevertProgram C a) = .error .revert := by
  have hs : Stmt.run σ (.loop a (.simple (.bool true)) (skippedLoopBody C false)) =
      .error .revert := by
    rw [Stmt.run_loop]
    exact TLoop.run_of_iterN (n := 1) rfl
  change TRun.seq (Stmt.runR (.loop a (.simple (.bool true)) (skippedLoopBody C false)))
    TRun.nil σ = _
  simp only [TRun.seq, hs]

/-- Independent target evaluation enters and reverts in its first turn. -/
theorem entered_revert_target (a : LoopAnn C MemCtx) (mc : Evm.Machine) :
    Evm.run (enteredRevertCompiled C a).code mc = .revert := by
  with_unfolding_all
    change ((Evm.loopRun
      (fun m => Evm.exec [.push (.val (Evm.wmod 1))] 0 m)
      (fun m => Evm.exec [.push (.val (Evm.wmod 0)), .jumpi 1, .revert] 0 m) mc).bind
      (fun m k => Evm.exec [] k m)) = _
  have ht : Evm.loopRun
      (fun m => Evm.exec [.push (.val (Evm.wmod 1))] 0 m)
      (fun m => Evm.exec [.push (.val (Evm.wmod 0)), .jumpi 1, .revert] 0 m) mc = .revert :=
    Evm.loopRun_of_iterN (n := 1) rfl
  rw [ht]
  rfl

theorem entered_revert_input (a : LoopAnn C MemCtx)
    {σ : State C MemCtx} {base : Nat → Fin Evm.W} {mc : Evm.Machine}
    (h : Evm.Memory.Objects.StateRepr 1 1 128 (liveLayout C) σ base mc) :
    (enteredRevertCompiled C a).Input 1 128 base σ mc :=
  ⟨h.legacy, by change 2 ≤ 128; decide +kernel,
    Evm.Memory.Loops.room_nonallocating (enteredRevertResult C a).cert rfl σ base mc⟩

/-- The attempted reverting body contributes an actual reached zero demand. -/
theorem entered_revert_demand (a : LoopAnn C MemCtx) (σ : State C MemCtx) :
    Evm.Memory.Loops.Demand (enteredRevertResult C a).cert σ 0 := by
  apply Evm.Memory.Loops.Demand.head
  exact .inr ⟨_, 0, .start, rfl, rfl⟩

/-- The original checked theorem is applied with its complete inhabited input. -/
theorem entered_revert_joint (a : LoopAnn C MemCtx) :
    ∃ mc : Evm.Machine, ∃ base : Nat → Fin Evm.W,
      Evm.run (constructionCompiled C).code memoryMachine = .ok mc 0 ∧
      (enteredRevertCompiled C a).Input 1 128 base (primitiveOutcome C).st mc ∧
      Prog.run (primitiveOutcome C).st (enteredRevertProgram C a) = .error .revert ∧
      Evm.run (enteredRevertCompiled C a).code mc = .revert ∧
      (enteredRevertCompiled C a).Agrees 1 128 base (primitiveOutcome C).st mc := by
  obtain ⟨mc, base, ht, _, hstate⟩ := construction_joint C
  have input := entered_revert_input C a hstate
  exact ⟨mc, base, ht, input, entered_revert_source C a _, entered_revert_target C a mc,
    Main.compiler_checked (enteredRevertCompiled C a) input⟩

end Solidity.Assurance.NonVacuityH28
