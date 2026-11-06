import Solidity.Backend.Passes.EmittedTail
import Solidity.Backend.Passes.AllocatingControls

/-! Inhabited allocating, reached-failure and loop controls for the general
target/compiler saved-tail laws. No new source semantics are introduced. -/
namespace Solidity.Backend.Passes.TailControls
open Solidity.Evm Solidity.Evm.Memory Solidity.Evm.Compiler
open Solidity.Backend.Passes.Controls.Fixture
open Solidity.Backend.Passes.AllocatingControls

/-- Actual allocating memory compilation has one shared non-stack output for
all tails, including its full dynamically selected representation. -/
theorem allocating_shared :
    ∃ canonical : Machine, run allocationStage.code {initialMachine with stack := []} = .ok canonical 0 ∧
      canonical.stack = [] ∧
      ∀ tail, run allocationStage.code {initialMachine with stack := tail} =
          .ok {canonical with stack := tail} 0 ∧
        (Compilation.memory allocationStage).Rep 1 6 initialBase (State.init C)
          {initialMachine with stack := tail} σ {canonical with stack := tail} := by
  simpa only [allocationStage.cert.pushes_zero, Nat.add_zero] using
    compilation_success_shared (Compilation.memory allocationStage) prefix_input rfl
      ReachabilityControls.fresh_state_reaches_fixture

/-- The previously populated allocating/read-write pipeline now has general
exact machine equality, not just one fixed-tail projection. -/
theorem pipeline_shared :
    ∃ canonical : Machine, canonical.stack = [] ∧
      ∀ tail, run (allocationStage.code ++ suffix.code) {initialMachine with stack := tail} =
        .ok {canonical with stack := tail} 0 := by
  obtain ⟨mb, ob, mid, final, ht, hstack, _, _, _, _⟩ := allocating_composition
  refine ⟨final, hstack, ?_⟩
  intro tail
  have he := run_tail (allocationStage.code ++ suffix.code) initialMachine tail
    (by rw [ht]; intro h; cases h)
  simpa only [ht, appendOut, appendTail, hstack, List.nil_append] using he

theorem reached_failure_all_tails (tail : List Word) :
    run (allocationStage.code ++ badSuffix.code) {initialMachine with stack := tail} = .revert := by
  have he := run_tail (allocationStage.code ++ badSuffix.code) initialMachine tail
    (by rw [reached_failure]; intro h; cases h)
  simpa only [reached_failure, appendOut, appendTail, List.nil_append] using he

/-- Appending an unbalanced POP to actual allocating code destroys a real
saved word. The compiler law does not certify this modified code. -/
theorem corruption :
    ∃ canonical : Machine,
      run allocationStage.code {initialMachine with stack := [w[41], w[19]]} =
        .ok {canonical with stack := [w[41], w[19]]} 0 ∧
      run (allocationStage.code ++ [.pop])
        {initialMachine with stack := [w[41], w[19]]} =
        .ok {canonical with stack := [w[19]]} 0 := by
  obtain ⟨canonical, _, _, hs⟩ := allocating_shared
  refine ⟨canonical, (hs _).1, ?_⟩
  rw [run_append_ok (hs _).1]
  rfl

private def condition : List Instr := [.mload 0]
private def body : List Instr := [.push w[1], .mload 0, .sub, .mstore 0]
private def loopInput : Machine :=
  {Machine.init with mem := fun a => if a = 0 then w[2] else w[0]}
private def loopOutput : Machine :=
  writeMachine (writeMachine loopInput 0 w[1]) 0 w[0]

private def loopMiddle : Machine := writeMachine loopInput 0 w[1]

private theorem sub_two : wmod (2 + (W - 1)) = (⟨1, by decide⟩ : Fin W) := by
  apply Fin.ext
  change (2 + (W - 1)) % W = 1
  have hw : 1 < W := by decide
  have he : 2 + (W - 1) = 1 + W := by omega
  rw [he, Nat.add_mod_right]
  exact Nat.mod_eq_of_lt hw

private theorem sub_one : wmod (1 + (W - 1)) = (⟨0, W_pos⟩ : Fin W) := by
  apply Fin.ext
  change (1 + (W - 1)) % W = 0
  have he : 1 + (W - 1) = W := by have := W_pos; omega
  rw [he, Nat.mod_self]

private theorem body_two : run body loopInput = .ok loopMiddle 0 := by
  have hmem : loopInput.mem 0 = w[2] := rfl
  simp only [body, run, exec_cons_zero, Instr.step, Machine.next,
    hmem, Out.ok_bind, exec_nil]
  rw [sub_two]
  rfl

private theorem body_one : run body loopMiddle = .ok loopOutput 0 := by
  have hmem : loopMiddle.mem 0 = w[1] := rfl
  simp only [body, run, exec_cons_zero, Instr.step, Machine.next,
    hmem, Out.ok_bind, exec_nil]
  rw [sub_one]
  rfl

private theorem turn_two :
    loopTurn (run condition) (run body) loopInput = .inl loopMiddle := by
  have hc : run condition loopInput = .ok (loopInput.push w[2]) 0 := rfl
  rw [loopTurn, hc]
  change (if (2 : Nat) = 0 then _ else _) = _
  rw [if_neg (by decide)]
  change (match run body loopInput with
    | .ok m 0 => (Sum.inl m : Machine ⊕ Evm.Out)
    | .ok _ (_ + 1) => (Sum.inr .fault : Machine ⊕ Evm.Out)
    | r => (Sum.inr r : Machine ⊕ Evm.Out)) = _
  rw [body_two]

private theorem turn_one :
    loopTurn (run condition) (run body) loopMiddle = .inl loopOutput := by
  have hc : run condition loopMiddle = .ok (loopMiddle.push w[1]) 0 := rfl
  rw [loopTurn, hc]
  change (if (1 : Nat) = 0 then _ else _) = _
  rw [if_neg (by decide)]
  change (match run body loopMiddle with
    | .ok m 0 => (Sum.inl m : Machine ⊕ Evm.Out)
    | .ok _ (_ + 1) => (Sum.inr .fault : Machine ⊕ Evm.Out)
    | r => (Sum.inr r : Machine ⊕ Evm.Out)) = _
  rw [body_one]

private theorem turn_zero :
    loopTurn (run condition) (run body) loopOutput = .inr (.ok loopOutput 0) := by
  have hc : run condition loopOutput = .ok (loopOutput.push w[0]) 0 := rfl
  rw [loopTurn, hc]
  rfl

/-- Both loop body executions are reached before the third condition exits. -/
theorem loop_reaches :
    loopIterN (run condition) (run body) 3 loopInput = .inr (.ok loopOutput 0) := by
  simp only [loopIterN, turn_two, turn_one, turn_zero]

theorem loop_all_tails (tail : List Word) :
    run [.loop condition body] (appendTail loopInput tail) =
      .ok (appendTail loopOutput tail) 0 := by
  have hl : loopRun (run condition) (run body) loopInput = .ok loopOutput 0 :=
    loopRun_of_iterN loop_reaches
  have ht : run [.loop condition body] loopInput = .ok loopOutput 0 := by
    change (loopRun (run condition) (run body) loopInput).bind (fun m k => exec [] k m) = _
    rw [hl]
    rfl
  have he := run_tail [.loop condition body] loopInput tail
    (by rw [ht]; intro h; cases h)
  simpa only [ht, appendOut] using he

end Solidity.Backend.Passes.TailControls
