import Solidity.Backend.InternalFlow.RuntimeFrameV3ScalarSourceCompilerClient
import Solidity.Backend.InternalFlow.RuntimeFrameTarget

/-!
Bridge for the scalar callRec fixture. The emitted prefix initializes the
otherwise unconstrained scratch pointer. Entry is on this prepared machine.
The cost is zero exactly for supported source outcomes fitting the six-word
arena, and W otherwise; allocation capacity excludes the latter states.
This does not change the source evaluator or claim correspondence for exhaustion.
-/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.CallsProgramBridge
open Evm Evm.Memory
open DisjointScalarReturn.Client (Γ F)
open ScalarSourceCompiler

/-- Initialize the pointer cell without changing represented caller locals. -/
def prepared (m : Machine) : Machine := writeMachine m 9 w[10]

def initCode : List Instr := [.push w[10], .mstore 9]

theorem prefix_run (m : Machine) : run initCode m = .ok (prepared m) 0 := rfl

/-- Arena capacity and exact source outcome determine admission. W is an
impossible allocation budget, not a claim that exhausted execution reverts. -/
def cost (depth : Nat) (σ : State CountdownWitness.P.C Γ) : Nat :=
  if (Client.selected depth).plan.arenaWords σ ≤ 6 then
    match (Client.input depth).run σ with
    | .ok _ => 0
    | .error .revert => 0
    | .error _ => W
  else W

theorem capacity_facts {depth frame : Nat}
    {σ : State CountdownWitness.P.C Γ}
    {base : Nat → Fin W} {m : Machine}
    (capacity : AllocationInput 1 frame (cost depth σ) σ base m) :
    cost depth σ = 0 ∧ (Client.selected depth).plan.arenaWords σ ≤ 6 ∧
      ((∃ out, (Client.input depth).run σ = .ok out) ∨
        (Client.input depth).run σ = .error .revert) := by
  have small : cost depth σ < W := by
    rcases capacity with zero | ⟨_, cursor, _, space⟩
    · rw [zero]; exact W_pos
    · omega
  by_cases room : (Client.selected depth).plan.arenaWords σ ≤ 6
  · simp only [cost, if_pos room] at small ⊢
    cases actual : (Client.input depth).run σ with
    | ok out => exact ⟨rfl, room, .inl ⟨out, rfl⟩⟩
    | error halt =>
      cases halt <;> simp only [actual] at small
      all_goals first | exact ⟨rfl, room, .inr rfl⟩ | omega
  · simp only [cost, if_neg room] at small
    omega

/-- The usual Calls input yields Entry after the checked initialization prefix.
The frame parameter may exceed 16; the reserved runtime arena remains [10,16). -/
theorem input_entry {depth L frame : Nat}
    {σ : State CountdownWitness.P.C Γ}
    {base : Nat → Fin W} {m : Machine}
    (repr : StateRepr L 1 frame F σ base m) (room : 1 + 15 ≤ frame)
    (capacity : AllocationInput 1 frame (cost depth σ) σ base m) :
    InterfaceV1.Entry (Client.selected depth).plan L 1 frame F σ base (prepared m) 10 := by
  have facts := capacity_facts capacity
  refine ⟨reserved_write repr 9 (by decide) (by omega) w[10],
    by change 5 ≤ 9; decide, by change 5 ≤ 9; decide,
    by change 8 ≤ 9; decide, by change 9 ≤ 9; decide,
    by change 9 < frame; omega, by change 9 ≤ 10; decide,
    ?_, ?_, .inl (by change 9 < 10; decide), ?_, ?_, .inl rfl⟩
  · omega
  · change Γ.length + 1 ≤ ScalarDemand.reserve ScalarReentry.count σ
    exact Nat.le_max_left _ _
  · have bound : (16 : Nat) < W := by decide
    omega
  · change upd m.mem 9 w[10] 9 = w[10]
    exact upd_same _ _ _

/-- The initialized image is a checked Calls producer, retaining both successful
and bare-revert executions. No input can select an exhausted source outcome. -/
def program (depth : Nat) : Calls.Program 1 F (.cons (Client.input depth) .nil) where
  frag := F
  code := initCode ++ (Client.selected depth).plan.code
  need := 15
  cost := cost depth
  -- Conservative metadata: rejected states have nonzero cost.
  allocates := true
  zeroCost := by intro impossible; cases impossible
  sound := by
    intro L frame σ base m repr room capacity
    obtain ⟨zero, fits, outcome⟩ := capacity_facts capacity
    have entry := input_entry repr room capacity
    rw [single_outcome]
    rcases outcome with ⟨out, source⟩ | source
    · obtain ⟨target, addresses, executed, represented, stack, extended, growth, _, _⟩ :=
        (Client.selected depth).returns (by decide) L frame σ base (prepared m) 10 entry out source
      refine .inl ⟨out, target, addresses, source, ?_, represented, stack, extended, ?_⟩
      · exact (run_append_ok (prefix_run m)).trans executed
      · rw [zero]
        intro cursor positive allocator space
        exact growth cursor positive
          (allocator.localWrite 9 (by decide) (by omega) w[10]) space
    · refine .inr ⟨source, ?_⟩
      exact (run_append_ok (prefix_run m)).trans
        ((Client.selected depth).bare_revert (by decide) L frame σ base (prepared m) 10 entry source)

/-- The theorem consumed by b3: standard Calls inputs give exact GrowingResult
for the original singleton source and the initialized scalar image. -/
theorem correct (depth : Nat) {L frame : Nat}
    {σ : State CountdownWitness.P.C Γ}
    {base : Nat → Fin W} {m : Machine}
    (repr : StateRepr L 1 frame F σ base m) (room : 1 + (program depth).need ≤ frame)
    (capacity : AllocationInput 1 frame ((program depth).cost σ) σ base m) :
    GrowingResult L 1 frame ((program depth).cost σ) (program depth).frag σ base m
      ((Prog.cons (Client.input depth) .nil).run σ) (run (program depth).code m) :=
  (program depth).sound repr room capacity

end Solidity.Backend.InternalFlow.RuntimeFrame.CallsProgramBridge
