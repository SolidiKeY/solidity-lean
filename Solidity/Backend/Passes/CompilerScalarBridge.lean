import Solidity.Backend.InternalFlow.RuntimeFrameV3ScalarSourceCompiler
import Solidity.Backend.InternalFlow.RuntimeFrameTarget

/-!
# From a selected scalar call to a `Calls.Program`

`selectedProgram` turns any result of the scalar selector
`ScalarSourceCompiler.compile`, for any contract, context and fragment, into a
`Calls.Program` of the singleton program. It is the fixture bridge
`InternalFlow.CallsProgramBridge` with the fixture replaced by a `Selected`
and its numerals by the selector's parameters under the arithmetic `Shape`.

The emitted prefix writes the scratch cursor `pointer + 1` into the pointer
cell; the arena is `[pointer + 1, arena)`. The cost is zero exactly when the
typed run returns or reverts bare and its reserve fits the arena, and `W`
otherwise, so `AllocationInput` excludes every other state: exhaustion, panic
and divergence are outside the input, not mapped to a machine outcome.
-/
namespace Solidity.Backend.Passes.CompilerScalarBridge

open Evm Evm.Memory
open Backend.InternalFlow.RuntimeFrame
open Backend.InternalFlow.RuntimeFrame.ScalarSourceCompiler

variable {C : Contract} {Γ : Ctx} {b c arena pointer bottom : Nat} {F : Frag Γ}
  {s : Stmt C Γ Γ}

/-- The arithmetic the selector's parameters must satisfy: the pointer cell
lies above the locals and the workspace, inside the arena bound, and the
arena bound is a machine address. -/
abbrev Shape (b c arena pointer bottom : Nat) (Γ : Ctx) : Prop :=
  bottom < pointer ∧ b + Γ.length ≤ pointer ∧ b + (c + 3 - b) ≤ pointer ∧
    pointer < arena ∧ b ≤ arena ∧ arena < W

/-- The pointer cell holds the scratch cursor `pointer + 1`. -/
def prepared (pointer : Nat) (m : Machine) : Machine :=
  writeMachine m pointer (.val (wmod (pointer + 1)))

def initCode (pointer : Nat) : List Instr := [.push (.val (wmod (pointer + 1))), .mstore pointer]

theorem prefix_run (pointer : Nat) (m : Machine) :
    run (initCode pointer) m = .ok (prepared pointer m) 0 := rfl

/-- Zero when the typed run returns or reverts bare and the reserve fits the
arena; otherwise `W`, an allocation budget no input meets. -/
def cost (selected : Selected b c arena pointer bottom F s) (σ : State C Γ) : Nat :=
  if pointer + 1 + selected.plan.arenaWords σ ≤ arena then
    match s.run σ with
    | .ok _ => 0
    | .error .revert => 0
    | .error _ => W
  else W

theorem capacity_facts (selected : Selected b c arena pointer bottom F s) {frame : Nat}
    {σ : State C Γ} {base : Nat → Fin W} {m : Machine}
    (capacity : AllocationInput b frame (cost selected σ) σ base m) :
    cost selected σ = 0 ∧ pointer + 1 + selected.plan.arenaWords σ ≤ arena ∧
      ((∃ out, s.run σ = .ok out) ∨ s.run σ = .error .revert) := by
  have small : cost selected σ < W := by
    rcases capacity with zero | ⟨_, cursor, _, space⟩
    · rw [zero]; exact W_pos
    · omega
  by_cases room : pointer + 1 + selected.plan.arenaWords σ ≤ arena
  · simp only [cost, if_pos room] at small ⊢
    cases actual : s.run σ with
    | ok out => exact ⟨rfl, room, .inl ⟨out, rfl⟩⟩
    | error halt =>
      cases halt <;> simp only [actual] at small
      all_goals first | exact ⟨rfl, room, .inr rfl⟩ | omega
  · simp only [cost, if_neg room] at small
    omega

/-- A `Calls` input gives the selector's `Entry` on the prepared machine. -/
theorem input_entry (selected : Selected b c arena pointer bottom F s)
    (shape : Shape b c arena pointer bottom Γ) {L frame : Nat}
    {σ : State C Γ} {base : Nat → Fin W} {m : Machine}
    (repr : StateRepr L b frame F σ base m) (room : arena ≤ frame)
    (capacity : AllocationInput b frame (cost selected σ) σ base m) :
    InterfaceV1.Entry selected.plan L b frame F σ base (prepared pointer m) (pointer + 1) := by
  obtain ⟨below, locals, work, inside, low, small⟩ := shape
  have facts := capacity_facts selected capacity
  refine ⟨reserved_write repr pointer locals (by omega) _,
    locals, locals, work, Nat.le_refl pointer,
    by change pointer < frame; omega, by change pointer ≤ pointer + 1; omega,
    ?_, ?_, .inl (by change pointer < pointer + 1; omega), ?_, ?_, .inl rfl⟩
  · have fits := facts.2.1
    omega
  · change Γ.length + 1 ≤ ScalarDemand.reserve selected.count σ
    exact Nat.le_max_left _ _
  · have fits := facts.2.1
    omega
  · change upd m.mem pointer (.val (wmod (pointer + 1))) pointer = _
    exact upd_same _ _ _

/-- **The generic bridge.** The initialized selected image as a checked
`Calls` producer of the singleton program, with both returning and
bare-reverting executions. -/
def selectedProgram (selected : Selected b c arena pointer bottom F s)
    (shape : Shape b c arena pointer bottom Γ) : Calls.Program b F (.cons s .nil) where
  frag := F
  code := initCode pointer ++ selected.plan.code
  need := arena - b
  cost := cost selected
  allocates := true
  zeroCost := by intro impossible; cases impossible
  sound := by
    intro L frame σ base m repr room capacity
    have wide : arena ≤ frame := by have low := shape.2.2.2.2.1; omega
    obtain ⟨zero, fits, outcome⟩ := capacity_facts selected capacity
    have entry := input_entry selected shape repr wide capacity
    rw [single_outcome]
    rcases outcome with ⟨out, source⟩ | source
    · obtain ⟨target, addresses, executed, represented, stack, extended, growth, _, _⟩ :=
        selected.returns shape.1 L frame σ base (prepared pointer m) (pointer + 1) entry out source
      refine .inl ⟨out, target, addresses, source, ?_, represented, stack, extended, ?_⟩
      · exact (run_append_ok (prefix_run pointer m)).trans executed
      · rw [zero]
        intro cursor positive allocator space
        exact growth cursor positive
          (allocator.localWrite pointer (by have below := shape.1; omega)
            (by have inside := shape.2.2.2.1; omega) _) space
    · refine .inr ⟨source, ?_⟩
      exact (run_append_ok (prefix_run pointer m)).trans
        (selected.bare_revert shape.1 L frame σ base (prepared pointer m) (pointer + 1) entry source)

end Solidity.Backend.Passes.CompilerScalarBridge

#print axioms Solidity.Backend.Passes.CompilerScalarBridge.selectedProgram
