import Solidity.Evm.Compiler

/-!
# Decidable static refusals for the checked compiler entry

`Compilation.Input` (`Solidity/Evm/Compiler.lean`) mixes two kinds of
premise. The *static* bounds checked here involve only numbers known before
any state is chosen: the array bound `L` against `Lmax` (`SimL.bound`, and on the core path
`L + pushes P ≤ Lmax`), the locals of the frame (`StateRepr.locals`:
`b + Γ.length ≤ frame`) and the reserved frame (`b + requiredFrame ≤ frame`).
Its *dynamic* part represents a particular typed state in a particular machine
(`Sim`, heap, pointers, allocator, the copy bound `copyBoundProg P σ ≤ L`).

`staticRefused` computes these bounds for each of the eleven branches;
`staticRefused_input` proves that when it fires no state, machine and base map
satisfy `Input`, and `staticRefused_of_input` is its contrapositive form:
every accepted input passes the check. The check is sound, not complete: it
omits bounds that are implied only through the dynamic part, such as
`frame < W` when `Γ` holds a represented memory pointer (`HeapRepr.above`), or
`0 < b` for a program whose allocation cost is positive in every state
(`AllocationInput`). Whether every passing state is represented (the true
converse) is the world-side question and is not decided here.
-/
namespace Solidity.Backend.Passes.WholeProgram

open Solidity.Evm Solidity.Evm.Compiler

variable {C : Contract} {b : Nat} {Γ Δ : Ctx} {F : Frag Γ} {P : Prog C Γ Δ}

/-- The static memory check: the array bound fits, the locals and the
reserved frame fit below `frame`. -/
def memoryRefused (b L frame locals need : Nat) : Bool :=
  decide (Lmax < L) || decide (frame < b + locals) || decide (frame < b + need)

/-- The static check of one compilation result, one case per branch.
`true` means the branch's `Input` is refuted for every state and machine. -/
def staticRefused (result : Compilation b F P) (L frame : Nat) : Bool :=
  match result with
  | .core _ _ => decide (Lmax < L + Evm.Prog.pushes P)
  | .memory _ => memoryRefused b L frame Γ.length (Memory.frameNeedProg P)
  | .referenceArrays _ => memoryRefused b L frame Γ.length 0
  | .objects _ => memoryRefused b L frame Γ.length (Memory.frameNeedProg P)
  | .construction _ => memoryRefused b L frame Γ.length (Memory.frameNeedProg P)
  | .memoryLoops out => memoryRefused b L frame Γ.length out.cert.need
  | .memoryLoopScopes out => memoryRefused b L frame Γ.length out.cert.need
  | .memoryCalls out _ => memoryRefused b L frame Γ.length out.need
  | .memoryCopy _ => memoryRefused b L frame Γ.length (Memory.frameNeedProg P)
  | .fixedMemory _ => memoryRefused b L frame Γ.length 0
  | .copyConstruction _ => memoryRefused b L frame Γ.length (Memory.frameNeedProg P)

/-- `memoryRefused` passes exactly when its three bounds hold. -/
theorem memoryRefused_false {b L frame locals need : Nat} :
    memoryRefused b L frame locals need = false ↔
      L ≤ Lmax ∧ b + locals ≤ frame ∧ b + need ≤ frame := by
  simp only [memoryRefused, Bool.or_eq_false_iff, decide_eq_false_iff_not, Nat.not_lt]
  exact and_assoc

/-- Every accepted input passes the static check. -/
theorem staticRefused_of_input (result : Compilation b F P) {L frame : Nat}
    {base : Nat → Fin W} {σ : State C Γ} {m : Machine}
    (h : result.Input L frame base σ m) : staticRefused result L frame = false := by
  cases result with
  | core _ _ => exact decide_eq_false (Nat.not_lt.mpr h.2)
  | memory _ => exact memoryRefused_false.mpr ⟨h.1.core.bound, h.1.locals, h.2.1⟩
  | referenceArrays _ =>
    exact memoryRefused_false.mpr ⟨h.state.core.bound, h.state.locals, Nat.le_trans
      (Nat.le_add_right _ _) h.state.locals⟩
  | objects _ => exact memoryRefused_false.mpr ⟨h.1.core.bound, h.1.locals, h.2⟩
  | construction _ => exact memoryRefused_false.mpr ⟨h.1.core.bound, h.1.locals, h.2.1⟩
  | memoryLoops _ => exact memoryRefused_false.mpr ⟨h.1.core.bound, h.1.locals, h.2.1⟩
  | memoryLoopScopes _ => exact memoryRefused_false.mpr ⟨h.1.core.bound, h.1.locals, h.2.1⟩
  | memoryCalls _ _ => exact memoryRefused_false.mpr ⟨h.1.core.bound, h.1.locals, h.2.1⟩
  | memoryCopy _ => exact memoryRefused_false.mpr ⟨h.1.core.bound, h.1.locals, h.2.1⟩
  | fixedMemory _ =>
    exact memoryRefused_false.mpr ⟨h.1.legacy.core.bound, h.1.legacy.locals, Nat.le_trans
      (Nat.le_add_right _ _) h.1.legacy.locals⟩
  | copyConstruction _ => exact memoryRefused_false.mpr ⟨h.1.core.bound, h.1.locals, h.2.1⟩

/-- **Static refusal**: when the check fires, no typed state, machine and
base map satisfy the branch's `Input`. -/
theorem staticRefused_input (result : Compilation b F P) {L frame : Nat}
    (h : staticRefused result L frame = true)
    {base : Nat → Fin W} {σ : State C Γ} {m : Machine} :
    ¬ result.Input L frame base σ m := fun hi => by
  rw [staticRefused_of_input result hi] at h
  cases h

/-- The branches whose `Input` reserves `requiredFrame` cells above `b`:
all but the core path and the reference-array and fixed-array paths, whose
`Input` bounds only the locals, not a temporary frame. -/
def reservesFrame (result : Compilation b F P) : Bool :=
  match result with
  | .core .. | .referenceArrays _ | .fixedMemory _ => false
  | _ => true

/-- The memory-calls path reserves its call frames. -/
theorem reservesFrame_of_isMemoryCalls (result : Compilation b F P)
    (h : result.isMemoryCalls = true) : reservesFrame result = true := by
  cases result <;> first | rfl | cases h

/-- The reserved-frame refusal (generalizing the fixture's
`source_frame_refused`): a frame below `b + requiredFrame` is refused. -/
theorem staticRefused_requiredFrame (result : Compilation b F P) {L frame : Nat}
    (hr : reservesFrame result = true) (h : frame < b + result.requiredFrame) :
    staticRefused result L frame = true := by
  cases result <;> simp_all [staticRefused, memoryRefused, reservesFrame,
    Compilation.requiredFrame]

/-- An array bound above `Lmax` is refused on every branch. -/
theorem staticRefused_of_lmax (result : Compilation b F P) {L frame : Nat}
    (h : Lmax < L) : staticRefused result L frame = true := by
  cases result <;> simp only [staticRefused, memoryRefused, Bool.or_eq_true,
    decide_eq_true_eq] <;> omega

/-- The array-bound refusal of `core_input_refused`, as an instance. -/
theorem staticRefused_core {G : Frag Δ} (cert : inFragP F P = some G) {L frame : Nat}
    (bound : Lmax < L + Evm.Prog.pushes P) :
    staticRefused (Compilation.core (b := b) G cert) L frame = true :=
  decide_eq_true bound

end Solidity.Backend.Passes.WholeProgram
