import Solidity.Backend.Environment.Composition

/-! H274/H57 versioned byte-memory load extension. Guards the regression that
v1 MLOAD returns none even on a populated numeric byte window. All v1 bodies,
statements and endpoints remain unchanged. This interpreter has no gas or
Source/physical-origin adequacy claim; consumer signature freeze is pending. -/
namespace Solidity.Backend.Environment.LoadV2

/-- Extend exactly one opcode, reusing the existing byte memory and word codec. -/
def step (frame : Frame) (i : Instr) (s : Slice) : Option Slice :=
  match i with
  | .op .MLOAD => match s.stack with
    | [] => none
    | offset :: tail => some ⟨uintOfNat (ofBytesBE (readMemory s.memory offset.1.toNat 32)) :: tail, s.memory⟩
  | _ => sliceStep frame i s

def run (frame : Frame) : Program → Slice → Option Slice
  | [], s => some s
  | i :: code, s => (step frame i s).bind (run frame code)

/-- Exact executable read; no desired result value is a premise. -/
theorem load_actual (frame : Frame) (memory : Memory) (offset : Word)
    (tail : List Word) :
    step frame (.op .MLOAD) ⟨offset::tail,memory⟩ =
      some ⟨uintOfNat (ofBytesBE (readMemory memory offset.1.toNat 32))::tail,memory⟩ := by
  first | rfl | simp only [step]

theorem load_underflow (frame : Frame) (memory : Memory) :
    step frame (.op .MLOAD) ⟨[],memory⟩ = none := by
  first | rfl | simp only [step]

/-- V1 is exactly retained on every other instruction, including its refusals. -/
theorem step_compatible (frame : Frame) (i : Instr) (s : Slice)
    (other : i ≠ .op .MLOAD) : step frame i s = sliceStep frame i s := by
  cases i with
  | push width value => rfl
  | op opcode => cases opcode <;> first | rfl | exact (other rfl).elim

theorem run_append (frame : Frame) (first second : Program) (s : Slice) :
    run frame (first++second) s = (run frame first s).bind (run frame second) := by
  induction first generalizing s with
  | nil => rfl
  | cons i code ih =>
    simp only [List.cons_append,run,Option.bind_assoc]
    cases step frame i s with
    | none => rfl
    | some next => exact ih next

#print axioms load_actual
#print axioms load_underflow
#print axioms step_compatible
#print axioms run_append
end Solidity.Backend.Environment.LoadV2
