import Solidity.Backend.Selection.Composition
import Solidity.Evm.Compiler

/-! The bytes stage of the Backend endpoint: checked-entry code
(`List Evm.Instr`, the `code` of every `Compilation`) either is refused, or is
assembled by the proved scalar selector into bytes whose byte-PC execution
agrees with `Evm.run` in both directions (success and fault).

Nothing here is a hypothesis about decoders, bridges or `Roadmap.Execution`:
the bytes are `encode` of the assembled program built by `scalarComposition`,
and their run is `LabelExec.advance` on those bytes.

Refusals are explicit: the selector refuses the code (`unselected`, R3), the
selected program does not fit the declared input height (`height`), or a
prefix exceeds the 1024-word stack (`capacity`). -/
namespace Solidity.Backend.Passes.Bytes
open Solidity.Backend Selection

/-! ## Static height check for a selected program -/

/-- The stack height after `p` from height `n`, refusing an underflowing row
or an instruction with no numeric/stack arity. -/
def heightAfter : Program → Nat → Option Nat
  | [], n => some n
  | i :: p, n => match LabelExec.arity i with
    | some (consumed, produced) =>
        if consumed ≤ n then heightAfter p (n - consumed + produced) else none
    | none => none

theorem heightAfter_shape : (p : Program) → (n k : Nat) →
    heightAfter p n = some k → LabelExec.CodeShape p n k
  | [], n, k, h => by
    simp only [heightAfter, Option.some.injEq] at h
    subst h
    exact .nil n
  | i :: p, n, k, h => by
    unfold heightAfter at h
    split at h
    · next consumed produced row =>
      split at h
      · next fits =>
        exact .cons (.mk consumed produced (n - consumed) row (by omega) (by omega))
          (heightAfter_shape p _ k h)
      · cases h
    · cases h

/-- Every instruction of a shaped program has a numeric/stack arity, so none
is a raw `JUMP`, `JUMPI` or `JUMPDEST`. -/
theorem shape_arity {p : Program} {n k : Nat} (shape : LabelExec.CodeShape p n k) :
    ∀ i ∈ p, (LabelExec.arity i).isSome = true := by
  induction shape with
  | nil => intro i member; cases member
  | cons head _ ih =>
    intro i member
    cases member with
    | head => cases head with | mk _ _ _ row _ _ => rw [row]; rfl
    | tail _ member => exact ih i member

/-- An instruction with an arity steps exactly as `Scalar.step`: success and
failure both. -/
theorem effect_of_arity (code : List UInt8) (i : Instr) (pc : Nat) (stack : Scalar.Stack)
    (row : (LabelExec.arity i).isSome = true) :
    LabelExec.effect code i ⟨pc, stack⟩ =
      (Scalar.step i stack).map fun next => ⟨pc + i.size, next⟩ := by
  cases i with
  | push n imm => rfl
  | op o =>
    cases o
    case JUMP => cases row
    case JUMPI => cases row
    case JUMPDEST => cases row
    all_goals cases stack <;> rfl

/-! ## Exact byte reach of a shaped scalar program -/

/-- Any byte run of a shaped program that reaches its end PC carries exactly
the `Scalar.run` result. With nothing after the code, the end PC is the end
of the bytes, so no later step exists. -/
theorem reach_run (code : Program) (shaped : ∀ i ∈ code, (LabelExec.arity i).isSome = true)
    (before : List UInt8) (input output : Scalar.Stack) (count : Nat)
    (reach : LabelExec.advance count (before ++ encode code) ⟨before.length, input⟩ =
      some ⟨before.length + size code, output⟩) :
    Scalar.run code input = some output := by
  induction code generalizing before input count with
  | nil =>
    cases count with
    | zero =>
      simp only [LabelExec.advance, Option.some.injEq, LabelExec.State.mk.injEq] at reach
      rw [reach.2]
      rfl
    | succ count =>
      simp only [LabelExec.advance, encode_nil, List.append_nil, LabelExec.step,
        List.drop_length, Creation.fetch, Option.bind_none, reduceCtorEq] at reach
  | cons i rest ih =>
    have positive : 0 < i.size := by cases i <;> simp only [Instr.size] <;> omega
    cases count with
    | zero =>
      simp only [LabelExec.advance, Option.some.injEq, LabelExec.State.mk.injEq, size,
        List.map_cons, List.sum_cons] at reach
      omega
    | succ count =>
      have row := shaped i (List.Mem.head _)
      have stepped : LabelExec.step (before ++ encode (i :: rest)) ⟨before.length, input⟩ =
          (Scalar.step i input).map fun next => ⟨before.length + i.size, next⟩ := by
        rw [encode_cons, LabelExec.step_prefix]
        exact effect_of_arity _ i _ input row
      cases first : Scalar.step i input with
      | none =>
        simp only [LabelExec.advance, stepped, first, Option.map_none, Option.bind_none,
          reduceCtorEq] at reach
      | some reached =>
        simp only [LabelExec.advance, stepped, first, Option.map_some, Option.bind_some] at reach
        have moved : LabelExec.advance count ((before ++ i.encode) ++ encode rest)
            ⟨(before ++ i.encode).length, reached⟩ =
              some ⟨(before ++ i.encode).length + size rest, output⟩ := by
          simpa only [encode_cons, List.append_assoc, List.length_append, Instr.length_encode,
            size, List.map_cons, List.sum_cons, Nat.add_assoc] using reach
        have tail := ih (fun j member => shaped j (List.Mem.tail _ member)) _ reached count moved
        simp only [Scalar.run, first, Option.bind_some]
        exact tail

/-! ## The accepted fragment and the stage -/

/-- Checked-entry code accepted by the bytes stage at input height `n`. -/
structure Accepted (ir : List Evm.Instr) (n : Nat) where
  output : Nat
  code : LabelExec.Code n output
  selected : compileScalar ir = some code.instructions

namespace Accepted

variable {ir : List Evm.Instr} {n : Nat}

/-- The proved composition certificate for the accepted code. -/
def composition (accepted : Accepted ir n) :
    CompositionCertificate ir (.code accepted.code.instructions) n accepted.output :=
  scalarComposition ir accepted.code accepted.selected

/-- The assembled program whose bytes are executed. -/
def program (accepted : Accepted ir n) : Program := accepted.composition.assembled.code

/-- The deployed bytes: the encoding of the assembled program. -/
def bytes (accepted : Accepted ir n) : List UInt8 := encode accepted.program

/-- The byte PC at which a run of the bytes has finished. -/
def finish (accepted : Accepted ir n) : Nat := size accepted.program

theorem program_eq (accepted : Accepted ir n) :
    accepted.program = accepted.code.instructions :=
  scalarComposition_code ir accepted.code accepted.selected

/-- A byte run reaching the end PC carries the scalar result. -/
theorem reach (accepted : Accepted ir n) (input output : Scalar.Stack) (count : Nat)
    (run : LabelExec.advance count accepted.bytes ⟨0, input⟩ = some ⟨accepted.finish, output⟩) :
    Scalar.run accepted.code.instructions input = some output := by
  have shaped := shape_arity accepted.code.shape
  apply reach_run accepted.code.instructions shaped [] input output count
  simpa only [bytes, finish, program_eq, List.nil_append, List.length_nil, Nat.zero_add] using run

/-- `Evm.run` of accepted code ends in exactly one of two ways. -/
theorem outcome (accepted : Accepted ir n) (input : Scalar.Stack)
    (m : Evm.Machine) (stack : m.stack = irStack input) :
    Evm.run ir m = .fault ∨ ∃ output, Evm.run ir m = .ok { m with stack := irStack output } 0 := by
  rw [compileScalar_equation ir _ accepted.selected input m stack]
  cases Scalar.run accepted.code.instructions input with
  | none => exact .inl rfl
  | some output => exact .inr ⟨output, rfl⟩

/-- Success: `Evm.run` ends with `output` iff the bytes have a stack-safe
byte-PC trace from PC 0 to the end PC with `output`. -/
theorem success_iff (accepted : Accepted ir n) (input output : Scalar.Stack)
    (height : input.length = n) (m : Evm.Machine) (stack : m.stack = irStack input) :
    Evm.run ir m = .ok { m with stack := irStack output } 0 ↔
      ∃ count, ExecutionTrace.Safe accepted.bytes count ⟨0, input⟩ ⟨accepted.finish, output⟩ := by
  constructor
  · intro actual
    exact accepted.composition.execute input output m height stack actual
  · intro ⟨count, trace⟩
    rw [compileScalar_equation ir _ accepted.selected input m stack,
      accepted.reach input output count trace.1]

/-- Fault: `Evm.run` faults iff no byte run of the bytes from PC 0 ever
reaches the end PC (with any stack). -/
theorem fault_iff (accepted : Accepted ir n) (input : Scalar.Stack)
    (height : input.length = n) (m : Evm.Machine) (stack : m.stack = irStack input) :
    Evm.run ir m = .fault ↔
      ∀ count output, LabelExec.advance count accepted.bytes ⟨0, input⟩ ≠
        some ⟨accepted.finish, output⟩ := by
  constructor
  · intro faulted count output run
    have none := (scalar_fault_iff ir _ accepted.selected input m stack).mp faulted
    rw [accepted.reach input output count run] at none
    cases none
  · intro unreached
    rcases accepted.outcome input m stack with faulted | ⟨output, actual⟩
    · exact faulted
    · obtain ⟨count, trace⟩ := (accepted.success_iff input output height m stack).mp actual
      exact absurd trace.1 (unreached count output)

end Accepted

/-- Why the bytes stage refuses checked-entry code. -/
inductive Refusal where
  /-- R3: the proved scalar selector refuses an instruction. -/
  | unselected
  /-- The selected program underflows from the declared input height. -/
  | height
  /-- A prefix of the selected program exceeds 1024 stack words. -/
  | capacity
  deriving DecidableEq, Repr

/-- The bytes stage at input height `n`: refusal or accepted code. -/
def stage (ir : List Evm.Instr) (n : Nat) : Except Refusal (Accepted ir n) :=
  match selected : compileScalar ir with
  | none => .error .unselected
  | some program =>
    match fits : heightAfter program n with
    | none => .error .height
    | some output =>
      if bounded : Scalar.stackBound program (n : Int) = true then
        .ok ⟨output, ⟨program, heightAfter_shape program n output fits, bounded⟩, selected⟩
      else .error .capacity

/-- R3 is exactly the selector's refusal. -/
theorem stage_unselected (ir : List Evm.Instr) (n : Nat) :
    stage ir n = .error .unselected ↔ compileScalar ir = none := by
  unfold stage
  split
  · next selected => exact ⟨fun _ => selected, fun _ => rfl⟩
  · next program selected =>
    refine ⟨fun refused => ?_, fun absent => by rw [selected] at absent; cases absent⟩
    split at refused
    · cases refused
    · split at refused <;> cases refused

/-- The bytes stage for checked-entry code: refusal, or the assembled bytes
of the proved scalar selector run exactly as `Evm.run` does, in both
directions, from every machine whose stack holds `n` words. -/
theorem bytes_stage (ir : List Evm.Instr) (n : Nat) :
    (∃ refusal, stage ir n = .error refusal) ∨
    ∃ accepted : Accepted ir n, stage ir n = .ok accepted ∧
      accepted.bytes = encode (scalarComposition ir accepted.code accepted.selected).assembled.code ∧
      ∀ (input : Scalar.Stack), input.length = n → ∀ (m : Evm.Machine), m.stack = irStack input →
        (∀ output, Evm.run ir m = .ok { m with stack := irStack output } 0 ↔
          ∃ count, ExecutionTrace.Safe accepted.bytes count ⟨0, input⟩
            ⟨accepted.finish, output⟩) ∧
        (Evm.run ir m = .fault ↔
          ∀ count output, LabelExec.advance count accepted.bytes ⟨0, input⟩ ≠
            some ⟨accepted.finish, output⟩) := by
  cases result : stage ir n with
  | error refusal => exact .inl ⟨refusal, rfl⟩
  | ok accepted =>
    refine .inr ⟨accepted, rfl, rfl, fun input height m stack => ⟨?_, ?_⟩⟩
    · intro output
      exact accepted.success_iff input output height m stack
    · exact accepted.fault_iff input height m stack

/-- The bytes stage for the code of every compiler result. -/
theorem compilation_bytes_stage {C : Contract} {b : Nat} {Γ Δ : Ctx} {F : Evm.Frag Γ}
    {P : Prog C Γ Δ} (r : Evm.Compiler.Compilation b F P) (n : Nat) :
    (∃ refusal, stage r.code n = .error refusal) ∨
    ∃ accepted : Accepted r.code n, stage r.code n = .ok accepted ∧
      ∀ (input : Scalar.Stack), input.length = n → ∀ (m : Evm.Machine), m.stack = irStack input →
        (∀ output, Evm.run r.code m = .ok { m with stack := irStack output } 0 ↔
          ∃ count, ExecutionTrace.Safe accepted.bytes count ⟨0, input⟩
            ⟨accepted.finish, output⟩) ∧
        (Evm.run r.code m = .fault ↔
          ∀ count output, LabelExec.advance count accepted.bytes ⟨0, input⟩ ≠
            some ⟨accepted.finish, output⟩) := by
  rcases bytes_stage r.code n with refused | ⟨accepted, staged, _, laws⟩
  · exact .inl refused
  · exact .inr ⟨accepted, staged, laws⟩

#print axioms heightAfter_shape
#print axioms shape_arity
#print axioms effect_of_arity
#print axioms reach_run
#print axioms Accepted.reach
#print axioms Accepted.outcome
#print axioms Accepted.success_iff
#print axioms Accepted.fault_iff
#print axioms stage_unselected
#print axioms bytes_stage
#print axioms compilation_bytes_stage

end Solidity.Backend.Passes.Bytes
