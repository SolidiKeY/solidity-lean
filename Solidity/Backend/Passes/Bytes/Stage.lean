import Solidity.Backend.Selection.Composition
import Solidity.Evm.Compiler

/-! The bytes stage of the Backend endpoint: checked-entry code
(`List Evm.Instr`, the `code` of every `Compilation`) either is refused, or is
assembled by the proved scalar selector into bytes whose execution on the
`LabelExec` byte-PC model agrees with `Evm.run` in both directions.

Success: `Evm.run` ends with a stack iff the bytes have a stack-safe trace to
their end PC with that stack. Fault: the composition needs a `CodeShape` at
the input height, which excludes underflow, the only fault of selected code;
so accepted code never faults (`Accepted.never_faults`) and `fault_iff` holds
with both sides false. The faults of selected code are exactly the `height`
refusals (`selected_fault_iff`): `Evm.run` faults iff the stage refuses it.

Nothing here is a hypothesis about decoders, bridges or `Roadmap.Execution`:
the bytes are `encode` of the assembled program built by `scalarComposition`,
and their run is `LabelExec.advance` on those bytes.

Refusals are explicit: the selector refuses the code (`unselected`, R3), the
selected program underflows from the declared input height (`height`), a
prefix exceeds the 1024-word stack (`capacity`), or an instruction has no
static arity (`unshaped`). -/
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

/-- An underflowing exchange has no result. -/
theorem exchange_short (a : Scalar.Word) : (k : Nat) → (stack : Scalar.Stack) →
    stack.length ≤ k → Scalar.exchange a k stack = none
  | _, [], _ => by cases ‹Nat› <;> rfl
  | 0, _ :: _, short => by simp only [List.length_cons] at short; omega
  | k + 1, _ :: rest, short => by
    simp only [List.length_cons] at short
    simp only [Scalar.exchange, exchange_short a k rest (by omega), Option.map_none]

/-- Fewer words than a numeric row consumes: no result. -/
theorem numeric_short (o : Op) (a b : Nat) (stack : Scalar.Stack)
    (row : LabelExec.numericArity o = some (a, b)) (short : stack.length < a) :
    Scalar.numericStep o stack = none := by
  cases hu : Scalar.unary o with
  | some f =>
    simp only [LabelExec.numericArity, hu, Option.some.injEq, Prod.mk.injEq] at row
    rcases row with ⟨rfl, rfl⟩
    match stack, short with
    | [], _ => simp only [Scalar.numericStep, hu, Scalar.applyUnary]
  | none =>
    cases hb : Scalar.binary o with
    | some f =>
      simp only [LabelExec.numericArity, hu, hb, Option.some.injEq, Prod.mk.injEq] at row
      rcases row with ⟨rfl, rfl⟩
      match stack, short with
      | [], _ => simp only [Scalar.numericStep, hu, hb, Scalar.applyBinary]
      | [_], _ => simp only [Scalar.numericStep, hu, hb, Scalar.applyBinary]
    | none =>
      cases ht : Scalar.ternary o with
      | none => simp only [LabelExec.numericArity, hu, hb, ht, reduceCtorEq] at row
      | some f =>
        simp only [LabelExec.numericArity, hu, hb, ht, Option.some.injEq, Prod.mk.injEq] at row
        rcases row with ⟨rfl, rfl⟩
        match stack, short with
        | [], _ => simp only [Scalar.numericStep, hu, hb, ht, Scalar.applyTernary]
        | [_], _ => simp only [Scalar.numericStep, hu, hb, ht, Scalar.applyTernary]
        | [_, _], _ => simp only [Scalar.numericStep, hu, hb, ht, Scalar.applyTernary]

/-- Fewer words than a row consumes: `Scalar.step` faults. -/
theorem step_short (i : Instr) (a b : Nat) (stack : Scalar.Stack)
    (row : LabelExec.arity i = some (a, b)) (short : stack.length < a) :
    Scalar.step i stack = none := by
  cases i with
  | push n imm =>
    simp only [LabelExec.arity, Option.some.injEq, Prod.mk.injEq] at row
    omega
  | op o =>
    cases o <;> simp only [LabelExec.arity, Scalar.step] at row ⊢
    case DUP n =>
      simp only [Option.some.injEq, Prod.mk.injEq] at row
      simp only [Scalar.duplicate, List.getElem?_eq_none (show stack.length ≤ n.val by omega),
        Option.map_none]
    case SWAP n =>
      simp only [Option.some.injEq, Prod.mk.injEq] at row
      cases stack with
      | nil => rfl
      | cons x rest =>
        simp only [List.length_cons] at short
        simp only [Scalar.swap, exchange_short x n.val rest (by omega), Option.map_none]
    case POP =>
      simp only [Option.some.injEq, Prod.mk.injEq] at row
      cases stack with
      | nil => rfl
      | cons _ _ => simp only [List.length_cons] at short; omega
    all_goals exact numeric_short _ _ _ _ row short

/-- A shaped program runs to completion from its input height. -/
theorem shape_total {p : Program} {n k : Nat} (shape : LabelExec.CodeShape p n k) :
    ∀ input : Scalar.Stack, input.length = n → ∃ output, Scalar.run p input = some output := by
  induction shape with
  | nil => intro input _; exact ⟨input, rfl⟩
  | cons head _ ih =>
    intro input height
    rcases head with ⟨consumed, produced, suffix, row, hin, hout⟩
    obtain ⟨next, stepped, length⟩ :=
      LabelExec.arity_domain _ consumed produced suffix input row (by omega)
    obtain ⟨output, rest⟩ := ih next (by omega)
    exact ⟨output, by simp only [Scalar.run, stepped, Option.bind_some, rest]⟩

/-- A program the height check refuses faults from every stack of that height. -/
theorem height_faults (p : Program) (shaped : ∀ i ∈ p, (LabelExec.arity i).isSome = true)
    (n : Nat) (refused : heightAfter p n = none) (input : Scalar.Stack)
    (height : input.length = n) : Scalar.run p input = none := by
  induction p generalizing n input with
  | nil => cases refused
  | cons i rest ih =>
    have isSome := shaped i (List.Mem.head _)
    cases row : LabelExec.arity i with
    | none => rw [row] at isSome; cases isSome
    | some pair =>
      obtain ⟨consumed, produced⟩ := pair
      simp only [heightAfter, row] at refused
      by_cases fits : consumed ≤ n
      · rw [if_pos fits] at refused
        obtain ⟨next, stepped, length⟩ :=
          LabelExec.arity_domain i consumed produced (n - consumed) input row (by omega)
        simp only [Scalar.run, stepped, Option.bind_some]
        exact ih (fun j member => shaped j (List.Mem.tail _ member)) _ refused next (by omega)
      · simp only [Scalar.run, step_short i consumed produced input row (by omega),
          Option.bind_none]

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

/-- Accepted code runs to completion from every input of its height. -/
theorem total (accepted : Accepted ir n) (input : Scalar.Stack) (height : input.length = n) :
    ∃ output, Scalar.run accepted.code.instructions input = some output :=
  shape_total accepted.code.shape input height

/-- Accepted code never faults: the fault side of `fault_iff` is empty. -/
theorem never_faults (accepted : Accepted ir n) (input : Scalar.Stack)
    (height : input.length = n) (m : Evm.Machine) (stack : m.stack = irStack input) :
    ∃ output, Evm.run ir m = .ok { m with stack := irStack output } 0 := by
  obtain ⟨output, run⟩ := accepted.total input height
  exact ⟨output, by rw [compileScalar_equation ir _ accepted.selected input m stack, run]⟩

/-- `Evm.run` of selected code ends in one of two ways (any input height). -/
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
reaches the end PC (with any stack). On accepted code both sides are false
(`never_faults`); faults of selected code are `height` refusals. -/
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
  /-- A selected instruction has no static arity (not expected to occur). -/
  | unshaped
  deriving DecidableEq, Repr

/-- The bytes stage at input height `n`: refusal or accepted code. -/
def stage (ir : List Evm.Instr) (n : Nat) : Except Refusal (Accepted ir n) :=
  match selected : compileScalar ir with
  | none => .error .unselected
  | some program =>
    if (program.all fun i => (LabelExec.arity i).isSome) = true then
      match fits : heightAfter program n with
      | none => .error .height
      | some output =>
        if bounded : Scalar.stackBound program (n : Int) = true then
          .ok ⟨output, ⟨program, heightAfter_shape program n output fits, bounded⟩, selected⟩
        else .error .capacity
    else .error .unshaped

/-- R3 is exactly the selector's refusal. -/
theorem stage_unselected (ir : List Evm.Instr) (n : Nat) :
    stage ir n = .error .unselected ↔ compileScalar ir = none := by
  unfold stage
  split
  · next selected => exact ⟨fun _ => selected, fun _ => rfl⟩
  · next program selected =>
    refine ⟨fun refused => ?_, fun absent => by rw [selected] at absent; cases absent⟩
    split at refused
    · split at refused
      · cases refused
      · split at refused <;> cases refused
    · cases refused

/-- A `height` refusal names a selected, shaped program that the height
check refuses. -/
theorem stage_height_spec {ir : List Evm.Instr} {n : Nat}
    (refused : stage ir n = .error .height) :
    ∃ program, compileScalar ir = some program ∧
      (∀ i ∈ program, (LabelExec.arity i).isSome = true) ∧ heightAfter program n = none := by
  unfold stage at refused
  split at refused
  · cases refused
  · next program selected =>
    split at refused
    · next shaped =>
      split at refused
      · next fits => exact ⟨program, selected, fun i member => List.all_eq_true.mp shaped i member, fits⟩
      · split at refused <;> cases refused
    · cases refused

/-- A `capacity` refusal names a selected program that passes the height check. -/
theorem stage_capacity_spec {ir : List Evm.Instr} {n : Nat}
    (refused : stage ir n = .error .capacity) :
    ∃ program output, compileScalar ir = some program ∧ heightAfter program n = some output := by
  unfold stage at refused
  split at refused
  · cases refused
  · next program selected =>
    split at refused
    · split at refused
      · cases refused
      · next output fits => exact ⟨program, output, selected, fits⟩
    · cases refused

/-- `height` refusals fault: `Evm.run` faults from every machine whose stack
holds `n` words. -/
theorem stage_height_faults {ir : List Evm.Instr} {n : Nat}
    (refused : stage ir n = .error .height) (input : Scalar.Stack) (height : input.length = n)
    (m : Evm.Machine) (stack : m.stack = irStack input) : Evm.run ir m = .fault := by
  obtain ⟨program, selected, shaped, fits⟩ := stage_height_spec refused
  rw [compileScalar_equation ir program selected input m stack,
    height_faults program shaped n fits input height]

/-- For selected code the faults are exactly the `height` refusals. -/
theorem selected_fault_iff {ir : List Evm.Instr} {n : Nat} {program : Program}
    (selected : compileScalar ir = some program) (shaped : stage ir n ≠ .error .unshaped)
    (input : Scalar.Stack) (height : input.length = n)
    (m : Evm.Machine) (stack : m.stack = irStack input) :
    Evm.run ir m = .fault ↔ stage ir n = .error .height := by
  cases result : stage ir n with
  | ok accepted =>
    obtain ⟨output, run⟩ := accepted.never_faults input height m stack
    rw [run]
    exact ⟨fun faulted => (by cases faulted), fun refused => (by cases refused)⟩
  | error refusal =>
    cases refusal with
    | unselected =>
      rw [(stage_unselected ir n).mp result] at selected
      cases selected
    | height => exact ⟨fun _ => rfl, fun _ => stage_height_faults result input height m stack⟩
    | capacity =>
      obtain ⟨program', output, selected', fits⟩ := stage_capacity_spec result
      obtain ⟨final, run⟩ := shape_total (heightAfter_shape program' n output fits) input height
      rw [compileScalar_equation ir program' selected' input m stack, run]
      exact ⟨fun faulted => (by cases faulted), fun refused => (by cases refused)⟩
    | unshaped => exact absurd result shaped

/-- The bytes stage for checked-entry code: refusal, or the assembled bytes
of the proved scalar selector run exactly as `Evm.run` does, in both
directions, from every machine whose stack holds `n` words. The bytes are
named by definition (the equation is `rfl`) so the statement shows them. -/
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
#print axioms exchange_short
#print axioms numeric_short
#print axioms step_short
#print axioms shape_total
#print axioms height_faults
#print axioms Accepted.total
#print axioms Accepted.never_faults
#print axioms Accepted.reach
#print axioms Accepted.outcome
#print axioms Accepted.success_iff
#print axioms Accepted.fault_iff
#print axioms stage_unselected
#print axioms stage_height_spec
#print axioms stage_capacity_spec
#print axioms stage_height_faults
#print axioms selected_fault_iff
#print axioms bytes_stage
#print axioms compilation_bytes_stage

end Solidity.Backend.Passes.Bytes
