import Solidity.Backend.Payments.CompilerExact
import Solidity.Backend.Selection.Composition

/-!
# The compiler endpoint: typed program and world to checked entry to bytes

`compiler_endpoint_correct` composes the checked entry `Evm.Compiler.compile`,
its exact agreement `Compilation.correct_exact`, and the proved scalar byte
selector `Selection.compileScalar` into one statement, `CompilerEndpoint`.
Every place where the chain stops is a named, decidable refusal:

* **R1** `compile b F P = none`: no checked branch accepts the program.
* **R2** `staticBound r L frame = false`: the accepted result's static
  resource bound (core: `L + pushes P ≤ Lmax`; memory branches:
  `b + requiredFrame ≤ frame`) fails for the world's bounds; then no world with
  those bounds is an `Input` (a consequence, proved by `input_bound`).
* **R3** `compileScalar r.code = none`: no byte selection for the emitted code.
  The selector takes numeric literals and operations, `pop`, `dup` and `swap`
  only; every statement the checked entry emits code for also emits a
  fixed-cell local (`mload`/`mstore`), storage access, `jumpi` (`assertTop`),
  `revert`, `call` or `loop`. So today only programs with empty code reach
  bytes; the byte half becomes informative as the selector widens.
* **R4** `Scalar.stackBound code input.length = false`: the selected bytes
  would exceed the 1024-word stack from that entry height.

Past the refusals the endpoint states the byte outcome: the target IR run
`Evm.run r.code m` and the encoded bytes agree (success with a capacity-safe
trace to the end of the code, or IR fault with the byte machine stuck), and
for every accepted world on a numeric stack the typed run succeeds with a byte
trace to the related state, or diverges with the byte machine stuck.

No stage is a hypothesis: the byte fault lemma `scalar_stuck` and the static
bound lemma `input_bound` are proved here.
-/
namespace Solidity.Backend

open Evm Evm.Compiler Selection

namespace Endpoint

/-! ## R2: the static resource bound of an accepted result -/

/-- The static resource bound `Input` states for each branch, over the world's
bounds `L` and `frame` only (no state, no machine). The reference-array and
fixed-memory branches state none, so they have no static refusal. -/
def staticBound {C : Contract} {b : Nat} {Γ Δ : Ctx} {F : Frag Γ} {P : Solidity.Prog C Γ Δ}
    (r : Compilation b F P) (L frame : Nat) : Bool :=
  match r with
  | .core _ _ => decide (L + Evm.Prog.pushes P ≤ Lmax)
  | .referenceArrays _ | .fixedMemory _ => true
  | r => decide (b + r.requiredFrame ≤ frame)

/-- Every accepted world meets the static bound. -/
theorem input_bound {C : Contract} {b L frame : Nat} {Γ Δ : Ctx} {F : Frag Γ}
    {P : Solidity.Prog C Γ Δ} (r : Compilation b F P) {base : Nat → Fin W}
    {σ : State C Γ} {m : Machine} (h : r.Input L frame base σ m) :
    staticBound r L frame = true := by
  cases r <;>
    simp only [staticBound, Compilation.requiredFrame, decide_eq_true_eq] <;>
    first | exact h.2 | exact h.2.1 | trivial

/-! ## R4 and the byte outcome of selected code -/

/-- Instructions the byte machine treats as control; scalar selection never
emits them. -/
def control : Instr → Bool
  | .op .JUMP | .op .JUMPI | .op .JUMPDEST => true
  | _ => false

/-- Off control instructions the byte step is the scalar step. -/
theorem effect_scalar (code : List UInt8) (i : Instr) (s : LabelExec.State)
    (free : control i = false) :
    LabelExec.effect code i s = (Scalar.step i s.stack).map
      fun stack => ⟨s.pc + i.size, stack⟩ := by
  obtain ⟨pc, stack⟩ := s
  cases i with
  | push n imm => rfl
  | op o =>
    cases o
    case JUMP => cases free
    case JUMPI => cases free
    case JUMPDEST => cases free
    all_goals rfl

/-- The byte machine is stuck: some reachable state inside the bytes (not at
their end, where `fetch` also returns `none`) has no supported step. -/
def Stuck (bytes : List UInt8) (start : LabelExec.State) : Prop :=
  ∃ k s, LabelExec.advance k bytes start = some s ∧ s.pc < bytes.length ∧
    LabelExec.step bytes s = none

theorem size_pos (i : Instr) : 0 < i.size := by
  cases i <;> simp only [Instr.size] <;> omega

/-- A scalar failure on control-free code leaves the byte machine stuck,
whatever bytes surround the code. -/
theorem scalar_stuck (code : Program) (before after : List UInt8) (input : Scalar.Stack)
    (free : code.all (fun i => !control i) = true) (fails : Scalar.run code input = none) :
    Stuck (before ++ (encode code ++ after)) ⟨before.length, input⟩ := by
  induction code generalizing before input with
  | nil => cases fails
  | cons i rest ih =>
    simp only [List.all_cons, Bool.and_eq_true, Bool.not_eq_true'] at free
    have bytes : before ++ (encode (i :: rest) ++ after) =
        before ++ (i.encode ++ (encode rest ++ after)) := by
      simp only [encode_cons, List.append_assoc]
    rw [bytes]
    cases step : Scalar.step i input with
    | none =>
      refine ⟨0, _, rfl, ?_, ?_⟩
      · have := size_pos i
        simp only [List.length_append, Instr.length_encode]
        omega
      · rw [LabelExec.step_prefix, effect_scalar _ _ _ free.1]
        simp only [step, Option.map_none]
    | some reached =>
      simp only [Scalar.run, step, Option.bind_some] at fails
      obtain ⟨k, s, run, inside, stuck⟩ := ih (before ++ i.encode) reached free.2 fails
      have shift : before ++ (i.encode ++ (encode rest ++ after)) =
          (before ++ i.encode) ++ (encode rest ++ after) := by
        simp only [List.append_assoc]
      refine ⟨k + 1, s, ?_, by rw [shift]; exact inside, by rw [shift]; exact stuck⟩
      have first : LabelExec.step (before ++ (i.encode ++ (encode rest ++ after)))
          ⟨before.length, input⟩ = some ⟨(before ++ i.encode).length, reached⟩ := by
        rw [LabelExec.step_prefix, LabelExec.effect_of_scalar _ _ _ _ _ step,
          List.length_append, Instr.length_encode]
      simp only [LabelExec.advance, first, Option.bind_some]
      rw [shift]
      exact run

/-- Selected certificates contain no control instruction. -/
theorem selectScalar_free (instruction : Evm.Instr) (certificate : InstructionCertificate instruction)
    (selected : selectScalar instruction = some certificate) :
    certificate.code.all (fun i => !control i) = true := by
  unfold selectScalar at selected
  cases instruction
  case push w =>
    cases w <;> simp only [selectNumeric, selectStack, Option.orElse] at selected
    all_goals cases selected <;> rfl
  case dup n =>
    rcases n with _ | index
    · cases selected
    · by_cases valid : index < 16
      · simp only [selectNumeric, selectStack, Option.orElse, valid, dite_true] at selected
        cases selected; rfl
      · simp only [selectNumeric, selectStack, Option.orElse, valid, dite_false] at selected
        cases selected
  case swap n =>
    rcases n with _ | index
    · cases selected
    · by_cases valid : index < 16
      · simp only [selectNumeric, selectStack, Option.orElse, valid, dite_true] at selected
        cases selected; rfl
      · simp only [selectNumeric, selectStack, Option.orElse, valid, dite_false] at selected
        cases selected
  all_goals cases selected <;> rfl

/-- Scalar-selected code contains no control instruction. -/
theorem compileScalar_free (ir : List Evm.Instr) (code : Program)
    (selected : compileScalar ir = some code) :
    code.all (fun i => !control i) = true := by
  induction ir generalizing code with
  | nil =>
    simp only [compileScalar, compileWith, Option.some.injEq] at selected
    subst code
    rfl
  | cons instruction rest ih =>
    cases first : selectScalar instruction with
    | none =>
      simp only [compileScalar, compileWith, first, Option.bind_none, reduceCtorEq] at selected
    | some certificate =>
      cases next : compileWith selectScalar rest with
      | none =>
        simp only [compileScalar, compileWith, first, next, Option.bind_some,
          Option.map_none, reduceCtorEq] at selected
      | some tailCode =>
        have codes : certificate.code ++ tailCode = code := by
          simpa only [compileScalar, compileWith, first, next, Option.bind_some,
            Option.map_some, Option.some.injEq] using selected
        subst code
        rw [List.all_append, selectScalar_free instruction certificate first, ih tailCode next]
        rfl

/-- IR and bytes agree on a numeric entry stack: both succeed, the bytes along
a capacity-safe trace to the end of the code, or the IR faults and the byte
machine is stuck. No other IR outcome occurs. -/
def ByteAgree (ir : List Evm.Instr) (code : Program) (input : Scalar.Stack) (m : Machine) : Prop :=
  (∃ output, Evm.run ir m = .ok { m with stack := irStack output } 0 ∧
    ExecutionTrace.Safe (encode code) code.length ⟨0, input⟩ ⟨size code, output⟩) ∨
  (Evm.run ir m = .fault ∧ Stuck (encode code) ⟨0, input⟩)

theorem byte_agree (ir : List Evm.Instr) (code : Program) (selected : compileScalar ir = some code)
    (input : Scalar.Stack) (capacity : Scalar.stackBound code (input.length : Int) = true)
    (m : Machine) (stack : m.stack = irStack input) : ByteAgree ir code input m := by
  have equation := compileScalar_equation ir code selected input m stack
  cases result : Scalar.run code input with
  | none =>
    rw [result] at equation
    refine .inr ⟨equation, ?_⟩
    simpa only [List.nil_append, List.append_nil, List.length_nil] using
      scalar_stuck code [] [] input (compileScalar_free ir code selected) result
  | some output =>
    rw [result] at equation
    refine .inl ⟨output, equation, ?_⟩
    simpa only [List.nil_append, List.append_nil, List.length_nil, Nat.zero_add] using
      ExecutionTrace.scalar_bytes code [] [] input output result capacity

/-! ## The composed typed-to-bytes outcome -/

/-- An accepted world on a numeric stack, through the bytes: the typed run
succeeds and the bytes reach the end of the code in the state `Rep` relates, or
the typed run diverges and the byte machine is stuck. -/
def AgreesBytes {C : Contract} {b : Nat} {Γ Δ : Ctx} {F : Frag Γ} {P : Solidity.Prog C Γ Δ}
    (r : Compilation b F P) (code : Program) (L frame : Nat) (base : Nat → Fin W)
    (σ : State C Γ) (m : Machine) (input : Scalar.Stack) : Prop :=
  (∃ o, P.run σ = .ok o ∧
    ExecutionTrace.Safe (encode code) code.length ⟨0, input⟩ ⟨size code, input⟩ ∧
    r.Rep (L + Evm.Prog.pushes P) frame base σ m o.st m) ∨
  (P.run σ = .error .diverge ∧ Stuck (encode code) ⟨0, input⟩)

theorem agrees_bytes {C : Contract} {b L frame : Nat} {Γ Δ : Ctx} {F : Frag Γ}
    {P : Solidity.Prog C Γ Δ} (r : Compilation b F P) {code : Program}
    {base : Nat → Fin W} {σ : State C Γ} {m : Machine} {input : Scalar.Stack}
    (exact : r.AgreesExact L frame base σ m) (bytes : ByteAgree r.code code input m)
    (stack : m.stack = irStack input) :
    AgreesBytes r code L frame base σ m input := by
  rcases exact with ⟨o, m', ho, hc, hst, hrep⟩ | ⟨-, hc⟩ | ⟨hd, hc⟩
  · rcases bytes with ⟨output, hb, trace⟩ | ⟨hb, -⟩
    · rw [hc] at hb
      cases hb
      have same : input = output := Selection.irStack_injective (stack.symm.trans hst.symm)
      subst same
      refine .inl ⟨o, ho, trace, ?_⟩
      have machine : ({ m with stack := irStack input } : Machine) = m := by
        rw [← stack]
      rw [machine] at hrep
      exact hrep
    · rw [hc] at hb; cases hb
  · rcases bytes with ⟨_, hb, -⟩ | ⟨hb, -⟩ <;> (rw [hc] at hb; cases hb)
  · rcases bytes with ⟨_, hb, -⟩ | ⟨-, stuck⟩
    · rw [hc] at hb; cases hb
    · exact .inr ⟨hd, stuck⟩

end Endpoint

open Endpoint

/-- **The compiler endpoint.** For every typed program, either the checked entry
refuses it (R1), or it returns a result `r` such that

* for every world bound `L frame`: the static bound fails and no world with
  those bounds is accepted (R2), or it holds and every accepted world agrees
  exactly (`AgreesExact`, no payment disjunct);
* the emitted code has no byte selection (R3), or it selects `code`, and for
  every numeric entry stack: the byte stack bound fails (R4), or IR and bytes
  agree, and every accepted world through these bytes satisfies `AgreesBytes`. -/
def CompilerEndpoint : Prop :=
  ∀ {C : Contract} {Γ Δ : Ctx} (b : Nat) (F : Frag Γ) (P : Solidity.Prog C Γ Δ),
    Compiler.compile b F P = none ∨
    ∃ r : Compilation b F P, Compiler.compile b F P = some r ∧
      (∀ L frame : Nat,
        (staticBound r L frame = false ∧
          ∀ (base : Nat → Fin W) (σ : State C Γ) (m : Machine), ¬ r.Input L frame base σ m) ∨
        (staticBound r L frame = true ∧
          ∀ (base : Nat → Fin W) (σ : State C Γ) (m : Machine),
            r.Input L frame base σ m → r.AgreesExact L frame base σ m)) ∧
      (compileScalar r.code = none ∨
        ∃ code : Program, compileScalar r.code = some code ∧
          ∀ input : Scalar.Stack,
            Scalar.stackBound code (input.length : Int) = false ∨
            (Scalar.stackBound code (input.length : Int) = true ∧
              ∀ (m : Machine), m.stack = irStack input →
                ByteAgree r.code code input m ∧
                ∀ (L frame : Nat) (base : Nat → Fin W) (σ : State C Γ),
                  r.Input L frame base σ m → AgreesBytes r code L frame base σ m input))

/-- `CompilerEndpoint` holds, composed from `Compilation.correct_exact`,
`input_bound`, `compileScalar_equation`, `ExecutionTrace.scalar_bytes` and
`scalar_stuck`; no stage is assumed. -/
theorem compiler_endpoint_correct : CompilerEndpoint := by
  intro C Γ Δ b F P
  cases accepted : Compiler.compile b F P with
  | none => exact .inl rfl
  | some r =>
    refine .inr ⟨r, rfl, ?_, ?_⟩
    · intro L frame
      cases bound : staticBound r L frame
      · exact .inl ⟨rfl, fun base σ m h => by rw [input_bound r h] at bound; cases bound⟩
      · exact .inr ⟨rfl, fun base σ m h => r.correct_exact h⟩
    · cases selected : compileScalar r.code with
      | none => exact .inl rfl
      | some code =>
        refine .inr ⟨code, rfl, fun input => ?_⟩
        cases capacity : Scalar.stackBound code (input.length : Int)
        · exact .inl rfl
        · refine .inr ⟨rfl, fun m stack => ⟨byte_agree r.code code selected input capacity m stack, ?_⟩⟩
          intro L frame base σ h
          exact agrees_bytes r (r.correct_exact h)
            (byte_agree r.code code selected input capacity m stack) stack

end Solidity.Backend

#print axioms Solidity.Backend.compiler_endpoint_correct
#print axioms Solidity.Backend.Endpoint.scalar_stuck
#print axioms Solidity.Backend.Endpoint.byte_agree
#print axioms Solidity.Backend.Endpoint.input_bound
