import Solidity.Backend.StructuredFlow.SourceDispatchRecognitionLaws
import Solidity.Backend.StructuredFlow.SourceDispatchLower
import Solidity.Backend.Payments.EntrySuccess

/-!
# Source template dispatch to the actual compiler entry

Guards a lexical-only dispatcher claiming compiler integration. This function
recognizes the exact existing Source term, checks its context-map operands,
reuses the published intrinsic program, and invokes `Evm.Compiler.compile`.
Syntax, operand typing, and the original core-fragment boundary have separate
refusals. Source operational correctness is supplied separately by the
existing per-construct theorems; extraction alone is not Source adequacy.
-/
namespace Solidity.Backend.StructuredFlow.SourceDispatch
open Solidity.Lowering.V07

inductive Refusal where
  | unsupportedSource
  | incompatibleMapping
  | outsideCoreFragment
  | compilerRefusal
  deriving DecidableEq, Repr

structure Compiled {E : Source.Env} {M : Bool} {R : List Source.STy}
    {k : Source.SCtx} {srcΓ srcΔ : Source.RCtx} (s : Source.RStmt E R M k srcΓ srcΔ)
    {C : Contract} {Γ : Ctx} (m : ContextMap srcΓ Γ) (base : Nat) (frame : Evm.Frag Γ) where
  plan : Plan E M s
  mapping : Mapping m plan
  outFrame : Evm.Frag (program (C := C) m plan mapping).1
  admitted : Evm.inFragP frame (program (C := C) m plan mapping).2 = some outFrame
  result : Evm.Compiler.Compilation base frame (program (C := C) m plan mapping).2
  accepted : Evm.Compiler.compile base frame (program (C := C) m plan mapping).2 = some result

/-- Executable Source-to-compiler dispatch, with the original admission checks. -/
def dispatch {E : Source.Env} {M : Bool} {R : List Source.STy}
    {k : Source.SCtx} {srcΓ srcΔ : Source.RCtx} (s : Source.RStmt E R M k srcΓ srcΔ)
    {C : Contract} {Γ : Ctx} (m : ContextMap srcΓ Γ) (base : Nat) (frame : Evm.Frag Γ) :
    Except Refusal (Compiled (C := C) s m base frame) :=
  match recognize s with
  | none => .error .unsupportedSource
  | some plan =>
    match mapping? m plan with
    | none => .error .incompatibleMapping
    | some mapping =>
      match hf : Evm.inFragP frame (program (C := C) m plan mapping).2 with
      | none => .error .outsideCoreFragment
      | some outFrame =>
        match hc : Evm.Compiler.compile base frame (program (C := C) m plan mapping).2 with
        | none => .error .compilerRefusal
        | some result => .ok ⟨plan,mapping,outFrame,hf,result,hc⟩

/-- The actual accepted entry is the original core compiler at the same code. -/
theorem Compiled.result_eq_core {E : Source.Env} {M : Bool} {R : List Source.STy}
    {k : Source.SCtx} {srcΓ srcΔ : Source.RCtx} {s : Source.RStmt E R M k srcΓ srcΔ}
    {C : Contract} {Γ : Ctx} {m : ContextMap srcΓ Γ} {base : Nat} {frame : Evm.Frag Γ}
    (compiled : Compiled (C := C) s m base frame) :
    compiled.result = .core compiled.outFrame compiled.admitted :=
  Option.some.inj (compiled.accepted.symm.trans
    (Evm.Compiler.compile_core_some compiled.admitted))

/-- Exact emitted code of the actual returned compiler artifact. -/
theorem Compiled.code_exact {E : Source.Env} {M : Bool} {R : List Source.STy}
    {k : Source.SCtx} {srcΓ srcΔ : Source.RCtx} {s : Source.RStmt E R M k srcΓ srcΔ}
    {C : Contract} {Γ : Ctx} {m : ContextMap srcΓ Γ} {base : Nat} {frame : Evm.Frag Γ}
    (compiled : Compiled (C := C) s m base frame) :
    compiled.result.code = Evm.compileProg base (program (C := C) m compiled.plan compiled.mapping).2 := by
  rw [compiled.result_eq_core]
  rfl

/-- All syntax outside the exact union is refused before lowering. -/
theorem dispatch_refuses {E : Source.Env} {M : Bool} {R : List Source.STy}
    {k : Source.SCtx} {srcΓ srcΔ : Source.RCtx} (s : Source.RStmt E R M k srcΓ srcΔ)
    {C : Contract} {Γ : Ctx} (m : ContextMap srcΓ Γ) (base : Nat) (frame : Evm.Frag Γ)
    (outside : ¬ Supported s) : dispatch (C := C) s m base frame = .error .unsupportedSource := by
  simp [dispatch,recognize_refuses s outside]

/-- Any original derived exit frame for this same program is the returned one. -/
theorem Compiled.output_unique {E : Source.Env} {M : Bool} {R : List Source.STy}
    {k : Source.SCtx} {srcΓ srcΔ : Source.RCtx} {s : Source.RStmt E R M k srcΓ srcΔ}
    {C : Contract} {Γ : Ctx} {m : ContextMap srcΓ Γ} {base : Nat} {frame : Evm.Frag Γ}
    (compiled : Compiled (C := C) s m base frame)
    (other : Evm.Frag (program (C := C) m compiled.plan compiled.mapping).1)
    (admitted : Evm.inFragP frame (program (C := C) m compiled.plan compiled.mapping).2 = some other) :
    compiled.outFrame = other := Option.some.inj (compiled.admitted.symm.trans admitted)

end Solidity.Backend.StructuredFlow.SourceDispatch
