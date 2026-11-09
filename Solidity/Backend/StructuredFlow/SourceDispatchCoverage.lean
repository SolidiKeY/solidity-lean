import Solidity.Backend.StructuredFlow.SourceDispatch
import Solidity.Backend.StructuredFlow.SourceDispatchSlotLaws
import Solidity.Backend.StructuredFlow.SourceDispatchCorrect

/-!
# Actual compiler-entry coverage for recognized Source templates

Guards separate syntax and mapping completeness laws concealing a reject-all
actual dispatcher. The generic acceptance theorem covers all sixteen selected
families, with the same core-fragment check retained by their existing APIs.
No Source-success or favourable-machine-run premise is used for compilation.
-/
namespace Solidity.Backend.StructuredFlow.SourceDispatch
open Solidity.Lowering.V07 Solidity.Lowering.G19

private theorem exitFrame_eq {Γ : Ctx} (frame : Evm.Frag Γ) :
    ForBreakCompiler.exitFrame frame = frame := by
  cases frame
  simp [ForBreakCompiler.exitFrame,Evm.Frag.push,Evm.Frag.restrict]

private theorem reset_admitted {srcΓ : Source.RCtx} {C : Contract} {Γ : Ctx}
    (frame : Evm.Frag Γ) (m : ContextMap srcΓ Γ) (i a : Source.Idx srcΓ .bool)
    (hi : (m.slot i).1 = .val .bool) (ha : (m.slot a).1 = .val .bool) :
    Evm.inFragP frame (AssignmentWhileReset.code (C := C) m i a hi ha) = some frame := by
  have pushes : Evm.Prog.pushes (AssignmentWhileBreak.code (C := C) m i a hi ha) = 0 := rfl
  have pays : Evm.Prog.pays (AssignmentWhileBreak.code (C := C) m i a hi ha) = false := rfl
  have shrinks : Evm.Prog.shrinks (AssignmentWhileBreak.code (C := C) m i a hi ha) = false := rfl
  simp [AssignmentWhileReset.code,AssignmentWhileReset.body,
    Evm.inFragP,Evm.inFrag,Evm.valIn,Evm.simpleIn,Evm.Frag.guard,
    Evm.Prog.pushes,Evm.Prog.pays,Evm.Prog.shrinks,
    Evm.Stmt.pushes,Evm.Stmt.pays,Evm.Stmt.shrinks,pushes,pays,shrinks,
    ForBreakCompiler.admitted,exitFrame_eq,Evm.Frag.restrict]

/-- Every selected builder is in the core fragment. The defensive refusal
branch is unreachable for this exact template union, including reset loops. -/
theorem program_admitted {E : Source.Env} {M : Bool} {R : List Source.STy}
    {k : Source.SCtx} {srcΓ srcΔ : Source.RCtx} {s : Source.RStmt E R M k srcΓ srcΔ}
    {C : Contract} {Γ : Ctx} (m : ContextMap srcΓ Γ) (plan : Plan E M s)
    (mapped : Mapping m plan) (frame : Evm.Frag Γ) :
    ∃ outFrame, Evm.inFragP frame (program (C := C) m plan mapped).2 = some outFrame := by
  cases plan <;> dsimp [Mapping,program] at mapped ⊢
  case blocks steps =>
    refine ⟨frame,?_⟩
    induction steps with
    | nil => rfl
    | cons step rest ih =>
      cases step
      exact ih
  all_goals try exact ⟨_,rfl⟩
  case whileContinue i a tail => exact ⟨frame,reset_admitted frame m i a _ _⟩
  case forContinue i a tail => exact ⟨frame,reset_admitted frame m i a _ _⟩

/-- Exact executable checks imply an actual accepted compiler artifact. -/
theorem dispatch_checked {E : Source.Env} {M : Bool} {R : List Source.STy}
    {k : Source.SCtx} {srcΓ srcΔ : Source.RCtx} {s : Source.RStmt E R M k srcΓ srcΔ}
    {C : Contract} {Γ : Ctx} (m : ContextMap srcΓ Γ) (base : Nat) (frame : Evm.Frag Γ)
    (plan : Plan E M s) (mapped : Mapping m plan)
    (outFrame : Evm.Frag (program (C := C) m plan mapped).1)
    (recognized : recognize s = some plan) (mapping : mapping? m plan = some mapped)
    (admitted : Evm.inFragP frame (program (C := C) m plan mapped).2 = some outFrame) :
    ∃ compiled, dispatch (C := C) s m base frame = .ok compiled ∧
      compiled.result.code = Evm.compileProg base (program (C := C) m plan mapped).2 := by
  unfold dispatch
  simp only [recognized,mapping]
  split
  next refused => simp [admitted] at refused
  next actualFrame accepted =>
    have compiler := Evm.Compiler.compile_core_some (b := base) accepted
    split
    next refused => simp [compiler] at refused
    next result acceptedCompiler =>
      refine ⟨_,rfl,?_⟩
      have core := Option.some.inj (acceptedCompiler.symm.trans compiler)
      change result.code = _
      rw [core]
      rfl

/-- Exact executable checks imply an actual accepted compiler artifact. -/
theorem dispatch_accepts {E : Source.Env} {M : Bool} {R : List Source.STy}
    {k : Source.SCtx} {srcΓ srcΔ : Source.RCtx} {s : Source.RStmt E R M k srcΓ srcΔ}
    {C : Contract} {Γ : Ctx} (m : ContextMap srcΓ Γ) (base : Nat) (frame : Evm.Frag Γ)
    (plan : Plan E M s) (mapped : Mapping m plan)
    (outFrame : Evm.Frag (program (C := C) m plan mapped).1)
    (recognized : recognize s = some plan) (mapping : mapping? m plan = some mapped)
    (admitted : Evm.inFragP frame (program (C := C) m plan mapped).2 = some outFrame) :
    ∃ compiled, dispatch (C := C) s m base frame = .ok compiled := by
  obtain ⟨compiled,accepted,_⟩ := dispatch_checked m base frame plan mapped outFrame recognized mapping admitted
  exact ⟨compiled,accepted⟩

/-- The original selected mapping and core-admission premises imply actual
entry success, without changing the data or universally strengthening admission. -/
theorem dispatch_complete {E : Source.Env} {M : Bool} {R : List Source.STy}
    {k : Source.SCtx} {srcΓ srcΔ : Source.RCtx} {s : Source.RStmt E R M k srcΓ srcΔ}
    {C : Contract} {Γ : Ctx} (m : ContextMap srcΓ Γ) (base : Nat) (frame : Evm.Frag Γ)
    (plan : Plan E M s) (recognized : recognize s = some plan) (valid : Mapping m plan)
    (outFrame : Evm.Frag (program (C := C) m plan valid).1)
    (admitted : Evm.inFragP frame (program (C := C) m plan valid).2 = some outFrame) :
    ∃ compiled, dispatch (C := C) s m base frame = .ok compiled :=
  dispatch_accepts m base frame plan valid outFrame recognized (mapping_exact m plan valid) admitted

/-- All sixteen original mapping domains reach actual compilation; syntax
recognition supplies the selected plan and no new core-admission premise. -/
theorem dispatch_template_complete {E : Source.Env} {M : Bool} {R : List Source.STy}
    {k : Source.SCtx} {srcΓ srcΔ : Source.RCtx} {s : Source.RStmt E R M k srcΓ srcΔ}
    {C : Contract} {Γ : Ctx} (m : ContextMap srcΓ Γ) (base : Nat) (frame : Evm.Frag Γ)
    (plan : Plan E M s) (valid : Mapping m plan) :
    ∃ compiled, dispatch (C := C) s m base frame = .ok compiled := by
  obtain ⟨outFrame,admitted⟩ := program_admitted (C := C) m plan valid frame
  exact dispatch_complete m base frame plan (recognize_plan_exact plan) valid outFrame admitted

/-- The defensive fragment/compiler-refusal constructors are unreachable on
this exact union. Real errors identify syntax or operand incompatibility. -/
theorem dispatch_error_boundary {E : Source.Env} {M : Bool} {R : List Source.STy}
    {k : Source.SCtx} {srcΓ srcΔ : Source.RCtx} (s : Source.RStmt E R M k srcΓ srcΔ)
    {C : Contract} {Γ : Ctx} (m : ContextMap srcΓ Γ) (base : Nat) (frame : Evm.Frag Γ)
    (why : Refusal) (failed : dispatch (C := C) s m base frame = .error why) :
    why = .unsupportedSource ∨ why = .incompatibleMapping := by
  cases recognized : recognize s with
  | none =>
    simp only [dispatch,recognized] at failed
    cases failed
    exact .inl rfl
  | some plan =>
    cases mapping : mapping? m plan with
    | none =>
      simp only [dispatch,recognized,mapping] at failed
      cases failed
      exact .inr rfl
    | some mapped =>
      obtain ⟨outFrame,admitted⟩ := program_admitted (C := C) m plan mapped frame
      obtain ⟨compiled,accepted⟩ := dispatch_accepts m base frame plan mapped outFrame recognized mapping admitted
      rw [accepted] at failed
      cases failed

end Solidity.Backend.StructuredFlow.SourceDispatch
