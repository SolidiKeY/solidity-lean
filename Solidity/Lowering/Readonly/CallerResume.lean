import Solidity.Lowering.Readonly.InvocationFrame

/-! Exact raw-call to caller-decoder transport. Raw execution is an explicit
premise, not produced by metadata or a storage frame. The existing extReturn
executes with the original caller locals and actual callee final state. -/
namespace Solidity.Lowering.Readonly.CallerResume
open Solidity.Source Solidity.Backend.Passes.SourceTypedCall
open Solidity.Roadmap (Outcome)
variable {E : Env} {Γ : RCtx} {ps : List STy}

theorem success (global : Glob E) (frame : Fr) (n : Nat) (d : Decl)
    (rs : List STy) (captured : Captured E ps) (locals : Locals E.layout Γ)
    (entry final : St E) (outcome : Outcome)
    (raw : (callAddr global frame n captured.receiver captured.value captured.input
      (d.fnMut == some .view || d.fnMut == some .pure)).run (L0 E, entry) =
        (.ok outcome, (L0 E, final))) :
    (resume global frame n d rs captured).run (locals, entry) =
      (extReturn rs outcome).run (locals, final) := by
  simp only [resume, EM.sub, bind, ExceptT.bind, ExceptT.bindCont,
    ExceptT.run, ExceptT.mk, StateT.bind]
  dsimp only [ExceptT.run] at raw
  rw [raw] <;> rfl

theorem halted (global : Glob E) (frame : Fr) (n : Nat) (d : Decl)
    (rs : List STy) (captured : Captured E ps) (locals : Locals E.layout Γ)
    (entry final : St E) (halt : Halt)
    (raw : (callAddr global frame n captured.receiver captured.value captured.input
      (d.fnMut == some .view || d.fnMut == some .pure)).run (L0 E, entry) =
        (.error halt, (L0 E, final))) :
    (resume global frame n d rs captured).run (locals, entry) =
      (.error halt, (locals, final)) := by
  simp only [resume, EM.sub, bind, ExceptT.bind, ExceptT.bindCont,
    ExceptT.run, ExceptT.mk, StateT.bind]
  dsimp only [ExceptT.run] at raw
  rw [raw] <;> rfl

/-- Complete external expression, with its actual capture state. Successful
raw bytes still pass through the declared-return decoder before use/discard. -/
theorem invocation {dn : DeclName} {rs : List STy}
    (i : InvocationFrame.Invocation E Γ dn ps rs) (outcome : Outcome) (final : St E)
    (raw : i.RawAt (.ok outcome) final) :
    (evalE i.global i.frame (i.horizon + 1)
      (.extCall i.target i.declaration i.signature i.value i.arguments)).run i.before =
      (extReturn rs outcome).run (i.after.1, final) := by
  rw [external_captured _ _ _ _ _ _ _ _ _ _ _ i.execution]
  exact success i.global i.frame i.horizon i.declaration rs i.captured i.after.1
    i.after.2 final outcome raw

/-- Non-returning raw executions bypass decoding, retaining the exact halt
and actual callee-final state after the real source argument capture. -/
theorem invocation_halted {dn : DeclName} {rs : List STy}
    (i : InvocationFrame.Invocation E Γ dn ps rs) (halt : Halt) (final : St E)
    (raw : i.RawAt (.error halt) final) :
    (evalE i.global i.frame (i.horizon + 1)
      (.extCall i.target i.declaration i.signature i.value i.arguments)).run i.before =
      (.error halt, (i.after.1, final)) := by
  rw [external_captured _ _ _ _ _ _ _ _ _ _ _ i.execution]
  exact halted i.global i.frame i.horizon i.declaration rs i.captured i.after.1
    i.after.2 final halt raw

end Solidity.Lowering.Readonly.CallerResume
