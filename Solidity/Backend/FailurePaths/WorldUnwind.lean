import Solidity.Backend.FailurePaths.Statements
import Solidity.Backend.MemoryOps.PhysicalWorldUnwind

/-!
# Explicit world unwind after a completed failure statement

The actual source world operation journal and local byte checkpoint are linked
through the published world projection. Neither the source heap nor its event
and log fields are silently restored; physical transient adequacy remains P7.
-/
namespace Solidity.Backend.FailurePaths
open Source

/-- The source statement runs at the dirty world reached by real journal ops.
The separate caller rollback restores the complete source execution journal.
The local byte checkpoint restores its two store projections and caller machine,
while retaining the exact immutable payload read before restoration. -/
theorem literal_world_unwind {E : Source.Env} {Γ : RCtx} {τ : STy}
    (global : Glob E) (frame : Fr) (extra offset : Nat) (expr : RExpr E Γ τ)
    (input : Failure.Input)
    (selected : Lowering.V08.LiteralFailureLowering.literalInput expr = some input)
    (locals : Locals E.layout Γ) (initial : St E)
    (ops : List (Source.Op E.layout E.lay E.lay))
    (saved live : Failure.Slice.Machine)
    (fits : Failure.Fits offset input.bytes) (stack : live.stack.length + 2 ≤ 1024) :
    let reached := {initial with ex := initial.ex.run ops}
    StatementReverts global frame (extra + 7) (.expr expr) locals reached reached input.bytes ∧
    (initial.ex.enter frame.this frame.sender frame.value frame.cd frame.static).rollback
      reached.ex = initial.ex ∧
    Failure.Local.execute (Failure.Local.save
      (MemoryOps.Physical.worldJournal initial.ex saved)) offset input
      (MemoryOps.Physical.worldJournal reached.ex live) =
      some (MemoryOps.Physical.worldJournal initial.ex saved, .revert input.bytes) := by
  let reached := {initial with ex := initial.ex.run ops}
  obtain ⟨_, source, outcome, _⟩ :=
    literal_statement global frame extra offset expr input selected locals reached
  refine ⟨source, Source.rollback_run initial.ex ops frame.this frame.sender frame.value frame.cd frame.static, ?_⟩
  rw [Failure.Local.execute_emitter _ offset input _ fits stack, outcome]
  rfl

#print axioms literal_world_unwind
end Solidity.Backend.FailurePaths
