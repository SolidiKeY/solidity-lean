import Solidity.Lowering.V08.CallableReflection

/-! Guards reflection witnesses that prove only observation injectivity while
all actual calls fail, or silently replace injective bytes with lossy length.
An actual funded setup/call and tagged observation share the SAME entire World
and return value. This is intrinsic callable reflection, not Source/ABI/compiler
adequacy or the canonical H68 bridge. -/
namespace H62.AuditV08Adapters.CallableReflectionJoint
open Solidity Solidity.Lowering.V08
open Solidity.ContractWorld
open CallableReflection

/-- A successful raw call, its tagged observation and the injectivity premise
coexist on the same funded setup and complete returned World. -/
def Joint : Prop := ∃ (world next : World Controls.catalog) (value : List UInt8),
  Controls.setup = .ok world ∧
  world.call (⟨Controls.self⟩ : Handle ()) Controls.entry Controls.paidCtx = .ok (next,value) ∧
  world.call (⟨Controls.self⟩ : Handle ()) (observeEntry Controls.entry tagged) Controls.paidCtx =
    .ok (next,tagged value) ∧
  (∀ a b, tagged a = tagged b → a = b)

/-- The published successful execution eliminates both failure cases. The
witness is the actual run result, not a World reconstructed from a vector. -/
theorem joint : Joint := by
  have success := Controls.funded_call
  cases setupRun : Controls.setup with
  | error halt => simp [Controls.paidObservation, setupRun, bind, Except.bind, Except.toOption] at success
  | ok world =>
    cases callRun : world.call (⟨Controls.self⟩ : Handle ()) Controls.entry Controls.paidCtx with
    | error halt => simp [Controls.paidObservation, setupRun, callRun, bind, Except.bind, Except.toOption] at success
    | ok pair =>
      refine ⟨world, pair.1, pair.2, setupRun, callRun, ?_, tagged_injective⟩
      rw [call_observeEntry, callRun]
      rfl

/-- Full original reflection equivalence on the same actual successful call;
both directions retain the exact World and exact bytes, not just a vector. -/
theorem actual : ∃ (world next : World Controls.catalog) (value : List UInt8),
    Controls.setup = .ok world ∧
    world.call (⟨Controls.self⟩ : Handle ()) Controls.entry Controls.paidCtx = .ok (next,value) ∧
    (world.call (⟨Controls.self⟩ : Handle ()) (observeEntry Controls.entry tagged) Controls.paidCtx =
      .ok (next,tagged value) ↔
      world.call (⟨Controls.self⟩ : Handle ()) Controls.entry Controls.paidCtx = .ok (next,value)) := by
  obtain ⟨world,next,value,setupRun,callRun,observed,injective⟩ := joint
  exact ⟨world,next,value,setupRun,callRun,
    success_iff world _ _ _ tagged injective next value⟩

/-- H69: lossy length deliberately lacks the theorem's injectivity premise.
This is a proved non-inhabitant, never a fabricated ordinary witness. -/
theorem length_not_injective :
    ¬ ∀ a b : List UInt8, a.length = b.length → a = b := by
  intro injective
  have impossible := injective [0xab,0xcd] [0xab,0xce] rfl
  cases impossible

/-- The original real paid calls can agree on length and differ in bytes. -/
theorem lossy_is_not_exact :
    Controls.extendedObservation.toOption = lossyAlternative.toOption ∧
    Controls.paidObservation.toOption ≠ exactAlternative.toOption :=
  ⟨lossy_equal, exact_distinct⟩

#print axioms joint
#print axioms actual
#print axioms length_not_injective
#print axioms lossy_is_not_exact
end H62.AuditV08Adapters.CallableReflectionJoint
