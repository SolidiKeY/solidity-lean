import Solidity.Lowering.P8.SourceSize
import Solidity.Lowering.V08.SourceTransactionControls

/-! Actual Source size-panic controls on a populated published caller state.
A length assignment changes a local BEFORE the array-length panic. Complete
source state and ordered observations are retained, without a transaction-end
rollback claim. The published fixture has toyFixed; this is not a pinned EVM,
full source admission or finalize-allocation/cursor-overflow certificate. -/
namespace Solidity.Roadmap.V16.SourceSizeControls
open Solidity Source
open Source.SemanticsExamples
open Solidity.Lowering.V08.SourceTransactionControls

abbrev Context : RCtx := [uint,uint]
def count : Nat := 2 ^ 64
def bigValue : Source.Val EB.layout uint := .int count (by decide)
def marker : Source.Val EB.layout uint := .int 77 (by decide)
def before (bytes : Roadmap.Bytes) : Source.EMState EB Context :=
  (.cons v1 (.cons marker .nil), initial bytes)
def reached (bytes : Roadmap.Bytes) : Source.EMState EB Context :=
  (.cons bigValue (.cons marker .nil), initial bytes)
def length : RExpr EB Context uint := .assign (.local .here) (lit count)
def allocation : RExpr EB Context (.bytes .memory) :=
  .newArray (by decide) length (by decide)

/-- Actual length evaluation writes only the selected local; the second
local and the COMPLETE populated Source state survive unchanged. -/
theorem child_success (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes) :
    (Source.evalE (global pipeline) F0 3 length).run (before bytes) =
      (.ok (.val bigValue), reached bytes) := by rfl

/-- The exact conversion used by the published panic law. -/
theorem conversion (bytes : Roadmap.Bytes) :
    (Source.indexNat (E := EB) (Γ := Context) (.val bigValue)).run (reached bytes) =
      (.ok count, reached bytes) := by rfl

/-- Independent kernel baseline, so the unchanged record's failure field
is itself discharged by actual execution rather than assumed. -/
theorem baseline (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes) :
    (Source.evalE (global pipeline) F0 4 allocation).run (before bytes) =
      (Source.panic .alloc, reached bytes) := by rfl

/-- A real inhabitant of every field of the unchanged producer premise. -/
def premise (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes) :
    Solidity.Backend.MemoryCopies.NewArrayLengthPanicPremise (global pipeline) F0 3
      (τ := .bytes .memory) (by decide) length (by decide) (.val bigValue) count
      (before bytes) (reached bytes) where
  evaluation := child_success pipeline bytes
  conversion := conversion bytes
  oversized := by decide
  failure := baseline pipeline bytes

/-- Instantiates the NEW derived law on an actual populated, mutating run. -/
theorem applied_failure (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes) :
    (Source.evalE (global pipeline) F0 4 allocation).run (before bytes) =
      (Source.panic .alloc, reached bytes) :=
  (premise pipeline bytes).failure_of_parts

/-- Complete actual result, both locals and the ENTIRE Source state, not a selection of matching cells. Ordered events/logs remain those of the populated input. -/
theorem full_observation :
    ∀ (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes),
    let output := (Source.evalE (global pipeline) F0 4 allocation).run (before bytes)
    (output.1, Source.RVal.amount (.val (output.2.1.get .here)), Source.RVal.amount (.val (output.2.1.get (.there .here))), output.2.2) = (Source.panic .alloc, .ok count, .ok 77, initial bytes) := by
  intro pipeline bytes
  dsimp only
  simp only [applied_failure]
  rfl

/-- Existing Source Hoare consequence: exact allocation-panic bytes and reached state; no successful exit or transaction-end rollback is introduced. -/
theorem panic_hoare :
    ∀ (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes),
    Source.Hoare (fun x => x = before bytes)
    (Source.evalE (global pipeline) F0 4 allocation)
    (fun _ _ => False) (fun halt output => halt = .revert (Source.panicData .alloc) ∧ output = reached bytes) := by
  intro pipeline bytes x hx
  subst x
  rw [applied_failure]
  exact ⟨rfl,rfl⟩

/-- The first local was changed before the panic; returning the initial locals would erase a real side effect. -/
theorem wrong_rollback :
    ∀ (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes),
    (Source.evalE (global pipeline) F0 4 allocation).run (before bytes) ≠ (Source.panic .alloc, before bytes) := by
  intro pipeline bytes
  rw [applied_failure]
  intro same
  have observed := congrArg (fun z => Source.RVal.amount (.val (z.2.1.get .here))) same
  change Except.ok count = Except.ok 1 at observed
  have bad : count = 1 := Except.ok.inj observed
  exact (by decide : count ≠ 1) bad

/-- Allocation panic data cannot be replaced by the empty revert payload. -/
theorem wrong_empty_revert :
    ∀ (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes),
    (Source.evalE (global pipeline) F0 4 allocation).run (before bytes) ≠ (.error (.revert []), reached bytes) := by
  intro pipeline bytes
  rw [applied_failure]
  intro same
  have bad : Source.Halt.revert (Source.panicData .alloc) = .revert [] := Except.error.inj (congrArg Prod.fst same)
  exact (by decide : Source.Halt.revert (Source.panicData .alloc) ≠ .revert []) bad

/-- At fuel four this actual expression panics; it is not a timeout. -/
theorem wrong_timeout :
    ∀ (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes),
    (Source.evalE (global pipeline) F0 4 allocation).run (before bytes) ≠ (.error .timeout, reached bytes) := by
  intro pipeline bytes
  rw [applied_failure]
  intro same
  have bad : Source.Halt.revert (Source.panicData .alloc) = .timeout := Except.error.inj (congrArg Prod.fst same)
  cases bad

/-- At fuel zero the actual expression times out before the length assignment, preserving its initial state. Timeout is not divergence. -/
theorem zero_fuel :
    ∀ (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes),
    (Source.evalE (global pipeline) F0 0 allocation).run (before bytes) = (.error .timeout, before bytes) := by
  intro pipeline bytes; rfl

/-- A zero-count certificate cannot inhabit the unchanged oversized premise; no new Source exclusion or admission predicate is imposed. -/
theorem wrong_count_premise :
    ∀ (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes),
    ¬ Nonempty (Solidity.Backend.MemoryCopies.NewArrayLengthPanicPremise (global pipeline) F0 3 (τ := .bytes .memory) (by decide) length (by decide) (.val bigValue) 0 (before bytes) (reached bytes)) := by
  rintro pipeline bytes ⟨p⟩
  have bad := p.oversized
  exact (by decide : ¬ 2 ^ 64 ≤ (0 : Nat)) bad

end Solidity.Roadmap.V16.SourceSizeControls

/-- info: 'Solidity.Roadmap.V16.SourceSizeControls.child_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Roadmap.V16.SourceSizeControls.child_success

/-- info: 'Solidity.Roadmap.V16.SourceSizeControls.conversion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Roadmap.V16.SourceSizeControls.conversion

/-- info: 'Solidity.Roadmap.V16.SourceSizeControls.baseline' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Roadmap.V16.SourceSizeControls.baseline

/-- info: 'Solidity.Roadmap.V16.SourceSizeControls.premise' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Roadmap.V16.SourceSizeControls.premise

/-- info: 'Solidity.Roadmap.V16.SourceSizeControls.applied_failure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Roadmap.V16.SourceSizeControls.applied_failure

/-- info: 'Solidity.Roadmap.V16.SourceSizeControls.full_observation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Roadmap.V16.SourceSizeControls.full_observation

/-- info: 'Solidity.Roadmap.V16.SourceSizeControls.panic_hoare' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Roadmap.V16.SourceSizeControls.panic_hoare

/-- info: 'Solidity.Roadmap.V16.SourceSizeControls.wrong_rollback' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Roadmap.V16.SourceSizeControls.wrong_rollback

/-- info: 'Solidity.Roadmap.V16.SourceSizeControls.wrong_empty_revert' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Roadmap.V16.SourceSizeControls.wrong_empty_revert

/-- info: 'Solidity.Roadmap.V16.SourceSizeControls.wrong_timeout' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Roadmap.V16.SourceSizeControls.wrong_timeout

/-- info: 'Solidity.Roadmap.V16.SourceSizeControls.zero_fuel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Roadmap.V16.SourceSizeControls.zero_fuel

/-- info: 'Solidity.Roadmap.V16.SourceSizeControls.wrong_count_premise' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Roadmap.V16.SourceSizeControls.wrong_count_premise
