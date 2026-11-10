import Solidity.Correctness.Lowering.Loops.WhileBreak
import Solidity.Correctness.Lowering.Checker.WhileBreak

/-!
# `lowerLoops_correct`

The generic family statement `Loops.LowerLoopsCorrect`, proved leaf by leaf
(one `Shape` constructor per G19 loop leaf), and its connection to the actual
producer: the quoted output of running the real `lowerLoops` and then the real
intrinsic elaborator (`Checker.RawProbe.actual`, `Checker.IntrinsicProbe.actual`)
is accepted by the kernel, and the actual Source typing of the same loop is the
family's Source statement. The producer itself is never unfolded.

Partiality: theorems speak of accepted outputs only. Producer refusals
(`break`/`continue` outside a loop, `return` outside a body, jumps in `try`
inside a loop, Lower.lean:448-449, 455, 474) and non-family outputs are not
covered; they are coverage gaps, not counterexamples.
-/
namespace Solidity.Correctness.Lowering

open Solidity.Lowering.V07
open Loops

/-- **Loop lowering correctness** on the accepted family (finish-line component
`Solidity.Goals.lowerLoopsCorrect`, owner e1-loops). -/
theorem lowerLoops_correct : Loops.LowerLoopsCorrect := by
  intro k E srcΓ returns M l u C Γ m p names output accepted
  cases accepted
  cases k with
  | whileBreak => exact ⟨.drop .refl, WhileBreak.endpoint m p names⟩

namespace Loops.Coverage

open Checker

/-- Position facts of the concrete caller pair `i, a` used by the probes. -/
def whileBreakPair : Pair Checker.WhileBreak.mapping where
  i := .here
  a := .there .here
  hi := rfl
  ha := rfl
  mapI := rfl
  mapA := rfl

/-- The fresh names the actual producer and elaborator chose. -/
def whileBreakNames : Fresh := ⟨Var.fresh "brk" 1, Var.fresh "se" 2⟩

/-- Kernel acceptance of the actual `lowerLoops` + `elabStmtsP` output for
`while (i = a) break;`. Guards against the family drifting from the producer:
a changed lowering or elaboration makes this `rfl` fail. -/
theorem whileBreak_accepts :
    Accepts .whileBreak whileBreakPair whileBreakNames IntrinsicProbe.actual.program := rfl

/-- The actual Source typing of the same loop is the family's Source statement. -/
theorem whileBreak_source (E : Source.Env) :
    SourceAssociation.resolved E =
      Shape.whileBreak.source (E := E) (returns := []) (M := false) (l := false) (u := false)
        whileBreakPair := rfl

/-- End to end for the actual sample: raw producer output accepted by the raw
matcher, intrinsic output accepted by the family, and the endpoint against the
actual resolved Source loop. -/
theorem whileBreak_actual (E : Source.Env) :
    RawProbe.checkRaw RawProbe.input RawProbe.actual.raw 1 = true ∧
    ∃ embedding : Thin IntrinsicProbe.Γ IntrinsicProbe.actual.program.1,
      Endpoint (SourceAssociation.resolved E) Shape.whileBreak.offset
        Checker.WhileBreak.mapping IntrinsicProbe.actual.program.2 embedding := by
  refine ⟨RawProbe.accepts_actual, ?_⟩
  rw [whileBreak_source E]
  exact lowerLoops_correct .whileBreak Checker.WhileBreak.mapping whileBreakPair whileBreakNames
    IntrinsicProbe.actual.program whileBreak_accepts

end Loops.Coverage

#print axioms lowerLoops_correct
#print axioms Loops.Coverage.whileBreak_accepts
#print axioms Loops.Coverage.whileBreak_source
#print axioms Loops.Coverage.whileBreak_actual

end Solidity.Correctness.Lowering
