import Solidity.MultiStep

/-!
# Rewrite-termination certificates

This module formalizes the proof obligation behind the calculus's proposed
natural-number measure.  Supplying a measure that decreases on every
`BlockStep` yields well-foundedness of the reverse step relation and a
monotonicity theorem for every finite derivation.

The concrete measure for all generated rules is intentionally not postulated:
it must be supplied as a `RewriteTerminationCertificate` once every rule's
decrease lemma has been proved.

Design note for `functionBodyExpand`: the expansion *grows* the block, so
no naive statement-count measure decreases. The intended measure weighs a
`Stmt.callStmt` as `1 + weight (expandCall …)`, which is well-defined
because the function table is acyclic (checked by the `blockCallFree`
lock-in in `Examples/Taclets/FunctionCallOps.lean` — structurally, a
`callRank` on table names with callees strictly smaller). Capture steps
(`functionCallArgCapture`) still decrease the complex-operand count.
-/

namespace Solidity

/-- The local proof obligation for a natural-number rewrite measure. -/
def BlockStepDecreases (measure : SolidityBlock → Nat) : Prop :=
  ∀ {before after}, BlockStep before after → measure after < measure before

/-- A decreasing natural-number measure rules out infinite forward rewrite
sequences. -/
theorem blockStep_wellFounded_of_decreases (measure : SolidityBlock → Nat)
    (hdec : BlockStepDecreases measure) :
    WellFounded (fun after before => BlockStep before after) := by
  refine Subrelation.wf
    (r := InvImage (fun a b : Nat => a < b) measure) ?_
    (InvImage.wf measure Nat.lt_wfRel.wf)
  intro after before hstep
  exact hdec hstep

/-- A checkable package for the remaining concrete termination proof. -/
structure RewriteTerminationCertificate where
  measure : SolidityBlock → Nat
  decreases : BlockStepDecreases measure

namespace RewriteTerminationCertificate

theorem wellFounded (cert : RewriteTerminationCertificate) :
    WellFounded (fun after before => BlockStep before after) :=
  blockStep_wellFounded_of_decreases cert.measure cert.decreases

/-- A certified measure cannot increase along a finite derivation. -/
theorem measure_le {before after : SolidityBlock}
    (cert : RewriteTerminationCertificate)
    (hsteps : BlockReflMultiStep before after) :
    cert.measure after ≤ cert.measure before := by
  induction hsteps with
  | refl => exact Nat.le_refl _
  | step hstep _ ih =>
      exact Nat.le_trans ih (Nat.le_of_lt (cert.decreases hstep))

end RewriteTerminationCertificate

end Solidity
