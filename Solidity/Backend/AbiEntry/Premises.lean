import Solidity.Backend.AbiEntry.Interface
import Solidity.Backend.AbiEntry.Premises.CalldataViewExtensions
import Solidity.Semantics.Run

/-!
# Explicit pending producer boundaries

The coordinator identified overlapping views as V11/G34 (queued); its named
premise is imported from CalldataViews. The original G35.03 boundary remains
separate. G24.03 belongs to V09 and is not frozen. These are
parameterized obligation records, not claims that either producer is complete.
No instance is supplied. In particular the source/target representation and
operation references must come from their actual producers; arbitrary choices
of those parameters do not certify source admission or backend execution.
Actual producer realization and independently pinned input coverage are
separate open requirements; these schemas cannot be consumed as evidence
of G35.03/G24.03 completion or as a completed G40 compiler interface.
-/
namespace Solidity.Backend.AbiEntry.Premises

/-- V11/G35.03: a copy or slice consumes the EXISTING typed decoded table.
The reference is indexed by the source element type and exact static length;
it retains the actual selected interval and its complete ordered contents.
This is the structural boundary only, not a calldata-byte decoder premise. -/
structure CalldataSlice {D : Source.Layout} {element : Source.STy} {fixed : Option Nat}
    (operation : Source.Calldata D → Nat → Nat → Nat → Option (List (Source.Data D element))) : Prop where
  exact : ∀ (calldata : Source.Calldata D) (offset length : Nat)
    (fixed_length : ∀ n, fixed = some n → n = length)
    (values : Fin length → Source.Data D element) (start stop : Nat),
    calldata.objects offset = some ⟨.array .calldata element fixed, .array length fixed_length values⟩ →
    operation calldata offset start stop =
      if start ≤ stop ∧ stop ≤ length then
        some (((List.ofFn values).drop start).take (stop - start)) else none

/-- V11/G35.03: source/target copy agreement is a distinct pending obligation.
This schema does not supply an emitted program or a runtime certificate.
Its reference retains an intrinsically typed source table and destination
state. Copy/slice bounds and representation hypotheses belong to the actual
producer reference, not an invented admission condition in this lane. -/
structure CopyAgreement {D : Source.Layout} {C : Contract} {Γ Δ : Ctx}
    (copy : Source.Calldata D → Nat → Nat → Nat →
      (initial : State C Γ) → TRes (Out C initial.H Δ))
    (reference : Source.Calldata D → Nat → Nat → Nat →
      (initial : State C Γ) → TRes (Out C initial.H Δ) → Prop) : Prop where
  sound : ∀ calldata offset start stop initial,
    reference calldata offset start stop initial (copy calldata offset start stop initial)
  exact : ∀ calldata offset start stop initial result,
    reference calldata offset start stop initial result →
      copy calldata offset start stop initial = result

/-- The source statement's full result, including original failure and state. -/
abbrev StatementResult (E : Source.Env) (before after : Source.RCtx) :=
  Except Source.Halt (Source.Out E.layout before after) ×
    (Source.Locals E.layout [] × Source.St E)

/-- V09/G24.03: actual typed statement execution to actual intrinsic statement
execution, relative to the producer's separately justified representation.
No source evaluator, lowering or default relation is provided here. -/
structure Statement {E : Source.Env} {C : Contract} {sourceBefore sourceAfter : Source.RCtx} {Γ Δ : Ctx}
    (global : Source.Glob E) (frame : Source.Fr) (horizon parameters : Nat)
    (source : Source.RStmt E [] false .body sourceBefore sourceAfter) (target : Stmt C Γ Δ)
    (Before : Source.Locals E.layout sourceBefore → Source.St E → State C Γ → Prop)
    (ResultRepr : (initial : State C Γ) → StatementResult E sourceBefore sourceAfter → TRes (Out C initial.H Δ) → Prop) : Prop where
  correct : ∀ locals state initial, Before locals state initial →
    ResultRepr initial
      ((Source.execS global frame horizon parameters none source locals).run (.nil, state))
      (target.run initial)

end Solidity.Backend.AbiEntry.Premises
