import Solidity.Source.Value

/-!
# Unchecked arithmetic and effect relation groundwork

P3 (H220) separates arithmetic/effect obligations from opaque producer linkage.
These relations are not an inhabited source/model statement simulation and do
not close F3. In particular, the second `Source.R` computation below is a
prospective decoded target observation, not the actual target by definition.
An endpoint instance must connect actual intrinsic elaboration, all state
components (including journals on failure), typed encodings, and horizons.
No normal-result or no-panic premise is built into these relations.
-/
namespace Solidity.Correctness.Lowering.Unchecked

open Solidity.Source

/-- Relate successful typed values; failures retain the exact `Halt`, including
panic/revert bytes, timeout and stuck diagnostics. This strong intermediate
relation does not equate a timeout with divergence. -/
def ResultRel {α β : Type} (values : α → β → Prop) : R α → R β → Prop
  | .ok a, .ok b => values a b
  | .error a, .error b => a = b
  | _, _ => False

/-- A full-state computation relation. Poststate is compared on *both* success
and failure, matching `ExceptT Halt (StateM ...)`, not `StateT ... (Except ...)`.
An application must instantiate `states` for every machine component; a locals
projection alone does not prove journal, heap, event or storage agreement.
This is a relation on computations, not a replacement operational semantics. -/
def EffectRel {S T α β : Type} (states : S → T → Prop)
    (values : α → β → Prop) (source : S → R α × S) (target : T → R β × T) : Prop :=
  ∀ s t, states s t →
    ResultRel values (source s).1 (target t).1 ∧ states (source s).2 (target t).2

/-- The selected pipeline indexes the actual computations, so effect-order
agreement must be supplied separately for legacy and via-IR. No order or fuel
conversion is silently fixed by the relation. -/
def PipelineEffectRel {S T α β : Type} (states : S → T → Prop)
    (values : α → β → Prop)
    (source : Roadmap.Pipeline → S → R α × S)
    (target : Roadmap.Pipeline → T → R β × T) : Prop :=
  ∀ pipeline, EffectRel states values (source pipeline) (target pipeline)

/-- Pure typed arithmetic obligation. The source type carries integer width
and signedness, or fixed-point width/signedness/scale. `checked = false` is the
unchecked body; checked controls and callees retain `true`. The target argument
must eventually be the decoded actual elaborated operation; no such instance
or producer correspondence is asserted here. -/
def ArithmeticRel {D : Layout} {τ : STy} (checked : Bool) (op : Source.BinOp)
    (x y : Source.Val D τ) (target : R (Source.Val D τ)) : Prop :=
  binVal checked op x y = target

/-- One composition law for all arithmetic arms. Exact failures propagate
without invoking a successful continuation; this does not by itself prove the
stateful `EffectRel` obligations or a lowering pass theorem. -/
theorem resultRel_bind {α β γ δ : Type} {values : α → β → Prop}
    {results : γ → δ → Prop} (source : R α) (target : R β)
    (left : α → R γ) (right : β → R δ)
    (related : ResultRel values source target)
    (next : ∀ a b, values a b → ResultRel results (left a) (right b)) :
    ResultRel results (source >>= left) (target >>= right) := by
  cases source with
  | ok a =>
    cases target with
    | ok b => exact next a b related
    | error e => exact False.elim related
  | error e =>
    cases target with
    | ok b => exact False.elim related
    | error f => exact related

#print axioms resultRel_bind

end Solidity.Correctness.Lowering.Unchecked
