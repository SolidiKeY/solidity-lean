import Solidity.Backend.AbiEntry.CompositionInterface
import Solidity.Backend.AbiEntry.RejectionInterface
import Solidity.Semantics.AbiEntry
import Solidity.Source.Eval

/-!
# G40 source-boundary obligation signatures

These records state contracts with source-graph controls only. No backend
runtime, decoder, source admission or representation instance is supplied.
The source relation is an explicit parameter and supplies no backend
execution evidence. Actual realization against the existing backend remains
a G40 obligation, not an assumed external result.
All raw decoder failures and all original fuels remain observable.
These are source-boundary agreements, NOT exported compiler/runtime
certificates. Compiler-facing representation and execution obligations remain
open until independently grounded in the actual producer/runtime interfaces.
The reexported rejection-consumer and ordered-composition signatures are
narrow concrete boundaries, not a compiled calldata decoder or complete
runtime-entry certificate.
-/
namespace Solidity.Backend.AbiEntry.Interface

/-- Successful entry retains both the indexed semantic result and the existing
typed immutable calldata carrier. Its object correspondence remains open. -/
structure Decoded (D : Source.Layout) (ps : List Solidity.AbiEntry.Param) where
  entries : Solidity.AbiEntry.Entries ps
  calldata : Source.Calldata D

/-- Raw entry agreement only. This intentionally says nothing about the
object table or emitted execution; neither follows from projecting Entries.
No canonical-layout or eager-copy admission restriction appears here. -/
structure RawDecoderAgreement (D : Source.Layout) (ps : List Solidity.AbiEntry.Param)
    (decode : Solidity.AbiEntry.Input → Nat → Except Solidity.AbiEntry.Fail (Decoded D ps)) : Prop where
  raw : ∀ input fuel,
    (decode input fuel).map Decoded.entries = Solidity.AbiEntry.entry input fuel ps
  input_bytes : ∀ input fuel result, decode input fuel = .ok result →
    result.calldata.input = input.data

/-- Obligations for the selectors and value checks consumed by actual source
entry. Getter precedence remains explicit; fallback parameters are handled by
entry/body composition, not silently erased by a selector-only agreement.
These equalities can be definitional when the helpers reuse Source. They
are source bookkeeping, not combined branch selection or runtime evidence. -/
structure DispatchHelpersAgreement {E : Source.Env} (global : Source.Glob E) (frame : Source.Fr)
    (ordinary : Roadmap.Bytes → Option Source.Decl)
    (getter : Roadmap.Bytes → Option (Source.Decl × List Source.STy × Source.STy))
    (special : Roadmap.Bytes → Option Source.Decl)
    (ordinaryValueOK specialValueOK : Source.Decl → Bool) : Prop where
  ordinary_exact : ∀ input, ordinary input = global.pickFn frame input
  getter_exact : ∀ input, getter input = global.pickGetter frame input
  special_empty : special [] = (E.special frame.contract .receive).orElse
    (fun _ => E.special frame.contract .fallback)
  special_nonempty : ∀ input, input ≠ [] → special input = E.special frame.contract .fallback
  ordinary_value : ∀ declaration, ordinaryValueOK declaration =
    !(decide (frame.value.val ≠ 0) && (declaration.fnMut != some .payable))
  special_value : ∀ declaration, specialValueOK declaration =
    !(decide (frame.value.val ≠ 0) && !declaration.specialPayable)

/-- Complete source result, retaining failures, locals, journal and observations.
No projection identifies an unsupported result with an empty revert. -/
abbrev EntryResult (E : Source.Env) :=
  Except Source.Halt Roadmap.Bytes × (Source.Locals E.layout [] × Source.St E)

/-- A source-result relation, with no runtime or code claim. It is deliberately
not named a backend execution judgment. -/
abbrev SourceEntryRelation (E : Source.Env) :=
  Source.Fr → Nat → Roadmap.Bytes → Source.St E → EntryResult E → Prop

/-- Source-only agreement against ACTUAL Source.dispatch. Runtime code is
absent by design: these fields alone cannot certify compilation. The eventual
G42/G49 export must additionally require actual backend execution and its
independently justified source/target representation. -/
structure SourceEntryAgreement {E : Source.Env} (global : Source.Glob E)
    (relation : SourceEntryRelation E) : Prop where
  exact_result : ∀ frame horizon input initial result,
    relation frame horizon input initial result ↔
      (Source.dispatch global frame horizon input).run (.nil, initial) = result
  coverage : ∀ frame horizon input initial,
    ∃ result, relation frame horizon input initial result

namespace SourceEntryAgreement

/-- Exact graph agreement constructs the complete record, including its
coverage field, without an additional coverage premise. -/
theorem of_exact_result {E : Source.Env} {global : Source.Glob E}
    {relation : SourceEntryRelation E}
    (exact_result : ∀ frame horizon input initial result,
      relation frame horizon input initial result ↔
        (Source.dispatch global frame horizon input).run (.nil, initial) = result) :
    SourceEntryAgreement global relation where
  exact_result := exact_result
  coverage := fun frame horizon input initial =>
    ⟨(Source.dispatch global frame horizon input).run (.nil, initial),
      (exact_result frame horizon input initial _).mpr rfl⟩

/-- The actual source graph inhabits this source-only agreement. This is not
an emitted runtime or representation certificate. -/
theorem graph {E : Source.Env} (global : Source.Glob E) :
    SourceEntryAgreement global (fun frame horizon input initial result =>
      (Source.dispatch global frame horizon input).run (.nil, initial) = result) :=
  of_exact_result (fun _ _ _ _ _ => Iff.rfl)

/-- Empty relations cannot satisfy exact graph agreement, even at horizon zero.
The original coverage field remains available to consumers. -/
theorem empty_refused {E : Source.Env} (global : Source.Glob E)
    (frame : Source.Fr) (initial : Source.St E) :
    ¬ SourceEntryAgreement global (fun _ _ _ _ _ => False) := by
  intro agreement
  obtain ⟨result, impossible⟩ := agreement.coverage frame 0 [] initial
  exact impossible

/-- info: 'Solidity.Backend.AbiEntry.Interface.SourceEntryAgreement.coverage' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms coverage
/-- info: 'Solidity.Backend.AbiEntry.Interface.SourceEntryAgreement.of_exact_result' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms of_exact_result
/-- info: 'Solidity.Backend.AbiEntry.Interface.SourceEntryAgreement.graph' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms graph
/-- info: 'Solidity.Backend.AbiEntry.Interface.SourceEntryAgreement.empty_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms empty_refused
end SourceEntryAgreement
end Solidity.Backend.AbiEntry.Interface
