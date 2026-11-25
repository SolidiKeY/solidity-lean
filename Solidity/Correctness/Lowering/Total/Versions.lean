import Solidity.Correctness.Lowering.Total.Versions.Marked

/-!
# Loop lowering: the boundaries of decoder versions (H1258, H1265)

The landed boundary (`Total.Boundary`) is for the landed decoder and is kept
as it is. This module gives decoder versions (`Decode.Tables`) one state
relation and a boundary each, beside it. The versions so far are the
width-aware `Decode.tablesW`, the address-aware `Decode.tablesA`, the
bytes-aware `Decode.tablesB` and the caller-aware `Decode.tablesS`:

* `Version.Relation.ValRel`, `Version.rel`: a model primitive is related to a
  Source Boolean, to a Source integer of the same sign holding the same
  number, at whatever width the decoder gave the slot, or (a `uint`) to the
  Source address with that number, or to the Source `bytesN` whose big-endian
  value (`Source.bytesNat`) is that number. Globals as in
  `loopRel`: primitive state variables of the running account, `msg.value`,
  the timestamp, a writable checking frame; the caller: the model's
  `msg.sender` is the Source frame's sender; and the running account: the
  model's own address is the Source frame's, and its own balance is the
  balance Source observes for that account (`Relation.ownBalance`). These
  clauses are part of `Version.rel`, so they hold at every version's boundary,
  also where the decoder has no reading of `msg.sender` or `address(this)`.
* `Version.Sound`: what total initial matching needs of a version's tables
  (`soundW`, `soundA`, `soundB`, `soundS`). It is not a correctness criterion for the tables: it
  does not say they agree with the types the model declared.
* `Version.initialMatchingAt`: total initial matching for every sound version,
  proved: every admitted
  Source execution of a successful decoded request has a related model state
  under the positional map. It is Source-to-model only. The converse fails at
  a narrow slot (a model `uint` holding 300 where the decoder says `uint8`),
  at an address slot (a model `uint` of `2^160` or more), at a `bytesN`
  slot (a model `uint` of `256^N` or more) and at the caller (a model
  `msg.sender` of `2^160` or more): such a model
  value has no related Source value, and nothing here claims it has. So the
  simulation at a version speaks only of entry states inside those ranges,
  and proving it includes proving that model results at such slots stay
  inside them.
* `Version.boundaryAt`, `residualAt_iff`, `contractV2At_iff`: a version's
  boundary with association `SpellsT`, and what the contract and its version 2
  ask at it; `boundary`, `boundaryA`, `boundaryB` and `boundaryS` are the
  instances.

The relation does not tie a slot's Source width to the model's declared width:
only the decoder does, and the model context of a request has erased it. The
policies, the simulation and the allocation trace are the landed ones, with
the defects listed in `Total.Boundary`. No goal is stated here.

Limits. Every version still has gaps: enums, function types,
references, calls and callee bodies, return slots, `unchecked`/`checked`
scopes, and contracts with functions, a constructor, initializers or transient
roots. The address-aware version reads marked locals and state variables and
the name `address`; between such operands the shared expressions (copy, `==`,
comparison) are spelled and Source types them, but `msg.sender` (read only by
the caller-aware version), `address(this)` and its balance (read only by the
self-aware `Decode.tablesT`, `Versions.Self`), `address(e)`/`payable(e)`, an address against a numeric
literal, and payable-only operations are gaps (`address payable` is read as
`address`), and a captured address, whose shape carries the marker twice, is a
gap too. `a.balance` over a marked operand is typed by Source, while the state
relation relates no balances. The bytes-aware version reads marked locals and
state variables and the names `bytesN`, as the right-aligned big-endian number
the model holds (not the left-aligned word of `Source.Observe`); indexing,
`.length`, equality, ordering, bitwise operators, shifts and implicit widening
between such operands are in the fragment, while `bytesN(e)` casts, bytes
literals and a captured `bytesN` are gaps. So the first conjunct of `residualAt_iff` (the
decoder is defined on every successful request) is not provable for any
version yet, and no version's contract can be the goal yet. A local the elaborator declares without a type marker is decoded
as a plain integer even if it was declared `address` or `bytesN`
(`Decode.localTyW`): a possibly wrong Source type, not a gap.

Bridge to the landed boundary: at the landed tables the generic decoder and
spelling relation are the landed ones (`Decode.decode_tables1`,
`spellsT_tables1`).
-/
namespace Solidity.Correctness.Lowering.Total

open Solidity.Roadmap.G49Final

namespace Version

open Simulation (StateRelation Positional InitialMatching lookup_of_mem wordDenote)

variable {T : Decode.Tables}

/-! ## The boundary of a decoder version -/

/-- The boundary of a decoder version at a state relation: the landed
admission, policies, simulation and allocation trace, with the version's
spelling relation as association. -/
def boundaryAt (T : Decode.Tables)
    (rel : (E : Source.Env) → (C : Contract) → StateRelation E C) : SemanticBoundary :=
  ⟨⟨SpellsT T, loopEntry, Observe.source, fun p => Observe.target p⟩,
    fun s _ _ p => Simulation.Simulates rel s p, Allocation.trace⟩

/-- **What the contract asks at a version's boundary**, for a state relation
that reflects Booleans and relates `false` to `false`: the decoder is defined
on every successful request and complete for the version's spelling relation;
the fresh-name scheme round-trips and the run's allocation scope is safe; each
successful pipeline simulates its decoded program and refines it. The e1
family obligations follow from the endpoint theorems. -/
theorem residualAt_iff (T : Decode.Tables)
    {rel : (E : Source.Env) → (C : Contract) → StateRelation E C}
    (reflect : ∀ E C H (v : Source.Val E.layout .bool) (b : Bool),
      (rel E C).val H .bool (.val .bool) v b → v = .bool b)
    (falseRel : ∀ E C H, (rel E C).val H .bool (.val .bool) (.bool false) false) :
    Residual (boundaryAt T rel) T.decode ↔
      (∀ r : Request, r.Succeeds → ∃ s, T.decode r = some s) ∧
      (∀ (r : Request) s, r.Succeeds → SpellsT T r s → T.decode r = some s) ∧
      (∀ (r : Request) o after parts program, r.pipeline o after parts program →
        Allocation.RoundTrip r.input.names ∧
        SafeSpellings r.input.names (Allocation.scope r o after).protectedNames
          (Allocation.scope r o after).generated) ∧
      (∀ (r : Request) o after parts program s, T.decode r = some s →
        r.pipeline o after parts program →
        Simulation.Simulates rel s program ∧
          Nonempty (PassCorrect (Observe.source s).behaviour
            (Observe.target program).behaviour)) := by
  constructor
  · intro h
    refine ⟨h.total, fun r s e spelled => (h.decoder r s e).mpr spelled,
      fun r o after parts program run => ?_,
      fun r o after parts program s d run =>
        h.pipeline r o after parts program s ⟨o, after, parts, program, run⟩ d run⟩
    obtain ⟨scopes, ⟨trace, law⟩, safe⟩ :=
      h.allocation r o after parts program ⟨o, after, parts, program, run⟩ run
    cases trace
    exact ⟨law, safe _ (List.mem_singleton.mpr rfl)⟩
  · intro ⟨covered, complete, allocation, pipeline⟩
    refine ⟨covered, fun r s e => ⟨decode_spellsT, complete r s e⟩,
      fun r o after parts program _ run =>
        ⟨_, ⟨rfl, (allocation r o after parts program run).1⟩, fun scope member => ?_⟩,
      fun r o after parts program s _ d run => pipeline r o after parts program s d run, ?_, ?_⟩
    · cases List.mem_singleton.mp member
      exact (allocation r o after parts program run).2
    · intro k E srcΓ returns M l u C Γ m pair extra names
      obtain ⟨embedding, endpoint⟩ := normalFamily_correct k (returns := returns) (M := M)
        (l := l) (u := u) m pair extra names (k.lowered pair extra names) rfl
      exact Simulation.of_endpoint reflect falseRel endpoint
    · intro k E srcΓ M l u C Γ m pair extra names
      exact Simulation.of_retEndpoint reflect falseRel
        (returnFamily_correct k (M := M) (l := l) (u := u) m pair extra names)

/-- The boundary admits every request whose whole pipeline succeeds. -/
theorem boundaryAt_fullDomain (T : Decode.Tables)
    (rel : (E : Source.Env) → (C : Contract) → StateRelation E C) :
    FullDomain (boundaryAt T rel) := fun _ h => h

/-- The width-aware version's boundary. -/
def boundary : SemanticBoundary := boundaryAt Decode.tablesW rel

/-- What the contract asks at the width-aware version's boundary. The first
conjunct is not provable while the decoder has gaps. -/
theorem residual_iff :
    LowerLoopsCorrectContract boundary boundary.reference Decode.tablesW.decode ↔
      (∀ r : Request, r.Succeeds → ∃ s, Decode.tablesW.decode r = some s) ∧
      (∀ (r : Request) s, r.Succeeds → SpellsT Decode.tablesW r s →
        Decode.tablesW.decode r = some s) ∧
      (∀ (r : Request) o after parts program, r.pipeline o after parts program →
        Allocation.RoundTrip r.input.names ∧
        SafeSpellings r.input.names (Allocation.scope r o after).protectedNames
          (Allocation.scope r o after).generated) ∧
      (∀ (r : Request) o after parts program s, Decode.tablesW.decode r = some s →
        r.pipeline o after parts program →
        Simulation.Simulates rel s program ∧
          Nonempty (PassCorrect (Observe.source s).behaviour
            (Observe.target program).behaviour)) :=
  (contract_reference_iff _ _).trans (residualAt_iff Decode.tablesW rel_reflect rel_false)

/-- **Version 2 of the contract at a sound version's boundary**, with total
initial matching discharged: five obligations are left. -/
theorem contractV2At_iff (sound : Sound T) :
    LowerLoopsCorrectContractV2 rel (boundaryAt T rel) (boundaryAt T rel).reference T.decode ↔
      (∀ r : Request, r.Succeeds → ∃ s, T.decode r = some s) ∧
      (∀ (r : Request) s, r.Succeeds → SpellsT T r s → T.decode r = some s) ∧
      (∀ (r : Request) o after parts program, r.pipeline o after parts program →
        Allocation.RoundTrip r.input.names ∧
        SafeSpellings r.input.names (Allocation.scope r o after).protectedNames
          (Allocation.scope r o after).generated) ∧
      (∀ (r : Request) o after parts program s, T.decode r = some s →
        r.pipeline o after parts program →
        Nonempty (PassCorrect (Observe.source s).behaviour (Observe.target program).behaviour)) ∧
      Simulation.Bound rel T.decode := by
  unfold LowerLoopsCorrectContractV2
  rw [contract_reference_iff, residualAt_iff T rel_reflect rel_false]
  exact ⟨fun ⟨⟨covered, complete, allocation, pipeline⟩, _, bound⟩ =>
      ⟨covered, complete, allocation,
        fun r o after parts program s d run => (pipeline r o after parts program s d run).2,
        bound⟩,
    fun ⟨covered, complete, allocation, refines, bound⟩ =>
      ⟨⟨covered, complete, allocation, fun r o after parts program s d run =>
        ⟨bound.simulates d run, refines r o after parts program s d run⟩⟩,
        initialMatchingAt sound, bound⟩⟩

/-- Version 2 of the contract at the width-aware version's boundary, with
total initial matching discharged: five obligations are left. -/
theorem contractV2_iff :
    LowerLoopsCorrectContractV2 rel boundary boundary.reference Decode.tablesW.decode ↔
      (∀ r : Request, r.Succeeds → ∃ s, Decode.tablesW.decode r = some s) ∧
      (∀ (r : Request) s, r.Succeeds → SpellsT Decode.tablesW r s →
        Decode.tablesW.decode r = some s) ∧
      (∀ (r : Request) o after parts program, r.pipeline o after parts program →
        Allocation.RoundTrip r.input.names ∧
        SafeSpellings r.input.names (Allocation.scope r o after).protectedNames
          (Allocation.scope r o after).generated) ∧
      (∀ (r : Request) o after parts program s, Decode.tablesW.decode r = some s →
        r.pipeline o after parts program →
        Nonempty (PassCorrect (Observe.source s).behaviour (Observe.target program).behaviour)) ∧
      Simulation.Bound rel Decode.tablesW.decode :=
  contractV2At_iff soundW

/-- The address-aware version's boundary. -/
def boundaryA : SemanticBoundary := boundaryAt Decode.tablesA rel

/-- The caller-aware tables are sound: they type locals and cells as the
bytes-aware ones do. -/
theorem soundS : Sound Decode.tablesS := ⟨soundB.localTy, soundB.cell⟩

/-- The caller-aware version's boundary. -/
def boundaryS : SemanticBoundary := boundaryAt Decode.tablesS rel

/-- The bytes-aware version's boundary. -/
def boundaryB : SemanticBoundary := boundaryAt Decode.tablesB rel

end Version

end Solidity.Correctness.Lowering.Total
