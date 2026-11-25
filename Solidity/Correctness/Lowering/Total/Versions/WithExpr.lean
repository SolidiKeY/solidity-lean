import Solidity.Correctness.Lowering.Total.Versions.Self
import Solidity.Correctness.Lowering.Total.Decode.Casts

/-!
# Boundaries of decoders with their own expression spelling

`Version.boundaryAt` is the boundary of `Tables.decode`. The decoders with
registered calls or casts (`Decode.Calls.decode`, `Decode.Casts.decode`) are
`Decode.WithExpr.decode T spell` for another expression decoder `spell`; this
module gives every such decoder its association, boundary and initial
matching, beside the versions' (nothing landed changes).

* `SpellsWith T spell`: as `SpellsT T`, with the block read by the shared
  statement traversal over `spell`. At `T.expr` it is `SpellsT T`
  (`spellsWith_original`). The traversal is a function here, not a relation:
  the relation does not characterize `spell` itself (for casts that is
  `Casts.expr_cast` and `Casts.conservative`), only everything around it.
  It still mentions no inference function.
* `decode_spellsWith`, `SpellsWith.unique`: the decoder is sound for it, and a
  request spells at most one program.
* `boundaryWith`, `residualWith_iff`: the boundary and what the contract asks
  at it (`residualOf_iff`).
* `initialMatchingWith`: total initial matching for every sound version's
  tables and every `spell`, proved (Source-to-model only, as
  `initialMatchingAt`).
* `boundaryC`, `initialMatchingC`: the instance with casts, bytes literals and
  the own-account reads: `Casts.decode tablesT registry1`.

The first conjunct of `residualWith_iff` is not provable while this decoder has
gaps (`Total.Versions`), so no contract here can be the goal yet. No goal is
stated.
-/
namespace Solidity.Correctness.Lowering.Total

open Solidity.Roadmap.G49Final

namespace Version

open Simulation (StateRelation InitialMatching)
open Source (Syn)

variable {T : Decode.Tables} {spell : RawExpr → Option (Syn .expr)}

/-- **The spelling relation of a decoder with its own expression spelling.** A
plain request spells a Source program when the statement traversal over
`spell` reads its raw input as a block that has a Source typing derivation
from the caller's locals in the version's unit, and the program is that
derivation's resolution. -/
def SpellsWith (T : Decode.Tables) (spell : RawExpr → Option (Syn .expr)) (r : Request)
    (s : SourceProgram) : Prop :=
  Decode.plain r = true ∧
  ∃ (C : Source.Ctx) (L : List (String × Source.STy)) (b : Syn (.list (.item .body)))
    (L' : List (String × Source.STy)) (d : Source.ItemsD C L b L'),
    T.context r = some C ∧ T.locals r.input.before.locals.1 = some L ∧
    Decode.Tables.WithExpr.items T spell .body r.input.raw = some b ∧
    s = ⟨C.env, C.rets, C.inModifier, .body, Source.tysOf L, Source.tysOf L', d.toR⟩

/-- The decoder is sound for the relation. -/
theorem decode_spellsWith {r : Request} {s : SourceProgram}
    (h : Decode.WithExpr.decode T spell r = some s) : SpellsWith T spell r s := by
  unfold Decode.WithExpr.decode at h
  split at h
  · rename_i p
    simp only [Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff,
      Option.some.injEq] at h
    obtain ⟨C, hC, L, hL, b, hb, ⟨L', d⟩, _, rfl⟩ := h
    exact ⟨p, C, L, b, L', d, hC, hL, hb, rfl⟩
  · cases h

/-- A request spells at most one program. -/
theorem SpellsWith.unique {r : Request} {s s' : SourceProgram} (h : SpellsWith T spell r s)
    (h' : SpellsWith T spell r s') : s = s' := by
  obtain ⟨_, C, L, b, L', d, hC, hL, hb, rfl⟩ := h
  obtain ⟨_, C', L₀, b', L'', d', hC', hL', hb', rfl⟩ := h'
  cases hC.symm.trans hC'
  cases hL.symm.trans hL'
  cases hb.symm.trans hb'
  obtain ⟨rfl, same⟩ := Source.ItemsD.unique d d'
  rw [eq_of_heq same]

/-- At the version's own expression decoder the relation is the version's. -/
theorem spellsWith_original (r : Request) (s : SourceProgram) :
    SpellsWith T T.expr r s ↔ SpellsT T r s := by
  constructor
  · rintro ⟨p, C, L, b, L', d, hC, hL, hb, rfl⟩
    exact ⟨p, C, L, b, L', d, hC, hL, Spells.items_spellsT _ _ _ hb, rfl⟩
  · rintro ⟨p, C, L, b, L', d, hC, hL, hb, rfl⟩
    exact ⟨p, C, L, b, L', d, hC, hL, hb.decode, rfl⟩

/-- A spelled program has the shape initial matching reads. -/
theorem shape_of_spellsWith {r : Request} {s : SourceProgram} (h : SpellsWith T spell r s) :
    Shape T r s := by
  obtain ⟨plain, C, L, b, L', d, hC, hL, _, rfl⟩ := h
  exact ⟨plain, C, L, _, _, hC, hL, rfl⟩

/-- **Total initial matching** for the decoder over any expression spelling,
at a sound version's tables. -/
theorem initialMatchingWith (sound : Sound T) (spell : RawExpr → Option (Syn .expr)) :
    InitialMatching rel (Decode.WithExpr.decode T spell) :=
  initialMatchingOf sound fun _ _ h => shape_of_spellsWith (decode_spellsWith h)

/-- The boundary of the decoder over an expression spelling. -/
def boundaryWith (T : Decode.Tables) (spell : RawExpr → Option (Syn .expr))
    (rel : (E : Source.Env) → (C : Contract) → StateRelation E C) : SemanticBoundary :=
  boundaryOf (SpellsWith T spell) rel

/-- **What the contract asks at that boundary**: the four obligations of
`residualOf_iff`, for `SpellsWith T spell` and `WithExpr.decode T spell`. -/
theorem residualWith_iff (T : Decode.Tables) (spell : RawExpr → Option (Syn .expr)) :
    LowerLoopsCorrectContract (boundaryWith T spell rel) (boundaryWith T spell rel).reference
        (Decode.WithExpr.decode T spell) ↔
      (∀ r : Request, r.Succeeds → ∃ s, Decode.WithExpr.decode T spell r = some s) ∧
      (∀ (r : Request) s, r.Succeeds → SpellsWith T spell r s →
        Decode.WithExpr.decode T spell r = some s) ∧
      (∀ (r : Request) o after parts program, r.pipeline o after parts program →
        Allocation.RoundTrip r.input.names ∧
        SafeSpellings r.input.names (Allocation.scope r o after).protectedNames
          (Allocation.scope r o after).generated) ∧
      (∀ (r : Request) o after parts program s, Decode.WithExpr.decode T spell r = some s →
        r.pipeline o after parts program →
        Simulation.Simulates rel s program ∧
          Nonempty (PassCorrect (Observe.source s).behaviour
            (Observe.target program).behaviour)) :=
  (contract_reference_iff _ _).trans
    (residualOf_iff (fun _ _ => decode_spellsWith) rel_reflect rel_false)

/-- The boundary of the decoder with casts, bytes literals and the own-account
reads. -/
def boundaryC : SemanticBoundary :=
  boundaryWith Decode.tablesT (Decode.Casts.expr Decode.tablesT CallSpellExt.registry1) rel

/-- Total initial matching for that decoder. -/
theorem initialMatchingC :
    InitialMatching rel (Decode.Casts.decode Decode.tablesT CallSpellExt.registry1) :=
  initialMatchingWith soundT _

end Version

end Solidity.Correctness.Lowering.Total
