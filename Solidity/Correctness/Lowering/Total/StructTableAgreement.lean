import Solidity.Correctness.Lowering.Total.StructTableAgreement.Refs

/-!
# Nested struct references and the declarations of their model tables

The obligation `StructDecode` and `StructRows` leave open: that a resolved nested
struct has its table type's members. The environment holds the actual successful
`StructDecode.decode C = .ok ps` output for the contract `c` between arbitrary
surrounding declaration lists: `E.decls = pre ++ ps.collect (some c) ++ post`.

For a struct reference in a member of a model table, `written_entry` connects
`ReferenceDecode.written?` and `Contract.structName?` to the `Contract.structs`
entries: the written name's first entry is keyed to the referenced table type
(`written_first`), or it has no entry and is the implicit table-name fallback.
`agrees` then derives `Agrees`: the generated declaration of that entry is the one
`Source.Env.lookup` selects and `Source.Env.declOf` finds, its identity is the
`Resolved` one, and `Source.Env.structFields` at any location the table's members
allow (`Placed`) are the referenced table's ordered members related by
`ReferenceDecode.Rep` (`StructDecode.Fields`). The premises are table facts only:
the written name is keyed once (`StructDecode.Declared` of the referencing table),
the referenced table is `Declared`, and no surrounding declaration of the scope
carries a keyed name (`StructDecode.Free`).

`edge_agrees` covers every reference of a member of every entry table, inside
arrays, fixed arrays and mapping values at the location `refsTy` gives it, when all
entry tables are `Declared` (`Closed`): the referenced table is again an entry
table, so the statement is pointwise over the finite table graph, cycles included,
and claims no expansion of recursive types. `table_agreement` adds that each
member's elaborated type has, at every such reference, the `Rep.struct` leaf whose
declaration identity is the generated one of the written name.

Distinguished failures: `fallback_unbound` (the written name has no entry: no
generated declaration carries it, so only surrounding declarations can); an
ambiguous written name — keyed more than once — is unresolved (`ambiguous`), while
`Source.Env.declOf` still selects the first entry, whose table is the referenced one
(`first_fields`); a member a location does not admit fails `Placed` (examples).
Absent and ambiguous written spellings (`unknownStruct`, `ambiguousStruct`) cannot
follow a successful decoding (`decode_written`).

Left to the decoder lane: discharging `Closed` and `Free` over the frozen production
domain, the `pre ++ generated ++ post` shape of its assembled unit, retained `RawTy`
agreement, frame correspondence and complete semantic binding.
-/
namespace Solidity.Correctness.Lowering.Total.StructTableAgreement

open Solidity.Semantics (lookupBy structDef structWidths)
open Source (STy DataLoc)
open ReferenceDecode (written? Resolved Rep structsTy)
open StructDecode (Gen Fields Declared Free maplessTy decode named Pairs)

/-- The members of a table type admit the location: a mapping only in storage. -/
def Placed (table : Name) (loc : DataLoc) : Prop :=
  ∀ x ∈ structDef table, loc = .storage ∨ maplessTy x.2 = true
instance (table : Name) (loc : DataLoc) : Decidable (Placed table loc) := by
  unfold Placed; infer_instance

/-- Every entry table of the contract is `Declared`. -/
def Closed (C : Contract) : Prop := ∀ e ∈ C.structs, Declared C e.2
instance (C : Contract) : Decidable (Closed C) := by unfold Closed; infer_instance

/-- **Agreement of a written name with a model table** from the contract `c`: its first
entry is the table, the declaration generated for it is the one lookup selects and
`declOf` finds, with the resolved identity, and its Source fields are the table's. -/
structure Agrees (C : Contract) (E : Source.Env) (c : String) (w s : Name) : Prop where
  entry : lookupBy w C.structs = some s
  decl : ∃ d, Gen C c (w, s) d ∧ E.lookup (some c) w = [d] ∧ E.declOf .struct ⟨some c, w⟩ = some d
  resolved : Resolved E (some c) w ⟨some c, w⟩
  fields : ∀ loc, Placed s loc → Fields C E c loc s (E.structFields ⟨some c, w⟩ loc)

/-- A table reference of a table: a member mentions it, at that location. -/
def Edge (t : Name) (loc : DataLoc) (p : Name × DataLoc) : Prop :=
  ∃ x ∈ structDef t, p ∈ refsTy loc x.2

variable {C : Contract} {c : String} {E : Source.Env} {pre post : List Source.Decl}

/-- The generated declaration of an entry is determined by it. -/
theorem Gen.unique {entry : Name × Name} {d d' : Source.Decl} (g : Gen C c entry d)
    (g' : Gen C c entry d') : d = d' := by
  obtain ⟨m, ms, rfl, hm, -⟩ := g
  obtain ⟨m', ms', rfl, hm', -⟩ := g'
  rw [hm] at hm'; cases hm'; rfl

section Unit
variable {ps : Source.Syn (.list (.part false))} (h : decode C = .ok ps)
  (hE : E.decls = pre ++ ps.collect (some c) ++ post)
include h hE

/-- With no struct of the name earlier in the scope, `declOf` finds the generated
declaration of the name's first entry. -/
theorem declOf_first {w e : Name} (hw : lookupBy w C.structs = some e)
    (first : ∀ d ∈ pre, ¬(d.kind = .struct ∧ d.scope = some c ∧ d.name = w)) :
    ∃ d, Gen C c (w, e) d ∧ E.declOf .struct ⟨some c, w⟩ = some d := by
  obtain ⟨d, find, g⟩ := StructDecode.gen_find (StructDecode.decode_collect h c) hw
  have none : pre.find? (fun d => d.kind == .struct && d.scope == some c && d.name == w) = none :=
    List.find?_eq_none.2 fun d md => by simpa using fun k s => (first d md ⟨k, s, ·⟩)
  exact ⟨d, g, by simp only [Source.Env.declOf, hE, List.find?_append, none, find,
    Option.none_or, Option.some_or]⟩

/-- **The bridge** for one reference: a written name keyed once, of a `Declared`
table, among `Free` surrounding declarations, agrees with the referenced table. -/
theorem agrees (free : Free C c (pre ++ post)) {s w : Name} (hw : written? C s = some w)
    (one : (C.structs.filter (·.1 == w)).length = 1) (dec : Declared C s) :
    Agrees C E c w s := by
  obtain ⟨e, he⟩ := lookupBy_some_of_filter (w := w) (l := C.structs) fun hn => by
    rw [hn] at one; cases one
  cases written_first hw he
  have clear : ∀ d ∈ pre ++ post, d.scope = some c → d.name ≠ w := fun d md sc nm => by
    have := free d md sc; rw [nm, he] at this; cases this
  obtain ⟨e', d, he', g, look, res⟩ := StructDecode.resolved h hE one fun d md ⟨sc, nm⟩ =>
    clear d md sc nm
  rw [he] at he'; cases he'
  obtain ⟨d', g', decl⟩ := declOf_first h hE he fun d md ⟨_, sc, nm⟩ =>
    clear d (List.mem_append_left _ md) sc nm
  cases Gen.unique g g'
  exact ⟨he, ⟨d, g, look, decl⟩, res, fun loc here =>
    StructDecode.structFields_closed h hE free he dec loc here⟩

/-- **Every referenced table**: when all entry tables are `Declared`, every reference
of a member of an entry table has a written name agreeing with the referenced table,
which is again an entry table. -/
theorem edge_agrees (free : Free C c (pre ++ post)) (closed : Closed C) {t : Name}
    (ht : t ∈ C.structs.map (·.2)) {loc : DataLoc} {p : Name × DataLoc} (edge : Edge t loc p) :
    ∃ w, written? C p.1 = some w ∧ Agrees C E c w p.1 ∧ (w, p.1) ∈ C.structs := by
  obtain ⟨⟨w0, t⟩, mt, rfl⟩ := List.mem_map.1 ht
  obtain ⟨x, hx, hp⟩ := edge
  obtain ⟨w, hw⟩ := decode_written h mt hx (mem_structsTy hp)
  have one := closed _ mt x hx p.1 (mem_structsTy hp) w hw
  obtain ⟨e, he⟩ := lookupBy_some_of_filter (w := w) (l := C.structs) fun hn => by
    rw [hn] at one; cases one
  cases written_first hw he
  have mem := lookupBy_mem he
  exact ⟨w, hw, agrees h hE free hw one (closed _ mem), mem⟩

/-- **Members of an entry table**: its Source fields at a location it admits, and at
every reference of every member the `Rep.struct` leaf, whose declaration is the one
generated for the written name, agreeing with the referenced table. -/
theorem table_agreement (free : Free C c (pre ++ post)) (closed : Closed C) {w0 t : Name}
    (ht : lookupBy w0 C.structs = some t) {loc : DataLoc} (here : Placed t loc) :
    Fields C E c loc t (E.structFields ⟨some c, w0⟩ loc) ∧
      ∀ x ∈ structDef t, ∃ τ, Rep C (structWidths t) E (some c) x.1 loc x.2 τ ∧
        ∀ p ∈ refsTy loc x.2, ∃ key w, written? C p.1 = some w ∧ Agrees C E c w p.1 ∧
          Rep C (structWidths t) E (some c) key p.2 (.ref (.struct p.1)) (.struct p.2 ⟨some c, w⟩) := by
  have mt := lookupBy_mem ht
  have fields := StructDecode.structFields_closed h hE free ht (closed _ mt) loc here
  refine ⟨fields, fun x hx => ?_⟩
  obtain ⟨τs, -, pairs⟩ := fields
  obtain ⟨τ, -, rep⟩ := Pairs.mem pairs hx
  refine ⟨τ, rep, fun p hp => ?_⟩
  obtain ⟨key, w', d, hw', res, leaf⟩ := Rep.leaf rep p hp
  obtain ⟨w, hw, ag, -⟩ := edge_agrees h hE free closed (List.mem_map_of_mem mt) ⟨x, hx, hp⟩
  rw [hw] at hw'; cases hw'
  obtain ⟨dd, g, look, -⟩ := ag.decl
  have eq := Resolved.eq res look
  obtain ⟨m, ms, rfl, -⟩ := g
  exact ⟨key, _, hw, ag, eq ▸ leaf⟩

/-! ## Failures kept apart -/

/-- **Implicit fallback**: a written name without an entry is the table name itself,
and no generated declaration carries it; the scope's declarations of it are the
surrounding ones only. -/
theorem fallback_unbound {s w : Name} (hw : written? C s = some w)
    (none : lookupBy w C.structs = none) : w = s ∧ (structDef s).isEmpty = false ∧
      (ps.collect (some c)).filter (named c w) = [] ∧
      E.declared (some c) w = pre.filter (named c w) ++ post.filter (named c w) := by
  obtain ⟨rfl, ne⟩ : w = s ∧ (structDef s).isEmpty = false := by
    rcases written_entry hw with h' | ⟨-, h'⟩
    · rw [none] at h'; cases h'
    · exact h'
  have g := StructDecode.gen_filter w (StructDecode.decode_collect h c)
  rw [lookupBy_none none] at g
  generalize hg : (ps.collect (some c)).filter (named c w) = gs at g
  cases g
  refine ⟨rfl, ne, rfl, ?_⟩
  have : E.declared (some c) w = pre.filter (named c w) ++
      (ps.collect (some c)).filter (named c w) ++ post.filter (named c w) := by
    simp only [Source.Env.declared, hE, List.filter_append]; rfl
  rw [this, hg, List.append_nil]

/-- **Ambiguous name**: a written name keyed by several entries is unresolved from the
scope, though its first entry is still the referenced table. -/
theorem ambiguous {s w : Name} (hw : written? C s = some w)
    (two : 2 ≤ (C.structs.filter (·.1 == w)).length) :
    lookupBy w C.structs = some s ∧ ¬ ∃ d, Resolved E (some c) w d := by
  have ne : C.structs.filter (·.1 == w) ≠ [] := fun hn => by rw [hn] at two; cases two
  obtain ⟨e, he⟩ := lookupBy_some_of_filter ne
  cases written_first hw he
  exact ⟨he, fun r => by have := (StructDecode.resolved_only h hE ne r).1; omega⟩

/-- **First entry**: without a struct of the name earlier in the scope, `structFields`
of a written name are the referenced table's, however often the name is keyed, under
the resolution obligations of that table's own references. -/
theorem first_fields {s w : Name} (hw : written? C s = some w)
    (keyed : C.structs.filter (·.1 == w) ≠ [])
    (first : ∀ d ∈ pre, ¬(d.kind = .struct ∧ d.scope = some c ∧ d.name = w))
    (loc : DataLoc) (here : Placed s loc)
    (res : ∀ x ∈ structDef s, ∀ s' ∈ structsTy x.2, ∀ w', written? C s' = some w' →
      ∃ d, Resolved E (some c) w' d) : Fields C E c loc s (E.structFields ⟨some c, w⟩ loc) := by
  obtain ⟨e, he⟩ := lookupBy_some_of_filter keyed
  cases written_first hw he
  exact StructDecode.structFields_typed h hE he first loc here res
end Unit

end Solidity.Correctness.Lowering.Total.StructTableAgreement
