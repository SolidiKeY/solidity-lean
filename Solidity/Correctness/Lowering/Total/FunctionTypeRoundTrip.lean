import Solidity.Correctness.Lowering.Total.FunctionTypeFuelLaws
import Solidity.Correctness.Lowering.Total.FunctionTypeRoundTrip.Leaves

/-!
# Loop lowering: the function-signature round trip

`FunctionTypeDecode` reads a retained function-type spelling back as a tree
(`readSig`, `ofDecl`, `ofRows`); `FunctionTypeParserLaws` proves the delimiter
law `fnParts?_fnTyStr`, `FunctionTypeFuelLaws` the fuel laws under the reading
hypotheses `Part.Splits`. Here they are composed, with every definition of
those modules unchanged: a tree whose leaves satisfy `Part.Canon` is read
back from its own spelling, annotations erased.

* `Part.Canon` (decidable): the conditions, at the leaves only. A function
  node adds none: either flag, any annotation, any number of parameters and
  returns (none included), any nesting.
  * elementary (`Spelled`): `bool`, `address`, `uintN`/`intN` at every width,
    `bytesN`; these are exactly the elementary leaves that read back
    (`elem_reads_iff`);
  * named (`NamedOk`): a `Well` component that is no function-type marker,
    reads as no elementary type (`ElemFree`) and ends in no location word
    (`locSuffix c = none`); the last two are exactly `leaf c = .named c`
    (`leaf_eq_named_iff`);
  * located (`LocatedOk`): the spelling `b ++ locName l` is a `Well`
    component and no function-type marker; the boundary is then the spelled
    one for every base (`leaf_located`).
* `Part.canon_splits`: `Part.Splits` holds at the tree's own spelling, by
  recursion on the tree (`fnParts?_fnTyStr` at each function node,
  `well_fnTyStr` for the node as a component, the leaf facts at the leaves).
* `readSig_roundtrip`: `readSig t.spell = some t.erase` for a canonical
  function tree, at `readSig`'s own fuel (the spelling length plus one). Its
  only premise is `Canon`: no `Part.Splits`, `fnParts?` equation or successful
  evaluation is assumed. `part_canon_iff`: the fuels that read it are exactly
  those from its depth on.
* `ofDecl_roundtrip`, `ofRows_roundtrip`, `ofRows_valueRows`: the same for a
  declaration's marker type and for marker rows (`fnRow?` on the row
  `k#function(…)`, `valueRows?`'s own rows), from their definitions.
* `canon_erase_inj`: canonical trees with one spelling have one erasure.

## What does not round-trip

`Canon` is sufficient; the leaf conditions `ElemFree`, `locSuffix c = none`
and `Spelled` are also necessary for the leaf itself. A tree outside it need
not come back, and nothing here makes it (the examples check each case):

* **unsupported elementary spellings**: `address payable`, `string`, `bytes`
  and `fixed` types are spelled `""` by `elemName`; a lone `""` parameter is
  read back as no parameter;
* **named leaves read as something else**: `uint256` (an elementary name),
  `Tmemory` (a location suffix: the type/location boundary is not recorded);
* **malformed or ambiguous components**: an empty name, a comma or an
  unbalanced bracket at the component's own depth (not `Well`): components
  merge or split, or the spelling is refused;
* **function-type suffixes**: a named or located component starting with
  `function(` (`function(uint)[]memory`) is taken for a function type and
  refused by `fnParts?`.

`Well` is the delimiter laws' sufficient condition, not shown necessary.
Nothing erased is recovered: the result is `t.erase`, the same for every
mutability, `internal` keyword and annotation (`readSig_annotation_free`);
`address payable` is not `Spelled`. These are conditions on spellings; they
are no premise or exclusion of `lowerLoopsCorrect`. Annotation agreement,
semantic binding, universal coverage and final validation stay with the
original decoder's unit integration.
-/

namespace Solidity.Correctness.Lowering.Total.FunctionTypeRoundTrip

open Source (DataLoc)
open FunctionTypeDecode
open FunctionTypeParserLaws (Well fnTy?_mk)

/-! ## Leaf conditions -/

instance : (e : Source.Elem) → Decidable (Spelled e)
  | .bool | .address | .int .. | .fixedBytes .. => isTrue trivial
  | .addressPayable | .string | .bytes | .fixed .. => isFalse id

/-- `fnTy? c = false`, decided on characters. -/
theorem notFn_iff (c : String) : fnTy? c = false ↔ ¬ c.data.take 9 = "function(".data := by
  rw [show fnTy? c = decide (c.data.take 9 = "function(".data) from fnTy?_mk c.data]
  exact decide_eq_false_iff_not

/-- `locSuffix c = none`, decided on characters. -/
theorem locFree_iff (c : String) : locSuffix c = none ↔ locL c.data = none := by
  rw [show locSuffix c = locL c.data from locSuffix_mk c.data]

/-- **A named leaf that reads back as itself**: a `Well` component, no
function-type marker, read as no elementary type, ending in no location word. -/
structure NamedOk (c : String) : Prop where
  well : Well c
  notFn : fnTy? c = false
  elemFree : ElemFree c
  locFree : locSuffix c = none

theorem namedOk_iff (c : String) : NamedOk c ↔
    Well c ∧ ¬ c.data.take 9 = "function(".data ∧ ElemFree c ∧ locL c.data = none :=
  ⟨fun h => ⟨h.well, (notFn_iff c).1 h.notFn, h.elemFree, (locFree_iff c).1 h.locFree⟩,
    fun ⟨w, f, e, l⟩ => ⟨w, (notFn_iff c).2 f, e, (locFree_iff c).2 l⟩⟩

instance (c : String) : Decidable (NamedOk c) := decidable_of_iff _ (namedOk_iff c).symm

/-- **A located leaf that reads back**: its spelling is a `Well` component and
no function-type marker. No condition on the boundary: `leaf_located`. -/
structure LocatedOk (b : String) (l : DataLoc) : Prop where
  well : Well (b ++ locName l)
  notFn : fnTy? (b ++ locName l) = false

theorem locatedOk_iff (b : String) (l : DataLoc) : LocatedOk b l ↔
    Well (b ++ locName l) ∧ ¬ (b ++ locName l).data.take 9 = "function(".data :=
  ⟨fun h => ⟨h.well, (notFn_iff _).1 h.notFn⟩, fun ⟨w, f⟩ => ⟨w, (notFn_iff _).2 f⟩⟩

instance (b : String) (l : DataLoc) : Decidable (LocatedOk b l) :=
  decidable_of_iff _ (locatedOk_iff b l).symm

/-- The two conditions under which `leaf` reads a component as that name:
exactly these. -/
theorem leaf_eq_named_iff (c : String) :
    leaf c = .named c ↔ ElemFree c ∧ locSuffix c = none := by
  unfold leaf ElemFree
  generalize Decode.typeNameB (.named c) = o
  generalize locSuffix c = q
  constructor
  · intro h
    split at h
    · cases h
    · rename_i ne
      refine ⟨fun e he => ne e he, ?_⟩
      split at h
      · cases h
      · rfl
  · rintro ⟨free, rfl⟩
    split
    · exact absurd rfl (free _)
    · rfl

/-- `leaf` reads a name only as itself. -/
theorem leaf_named {c n : String} (h : leaf c = .named n) : n = c := by
  unfold leaf at h
  generalize Decode.typeNameB (.named c) = o at h
  generalize locSuffix c = q at h
  split at h
  · cases h
  · split at h
    · cases h
    · cases h
      rfl

/-- An elementary type's spelling reads back exactly when it is `Spelled`. -/
theorem elem_reads_iff (e : Source.Elem) : leaf (elemName e) = .elem e ↔ Spelled e := by
  constructor
  · intro h
    cases e with
    | bool | address | int | fixedBytes => trivial
    | addressPayable | string | bytes | fixed =>
      have : leaf "" = .named "" := (leaf_mk []).trans (by decide)
      rw [show elemName _ = "" from rfl, this] at h
      cases h
  · exact fun h => (spelled_leaf h).1

end Solidity.Correctness.Lowering.Total.FunctionTypeRoundTrip

/-! ## Canonical trees (in the trees' namespace, for `t.Canon`) -/

namespace Solidity.Correctness.Lowering.Total.FunctionTypeDecode

open FunctionTypeRoundTrip
open FunctionTypeParserLaws (Well fnParts?_fnTyStr well_fnTyStr)

mutual
/-- **The round-trip conditions**, at the leaves: `Spelled` elementary types,
`NamedOk` names, `LocatedOk` references. A function node adds none. -/
def Part.Canon {α : Type} : Part α → Prop
  | .elem e => Spelled e
  | .named c => NamedOk c
  | .located b l => LocatedOk b l
  | .fn _ _ ps rs => ps.Canon ∧ rs.Canon
/-- Every component canonical. -/
def Parts.Canon {α : Type} : Parts α → Prop
  | .nil => True
  | .cons t ts => t.Canon ∧ ts.Canon
end

mutual
/-- `Canon` is decidable (in the kernel, on a concrete tree). -/
def Part.decCanon {α : Type} : (t : Part α) → Decidable t.Canon
  | .elem e => inferInstanceAs (Decidable (Spelled e))
  | .named c => inferInstanceAs (Decidable (NamedOk c))
  | .located b l => inferInstanceAs (Decidable (LocatedOk b l))
  | .fn _ _ ps rs => @instDecidableAnd _ _ ps.decCanon rs.decCanon
def Parts.decCanon {α : Type} : (ts : Parts α) → Decidable ts.Canon
  | .nil => isTrue trivial
  | .cons t ts => @instDecidableAnd _ _ t.decCanon ts.decCanon
end

instance {α : Type} (t : Part α) : Decidable t.Canon := t.decCanon
instance {α : Type} (ts : Parts α) : Decidable ts.Canon := ts.decCanon

mutual
/-- The conditions do not mention annotations. -/
theorem Part.canon_erase {α : Type} : (t : Part α) → (t.erase.Canon ↔ t.Canon)
  | .elem _ | .named _ | .located _ _ => Iff.rfl
  | .fn _ _ ps rs => and_congr (Parts.canon_erase ps) (Parts.canon_erase rs)
theorem Parts.canon_erase {α : Type} : (ts : Parts α) → (ts.erase.Canon ↔ ts.Canon)
  | .nil => Iff.rfl
  | .cons t ts => and_congr (Part.canon_erase t) (Parts.canon_erase ts)
end

mutual
/-- **The reading hypotheses, discharged.** A canonical tree satisfies
`Part.Splits` at its own spelling, and that spelling is a `Well` component (so
it may stand inside another signature). -/
theorem Part.canon_splits {α : Type} :
    (t : Part α) → t.Canon → t.Splits t.spell ∧ Well t.spell
  | .elem _, h =>
    have l := spelled_leaf h
    ⟨⟨l.2.1, l.1⟩, l.2.2⟩
  | .named c, h => ⟨⟨h.notFn, (leaf_eq_named_iff c).2 ⟨h.elemFree, h.locFree⟩⟩, h.well⟩
  | .located b l, h => ⟨⟨h.notFn, leaf_located b l⟩, h.well⟩
  | .fn ext _ ps rs, ⟨hp, hr⟩ =>
    have p := Parts.canon_splits ps hp
    have r := Parts.canon_splits rs hr
    ⟨⟨ps.spells, rs.spells, fnParts?_fnTyStr ext p.2 (fun c m => (r.2 c m).1), p.1, r.1⟩,
      well_fnTyStr ext p.2 r.2⟩
/-- Canonical components satisfy their hypotheses, pointwise and in order, and
each spelling is `Well`. -/
theorem Parts.canon_splits {α : Type} :
    (ts : Parts α) → ts.Canon → ts.Splits ts.spells ∧ ∀ c ∈ ts.spells, Well c
  | .nil, _ => ⟨rfl, fun _ m => nomatch m⟩
  | .cons t ts, ⟨ht, hts⟩ =>
    have a := Part.canon_splits t ht
    have b := Parts.canon_splits ts hts
    ⟨⟨t.spell, ts.spells, rfl, a.1, b.1⟩, fun c m => by
      rcases List.mem_cons.1 m with rfl | m
      · exact a.2
      · exact b.2 c m⟩
end

end Solidity.Correctness.Lowering.Total.FunctionTypeDecode

namespace Solidity.Correctness.Lowering.Total.FunctionTypeRoundTrip

open Source (DataLoc)
open FunctionTypeDecode
open FunctionTypeParserLaws (fnTy?_mk fnTy?_fnTyStr)
open FunctionTypeParserLaws.Str (drop_mk startsWith_mk)

/-! ## The round trip -/

/-- A canonical tree is read from its spelling exactly with fuel from its
structural depth on (a leaf included: fuel `1`). -/
theorem part_canon_iff {α : Type} {t : Part α} (h : t.Canon) (n : Nat) :
    part n t.spell = some t.erase ↔ t.depth ≤ n :=
  part_splits_iff (Part.canon_splits t h).1 n

/-- **The signature round trip.** `readSig`, at its own fuel (the spelling
length plus one), reads the spelling of a canonical function tree back as the
tree with its annotations erased: either visibility flag, parameters and
returns in order, empty lists, any nesting. -/
theorem readSig_roundtrip {α : Type} {ext : Bool} {a : α} {ps rs : Parts α}
    (h : (Part.fn ext a ps rs).Canon) :
    readSig (Part.fn ext a ps rs).spell = some (Part.fn ext a ps rs).erase :=
  readSig_spell (Part.canon_splits _ h).1

/-- The same on the spelling as `fnTyStr` writes it. -/
theorem readSig_fnTyStr {α : Type} (ext : Bool) (a : α) {ps rs : Parts α}
    (hp : ps.Canon) (hr : rs.Canon) :
    readSig (fnTyStr ps.spells rs.spells ext) = some (.fn ext () ps.erase rs.erase) :=
  readSig_roundtrip (a := a) ⟨hp, hr⟩

/-- A canonical leaf's spelling is no retained signature: `readSig` reads
function types only. -/
theorem readSig_leaf {α : Type} {t : Part α} (h : t.Canon)
    (isLeaf : ∀ ext a ps rs, t ≠ .fn ext a ps rs) : readSig t.spell = none := by
  have s := (Part.canon_splits t h).1
  unfold readSig
  cases t with
  | elem _ | named _ | located _ _ => rw [if_neg (by rw [s.1]; exact Bool.false_ne_true)]
  | fn ext a ps rs => exact absurd rfl (isLeaf ext a ps rs)

/-- The reading keeps no annotation: trees with one erasure, whatever their
mutabilities and `internal` keywords, have one spelling, read as that erasure. -/
theorem readSig_annotation_free {α β : Type} {ext : Bool} {a : α} {b : β} {ps rs : Parts α}
    {ps' rs' : Parts β} (h : (Part.fn ext a ps rs).Canon)
    (same : (Part.fn ext a ps rs).erase = (Part.fn ext b ps' rs').erase) :
    readSig (Part.fn ext a ps rs).spell = some (Part.fn ext b ps' rs').erase :=
  same ▸ readSig_roundtrip h

/-- **Canonical spellings determine the tree up to annotations.** -/
theorem canon_erase_inj {α β : Type} {t : Part α} {u : Part β} (ht : t.Canon) (hu : u.Canon)
    (same : t.spell = u.spell) : t.erase = u.erase := by
  have a := (part_canon_iff ht (max t.depth u.depth)).2 (Nat.le_max_left _ _)
  have b := (part_canon_iff hu (max t.depth u.depth)).2 (Nat.le_max_right _ _)
  rw [same, b] at a
  exact (Option.some.inj a).symm

/-! ## Declarations and marker rows -/

/-- **`ofDecl`.** The marker type `expandTy` leaves for a canonical function
type is read back. -/
theorem ofDecl_roundtrip {α : Type} {ext : Bool} {a : α} {ps rs : Parts α}
    (h : (Part.fn ext a ps rs).Canon) :
    ofDecl (.named (Part.fn ext a ps rs).spell) = some (Part.fn ext a ps rs).erase :=
  readSig_roundtrip h

theorem append_data (k s : String) : k ++ "#" ++ s = ⟨k.data ++ '#' :: s.data⟩ :=
  String.ext (by simp)

/-- `fnRow?` finds the marker row `k#function(…)` standing first and returns
the spelling behind `k#`. -/
theorem fnRow?_marker (k : String) {s : String} (isFn : fnTy? s = true) (w : Nat)
    (rows : List (String × Nat)) : fnRow? ((k ++ "#" ++ s, w) :: rows) k = some s := by
  have t9 : s.data.take 9 = "function(".data := by
    have := isFn
    rw [show fnTy? s = decide (s.data.take 9 = "function(".data) from fnTy?_mk s.data] at this
    exact of_decide_eq_true this
  have pre : k ++ "#function(" = ⟨k.data ++ "#function(".data⟩ := String.ext (by simp)
  have st : (k ++ "#" ++ s).startsWith (k ++ "#function(") = true := by
    rw [append_data, pre, startsWith_mk]
    refine decide_eq_true ?_
    rw [List.length_append, List.take_append]
    simp only [List.take_of_length_le (Nat.le_add_right _ _), Nat.add_sub_cancel_left]
    show k.data ++ '#' :: s.data.take 9 = _
    rw [t9]
  have dr : (k ++ "#" ++ s).drop (k.length + 1) = s := by
    rw [append_data, drop_mk]
    refine String.ext ?_
    show (k.data ++ '#' :: s.data).drop (k.data.length + 1) = s.data
    rw [show k.data ++ '#' :: s.data = (k.data ++ ['#']) ++ s.data by simp]
    exact List.drop_left' (by simp)
  simp only [fnRow?, List.findSome?_cons, st, if_true, dr]

/-- A row that is no marker of `k` is passed over. -/
theorem fnRow?_skip (k : String) {k' : String} (w : Nat) (rows : List (String × Nat))
    (h : k'.startsWith (k ++ "#function(") = false) :
    fnRow? ((k', w) :: rows) k = fnRow? rows k := by
  simp only [fnRow?, List.findSome?_cons, h, Bool.false_eq_true, if_false]

/-- **`ofRows`.** Marker rows whose first row is `k#` followed by a canonical
function type's spelling are read, at the key `k`, as its erased tree. -/
theorem ofRows_roundtrip {α : Type} {ext : Bool} {a : α} {ps rs : Parts α}
    (h : (Part.fn ext a ps rs).Canon) (k : String) (w : Nat) (rows : List (String × Nat)) :
    ofRows ((k ++ "#" ++ (Part.fn ext a ps rs).spell, w) :: rows) k
      = some (Part.fn ext a ps rs).erase := by
  unfold ofRows
  rw [fnRow?_marker k (s := (Part.fn ext a ps rs).spell) (fnTy?_fnTyStr _ _ ext),
    Option.bind_some]
  exact readSig_roundtrip h

/-- **`valueRows?`.** The rows the elaborator keeps for a canonical function
type (a `uint` tag and its marker row) are read back, at a local's key `""`. -/
theorem ofRows_valueRows {α : Type} {ext : Bool} {a : α} {ps rs : Parts α}
    (h : (Part.fn ext a ps rs).Canon) :
    ∃ rows, valueRows? (Part.fn ext a ps rs).spell = some (.uint, rows) ∧
      ofRows rows "" = some (Part.fn ext a ps rs).erase :=
  ⟨_, valueRows_fn (fnTy?_fnTyStr _ _ ext), by
    have := ofRows_roundtrip h "" 0 []
    rwa [show "" ++ "#" ++ (Part.fn ext a ps rs).spell = "#" ++ (Part.fn ext a ps rs).spell from
      String.ext (by simp)] at this⟩

end Solidity.Correctness.Lowering.Total.FunctionTypeRoundTrip
