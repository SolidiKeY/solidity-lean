import Solidity.Storage.Representation.GraphRepresentation
import Solidity.Semantics.RecursiveStorage.Legacy

/-! Compatibility with committed finite intrinsic legacy/graph layouts.
The ordinary and graph sources remain independently defined; these are
representation bridge theorems, not new source semantics. -/
namespace Solidity.Storage.Representation.Graph

/-- Existing finite legacy layout evidence and TypeRep choose the same sizes. -/
theorem inlineSize_legacy {n : Nat} {G : TypeGraph.Schema n} {A : Solidity.Ty}
    {B : TypeGraph.Ty n} (layout : TypeGraph.Legacy.Layout G A B) {t : STy}
    (shape : TypeRep A t) : t.size = inlineSize G B := by
  refine TypeGraph.Legacy.Layout.rec
    (motive_1 := fun {A B} _ => ∀ {t : STy}, TypeRep A t → t.size = inlineSize G B)
    (motive_2 := fun {as bs} _ => ∀ {ts : List STy}, FieldTypesRep as ts →
      STy.sizes ts = (bs.map (fun f => inlineSize G f.2)).sum)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ layout shape
  · intro p t shape
    cases shape
    rfl
  · intro s i fields ih t shape
    cases shape with
    | strct _ ts types =>
      rw [STy.size, inlineSize_node]
      exact ih types
  · intro A B elem ih t shape
    cases shape
    rfl
  · intro A B elem size ih t shape
    cases shape with
    | fixed _ element =>
      exact congrArg (fun s => size.val * s) (ih element)
  · intro A B K elem ih t shape
    cases shape
    rfl
  · intro ts types
    cases types
    rfl
  · intro f A B as bs head tail ih it ts types
    cases types with
    | cons h r =>
      change _ + _ = _ + _
      rw [ih h, it r]
      rfl

/-- Mapping-only path compatibility reuses the committed intrinsic KeyPath. -/
theorem keypath_supported {n : Nat} {G : TypeGraph.Schema n}
    {A U : Solidity.Ty} {B V : TypeGraph.Ty n}
    {layout : TypeGraph.Legacy.Layout G A B} {leaf : TypeGraph.Legacy.Layout G U V}
    (path : TypeGraph.Legacy.KeyPath layout leaf) : PathSupported path.graph := by
  induction path with
  | nil => exact True.intro
  | key K k rest ih => exact ⟨True.intro, ih⟩

/-- Every committed typed mapping-chain read reaches a represented subtree,
at the graph path's same symbolic Loc, with no chain-length cutoff. -/
theorem keypath_subvalue_rep {n : Nat} {G : TypeGraph.Schema n}
    {A U : Solidity.Ty} {B V : TypeGraph.Ty n}
    {layout : TypeGraph.Legacy.Layout G A B} {leaf : TypeGraph.Legacy.Layout G U V}
    (path : TypeGraph.Legacy.KeyPath layout leaf) :
    ∀ (source : SVal A) (value : SVal U) {t : STy} {l : Loc} {w : Store},
      ValueRep source t l w → source.find path.legacy = some value →
      ∃ u, TypeRep U u ∧ ValueRep value u (pathLoc path.graph l) w := by
  induction path with
  | nil =>
    intro source value t l w represented found
    simp only [TypeGraph.Legacy.KeyPath.legacy, SVal.find_nil, Option.some.injEq] at found
    subst value
    exact ⟨t, represented.type, represented⟩
  | key K k rest ih =>
    intro source value t l w represented found
    cases source with
    | map entries fallback =>
      cases represented with
      | mapping _ _ child _ _ _ values =>
        let selected := (Semantics.lookupBy k entries.toList).getD fallback
        have selectedFound : selected.find rest.legacy = some value := by
          dsimp only [selected]
          rw [TypeGraph.Legacy.KeyPath.legacy, SVal.find_key] at found
          cases h : Semantics.lookupBy k entries.toList <;>
            simp only [h, Option.getD_none, Option.getD_some] at found ⊢ <;> exact found
        exact ih selected value (values k) selectedFound

/-- Existing whole legacy mapping representation extends to a graph word
observation through the committed semantic compatibility interface. -/
theorem keypath_word_represented {n : Nat} {G : TypeGraph.Schema n} {A : Solidity.Ty}
    {B : TypeGraph.Ty n} {layout : TypeGraph.Legacy.Layout G A B} {p : PrimTy}
    (path : TypeGraph.Legacy.KeyPath layout (TypeGraph.Legacy.Layout.prim p))
    (source : SVal A) (value : p.Denote) {t : STy} {l : Loc} {w : Store}
    (represented : ValueRep source t l w) (found : source.find path.legacy = some (.prim value)) :
    Represented (layout.encode source) [.word path.graph] l w := by
  obtain ⟨u, shape, leafRep⟩ := keypath_subvalue_rep path source (.prim value) represented found
  cases shape
  have graphFound : (layout.encode source).find path.graph = some (.prim value) := by
    rw [path.find_encode, found]
    rfl
  simpa only [List.map_cons, List.map_nil, Query.prefix, path_append_nil] using
    (Represented.prefix path.graph graphFound (keypath_supported path)
      (represented_scalar (G := G) value leafRep))

/-- A legacy represented array provides a graph header with exact length and
bounded retained extent; the existing bridge's extent cap never adds slots. -/
theorem legacy_array_header {n : Nat} {G : TypeGraph.Schema n} {E : Solidity.Ty}
    {F : TypeGraph.Ty n} (elem : TypeGraph.Legacy.Layout G E F)
    {count : Nat} {vs : SVec E count} {sh : SList E} {hn : count < 2 ^ 256}
    {t : STy} {l : Loc} {w : Store}
    (represented : ValueRep (.array vs sh hn) (.darr t) l w) :
    Represented ((TypeGraph.Legacy.Layout.array elem).encode (.array vs sh hn)) [.length .nil] l w := by
  intro q member
  simp only [List.mem_singleton] at member
  subst q
  cases represented with
  | array _ _ _ _ _ _ _ live extent header _ =>
    refine ⟨True.intro, ?_, ?_⟩
    · change count ≤ lmax ∧ min (vs.toList ++ sh.toList).length (2 ^ 256) ≤ lmax
      exact ⟨live, Nat.le_trans (Nat.min_le_left _ _) extent⟩
    · intro value observed
      change some (lengthWord count hn) = some value at observed
      exact (Subtype.ext header).trans (Option.some.inj observed)

/-- Mapping-chain array-header representation also crosses the committed bridge. -/
theorem keypath_header_represented {n : Nat} {G : TypeGraph.Schema n} {A E : Solidity.Ty}
    {B F : TypeGraph.Ty n} {layout : TypeGraph.Legacy.Layout G A B}
    (elem : TypeGraph.Legacy.Layout G E F)
    (path : TypeGraph.Legacy.KeyPath layout (TypeGraph.Legacy.Layout.array elem))
    (source : SVal A) {count : Nat} {vs : SVec E count} {sh : SList E} {hn : count < 2 ^ 256}
    {t : STy} {l : Loc} {w : Store} (represented : ValueRep source t l w)
    (found : source.find path.legacy = some (.array vs sh hn)) :
    Represented (layout.encode source) [.length path.graph] l w := by
  obtain ⟨u, shape, leafRep⟩ := keypath_subvalue_rep path source (.array vs sh hn) represented found
  cases shape
  have graphFound : (layout.encode source).find path.graph =
      some ((TypeGraph.Legacy.Layout.array elem).encode (.array vs sh hn)) := by
    rw [path.find_encode, found]
    rfl
  simpa only [List.map_cons, List.map_nil, Query.prefix, path_append_nil] using
    (Represented.prefix path.graph graphFound (keypath_supported path) (legacy_array_header elem leafRep))

end Solidity.Storage.Representation.Graph
