import Solidity.Storage.Representation.GraphFrames
import Solidity.Storage.Representation.Transport

/-! Finite represented observations of existing typed graph values. Source
reads are the committed Value.observe, including failures. Successful word/
length observations are transported; presence and extent stay source metadata.
No finite STy unrolling or public runtime-depth cutoff is required. -/
namespace Solidity.Storage.Representation.Graph

/-- Typed observation demands, not a source/value/path IR. -/
inductive Query {n : Nat} (G : TypeGraph.Schema n) (A : TypeGraph.Ty n) where
  | word {p : PrimTy} (path : TypeGraph.Path G A (.prim p))
  | length {E : TypeGraph.Ty n} (path : TypeGraph.Path G A (.array E))

noncomputable def Query.location {n : Nat} {G : TypeGraph.Schema n} {A : TypeGraph.Ty n}
    (q : Query G A) (l : Loc) : Loc :=
  match q with
  | .word p => pathLoc p l
  | .length p => pathLoc p l

noncomputable def Query.supported {n : Nat} {G : TypeGraph.Schema n} {A : TypeGraph.Ty n} :
    Query G A → Prop
  | .word p => PathSupported p
  | .length p => PathSupported p

/-- Only terminal primitive normalization/length-word conversion, not encoding
executed to define a source read. -/
def Query.read {n : Nat} {G : TypeGraph.Schema n} {A : TypeGraph.Ty n}
    (source : TypeGraph.Value G A) : Query G A → Option Semantics.Word
  | .word p => (source.observe p).map PrimTy.toWord
  | .length p => (source.observe p).map (fun h => lengthWord h.1.val h.1.isLt)

/-- Query-local terminal-header bounds. Word queries do not assert bounds
for every intermediate array; whole legacy ValueRep remains the stronger
full-value relation. Path index bounds are checked separately. -/
def Query.compatible {n : Nat} {G : TypeGraph.Schema n} {A : TypeGraph.Ty n}
    (source : TypeGraph.Value G A) : Query G A → Prop
  | .word _ => True
  | .length p => match source.observe p with
    | none => True
    | some h => h.1.val ≤ lmax ∧ h.2.val ≤ lmax

def Query.prefix {n : Nat} {G : TypeGraph.Schema n} {A B : TypeGraph.Ty n}
    (p : TypeGraph.Path G A B) : Query G B → Query G A
  | .word q => .word (p.append q)
  | .length q => .length (p.append q)

theorem Query.location_prefix {n : Nat} {G : TypeGraph.Schema n} {A B : TypeGraph.Ty n}
    (p : TypeGraph.Path G A B) (q : Query G B) (l : Loc) :
    (q.prefix p).location l = q.location (pathLoc p l) := by
  cases q with
  | word q => exact pathLoc_append p q l
  | length q => exact pathLoc_append p q l

theorem Query.supported_prefix {n : Nat} {G : TypeGraph.Schema n} {A B : TypeGraph.Ty n}
    (p : TypeGraph.Path G A B) (q : Query G B) :
    (q.prefix p).supported ↔ PathSupported p ∧ q.supported := by
  cases q with
  | word q => exact PathSupported_append p q
  | length q => exact PathSupported_append p q

theorem Query.read_prefix {n : Nat} {G : TypeGraph.Schema n} {A B : TypeGraph.Ty n}
    (root : TypeGraph.Value G A) (child : TypeGraph.Value G B)
    (p : TypeGraph.Path G A B) (q : Query G B) (found : root.find p = some child) :
    (q.prefix p).read root = q.read child := by
  cases q <;> simp only [Query.read, Query.prefix, TypeGraph.Value.observe_append,
    found, Option.bind_some]

theorem Query.compatible_prefix {n : Nat} {G : TypeGraph.Schema n} {A B : TypeGraph.Ty n}
    (root : TypeGraph.Value G A) (child : TypeGraph.Value G B)
    (p : TypeGraph.Path G A B) (q : Query G B) (found : root.find p = some child) :
    (q.prefix p).compatible root = q.compatible child := by
  cases q with
  | word q => rfl
  | length q => simp only [Query.compatible, Query.prefix, TypeGraph.Value.observe_append,
      found, Option.bind_some]

/-- A finite observation relation for the actual typed graph source. -/
noncomputable def Represented {n : Nat} {G : TypeGraph.Schema n} {A : TypeGraph.Ty n}
    (source : TypeGraph.Value G A) (queries : List (Query G A)) (l : Loc) (w : Store) : Prop :=
  ∀ q ∈ queries, q.supported ∧ q.compatible source ∧
    ∀ value, q.read source = some value → w (q.location l) = value

/-- The primitive base case extends the existing intrinsic value relation. -/
theorem represented_scalar {n : Nat} {G : TypeGraph.Schema n} {p : PrimTy}
    (v : p.Denote) {l : Loc} {w : Store} (h : ValueRep (.prim v) .word l w) :
    Represented (TypeGraph.Value.prim (G := G) v) [.word .nil] l w := by
  intro q member
  simp only [List.mem_singleton] at member
  subst q
  refine ⟨True.intro, True.intro, ?_⟩
  intro value observed
  change some (PrimTy.toWord v) = some value at observed
  exact (scalar_read h).trans (Option.some.inj observed)

/-- Representation composes through any existing typed graph path, including
recursive declaration paths of arbitrary finite length. -/
theorem Represented.prefix {n : Nat} {G : TypeGraph.Schema n} {A B : TypeGraph.Ty n}
    {root : TypeGraph.Value G A} {child : TypeGraph.Value G B}
    (p : TypeGraph.Path G A B) {queries : List (Query G B)} {l : Loc} {w : Store}
    (found : root.find p = some child) (supported : PathSupported p)
    (h : Represented child queries (pathLoc p l) w) :
    Represented root (queries.map (Query.prefix p)) l w := by
  intro q member
  obtain ⟨suffix, suffixMember, rfl⟩ := List.mem_map.mp member
  obtain ⟨ok, compatible, represented⟩ := h suffix suffixMember
  refine ⟨(Query.supported_prefix p suffix).mpr ⟨supported, ok⟩, ?_, ?_⟩
  · rw [Query.compatible_prefix root child p suffix found]
    exact compatible
  · intro value observed
    rw [Query.location_prefix]
    apply represented value
    rwa [Query.read_prefix root child p suffix found] at observed

def Query.apart {n : Nat} {G : TypeGraph.Schema n} {A U : TypeGraph.Ty n}
    (p : TypeGraph.Path G A U) : Query G A → Prop
  | .word q => Apart G p q
  | .length q => Apart G p q

theorem Query.read_frame {n : Nat} {G : TypeGraph.Schema n} {A U : TypeGraph.Ty n}
    (root result : TypeGraph.Value G A) (p : TypeGraph.Path G A U) (new : TypeGraph.Value G U)
    (saved : root.save p new = some result) (q : Query G A) (apart : q.apart p) :
    q.read result = q.read root := by
  cases q <;> simp only [Query.read, Apart.observe_save apart root result new saved]

theorem Query.compatible_frame {n : Nat} {G : TypeGraph.Schema n} {A U : TypeGraph.Ty n}
    (root result : TypeGraph.Value G A) (p : TypeGraph.Path G A U) (new : TypeGraph.Value G U)
    (saved : root.save p new = some result) (q : Query G A) (apart : q.apart p) :
    q.compatible result = q.compatible root := by
  cases q with
  | word q => rfl
  | length q => simp only [Query.compatible, Apart.observe_save apart root result new saved]

/-- Recursive source frames and an explicit symbolic nonalias boundary preserve
represented observations. Numeric nonalias follows from FiniteRun on the
covered locations, never from global injectivity. -/
theorem Represented.write_frame {n : Nat} {G : TypeGraph.Schema n} {A U : TypeGraph.Ty n}
    {root result : TypeGraph.Value G A} {queries : List (Query G A)} {l x : Loc} {w : Store}
    (h : Represented root queries l w) (p : TypeGraph.Path G A U) (new : TypeGraph.Value G U)
    (saved : root.save p new = some result) (value : Semantics.Word)
    (apart : ∀ q ∈ queries, q.apart p) (nonalias : ∀ q ∈ queries, q.location l ≠ x) :
    Represented result queries l (write w x value) := by
  intro q member
  obtain ⟨supported, compatible, represented⟩ := h q member
  refine ⟨supported, ?_, ?_⟩
  · rw [Query.compatible_frame root result p new saved q (apart q member)]
    exact compatible
  · intro word observed
    rw [write_other _ _ _ _ (nonalias q member)]
    apply represented word
    rwa [Query.read_frame root result p new saved q (apart q member)] at observed

/-- Recursive ancestor array-header representation frames an element write,
with the explicit symbolic header/word nonalias boundary. -/
theorem Represented.header_write_frame {n : Nat} {G : TypeGraph.Schema n}
    {A E U : TypeGraph.Ty n} {root result : TypeGraph.Value G A} {l x : Loc} {w : Store}
    (stem : TypeGraph.Path G A (.array E)) (i : TypeGraph.Index) (tail : TypeGraph.Path G E U)
    (h : Represented root [.length stem] l w) (new : TypeGraph.Value G U)
    (saved : root.save (stem.append (.cons (.index i) tail)) new = some result)
    (value : Semantics.Word) (nonalias : pathLoc stem l ≠ x) :
    Represented result [.length stem] l (write w x value) := by
  intro q member
  simp only [List.mem_singleton] at member
  subst q
  obtain ⟨supported, compatible, represented⟩ := h (.length stem) (by simp only [List.mem_singleton])
  have header : result.observe stem = root.observe stem :=
    ancestor_header_frame stem i tail root result new saved
  refine ⟨supported, ?_, ?_⟩
  · simpa only [Query.compatible, header] using compatible
  · intro word observed
    change write w x value (pathLoc stem l) = word
    rw [write_other _ _ _ _ nonalias]
    apply represented word
    simpa only [Query.read, header] using observed

/-- A covered successful graph demand exports the exact numeric word. -/
theorem Represented.numeric {n : Nat} {G : TypeGraph.Schema n} {A : TypeGraph.Ty n}
    {root : TypeGraph.Value G A} {queries : List (Query G A)} {l : Loc} {w : Store}
    (h : Represented root queries l w) {N : Nat} {H : Pre → Nat} {xs : List Loc} {m : WordStore}
    (transported : Transport N H xs w m) (q : Query G A) (member : q ∈ queries)
    (covered : q.location l ∈ xs) (value : Semantics.Word) (observed : q.read root = some value) :
    m (Loc.word N H (q.location l)) = value :=
  (transported _ covered).trans ((h q member).2.2 value observed)

end Solidity.Storage.Representation.Graph
