import Solidity.Backend.StorageOps.ClearDemands

/-! Populated hashed-array/mapping controls for actual clear demand realization.
The target is the owner's numeric WordStore; no emitted EVM/world claim. -/
namespace Solidity.Backend.StorageOps.ClearDemandControls
open TypeGraph Solidity.Storage Solidity.Storage.Representation Solidity.Storage.Representation.Graph
private def z : Fin 1 := ⟨0, by decide⟩
private def fields : List (Name × TypeGraph.Ty 1) :=
  [("word", .prim .bool), ("memo", .mapping .bool (.prim .bool))]
private def graph : Schema 1 where
  origin := "v10-clear-demand-controls"
  declId := fun _ => 0
  declId_injective := by intro i j _; apply Fin.ext; omega
  name := fun _ => "Item"
  fields := fun _ => fields
  rank := fun _ => 1
  nonempty := fun _ => rfl
  distinct := fun _ => rfl
  guarded := by
    intro i f hf
    simp only [fields, List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl <;> exact Nat.zero_lt_succ 0
private def nodeFields : TypeGraph.Fields graph fields := fun p => match p with
  | .here => .prim true
  | .there .here => .mapping (fun _ => .present (.prim true))
  | .there (.there p) => nomatch p
private def item : Value graph (.node z) := .node nodeFields
private def old : Value graph (.array (.node z)) :=
  .array ⟨2, by decide⟩ ⟨1, by decide⟩ (by decide) (fun _ => .present item)
private def ix (n : Nat) (h : n < 2 ^ 256) : Index := ⟨n, h⟩
private def index0 : Index := ix 0 (by decide)
private def index1 : Index := ix 1 (by decide)
private def index2 : Index := ix 2 (by decide)
private def wordPath (i : Index) : TypeGraph.Path graph (.array (.node z)) (.prim .bool) :=
  .cons (.index i) (.cons (.field .here) .nil)
private def memoStem (i : Index) : TypeGraph.Path graph (.array (.node z)) (.mapping .bool (.prim .bool)) :=
  .cons (.index i) (.cons (.field (.there .here)) .nil)
private def memoPath (i : Index) (key : Bool := false) : TypeGraph.Path graph (.array (.node z)) (.prim .bool) :=
  (memoStem i).append (.cons (.key key) .nil)
private def queries : List (Query graph (.array (.node z))) :=
  [.word (wordPath index1), .word (memoPath index0), .word (memoPath index1),
    .word (memoPath index0 true), .word (memoPath index1 true)]
private def base : Solidity.Storage.Loc := .root 0
private def one : Semantics.Word := PrimTy.toWord (p := .bool) true
private def seven : Semantics.Word := ⟨7, by decide⟩
private def zero : Semantics.Word := ClearDemands.zero
private def hash (p : Solidity.Storage.Pre) : Nat :=
  if p = .data 0 then 4 else if p = .entry 0 5 then 8 else if p = .entry 0 7 then 12
  else if p = .entry 1 5 then 16 else if p = .entry 1 7 then 20 else 0
private def preimages : List Solidity.Storage.Pre := [.data 0, .entry 0 5, .entry 0 7, .entry 1 5, .entry 1 7]
private def store : Store := fun l =>
  if l = .root 2 then seven else if l = .root 0 ∨ l = .data (.root 0) 0 ∨ l = .data (.root 0) 2 ∨
    l = .hash 0 (.data (.root 0) 1) 0 ∨ l = .hash 0 (.data (.root 0) 3) 0 ∨
    l = .hash 1 (.data (.root 0) 1) 0 ∨ l = .hash 1 (.data (.root 0) 3) 0 then one else zero
private def machine : WordStore := fun a =>
  if a = 2 then seven else if a = 0 ∨ a = 4 ∨ a = 6 ∨ a = 8 ∨ a = 12 ∨ a = 16 ∨ a = 20 then one else zero
private noncomputable def afterMachine : WordStore := ClearDemands.numericClear (N := 32) old base hash machine
private noncomputable def afterStore : Store :=
  (ClearDemands.updates old base).foldl (fun w op => write w op.1 op.2) store

/-- Actual demand order: one LIVE payload, then its array header. The older
shadow payload and BOTH live/retained mappings are not clear demands. -/
theorem exact_demands : ClearDemands.demands old = [.word (wordPath index0), .length .nil] := rfl

theorem exact_locations : ClearDemands.coveredLocations old queries base =
    [.data (.root 0) 0, .root 0, .data (.root 0) 2,
      .hash 0 (.data (.root 0) 1) 0, .hash 0 (.data (.root 0) 3) 0,
      .hash 1 (.data (.root 0) 1) 0, .hash 1 (.data (.root 0) 3) 0] := rfl

private theorem run : FiniteRun 32 4 1 hash preimages (ClearDemands.coveredLocations old queries base) := by
  constructor
  · intro p
    simp only [hash]
    split <;> (first | decide | (split <;> (first | decide |
      (split <;> (first | decide | (split <;> (first | decide | (split <;> decide))))))))
  · decide
  · decide
  · decide
  · rw [exact_locations]
    intro l member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [Solidity.Storage.Loc.Bounded] <;> decide
  · rw [exact_locations]
    intro l member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

private theorem initial : Transport 32 hash (ClearDemands.coveredLocations old queries base) store machine := by
  rw [exact_locations]
  intro l member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

private theorem before : Represented old (ClearDemands.demands old ++ queries) base store := by
  rw [exact_demands]
  intro q member
  simp only [queries, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · refine ⟨?_, ?_, ?_⟩
    · change 0 < lmax ∧ True ∧ True
      exact ⟨by decide, True.intro, True.intro⟩
    · exact True.intro
    · intro word observed
      change some one = some word at observed
      cases observed
      rfl
  · refine ⟨?_, ?_, ?_⟩
    · change True
      exact True.intro
    · change 1 ≤ lmax ∧ 2 ≤ lmax
      exact ⟨by decide, by decide⟩
    · intro word observed
      change some one = some word at observed
      cases observed
      rfl
  · refine ⟨?_, ?_, ?_⟩
    · change 1 < lmax ∧ True ∧ True
      exact ⟨by decide, True.intro, True.intro⟩
    · exact True.intro
    · intro word observed
      change some one = some word at observed
      cases observed
      rfl
  · refine ⟨?_, ?_, ?_⟩
    · change 0 < lmax ∧ True ∧ True ∧ True
      exact ⟨by decide, True.intro, True.intro, True.intro⟩
    · exact True.intro
    · intro word observed
      change some one = some word at observed
      cases observed
      rfl
  · refine ⟨?_, ?_, ?_⟩
    · change 1 < lmax ∧ True ∧ True ∧ True
      exact ⟨by decide, True.intro, True.intro, True.intro⟩
    · exact True.intro
    · intro word observed
      change some one = some word at observed
      cases observed
      rfl
  · refine ⟨?_, True.intro, ?_⟩
    · change 0 < lmax ∧ True ∧ True ∧ True
      exact ⟨by decide, True.intro, True.intro, True.intro⟩
    · intro word observed
      change some one = some word at observed
      cases observed
      rfl
  · refine ⟨?_, True.intro, ?_⟩
    · change 1 < lmax ∧ True ∧ True ∧ True
      exact ⟨by decide, True.intro, True.intro, True.intro⟩
    · intro word observed
      change some one = some word at observed
      cases observed
      rfl

private theorem separate : ∀ q ∈ queries, q ∉ ClearDemands.demands old →
    ∀ d ∈ ClearDemands.demands old, q.location base ≠ d.location base := by
  intro q member _ d demanded
  simp only [queries, List.mem_cons, List.not_mem_nil, or_false] at member
  rw [exact_demands] at demanded
  simp only [List.mem_cons, List.not_mem_nil, or_false] at demanded
  rcases member with rfl | rfl | rfl | rfl | rfl <;> rcases demanded with rfl | rfl <;> decide

/-- Real hashed input run, OLD relation and source-generated coverage inhabit
the operation bridge; every generated and framed output query agrees. -/
theorem represented_numeric_clear :
    Represented (recursiveClear old) (ClearDemands.demands old ++ queries) base afterStore ∧
    Transport 32 hash (ClearDemands.coveredLocations old queries base) afterStore afterMachine ∧
    ∀ q ∈ ClearDemands.demands old ++ queries, ∀ word, q.read (recursiveClear old) = some word →
      afterMachine ((q.location base).word 32 hash) = word :=
  ClearDemands.complete_numeric old queries base hash preimages run store machine before initial separate

/-- Complete ordered fixture observations: live and retained words/mappings,
live-vs-retained aliases, malformed path, headers/extents, numeric words and
outside sentinel, BEFORE then AFTER. -/
theorem ordered_observations :
    (old.length.val, old.extent.val, old.observe (wordPath index0), old.observe (wordPath index1),
      old.observe (memoPath index0), old.observe (memoPath index1), old.observe (wordPath index2),
      (wordPath index0).readLive Value.dflt old |>.map Value.head,
      (wordPath index1).readLive Value.dflt old |>.map Value.head,
      (recursiveClear old).length.val, (recursiveClear old).extent.val,
      (recursiveClear old).observe (wordPath index0), (recursiveClear old).observe (wordPath index1),
      (recursiveClear old).observe (memoPath index0), (recursiveClear old).observe (memoPath index1),
      (recursiveClear old).observe (wordPath index2),
      (wordPath index0).readLive Value.dflt (recursiveClear old) |>.map Value.head,
      (wordPath index1).readLive Value.dflt (recursiveClear old) |>.map Value.head,
      machine 0, machine 4, machine 6, machine 8, machine 12, machine 2,
      afterMachine 0, afterMachine 4, afterMachine 6, afterMachine 8, afterMachine 12, afterMachine 2,
      old.observe (memoPath index0 true), old.observe (memoPath index1 true),
      (recursiveClear old).observe (memoPath index0 true), (recursiveClear old).observe (memoPath index1 true),
      machine 16, machine 20, afterMachine 16, afterMachine 20) =
    (1, 2, some true, some true, some true, some true, none, some true, none,
      0, 2, some false, some true, some true, some true, none, none, none,
      one, one, one, one, one, seven, zero, zero, one, one, one, seven,
      some true, some true, some true, some true, one, one, one, one) := rfl

/-- Wrong whole-extent clearing and mapping erasure violate observed frames. -/
theorem wrong_shadow_negative : (writeWord afterMachine 6 zero) 6 ≠ afterMachine 6 := by decide

theorem wrong_mapping_negative :
    (writeWord afterMachine 8 zero) 8 ≠ afterMachine 8 ∧
    (writeWord afterMachine 12 zero) 12 ≠ afterMachine 12 := by decide

private def numericView (m : WordStore) := (m 0, m 4, m 6, m 8, m 12, m 2)

/-- Full numeric observation vectors for both wrong algorithms, preserving the
same order as the correct fixture rather than reporting only a selected word. -/
theorem wrong_ordered_vectors :
    (numericView afterMachine, numericView (writeWord afterMachine 6 zero),
      numericView (writeWord (writeWord afterMachine 8 zero) 12 zero)) =
    ((zero, zero, one, one, one, seven), (zero, zero, zero, one, one, seven),
      (zero, zero, one, zero, zero, seven)) := rfl

theorem no_global_hash_injectivity : hash (.entry 10 99) = hash (.entry 11 99) ∧
    (Solidity.Storage.Pre.entry 10 99) ≠ .entry 11 99 := by constructor; rfl; decide

/-- Constant hashing would hit the root, so it cannot satisfy this SAME run's
existing region premise. No new cryptographic exclusion is added. -/
theorem bad_hash_rejected :
    ¬ FiniteRun 32 4 1 (fun _ => 0) preimages (ClearDemands.coveredLocations old queries base) := by
  intro bad
  have misses := bad.regions.2 (.data 0) (by decide) 0 (by decide)
  exact misses (by decide)

/-- A malformed retained read stays NONE, although its unbounded slot formula
aliases a real mapping word. The owner bound fails exactly at that offset. -/
theorem malformed_alias_control :
    old.observe (wordPath index2) = none ∧ (recursiveClear old).observe (wordPath index2) = none ∧
    (pathLoc (wordPath index2) base).word 32 hash = (pathLoc (memoPath index0) base).word 32 hash ∧
    pathLoc (wordPath index2) base ≠ pathLoc (memoPath index0) base ∧
    ¬ (pathLoc (wordPath index2) base).Bounded 4 1 := by
  refine ⟨rfl, rfl, rfl, by decide, ?_⟩
  change ¬ ((0 : Nat) < 1 ∧ 4 < 4)
  decide

private def empty : Value graph (.array (.node z)) :=
  .array ⟨2, by decide⟩ ⟨0, by decide⟩ (by decide) (fun _ => .present item)
private def emptyMachine : WordStore := writeWord machine 0 zero
private noncomputable def emptyAfter : WordStore := ClearDemands.numericClear (N := 32) empty base hash emptyMachine

/-- Delete an empty-but-retained array: only its already-zero header is a
clear demand. BOTH older words/mappings and outside sentinel remain. -/
theorem empty_retained_ordered :
    (ClearDemands.demands empty, empty.length.val, empty.extent.val,
      empty.observe (wordPath index0), empty.observe (wordPath index1),
      empty.observe (memoPath index0), empty.observe (memoPath index1),
      empty.observe (wordPath index2),
      (recursiveClear empty).length.val, (recursiveClear empty).extent.val,
      (recursiveClear empty).observe (wordPath index0), (recursiveClear empty).observe (wordPath index1),
      (recursiveClear empty).observe (memoPath index0), (recursiveClear empty).observe (memoPath index1),
      (recursiveClear empty).observe (wordPath index2), numericView emptyMachine, numericView emptyAfter,
      empty.observe (memoPath index0 true), empty.observe (memoPath index1 true),
      (recursiveClear empty).observe (memoPath index0 true), (recursiveClear empty).observe (memoPath index1 true),
      emptyMachine 16, emptyMachine 20, emptyAfter 16, emptyAfter 20) =
    ([.length .nil], 0, 2, some true, some true, some true, some true, none,
      0, 2, some true, some true, some true, some true, none,
      (zero, one, one, one, one, seven), (zero, one, one, one, one, seven),
      some true, some true, some true, some true, one, one, one, one) := rfl

private def absentSlots (i : Fin 2) : Slot graph (.node z) :=
  if i.val = 0 then .absent else .present item
private def absent : Value graph (.array (.node z)) :=
  .array ⟨2, by decide⟩ ⟨1, by decide⟩ (by decide) absentSlots
private def absentMachine : WordStore := writeWord (writeWord (writeWord machine 4 zero) 8 zero) 16 zero
private noncomputable def absentAfter : WordStore :=
  ClearDemands.numericClear (N := 32) absent base hash absentMachine

/-- Absent LIVE slots remain absent but are logically readable via defaults.
The older present slot/maps remain visible; only header is generated. -/
theorem absent_slot_ordered :
    (ClearDemands.demands absent, absent.length.val, absent.extent.val,
      absent.observe (wordPath index0), absent.observe (wordPath index1),
      absent.observe (memoPath index0), absent.observe (memoPath index1),
      absent.observe (wordPath index2),
      ((wordPath index0).readLive Value.dflt absent).map Value.head,
      (recursiveClear absent).length.val, (recursiveClear absent).extent.val,
      (recursiveClear absent).observe (wordPath index0), (recursiveClear absent).observe (wordPath index1),
      (recursiveClear absent).observe (memoPath index0), (recursiveClear absent).observe (memoPath index1),
      (recursiveClear absent).observe (wordPath index2),
      ((wordPath index0).readLive Value.dflt (recursiveClear absent)).map Value.head,
      numericView absentMachine, numericView absentAfter,
      absent.observe (memoPath index0 true), absent.observe (memoPath index1 true),
      (recursiveClear absent).observe (memoPath index0 true), (recursiveClear absent).observe (memoPath index1 true),
      absentMachine 16, absentMachine 20, absentAfter 16, absentAfter 20) =
    ([.length .nil], 1, 2, some false, some true, some false, some true, none, some false,
      0, 2, some false, some true, some false, some true, none, none,
      (one, zero, one, zero, one, seven), (zero, zero, one, zero, one, seven),
      some false, some true, some false, some true, zero, one, zero, one) := rfl

theorem absent_remains_absent :
    absent.slots ⟨0, by decide⟩ = .absent ∧ (recursiveClear absent).slots ⟨0, by decide⟩ = .absent :=
  ⟨rfl, rfl⟩

/-- Garbage at a defaulted missing slot is rejected by the OLD owner relation;
absence alone never supplies a fact about a numeric storage cell. -/
theorem bad_absent_representation : ¬ Represented absent [.word (wordPath index0)] base store := by
  intro bad
  have impossible := (bad (.word (wordPath index0)) List.mem_cons_self).2.2 zero rfl
  change one = zero at impossible
  exact (by decide : one ≠ zero) impossible

private def nestedType : Nat → TypeGraph.Ty 1
  | 0 => .node z
  | depth + 1 => .array (nestedType depth)

/-- Independently varying runtime lengths at every finite nested level. -/
private def nestedValue : (depth : Nat) → (Nat → Index) → Value graph (nestedType depth)
  | 0, _ => item
  | depth + 1, lengths => .array
      ⟨(lengths depth).val + 1, by have h := (lengths depth).isLt; omega⟩
      (lengths depth) (Nat.le_succ _)
      (fun _ => .present (nestedValue depth lengths))

private def nestedPath : (depth : Nat) → TypeGraph.Path graph (nestedType depth) (.prim .bool)
  | 0 => .cons (.field .here) .nil
  | depth + 1 => .cons (.index index0) (nestedPath depth)

private theorem nested_found (depth : Nat) (lengths : Nat → Index) :
    (nestedValue (depth + 1) lengths).find (.cons (.index index0) .nil) =
      some (nestedValue depth lengths) := by
  simp only [nestedValue, Value.find, Path.read, Step.get, index0, ix,
    dif_pos (Nat.zero_lt_succ (lengths depth).val), Slot.getD, Option.bind_some]

private theorem nested_old_word (depth : Nat) (lengths : Nat → Index) :
    (nestedValue depth lengths).observe (nestedPath depth) = some true := by
  induction depth with
  | zero => rfl
  | succ depth ih =>
    change (nestedValue (depth + 1) lengths).observe
      ((TypeGraph.Path.cons (.index index0) .nil).append (nestedPath depth)) = some true
    rw [Value.observe_append, nested_found, Option.bind_some]
    exact ih

private theorem nested_member (depth : Nat) (lengths : Nat → Index)
    (positive : ∀ k < depth, 0 < (lengths k).val) :
    Query.word (nestedPath depth) ∈ ClearDemands.demands (nestedValue depth lengths) := by
  induction depth with
  | zero => exact List.mem_cons_self
  | succ depth ih =>
    have live : 0 < (lengths depth).val := positive depth (Nat.lt_succ_self _)
    have child := ih (fun k bound => positive k (Nat.lt_trans bound (Nat.lt_succ_self _)))
    change Query.word (nestedPath (depth + 1)) ∈
      (List.finRange (lengths depth).val).flatMap (fun i =>
        (ClearDemands.demands (nestedValue depth lengths)).map
          (Query.prefix (.cons (.index ⟨i.val, Nat.lt_trans i.isLt (lengths depth).isLt⟩) .nil))) ++
      [.length .nil]
    apply List.mem_append.mpr
    apply Or.inl
    exact List.mem_flatMap.mpr ⟨⟨0, live⟩, List.mem_ofFn.mpr ⟨⟨0, live⟩, rfl⟩,
      List.mem_map.mpr ⟨.word (nestedPath depth), child, rfl⟩⟩

private theorem nested_new_word (depth : Nat) (lengths : Nat → Index)
    (positive : ∀ k < depth, 0 < (lengths k).val) :
    (recursiveClear (nestedValue depth lengths)).observe (nestedPath depth) = some false := by
  have cleared := ClearDemands.listed_zero (nestedValue depth lengths) (.word (nestedPath depth))
    (nested_member depth lengths positive)
  change ((recursiveClear (nestedValue depth lengths)).observe (nestedPath depth)).map
    (PrimTy.toWord (p := .bool)) = some zero at cleared
  cases observed : (recursiveClear (nestedValue depth lengths)).observe (nestedPath depth) with
  | none => simp only [observed, Option.map_none] at cleared; cases cleared
  | some bit =>
    cases bit with
    | false => rfl
    | true =>
      simp only [observed, Option.map_some] at cleared
      exact False.elim ((by decide : one ≠ zero) (Option.some.inj cleared))

private def nestedMemoStem : (depth : Nat) →
    TypeGraph.Path graph (nestedType depth) (.mapping .bool (.prim .bool))
  | 0 => .cons (.field (.there .here)) .nil
  | depth + 1 => .cons (.index index0) (nestedMemoStem depth)
private def nestedMemoPath (depth : Nat) (key : Bool) :
    TypeGraph.Path graph (nestedType depth) (.prim .bool) :=
  (nestedMemoStem depth).append (.cons (.key key) .nil)
private theorem nested_old_memo (depth : Nat) (lengths : Nat → Index) (key : Bool) :
    (nestedValue depth lengths).observe (nestedMemoPath depth key) = some true := by
  induction depth with
  | zero => rfl
  | succ depth ih =>
    change (nestedValue (depth + 1) lengths).observe
      ((TypeGraph.Path.cons (.index index0) .nil).append (nestedMemoPath depth key)) = some true
    rw [Value.observe_append, nested_found, Option.bind_some]
    exact ih
private theorem nested_new_memo (depth : Nat) (lengths : Nat → Index) (key : Bool) :
    (recursiveClear (nestedValue depth lengths)).observe (nestedMemoPath depth key) = some true := by
  calc
    _ = (nestedValue depth lengths).observe (nestedMemoPath depth key) := by
      simp only [nestedMemoPath, Value.observe_append, recursiveClear_mapping_read]
    _ = some true := nested_old_memo depth lengths key

/-- Inhabited witnesses at EVERY finite recursive constructor depth and arbitrary
independently varying nonempty inner/outer lengths. Positivity is required only
for this changed-read witness; the algorithm and footprint theorem handle zero.
The complete ordered selected observations include raw and normalized reads. -/
theorem all_depth_ordered (depth : Nat) (lengths : Nat → Index)
    (positive : ∀ k < depth, 0 < (lengths k).val) :
    ((nestedValue depth lengths).observe (nestedPath depth),
      (recursiveClear (nestedValue depth lengths)).observe (nestedPath depth),
      (Query.word (nestedPath depth)).read (nestedValue depth lengths),
      (Query.word (nestedPath depth)).read (recursiveClear (nestedValue depth lengths)),
      (nestedValue depth lengths).observe (nestedMemoPath depth false),
      (nestedValue depth lengths).observe (nestedMemoPath depth true),
      (recursiveClear (nestedValue depth lengths)).observe (nestedMemoPath depth false),
      (recursiveClear (nestedValue depth lengths)).observe (nestedMemoPath depth true)) =
    (some true, some false, some one, some zero, some true, some true, some true, some true) := by
  simp only [Query.read, nested_old_word, nested_new_word depth lengths positive,
    nested_old_memo, nested_new_memo, Option.map_some]
  rfl

private def size2 : FixedSize := ⟨2, by decide, by decide⟩
private abbrev FixedPair := Value graph (.fixed (.array (.node z)) size2)
private def fixedSlots (i : Fin 2) : Slot graph (.array (.node z)) :=
  if i.val = 0 then .present old else .present empty
private def fixedPair : FixedPair := .fixed fixedSlots
private def fixedWord (outer inner : Index) : TypeGraph.Path graph (.fixed (.array (.node z)) size2) (.prim .bool) :=
  .cons (.fixed outer) (wordPath inner)
private def fixedMemo (outer inner : Index) (key : Bool := false) : TypeGraph.Path graph (.fixed (.array (.node z)) size2) (.prim .bool) :=
  .cons (.fixed outer) (memoPath inner key)
private def fixedHeader (outer : Index) : TypeGraph.Path graph (.fixed (.array (.node z)) size2) (.array (.node z)) :=
  .cons (.fixed outer) .nil
private def headerView {A E : TypeGraph.Ty 1} (value : Value graph A)
    (path : TypeGraph.Path graph A (.array E)) : Option (Nat × Nat) :=
  (value.observe path).map (fun h => (h.1.val, h.2.val))

/-- Fixed/node/array/mapping combination with DIFFERENT runtime live lengths.
Only first array's LIVE payload is cleared; both headers reset; all shadows,
both keys of four mappings, and malformed failures retain exact observations. -/
theorem fixed_combination_ordered :
    (ClearDemands.demands fixedPair,
      headerView fixedPair (fixedHeader index0), headerView fixedPair (fixedHeader index1),
      fixedPair.observe (fixedWord index0 index0), fixedPair.observe (fixedWord index0 index1),
      fixedPair.observe (fixedWord index1 index0), fixedPair.observe (fixedWord index1 index1),
      fixedPair.observe (fixedMemo index0 index0), fixedPair.observe (fixedMemo index0 index1),
      fixedPair.observe (fixedMemo index1 index0), fixedPair.observe (fixedMemo index1 index1),
      fixedPair.observe (fixedWord index2 index0), fixedPair.observe (fixedWord index0 index2),
      ((fixedWord index0 index0).readLive Value.dflt fixedPair).map Value.head,
      ((fixedWord index1 index0).readLive Value.dflt fixedPair).map Value.head,
      headerView (recursiveClear fixedPair) (fixedHeader index0), headerView (recursiveClear fixedPair) (fixedHeader index1),
      (recursiveClear fixedPair).observe (fixedWord index0 index0), (recursiveClear fixedPair).observe (fixedWord index0 index1),
      (recursiveClear fixedPair).observe (fixedWord index1 index0), (recursiveClear fixedPair).observe (fixedWord index1 index1),
      (recursiveClear fixedPair).observe (fixedMemo index0 index0), (recursiveClear fixedPair).observe (fixedMemo index0 index1),
      (recursiveClear fixedPair).observe (fixedMemo index1 index0), (recursiveClear fixedPair).observe (fixedMemo index1 index1),
      (recursiveClear fixedPair).observe (fixedWord index2 index0), (recursiveClear fixedPair).observe (fixedWord index0 index2),
      ((fixedWord index0 index0).readLive Value.dflt (recursiveClear fixedPair)).map Value.head,
      ((fixedWord index1 index0).readLive Value.dflt (recursiveClear fixedPair)).map Value.head,
      fixedPair.observe (fixedMemo index0 index0 true), fixedPair.observe (fixedMemo index0 index1 true),
      fixedPair.observe (fixedMemo index1 index0 true), fixedPair.observe (fixedMemo index1 index1 true),
      (recursiveClear fixedPair).observe (fixedMemo index0 index0 true), (recursiveClear fixedPair).observe (fixedMemo index0 index1 true),
      (recursiveClear fixedPair).observe (fixedMemo index1 index0 true), (recursiveClear fixedPair).observe (fixedMemo index1 index1 true)) =
    ([.word (fixedWord index0 index0), .length (fixedHeader index0), .length (fixedHeader index1)],
      some (1, 2), some (0, 2), some true, some true, some true, some true,
      some true, some true, some true, some true, none, none, some true, none,
      some (0, 2), some (0, 2), some false, some true, some true, some true,
      some true, some true, some true, some true, none, none, none, none,
      some true, some true, some true, some true, some true, some true, some true, some true) := rfl

private def numericViewAll (m : WordStore) := (numericView m, m 16, m 20)

/-- Both Bool keys at BOTH mappings appear in every complete numeric vector.
The TRUE-only erasure would evade the old false-only observations and is
now explicitly discriminated. -/
theorem complete_wrong_vectors :
    (numericViewAll afterMachine,
      numericViewAll (writeWord afterMachine 6 zero),
      numericViewAll (writeWord (writeWord afterMachine 8 zero) 12 zero),
      numericViewAll (writeWord (writeWord afterMachine 16 zero) 20 zero)) =
    (((zero, zero, one, one, one, seven), one, one),
      ((zero, zero, zero, one, one, seven), one, one),
      ((zero, zero, one, zero, zero, seven), one, one),
      ((zero, zero, one, one, one, seven), zero, zero)) := rfl

theorem wrong_true_mapping_negative :
    (writeWord afterMachine 16 zero) 16 ≠ afterMachine 16 ∧
    (writeWord afterMachine 20 zero) 20 ≠ afterMachine 20 := by decide

private theorem nested_shadow_found (depth : Nat) (lengths : Nat → Index) :
    (nestedValue (depth + 1) lengths).find (.cons (.index (lengths depth)) .nil) =
      some (nestedValue depth lengths) := by
  simp only [nestedValue, Value.find, Path.read, Step.get,
    dif_pos (Nat.lt_succ_self (lengths depth).val), Slot.getD, Option.bind_some]

/-- Every finite outer level includes an older retained shadow, with arbitrary
runtime length. Its payload remains TRUE, its live read remains NONE, and clear
preserves extent while resetting only the live header. -/
theorem all_depth_header_shadow_ordered (depth : Nat) (lengths : Nat → Index) :
    (headerView (nestedValue (depth + 1) lengths) .nil,
      headerView (recursiveClear (nestedValue (depth + 1) lengths)) .nil,
      (nestedValue (depth + 1) lengths).observe (.cons (.index (lengths depth)) (nestedPath depth)),
      (recursiveClear (nestedValue (depth + 1) lengths)).observe (.cons (.index (lengths depth)) (nestedPath depth)),
      (TypeGraph.Path.cons (.index (lengths depth)) (nestedPath depth)).readLive Value.dflt
        (nestedValue (depth + 1) lengths) |>.map Value.head,
      (TypeGraph.Path.cons (.index (lengths depth)) (nestedPath depth)).readLive Value.dflt
        (recursiveClear (nestedValue (depth + 1) lengths)) |>.map Value.head) =
    (some ((lengths depth).val, (lengths depth).val + 1), some (0, (lengths depth).val + 1),
      some true, some true, none, none) := by
  have oldWord : (nestedValue (depth + 1) lengths).observe
      (.cons (.index (lengths depth)) (nestedPath depth)) = some true := by
    change (nestedValue (depth + 1) lengths).observe
      ((TypeGraph.Path.cons (.index (lengths depth)) .nil).append (nestedPath depth)) = some true
    rw [Value.observe_append, nested_shadow_found, Option.bind_some]
    exact nested_old_word depth lengths
  have frame : (recursiveClear (nestedValue (depth + 1) lengths)).find
      (.cons (.index (lengths depth)) .nil) =
      (nestedValue (depth + 1) lengths).find (.cons (.index (lengths depth)) .nil) :=
    ClearDemands.shadow_find_frame _ _ _ _ (lengths depth) (Nat.le_refl _)
  have newWord : (recursiveClear (nestedValue (depth + 1) lengths)).observe
      (.cons (.index (lengths depth)) (nestedPath depth)) = some true := by
    change (recursiveClear (nestedValue (depth + 1) lengths)).observe
      ((TypeGraph.Path.cons (.index (lengths depth)) .nil).append (nestedPath depth)) = some true
    rw [Value.observe_append, frame, nested_shadow_found, Option.bind_some]
    exact nested_old_word depth lengths
  rw [oldWord, newWord]
  simp only [nestedValue, recursiveClear, headerView, Value.observe, Value.find, Path.read,
    Option.map_some, Value.head, Path.readLive, Step.getLive,
    Nat.lt_irrefl, Nat.not_lt_zero, if_false, Option.bind_none, Option.map_none]

/-- info: 'Solidity.Backend.StorageOps.ClearDemandControls.exact_demands' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms exact_demands
/-- info: 'Solidity.Backend.StorageOps.ClearDemandControls.exact_locations' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms exact_locations
/-- info: 'Solidity.Backend.StorageOps.ClearDemandControls.represented_numeric_clear' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms represented_numeric_clear
/-- info: 'Solidity.Backend.StorageOps.ClearDemandControls.ordered_observations' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms ordered_observations
/-- info: 'Solidity.Backend.StorageOps.ClearDemandControls.wrong_shadow_negative' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms wrong_shadow_negative
/-- info: 'Solidity.Backend.StorageOps.ClearDemandControls.wrong_mapping_negative' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms wrong_mapping_negative
/-- info: 'Solidity.Backend.StorageOps.ClearDemandControls.wrong_ordered_vectors' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms wrong_ordered_vectors
/-- info: 'Solidity.Backend.StorageOps.ClearDemandControls.no_global_hash_injectivity' does not depend on any axioms -/
#guard_msgs in #print axioms no_global_hash_injectivity
/-- info: 'Solidity.Backend.StorageOps.ClearDemandControls.bad_hash_rejected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms bad_hash_rejected
/-- info: 'Solidity.Backend.StorageOps.ClearDemandControls.malformed_alias_control' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms malformed_alias_control
/-- info: 'Solidity.Backend.StorageOps.ClearDemandControls.empty_retained_ordered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms empty_retained_ordered
/-- info: 'Solidity.Backend.StorageOps.ClearDemandControls.absent_slot_ordered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms absent_slot_ordered
/-- info: 'Solidity.Backend.StorageOps.ClearDemandControls.absent_remains_absent' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms absent_remains_absent
/-- info: 'Solidity.Backend.StorageOps.ClearDemandControls.bad_absent_representation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms bad_absent_representation
/-- info: 'Solidity.Backend.StorageOps.ClearDemandControls.all_depth_ordered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms all_depth_ordered
/-- info: 'Solidity.Backend.StorageOps.ClearDemandControls.fixed_combination_ordered' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms fixed_combination_ordered
/-- info: 'Solidity.Backend.StorageOps.ClearDemandControls.complete_wrong_vectors' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms complete_wrong_vectors
/-- info: 'Solidity.Backend.StorageOps.ClearDemandControls.wrong_true_mapping_negative' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms wrong_true_mapping_negative
/-- info: 'Solidity.Backend.StorageOps.ClearDemandControls.all_depth_header_shadow_ordered' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in #print axioms all_depth_header_shadow_ordered

private def alternating (k : Nat) : Index := if k % 2 = 0 then index1 else index2

/-- Explicit inhabited changed-read family at every finite depth, with actual
alternating live lengths1/2, both mapping keys and all ordered word reads. -/
theorem alternating_depth_nontrivial (depth : Nat) :
    ((nestedValue depth alternating).observe (nestedPath depth),
      (recursiveClear (nestedValue depth alternating)).observe (nestedPath depth),
      (Query.word (nestedPath depth)).read (nestedValue depth alternating),
      (Query.word (nestedPath depth)).read (recursiveClear (nestedValue depth alternating)),
      (nestedValue depth alternating).observe (nestedMemoPath depth false),
      (nestedValue depth alternating).observe (nestedMemoPath depth true),
      (recursiveClear (nestedValue depth alternating)).observe (nestedMemoPath depth false),
      (recursiveClear (nestedValue depth alternating)).observe (nestedMemoPath depth true)) =
    (some true, some false, some one, some zero, some true, some true, some true, some true) := by
  apply all_depth_ordered
  intro k _
  unfold alternating
  split <;> decide

/-- info: 'Solidity.Backend.StorageOps.ClearDemandControls.alternating_depth_nontrivial' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms alternating_depth_nontrivial

end Solidity.Backend.StorageOps.ClearDemandControls
