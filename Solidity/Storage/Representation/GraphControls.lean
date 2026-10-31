import Solidity.Storage.Representation.GraphCompatibility

/-! Recursive graph witnesses and controls. Depth parameters below are
universally quantified, not a fixed supported-depth bound. -/
namespace Solidity.Storage.Representation.Graph.Controls
private def idx : Fin 1 := ⟨0, by decide⟩
private def zero : PrimTy.uint.Denote := ⟨0, by decide⟩
private def nine : PrimTy.uint.Denote := ⟨9, by decide⟩
private def fields : List (Name × TypeGraph.Ty 1) :=
  [("value", .prim .uint), ("next", .mapping .bool (.node idx))]

def schema : TypeGraph.Schema 1 where
  origin := "storage-representation-recursive-control"
  declId := fun _ => 27
  declId_injective := by intro i j _; apply Fin.ext; omega
  name := fun _ => "Node"
  fields := fun _ => fields
  rank := fun _ => 1
  nonempty := fun _ => rfl
  distinct := fun _ => rfl
  guarded := by
    intro i f member
    simp only [fields, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> exact Nat.zero_lt_succ 0

private def scalar : TypeGraph.Path schema (.node idx) (.prim .uint) := .cons (.field .here) .nil
private def next : TypeGraph.Path schema (.node idx) (.node idx) :=
  .cons (.field (.there .here)) (.cons (.key false) .nil)

def deep : Nat → TypeGraph.Path schema (.node idx) (.prim .uint)
  | 0 => scalar
  | n + 1 => next.append (deep n)

def other (n : Nat) : TypeGraph.Path schema (.node idx) (.prim .uint) :=
  .cons (.field (.there .here)) (.cons (.key true) (deep n))

def empty : TypeGraph.Value schema (.node idx) := TypeGraph.Value.dflt _

theorem inline_node_size : inlineSize schema (.node idx) = 2 := by
  rw [inlineSize_node]
  rfl

/-- All finite recursive mapping depths have successful independent source reads. -/
theorem empty_find_deep (n : Nat) : empty.find (deep n) = some (.prim zero) := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih

theorem empty_observe_deep (n : Nat) : empty.observe (deep n) = some zero := by
  unfold TypeGraph.Value.observe
  rw [empty_find_deep]
  rfl

theorem deep_supported (n : Nat) : PathSupported (deep n) := by
  induction n with
  | zero => exact ⟨True.intro, True.intro⟩
  | succ n ih => exact ⟨True.intro, ⟨True.intro, ih⟩⟩

/-- Every finite recursive depth has an inhabited represented observation. -/
theorem empty_represented_deep (n : Nat) :
    Represented empty [.word (deep n)] (.root 0) (fun _ => zero) := by
  have base : Represented (TypeGraph.Value.prim (G := schema) zero) [.word .nil]
      (pathLoc (deep n) (.root 0)) (fun _ => zero) :=
    represented_scalar zero (.scalar zero _ _ rfl)
  have composed : Represented empty
      ([Query.word (G := schema) (.nil : TypeGraph.Path schema (.prim .uint) (.prim .uint))].map
        (Query.prefix (deep n))) (.root 0) (fun _ => zero) :=
    Represented.prefix (deep n) (empty_find_deep n) (deep_supported n) base
  simpa only [List.map_cons, List.map_nil, Query.prefix, path_append_nil] using composed

/-- The same arbitrary-depth witness transports through any covered finite run. -/
theorem empty_numeric_deep (n : Nat) {N L R : Nat} {H : Pre → Nat} {P : List Pre}
    {xs : List Loc} (run : FiniteRun N L R H P xs)
    (covered : pathLoc (deep n) (.root 0) ∈ xs) :
    ∃ m : WordStore, Transport N H xs (fun _ => zero) m ∧
      m (Loc.word N H (pathLoc (deep n) (.root 0))) = zero := by
  obtain ⟨m, transported, _⟩ := transport_exists run (fun _ => zero) (fun _ => zero)
  refine ⟨m, transported, ?_⟩
  apply (empty_represented_deep n).numeric transported (.word (deep n)) (by simp only [List.mem_singleton]) covered zero
  simp only [Query.read, empty_observe_deep, Option.map_some]
  rfl

theorem empty_find_other (n : Nat) : empty.find (other n) = some (.prim zero) :=
  empty_find_deep n

theorem other_supported (n : Nat) : PathSupported (other n) :=
  ⟨True.intro, ⟨True.intro, deep_supported n⟩⟩

theorem empty_represented_other (n : Nat) :
    Represented empty [.word (other n)] (.root 0) (fun _ => zero) := by
  have base : Represented (TypeGraph.Value.prim (G := schema) zero) [.word .nil]
      (pathLoc (other n) (.root 0)) (fun _ => zero) :=
    represented_scalar zero (.scalar zero _ _ rfl)
  simpa only [List.map_cons, List.map_nil, Query.prefix, path_append_nil] using
    (Represented.prefix (other n) (empty_find_other n) (other_supported n) base)

theorem deep_other_apart (n : Nat) : Apart schema (deep (n + 1)) (other n) :=
  .under (TypeGraph.Step.field (G := schema) (i := idx) (.there .here))
    (.fork (StepApart.key (K := .bool) false true Bool.false_ne_true) (deep n) (deep n))

private def changed : TypeGraph.Value schema (.node idx) :=
  (empty.save (deep 3) (.prim nine)).getD empty

theorem saved : empty.save (deep 3) (.prim nine) = some changed := rfl

theorem observed_written : changed.observe (deep 3) = some nine := by
  unfold TypeGraph.Value.observe
  rw [TypeGraph.Value.find_save empty changed (deep 3) (.prim nine) saved]
  rfl

theorem observed_other : changed.observe (other 2) = some zero := by
  rw [(deep_other_apart 2).observe_save empty changed (.prim nine) saved]
  unfold TypeGraph.Value.observe
  rw [empty_find_other]
  rfl

theorem nonalias : pathLoc (other 2) (.root 0) ≠ pathLoc (deep 3) (.root 0) := by decide

theorem represented_written : Represented changed [.word (deep 3)] (.root 0)
    (write (fun _ => zero) (pathLoc (deep 3) (.root 0)) nine) := by
  have base : Represented (TypeGraph.Value.prim (G := schema) nine) [.word .nil]
      (pathLoc (deep 3) (.root 0))
      (write (fun _ => zero) (pathLoc (deep 3) (.root 0)) nine) :=
    represented_scalar nine (.scalar nine _ _ (write_same _ _ _))
  simpa only [List.map_cons, List.map_nil, Query.prefix, path_append_nil] using
    (Represented.prefix (deep 3)
      (TypeGraph.Value.find_save empty changed (deep 3) (.prim nine) saved) (deep_supported 3) base)

theorem represented_other : Represented changed [.word (other 2)] (.root 0)
    (write (fun _ => zero) (pathLoc (deep 3) (.root 0)) nine) := by
  apply (empty_represented_other 2).write_frame (deep 3) (.prim nine) saved nine
  · intro q member
    simp only [List.mem_singleton] at member
    subst q
    exact deep_other_apart 2
  · intro q member
    simp only [List.mem_singleton] at member
    subst q
    exact nonalias

private def one : Semantics.Word := ⟨1, by decide⟩
private def i0 : TypeGraph.Index := ⟨0, by decide⟩
private def i1 : TypeGraph.Index := ⟨1, by decide⟩
private def smallArray : TypeGraph.Value schema (.array (.prim .uint)) :=
  .array ⟨1, by decide⟩ ⟨1, by decide⟩ (by decide) (fun _ => .absent)
private def oversized : TypeGraph.Value schema (.array (.prim .uint)) :=
  .array ⟨lmax + 1, by decide⟩ ⟨0, by decide⟩ (Nat.zero_le _) (fun _ => .absent)

theorem graph_header_represented :
    Represented smallArray [.length .nil] (.root 0) (fun _ => one) := by
  intro q member
  simp only [List.mem_singleton] at member
  subst q
  refine ⟨True.intro, ?_, ?_⟩
  · change 1 ≤ lmax ∧ 1 ≤ lmax
    exact ⟨by decide, by decide⟩
  · intro value observed
    change some one = some value at observed
    exact Option.some.inj observed

theorem oversized_header_rejected (w : Store) :
    ¬ Represented oversized [.length .nil] (.root 0) w := by
  intro h
  have bounds : (Query.length .nil).compatible oversized :=
    (h (.length .nil) (by simp only [List.mem_singleton])).2.1
  change 0 ≤ lmax ∧ lmax + 1 ≤ lmax at bounds
  omega

/-- The graph relation is deliberately finite/query-local, not full ValueRep. -/
theorem oversized_word_is_query_local :
    Represented oversized [.word (.cons (.index i0) .nil)] (.root 0) (fun _ => zero) := by
  intro q member
  simp only [List.mem_singleton] at member
  subst q
  refine ⟨⟨by change (0 : Nat) < lmax; decide, True.intro⟩, True.intro, ?_⟩
  intro value observed
  change some zero = some value at observed
  exact Option.some.inj observed

theorem graph_index_bound_rejected (w : Store) :
    ¬ Represented oversized
      [.word (.cons (.index (⟨lmax, by decide⟩ : TypeGraph.Index)) .nil)] (.root 0) w := by
  intro h
  have bounds : PathSupported (TypeGraph.Path.cons (.index (E := .prim .uint) (⟨lmax, by decide⟩ : TypeGraph.Index)) .nil) :=
    (h (.word (.cons (.index (⟨lmax, by decide⟩ : TypeGraph.Index)) .nil))
    (by simp only [List.mem_singleton])).1
  change lmax < lmax ∧ True at bounds
  omega

private def arrayChanged : TypeGraph.Value schema (.array (.prim .uint)) :=
  (smallArray.save (.cons (.index i0) .nil) (.prim nine)).getD smallArray
private theorem arraySaved : smallArray.save (.cons (.index i0) .nil) (.prim nine) = some arrayChanged := rfl

/-- Ancestor header framing is distinct from divergent-query framing. -/
theorem recursive_header_frame_control :
    Represented arrayChanged [.length .nil] (.root 0)
      (write (fun _ => one) (.data (.root 0) 0) nine) :=
  Represented.header_write_frame .nil i0 .nil graph_header_represented (.prim nine)
    arraySaved nine (by decide)

theorem failed_graph_read_frame : arrayChanged.observe (.cons (.index i1) .nil) = none := by
  have apart : Apart schema (TypeGraph.Path.cons (.index (E := .prim .uint) i0) .nil) (.cons (.index (E := .prim .uint) i1) .nil) :=
    .fork (.index i0 i1 (by decide)) .nil .nil
  exact (apart.observe_save smallArray arrayChanged (.prim nine) arraySaved).trans (by rfl)

private def legacyLayout : TypeGraph.Legacy.Layout schema
    (.ref (.mapping .bool (.ref (.mapping .bool Ty.uint))))
    (.mapping .bool (.mapping .bool (.prim .uint))) := .mapping .bool (.mapping .bool (.prim .uint))
private def legacyPath : TypeGraph.Legacy.KeyPath legacyLayout (TypeGraph.Legacy.Layout.prim .uint) :=
  .key .bool false (.key .bool true .nil)
private def legacyValue : SVal (.ref (.mapping .bool (.ref (.mapping .bool Ty.uint)))) :=
  .map .nil (.map .nil (.prim zero))

theorem legacy_represented : ValueRep legacyValue (.map (.map .word)) (.root 0) (fun _ => zero) := by
  apply ValueRep.mapping
  · exact .mapping .bool (.scalar .uint)
  · intro k
    simp only [SMap.toList_nil, Semantics.lookupBy, Option.getD_none]
    apply ValueRep.mapping
    · exact .scalar .uint
    · intro q
      simp only [SMap.toList_nil, Semantics.lookupBy, Option.getD_none]
      exact .scalar zero _ _ rfl

/-- This is an extension of the existing whole legacy mapping relation. -/
theorem legacy_graph_extension :
    Represented (legacyLayout.encode legacyValue) [.word legacyPath.graph] (.root 0) (fun _ => zero) := by
  apply keypath_word_represented legacyPath legacyValue zero legacy_represented
  simp only [legacyPath, TypeGraph.Legacy.KeyPath.legacy, legacyValue,
    SVal.find_key, SVal.find_nil, SMap.toList_nil, Semantics.lookupBy]

/-- Aliasing a written path cannot preserve its old zero representation. -/
theorem written_not_framed : ¬ Represented changed [.word (deep 3)] (.root 0) (fun _ => zero) := by
  intro h
  have observed : (Query.word (deep 3)).read changed = some nine := by
    simp only [Query.read, observed_written, Option.map_some]
    rfl
  have eq : zero = nine := (h (.word (deep 3)) (by simp only [List.mem_singleton])).2.2 nine observed
  have bad : (0 : Int) = 9 := congrArg Subtype.val eq
  omega

private def hash (p : Pre) : Nat := (match p with
  | .entry k w => if k = 0 then
      (if w = 1 then 4 else if w = 5 then 8 else if w = 9 then 12 else
        if w = 17 then 20 else if w = 21 then 24 else 28)
    else if w = 1 then 16 else 28
  | .data _ => 28) % 32
private def preimages : List Pre :=
  [.entry 0 1, .entry 0 5, .entry 0 9, .entry 1 1, .entry 0 17, .entry 0 21]
private noncomputable def touched : List Loc := [pathLoc (deep 3) (.root 0), pathLoc (other 2) (.root 0)]

/-- A nonvacuous two-branch recursive prefix under the original region premise. -/
theorem recursive_run : FiniteRun 32 2 2 hash preimages touched := by
  constructor
  · intro p
    exact Nat.mod_lt _ (by decide)
  · decide
  · decide
  · decide
  · intro l member
    simp only [touched, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · change Loc.Bounded 2 2 (.hash 0 (.hash 0 (.hash 0 (.root 1) 1) 1) 0)
      simp only [Loc.Bounded]
      decide
    · change Loc.Bounded 2 2 (.hash 0 (.hash 0 (.hash 1 (.root 1) 1) 1) 0)
      simp only [Loc.Bounded]
      decide
  · intro l member p hp
    simp only [touched, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · change p ∈ [.entry 0 1, .entry 0 5, .entry 0 9] at hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl <;> decide
    · change p ∈ [.entry 1 1, .entry 0 17, .entry 0 21] at hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl <;> decide

/-- Actual recursive source save, source frame, symbolic and numeric writes agree. -/
theorem recursive_numeric_combination : ∃ m : WordStore,
    Transport 32 hash touched
      (write (fun _ => zero) (pathLoc (deep 3) (.root 0)) nine) m ∧
      m 12 = nine ∧ m 24 = zero ∧ m 31 = zero := by
  obtain ⟨m, initial, outside⟩ := transport_exists recursive_run (fun _ => zero) (fun _ => zero)
  have next : Transport 32 hash touched
      (write (fun _ => zero) (pathLoc (deep 3) (.root 0)) nine)
      (writeWord m (Loc.word 32 hash (pathLoc (deep 3) (.root 0))) nine) :=
    transport_write recursive_run initial _ (by simp only [touched, List.mem_cons, true_or]) nine
  refine ⟨_, next, ?_, ?_, ?_⟩
  · have observed : (Query.word (deep 3)).read changed = some nine := by
      simp only [Query.read, observed_written, Option.map_some]
      rfl
    exact represented_written.numeric next (.word (deep 3)) (by simp only [List.mem_singleton])
      (by change pathLoc (deep 3) (.root 0) ∈ touched; exact List.mem_cons_self) nine observed
  · have observed : (Query.word (other 2)).read changed = some zero := by
      simp only [Query.read, observed_other, Option.map_some]
      rfl
    exact represented_other.numeric next (.word (other 2)) (by simp only [List.mem_singleton])
      (by change pathLoc (other 2) (.root 0) ∈ touched; exact List.mem_cons_of_mem _ (List.mem_singleton.mpr rfl)) zero observed
  · change (if (31 : Nat) = 12 then nine else m 31) = zero
    rw [if_neg (by decide : (31 : Nat) ≠ 12)]
    exact outside 31 (by decide)

/-- info: 'Solidity.Storage.Representation.Graph.inlineSize_node' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms inlineSize_node
/-- info: 'Solidity.Storage.Representation.Graph.Apart.observe_save' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms Apart.observe_save
/-- info: 'Solidity.Storage.Representation.Graph.Represented.prefix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Represented.prefix
/-- info: 'Solidity.Storage.Representation.Graph.Represented.write_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Represented.write_frame
/-- info: 'Solidity.Storage.Representation.Graph.Controls.empty_represented_deep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms empty_represented_deep
/-- info: 'Solidity.Storage.Representation.Graph.Controls.empty_numeric_deep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms empty_numeric_deep
/-- info: 'Solidity.Storage.Representation.Graph.Controls.represented_written' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms represented_written
/-- info: 'Solidity.Storage.Representation.Graph.Controls.represented_other' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms represented_other
/-- info: 'Solidity.Storage.Representation.Graph.ancestor_observation_frame' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms ancestor_observation_frame
/-- info: 'Solidity.Storage.Representation.Graph.ancestor_header_frame' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms ancestor_header_frame
/-- info: 'Solidity.Storage.Representation.Graph.Represented.header_write_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Represented.header_write_frame
/-- info: 'Solidity.Storage.Representation.Graph.inlineSize_legacy' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms inlineSize_legacy
/-- info: 'Solidity.Storage.Representation.Graph.keypath_subvalue_rep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms keypath_subvalue_rep
/-- info: 'Solidity.Storage.Representation.Graph.keypath_word_represented' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms keypath_word_represented
/-- info: 'Solidity.Storage.Representation.Graph.keypath_header_represented' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms keypath_header_represented
/-- info: 'Solidity.Storage.Representation.Graph.Controls.recursive_numeric_combination' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms recursive_numeric_combination
end Solidity.Storage.Representation.Graph.Controls
