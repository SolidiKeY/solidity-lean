import Solidity.Backend.StorageOps.RecursiveLifecycleFacts
import Solidity.Storage.Representation.GraphRepresentation

/-! Finite demands generated from the actual recursive clear shape. This is a
finite demand realization, not an eager/emitted execution trace. Mappings and
older shadows remain opaque; absent slots retain their defaulted observations. -/
namespace Solidity.Backend.StorageOps.ClearDemands
open TypeGraph Solidity.Storage Solidity.Storage.Representation Solidity.Storage.Representation.Graph

def positions {n : Nat} : (fs : List (Name × TypeGraph.Ty n)) →
    List (Sigma (fun T => Field fs T))
  | [] => []
  | (_, T) :: rest => ⟨T, .here⟩ :: (positions rest).map
      (fun p => ⟨p.1, .there p.2⟩)

mutual
/-- Enumerate demanded primitive/header words by structural source recursion.
Dynamic levels enumerate exactly their old live runtime length. -/
def demands {n : Nat} {G : Schema n} {T : TypeGraph.Ty n}
    (value : Value G T) : List (Query G T) :=
  Value.casesOn (motive_1 := fun T _ => List (Query G T)) value
    (fun _ => [.word .nil])
    (fun {i} fields => (positions (G.fields i)).flatMap (fun p =>
      (demands (fields p.2)).map (Query.prefix (.cons (.field p.2) .nil))))
    (fun _ length bound slots =>
      (List.finRange length.val).flatMap (fun i =>
        (slotDemands (slots ⟨i.val, Nat.lt_of_lt_of_le i.isLt bound⟩)).map
          (Query.prefix (.cons (.index ⟨i.val, Nat.lt_trans i.isLt length.isLt⟩) .nil))) ++
      [.length .nil])
    (fun {_ m} slots => (List.finRange m.val).flatMap (fun i =>
      (slotDemands (slots i)).map (Query.prefix
        (.cons (.fixed ⟨i.val, Nat.lt_trans i.isLt m.property.2⟩) .nil))))
    (fun _ => [])

def slotDemands {n : Nat} {G : Schema n} {T : TypeGraph.Ty n}
    (slot : Slot G T) : List (Query G T) :=
  Slot.casesOn (motive_2 := fun T _ => List (Query G T)) slot [] (fun value => demands value)
end

private theorem demands_prim {n : Nat} {G : Schema n} {p : PrimTy} (v : p.Denote) :
    demands (Value.prim (G := G) v) = [.word .nil] := rfl

private theorem demands_node {n : Nat} {G : Schema n} {i : Fin n}
    (fields : TypeGraph.Fields G (G.fields i)) :
    demands (Value.node fields) = (positions (G.fields i)).flatMap (fun p =>
      (demands (fields p.2)).map (Query.prefix (.cons (.field p.2) .nil))) := rfl

private theorem demands_array {n : Nat} {G : Schema n} {E : TypeGraph.Ty n}
    (extent : Extent) (length : Index) (bound : length.val ≤ extent.val)
    (slots : Fin extent.val → Slot G E) :
    demands (Value.array extent length bound slots) =
      (List.finRange length.val).flatMap (fun i =>
        (slotDemands (slots ⟨i.val, Nat.lt_of_lt_of_le i.isLt bound⟩)).map
          (Query.prefix (.cons (.index ⟨i.val, Nat.lt_trans i.isLt length.isLt⟩) .nil))) ++
      [.length .nil] := rfl

private theorem demands_fixed {n : Nat} {G : Schema n} {E : TypeGraph.Ty n} {m : FixedSize}
    (slots : Fin m.val → Slot G E) :
    demands (Value.fixed slots) = (List.finRange m.val).flatMap (fun i =>
      (slotDemands (slots i)).map (Query.prefix
        (.cons (.fixed ⟨i.val, Nat.lt_trans i.isLt m.property.2⟩) .nil))) := rfl

theorem mapping_barrier {n : Nat} {G : Schema n} {K : PrimTy} {V : TypeGraph.Ty n}
    (slots : K.Denote → Slot G V) : demands (Value.mapping slots) = [] := rfl

theorem absent_demands {n : Nat} {G : Schema n} {T : TypeGraph.Ty n} :
    slotDemands (Slot.absent : Slot G T) = [] := rfl

def zero : Semantics.Word := PrimTy.toWord (p := .bool) false

theorem default_zero (p : PrimTy) : PrimTy.toWord p.dflt = zero := by
  cases p <;> rfl

mutual
/-- Every generated demand observes the actual cleared word. -/
theorem listed_zero {n : Nat} {G : Schema n} :
    {T : TypeGraph.Ty n} → (value : Value G T) →
    ∀ q ∈ demands value, q.read (recursiveClear value) = some zero
  | _, .prim v, q, member => by
    simp only [demands_prim, List.mem_singleton] at member
    subst q
    exact congrArg some (default_zero _)
  | _, .node fields, q, member => by
    simp only [demands_node, List.mem_flatMap] at member
    obtain ⟨p, _, member⟩ := member
    obtain ⟨child, inside, same⟩ := List.mem_map.mp member
    subst q
    rw [Query.read_prefix _ _ (.cons (.field p.2) .nil) child rfl]
    exact listed_zero (fields p.2) child inside
  | _, .array extent length bound slots, q, member => by
    simp only [demands_array, List.mem_append, List.mem_flatMap, List.mem_singleton] at member
    rcases member with ⟨i, _, member⟩ | same
    · obtain ⟨child, inside, same⟩ := List.mem_map.mp member
      subst q
      have live : i.val < length.val := i.isLt
      have found : (recursiveClear (.array extent length bound slots)).find
          (.cons (.index ⟨i.val, Nat.lt_trans i.isLt length.isLt⟩) .nil) =
          some ((recursiveClearSlot (slots ⟨i.val, Nat.lt_of_lt_of_le i.isLt bound⟩)).getD (Value.dflt _)) := by
        simp only [recursiveClear, Value.find, Path.read, Step.get, visit_prefix,
          dif_pos (Nat.lt_of_lt_of_le i.isLt bound), if_pos live, Option.bind_some]
      rw [Query.read_prefix _ _ _ child found]
      exact listed_slot_zero _ child inside
    · subst q
      rfl
  | _, @Value.fixed _ _ E m slots, q, member => by
    simp only [demands_fixed, List.mem_flatMap] at member
    obtain ⟨i, _, member⟩ := member
    obtain ⟨child, inside, same⟩ := List.mem_map.mp member
    subst q
    have found : (recursiveClear (Value.fixed slots)).find
        (.cons (.fixed ⟨i.val, Nat.lt_trans i.isLt m.property.2⟩) .nil) =
        some ((recursiveClearSlot (slots i)).getD (Value.dflt E)) := by
      simp only [recursiveClear, Value.find, Path.read, Step.get, dif_pos i.isLt,
        Option.bind_some]
    rw [Query.read_prefix _ _ _ child found]
    exact listed_slot_zero _ child inside
  | _, .mapping _, _, member => by cases member

theorem listed_slot_zero {n : Nat} {G : Schema n} :
    {T : TypeGraph.Ty n} → (slot : Slot G T) →
    ∀ q ∈ slotDemands slot,
      q.read ((recursiveClearSlot slot).getD (Value.dflt _)) = some zero
  | _, .absent, _, member => by cases member
  | _, .present value, q, member => listed_zero value q member
end


/-- The generated finite demand list drives actual zero writes, without reading
any graph result as a target oracle. -/
noncomputable def updates {n : Nat} {G : Schema n} {T : TypeGraph.Ty n}
    (value : Value G T) (base : Solidity.Storage.Loc) : List (Solidity.Storage.Loc × Semantics.Word) :=
  (demands value).map (fun q => (q.location base, zero))

noncomputable def numericClear {n N : Nat} {G : Schema n} {T : TypeGraph.Ty n}
    (value : Value G T) (base : Solidity.Storage.Loc) (hash : Solidity.Storage.Pre → Nat)
    (machine : WordStore) : WordStore :=
  (updates value base).foldl (fun store op => writeWord store (op.1.word N hash) op.2) machine

/-- Owner transport applies to the operation-GENERATED demand list. It does not
supply support/bounds/coverage for a particular compiler invocation. -/
theorem numeric_transport {n N L R : Nat} {G : Schema n} {T : TypeGraph.Ty n}
    {hash : Solidity.Storage.Pre → Nat} {P : List Solidity.Storage.Pre}
    {locations : List Solidity.Storage.Loc} (run : FiniteRun N L R hash P locations)
    (value : Value G T) (base : Solidity.Storage.Loc) (store : Store) (machine : WordStore)
    (initial : Transport N hash locations store machine)
    (covered : ∀ q ∈ demands value, q.location base ∈ locations) :
    Transport N hash locations
      ((updates value base).foldl (fun store op => write store op.1 op.2) store)
      (numericClear (N := N) value base hash machine) := by
  apply transport_sequence run initial (updates value base)
  intro op member
  obtain ⟨q, inside, same⟩ := List.mem_map.mp member
  subst op
  exact covered q inside

/-- Numeric frames are actual outside-address frames, without a global hash
injectivity premise or any claim about unrepresented graph observations. -/
theorem numeric_outside {n N : Nat} {G : Schema n} {T : TypeGraph.Ty n}
    (value : Value G T) (base : Solidity.Storage.Loc) (hash : Solidity.Storage.Pre → Nat)
    (machine : WordStore) (address : Nat)
    (outside : ∀ q ∈ demands value, address ≠ (q.location base).word N hash) :
    numericClear (N := N) value base hash machine address = machine address := by
  apply sequence_outside_frame N hash machine (updates value base) address
  intro op member
  obtain ⟨q, inside, same⟩ := List.mem_map.mp member
  subst op
  exact outside q inside


private theorem fold_zero_preserves {n : Nat} {G : Schema n} {T : TypeGraph.Ty n}
    (qs : List (Query G T)) (base location : Solidity.Storage.Loc) (store : Store)
    (already : store location = zero) :
    (qs.foldl (fun w q => write w (q.location base) zero) store) location = zero := by
  induction qs generalizing store with
  | nil => exact already
  | cons q rest ih =>
    apply ih
    by_cases same : location = q.location base
    · subst location
      exact write_same store (q.location base) zero
    · exact (write_other store (q.location base) location zero same).trans already

theorem fold_zero_member {n : Nat} {G : Schema n} {T : TypeGraph.Ty n}
    (qs : List (Query G T)) (base : Solidity.Storage.Loc) (store : Store)
    (q : Query G T) (member : q ∈ qs) :
    (qs.foldl (fun w q => write w (q.location base) zero) store) (q.location base) = zero := by
  induction qs generalizing store with
  | nil => cases member
  | cons first rest ih =>
    rcases List.mem_cons.mp member with equal | later
    · subst q
      exact fold_zero_preserves rest base (first.location base)
        (write store (first.location base) zero) (write_same store (first.location base) zero)
    · exact ih (write store (first.location base) zero) later

/-- Actual generated zero writes represent every generated cleared demand.
Support and terminal-header bounds are exact public metadata certificates;
this is not a claim that arbitrary input graphs satisfy them. -/
theorem represented_clear {n : Nat} {G : Schema n} {T : TypeGraph.Ty n}
    (value : Value G T) (base : Solidity.Storage.Loc) (store : Store)
    (supported : ∀ q ∈ demands value, q.supported)
    (compatible : ∀ q ∈ demands value, q.compatible (recursiveClear value)) :
    Represented (recursiveClear value) (demands value) base
      ((updates value base).foldl (fun w op => write w op.1 op.2) store) := by
  intro q member
  refine ⟨supported q member, compatible q member, ?_⟩
  intro word observed
  have equal : word = zero := Option.some.inj (observed.symm.trans (listed_zero value q member))
  subst word
  simp only [updates, List.foldl_map]
  exact fold_zero_member (demands value) base store q member


/-- Mapping barriers frame every typed query BELOW the mapping, including
failures/defaulted reads and nested headers; not merely its unit-valued head. -/
theorem mapping_query_frame {n : Nat} {G : Schema n} {A V : TypeGraph.Ty n} {K : PrimTy}
    (value : Value G A) (stem : TypeGraph.Path G A (.mapping K V))
    (q : Query G (.mapping K V)) :
    (q.prefix stem).read (recursiveClear value) = (q.prefix stem).read value := by
  cases q <;> simp only [Query.read, Query.prefix, Value.observe_append,
    recursiveClear_mapping_read]

/-- The numeric clear of a mapping performs NO writes. -/
theorem mapping_numeric_identity {n N : Nat} {G : Schema n} {K : PrimTy} {V : TypeGraph.Ty n}
    (slots : K.Denote → Slot G V) (base : Solidity.Storage.Loc)
    (hash : Solidity.Storage.Pre → Nat) (machine : WordStore) :
    numericClear (N := N) (Value.mapping slots) base hash machine = machine := rfl


/-- Connect ACTUAL aggregate path deletion to public represented demands plus
numeric finite transport. The target sequence is a demand realization of the
captured old shape, not emitted code that reads/loops on machine headers. -/
theorem delete_numeric {n N L R : Nat} {G : Schema n} {A T : TypeGraph.Ty n}
    {hash : Solidity.Storage.Pre → Nat} {P : List Solidity.Storage.Pre}
    {locations : List Solidity.Storage.Loc} (run : FiniteRun N L R hash P locations)
    (root result : Value G A) (stem : TypeGraph.Path G A T) (old : Value G T)
    (found : root.find stem = some old) (deleted : deleteAt root stem = some result)
    (base : Solidity.Storage.Loc) (store : Store) (machine : WordStore)
    (initial : Transport N hash locations store machine) (stemSupported : PathSupported stem)
    (supported : ∀ q ∈ demands old, q.supported)
    (compatible : ∀ q ∈ demands old, q.compatible (recursiveClear old))
    (covered : ∀ q ∈ demands old, q.location (pathLoc stem base) ∈ locations) :
    let afterStore := (updates old (pathLoc stem base)).foldl (fun w op => write w op.1 op.2) store
    let afterMachine := numericClear (N := N) old (pathLoc stem base) hash machine
    Represented result ((demands old).map (Query.prefix stem)) base afterStore ∧
    Transport N hash locations afterStore afterMachine := by
  constructor
  · exact Represented.prefix stem (deleteAt_readback root result stem old found deleted)
      stemSupported (represented_clear old (pathLoc stem base) store supported compatible)
  · exact numeric_transport run old (pathLoc stem base) store machine initial covered


theorem fold_outside {n : Nat} {G : Schema n} {T : TypeGraph.Ty n}
    (qs : List (Query G T)) (base location : Solidity.Storage.Loc) (store : Store)
    (outside : ∀ q ∈ qs, location ≠ q.location base) :
    (qs.foldl (fun w q => write w (q.location base) zero) store) location = store location := by
  induction qs generalizing store with
  | nil => rfl
  | cons first rest ih =>
    exact (ih (write store (first.location base) zero)
      (fun q member => outside q (List.mem_cons_of_mem _ member))).trans
      (write_other store (first.location base) location zero (outside first List.mem_cons_self))

theorem mapping_compatible_frame {n : Nat} {G : Schema n} {A V : TypeGraph.Ty n} {K : PrimTy}
    (value : Value G A) (stem : TypeGraph.Path G A (.mapping K V))
    (q : Query G (.mapping K V)) :
    (q.prefix stem).compatible (recursiveClear value) = (q.prefix stem).compatible value := by
  cases q <;> simp only [Query.compatible, Query.prefix, Value.observe_append,
    recursiveClear_mapping_read]

/-- Preserve initially represented mapping queries alongside the actual clear
writes. Symbolic address separation is an explicit layout certificate; it is
not inferred merely from the graph barrier. Numeric transport still needs the
owner FiniteRun over ALL demanded and framed queries. -/
theorem mapping_represented_frame {n : Nat} {G : Schema n} {A V : TypeGraph.Ty n} {K : PrimTy}
    (value : Value G A) (stem : TypeGraph.Path G A (.mapping K V))
    (qs : List (Query G (.mapping K V))) (base : Solidity.Storage.Loc) (store : Store)
    (before : Represented value (qs.map (Query.prefix stem)) base store)
    (separate : ∀ q ∈ qs, ∀ d ∈ demands value,
      (q.prefix stem).location base ≠ d.location base) :
    Represented (recursiveClear value) (qs.map (Query.prefix stem)) base
      ((updates value base).foldl (fun w op => write w op.1 op.2) store) := by
  intro query member
  obtain ⟨q, inside, same⟩ := List.mem_map.mp member
  subst query
  obtain ⟨supported, compatible, represented⟩ := before (q.prefix stem) (List.mem_map.mpr ⟨q, inside, rfl⟩)
  refine ⟨supported, ?_, ?_⟩
  · rw [mapping_compatible_frame]
    exact compatible
  · intro word observed
    rw [mapping_query_frame] at observed
    simp only [updates, List.foldl_map]
    exact (fold_outside (demands value) base ((q.prefix stem).location base) store
      (separate q inside)).trans (represented word observed)


/-- Every logical read below an older retained array slot is unchanged, even
when that slot is absent/defaulted or the requested index is out of extent. -/
theorem shadow_find_frame {n : Nat} {G : Schema n} {E : TypeGraph.Ty n}
    (extent : Extent) (length : Index) (bound : length.val ≤ extent.val)
    (slots : Fin extent.val → Slot G E) (i : Index) (shadow : length.val ≤ i.val) :
    (recursiveClear (.array extent length bound slots)).find (.cons (.index i) .nil) =
      (Value.array extent length bound slots).find (.cons (.index i) .nil) := by
  by_cases inside : i.val < extent.val
  · simp only [recursiveClear, Value.find, Path.read, Step.get, dif_pos inside, Option.bind_some]
    rw [visit_frame _ _ _ ⟨i.val, inside⟩ shadow]
  · simp only [recursiveClear, Value.find, Path.read, Step.get, dif_neg inside, Option.bind_none]

theorem shadow_query_frame {n : Nat} {G : Schema n} {E : TypeGraph.Ty n}
    (extent : Extent) (length : Index) (bound : length.val ≤ extent.val)
    (slots : Fin extent.val → Slot G E) (i : Index) (shadow : length.val ≤ i.val)
    (q : Query G E) :
    (q.prefix (.cons (.index i) .nil)).read (recursiveClear (.array extent length bound slots)) =
      (q.prefix (.cons (.index i) .nil)).read (.array extent length bound slots) := by
  cases q <;> simp only [Query.read, Query.prefix, Value.observe_append,
    shadow_find_frame extent length bound slots i shadow]

theorem shadow_compatible_frame {n : Nat} {G : Schema n} {E : TypeGraph.Ty n}
    (extent : Extent) (length : Index) (bound : length.val ≤ extent.val)
    (slots : Fin extent.val → Slot G E) (i : Index) (shadow : length.val ≤ i.val)
    (q : Query G E) :
    (q.prefix (.cons (.index i) .nil)).compatible (recursiveClear (.array extent length bound slots)) =
      (q.prefix (.cons (.index i) .nil)).compatible (.array extent length bound slots) := by
  cases q <;> simp only [Query.compatible, Query.prefix, Value.observe_append,
    shadow_find_frame extent length bound slots i shadow]

/-- Initially represented older-shadow queries survive the generated writes.
Absent/defaulted and failed reads retain their exact Option observations. -/
theorem shadow_represented_frame {n : Nat} {G : Schema n} {E : TypeGraph.Ty n}
    (extent : Extent) (length : Index) (bound : length.val ≤ extent.val)
    (slots : Fin extent.val → Slot G E) (i : Index) (shadow : length.val ≤ i.val)
    (qs : List (Query G E)) (base : Solidity.Storage.Loc) (store : Store)
    (before : Represented (.array extent length bound slots)
      (qs.map (Query.prefix (.cons (.index i) .nil))) base store)
    (separate : ∀ q ∈ qs, ∀ d ∈ demands (.array extent length bound slots),
      (q.prefix (.cons (.index i) .nil)).location base ≠ d.location base) :
    Represented (recursiveClear (.array extent length bound slots))
      (qs.map (Query.prefix (.cons (.index i) .nil))) base
      ((updates (.array extent length bound slots) base).foldl (fun w op => write w op.1 op.2) store) := by
  intro query member
  obtain ⟨q, inside, same⟩ := List.mem_map.mp member
  subst query
  obtain ⟨supported, compatible, represented⟩ := before _ (List.mem_map.mpr ⟨q, inside, rfl⟩)
  refine ⟨supported, ?_, ?_⟩
  · rw [shadow_compatible_frame extent length bound slots i shadow]
    exact compatible
  · intro word observed
    rw [shadow_query_frame extent length bound slots i shadow] at observed
    simp only [updates, List.foldl_map]
    exact (fold_outside _ base _ store (separate q inside)).trans (represented word observed)

/-- ACTUAL aggregate path deletion frames represented disjoint observations.
Query/source frames reuse the owner; separation is checked against every
GENERATED leaf/header address at the actual prefix location. -/
theorem delete_outside_frame {n : Nat} {G : Schema n} {A T : TypeGraph.Ty n}
    (root result : Value G A) (stem : TypeGraph.Path G A T) (old : Value G T)
    (found : root.find stem = some old) (deleted : deleteAt root stem = some result)
    (qs : List (Query G A)) (base : Solidity.Storage.Loc) (store : Store)
    (before : Represented root qs base store) (apart : ∀ q ∈ qs, q.apart stem)
    (separate : ∀ q ∈ qs, ∀ d ∈ demands old,
      q.location base ≠ d.location (pathLoc stem base)) :
    Represented result qs base
      ((updates old (pathLoc stem base)).foldl (fun w op => write w op.1 op.2) store) := by
  have saved := deleteAt_saved root result stem old found deleted
  intro q member
  obtain ⟨supported, compatible, represented⟩ := before q member
  refine ⟨supported, ?_, ?_⟩
  · rw [Query.compatible_frame root result stem (recursiveClear old) saved q (apart q member)]
    exact compatible
  · intro word observed
    rw [Query.read_frame root result stem (recursiveClear old) saved q (apart q member)] at observed
    simp only [updates, List.foldl_map]
    exact (fold_outside _ (pathLoc stem base) _ store (separate q member)).trans (represented word observed)

theorem positions_mem {n : Nat} {fs : List (Name × TypeGraph.Ty n)} {T : TypeGraph.Ty n}
    (p : Field fs T) : (⟨T, p⟩ : Sigma (fun U => Field fs U)) ∈ positions fs := by
  induction p with
  | here => exact List.mem_cons_self
  | there p ih =>
    exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨⟨_, p⟩, ih, rfl⟩)

theorem fin_mem (i : Fin n) : i ∈ List.finRange n :=
  List.mem_ofFn.mpr ⟨i, rfl⟩

theorem prefix_find_frame {n : Nat} {G : Schema n} {A B : TypeGraph.Ty n}
    (left right : Value G A) (stem : TypeGraph.Path G A B) (q : Query G B)
    (same : left.find stem = right.find stem) :
    (q.prefix stem).read left = (q.prefix stem).read right ∧
      (q.prefix stem).compatible left = (q.prefix stem).compatible right := by
  constructor
  · cases q <;> simp only [Query.read, Query.prefix, Value.observe_append, same]
  · cases q <;> simp only [Query.compatible, Query.prefix, Value.observe_append, same]

mutual
/-- Complete query footprint: every demand omitted by structural enumeration
retains its actual Option read and terminal-header compatibility. No assumption
of desired preservation, global hash injectivity or admission cutoff is used. -/
theorem outside_frame {n : Nat} {G : Schema n} :
    {T : TypeGraph.Ty n} → (value : Value G T) → (q : Query G T) → q ∉ demands value →
      q.read (recursiveClear value) = q.read value ∧
      q.compatible (recursiveClear value) = q.compatible value
  | _, .prim v, q, outside => by
    cases q with
    | word path =>
      cases path with
      | nil => exact False.elim (outside List.mem_cons_self)
      | cons step rest => cases step
    | length path => cases path with | cons step rest => cases step
  | _, @Value.node _ _ i fields, q, outside => by
    have childFrame : ∀ {U : TypeGraph.Ty n} (position : Field (G.fields i) U) (child : Query G U),
        child.prefix (.cons (.field position) .nil) ∉ demands (Value.node fields) →
        (child.prefix (.cons (.field position) .nil)).read (recursiveClear (.node fields)) =
          (child.prefix (.cons (.field position) .nil)).read (.node fields) ∧
        (child.prefix (.cons (.field position) .nil)).compatible (recursiveClear (.node fields)) =
          (child.prefix (.cons (.field position) .nil)).compatible (.node fields) := by
      intro U position child omitted
      have absent : child ∉ demands (fields position) := by
        intro member
        apply omitted
        rw [demands_node]
        exact List.mem_flatMap.mpr ⟨⟨U, position⟩, positions_mem position,
          List.mem_map.mpr ⟨child, member, rfl⟩⟩
      have frame := outside_frame (fields position) child absent
      constructor
      · rw [Query.read_prefix _ _ _ _ rfl, Query.read_prefix _ _ _ _ rfl]
        exact frame.1
      · rw [Query.compatible_prefix _ _ _ _ rfl, Query.compatible_prefix _ _ _ _ rfl]
        exact frame.2
    cases q with
    | word path => cases path with | cons step rest => cases step with
      | field position => exact childFrame position (.word rest) outside
    | length path => cases path with | cons step rest => cases step with
      | field position => exact childFrame position (.length rest) outside
  | _, .array extent length bound slots, q, outside => by
    have childFrame : ∀ (i : Index) (child : Query G _),
        child.prefix (.cons (.index i) .nil) ∉ demands (.array extent length bound slots) →
        (child.prefix (.cons (.index i) .nil)).read (recursiveClear (.array extent length bound slots)) =
          (child.prefix (.cons (.index i) .nil)).read (.array extent length bound slots) ∧
        (child.prefix (.cons (.index i) .nil)).compatible (recursiveClear (.array extent length bound slots)) =
          (child.prefix (.cons (.index i) .nil)).compatible (.array extent length bound slots) := by
      intro i child omitted
      by_cases live : i.val < length.val
      · have allocated : i.val < extent.val := Nat.lt_of_lt_of_le live bound
        have absent : child ∉ slotDemands (slots ⟨i.val, allocated⟩) := by
          intro member
          apply omitted
          rw [demands_array]
          exact List.mem_append.mpr (Or.inl (List.mem_flatMap.mpr
            ⟨⟨i.val, live⟩, fin_mem _, List.mem_map.mpr ⟨child, member, rfl⟩⟩))
        have frame := outside_slot_frame (slots ⟨i.val, allocated⟩) child absent
        have before : (Value.array extent length bound slots).find (.cons (.index i) .nil) =
            some ((slots ⟨i.val, allocated⟩).getD (Value.dflt _)) := by
          simp only [Value.find, Path.read, Step.get, dif_pos allocated, Option.bind_some]
        have after : (recursiveClear (.array extent length bound slots)).find (.cons (.index i) .nil) =
            some ((recursiveClearSlot (slots ⟨i.val, allocated⟩)).getD (Value.dflt _)) := by
          simp only [recursiveClear, Value.find, Path.read, Step.get, dif_pos allocated,
            Option.bind_some, visit_prefix, if_pos live]
        constructor
        · rw [Query.read_prefix _ _ _ _ after, Query.read_prefix _ _ _ _ before]
          exact frame.1
        · rw [Query.compatible_prefix _ _ _ _ after, Query.compatible_prefix _ _ _ _ before]
          exact frame.2
      · exact ⟨shadow_query_frame extent length bound slots i (Nat.le_of_not_gt live) child,
          shadow_compatible_frame extent length bound slots i (Nat.le_of_not_gt live) child⟩
    cases q with
    | word path => cases path with | cons step rest => cases step with
      | index i => exact childFrame i (.word rest) outside
    | length path =>
      cases path with
      | nil =>
        exact False.elim (outside (List.mem_append.mpr (Or.inr List.mem_cons_self)))
      | cons step rest => cases step with
        | index i => exact childFrame i (.length rest) outside
  | _, @Value.fixed _ _ E m slots, q, outside => by
    have childFrame : ∀ (i : Index) (child : Query G E),
        child.prefix (.cons (.fixed i) .nil) ∉ demands (Value.fixed slots) →
        (child.prefix (.cons (.fixed i) .nil)).read (recursiveClear (.fixed slots)) =
          (child.prefix (.cons (.fixed i) .nil)).read (.fixed slots) ∧
        (child.prefix (.cons (.fixed i) .nil)).compatible (recursiveClear (.fixed slots)) =
          (child.prefix (.cons (.fixed i) .nil)).compatible (.fixed slots) := by
      intro i child omitted
      by_cases allocated : i.val < m.val
      · have absent : child ∉ slotDemands (slots ⟨i.val, allocated⟩) := by
          intro member
          apply omitted
          rw [demands_fixed]
          exact List.mem_flatMap.mpr ⟨⟨i.val, allocated⟩, fin_mem _,
            List.mem_map.mpr ⟨child, member, rfl⟩⟩
        have frame := outside_slot_frame (slots ⟨i.val, allocated⟩) child absent
        have before : (Value.fixed slots).find (.cons (.fixed i) .nil) =
            some ((slots ⟨i.val, allocated⟩).getD (Value.dflt E)) := by
          simp only [Value.find, Path.read, Step.get, dif_pos allocated, Option.bind_some]
        have after : (recursiveClear (Value.fixed slots)).find (.cons (.fixed i) .nil) =
            some ((recursiveClearSlot (slots ⟨i.val, allocated⟩)).getD (Value.dflt E)) := by
          simp only [recursiveClear, Value.find, Path.read, Step.get, dif_pos allocated, Option.bind_some]
        constructor
        · rw [Query.read_prefix _ _ _ _ after, Query.read_prefix _ _ _ _ before]
          exact frame.1
        · rw [Query.compatible_prefix _ _ _ _ after, Query.compatible_prefix _ _ _ _ before]
          exact frame.2
      · apply prefix_find_frame _ _ (.cons (.fixed i) .nil) child
        simp only [recursiveClear, Value.find, Path.read, Step.get, dif_neg allocated, Option.bind_none]
    cases q with
    | word path => cases path with | cons step rest => cases step with
      | fixed i => exact childFrame i (.word rest) outside
    | length path => cases path with | cons step rest => cases step with
      | fixed i => exact childFrame i (.length rest) outside
  | _, .mapping slots, q, _ => ⟨rfl, rfl⟩

theorem outside_slot_frame {n : Nat} {G : Schema n} :
    {T : TypeGraph.Ty n} → (slot : Slot G T) → (q : Query G T) → q ∉ slotDemands slot →
      q.read ((recursiveClearSlot slot).getD (Value.dflt _)) = q.read (slot.getD (Value.dflt _)) ∧
      q.compatible ((recursiveClearSlot slot).getD (Value.dflt _)) = q.compatible (slot.getD (Value.dflt _))
  | _, .absent, _, _ => ⟨rfl, rfl⟩
  | _, .present value, q, outside => outside_frame value q outside
end

mutual
/-- Header compatibility of generated demands follows from the OLD represented
bounds: clear resets lengths and preserves extents. No post-state bound is
assumed as a desired preservation premise. -/
theorem listed_compatible {n : Nat} {G : Schema n} :
    {T : TypeGraph.Ty n} → (value : Value G T) →
    ∀ q ∈ demands value, q.compatible value → q.compatible (recursiveClear value)
  | _, .prim v, q, member, before => by
    simp only [demands_prim, List.mem_singleton] at member
    subst q
    exact True.intro
  | _, .node fields, q, member, before => by
    simp only [demands_node, List.mem_flatMap] at member
    obtain ⟨p, _, member⟩ := member
    obtain ⟨child, inside, same⟩ := List.mem_map.mp member
    subst q
    rw [Query.compatible_prefix _ _ _ _ rfl] at before ⊢
    exact listed_compatible (fields p.2) child inside before
  | _, .array extent length bound slots, q, member, before => by
    simp only [demands_array, List.mem_append, List.mem_flatMap, List.mem_singleton] at member
    rcases member with ⟨i, _, member⟩ | same
    · obtain ⟨child, inside, same⟩ := List.mem_map.mp member
      subst q
      have live : i.val < length.val := i.isLt
      have oldFound : (Value.array extent length bound slots).find
          (.cons (.index ⟨i.val, Nat.lt_trans i.isLt length.isLt⟩) .nil) =
          some ((slots ⟨i.val, Nat.lt_of_lt_of_le i.isLt bound⟩).getD (Value.dflt _)) := by
        simp only [Value.find, Path.read, Step.get, dif_pos (Nat.lt_of_lt_of_le i.isLt bound), Option.bind_some]
      have newFound : (recursiveClear (.array extent length bound slots)).find
          (.cons (.index ⟨i.val, Nat.lt_trans i.isLt length.isLt⟩) .nil) =
          some ((recursiveClearSlot (slots ⟨i.val, Nat.lt_of_lt_of_le i.isLt bound⟩)).getD (Value.dflt _)) := by
        simp only [recursiveClear, Value.find, Path.read, Step.get, visit_prefix,
          dif_pos (Nat.lt_of_lt_of_le i.isLt bound), if_pos live, Option.bind_some]
      rw [Query.compatible_prefix _ _ _ _ oldFound] at before
      rw [Query.compatible_prefix _ _ _ _ newFound]
      exact listed_slot_compatible _ child inside before
    · subst q
      change length.val ≤ lmax ∧ extent.val ≤ lmax at before
      change 0 ≤ lmax ∧ extent.val ≤ lmax
      exact ⟨Nat.zero_le _, before.2⟩
  | _, @Value.fixed _ _ E m slots, q, member, before => by
    simp only [demands_fixed, List.mem_flatMap] at member
    obtain ⟨i, _, member⟩ := member
    obtain ⟨child, inside, same⟩ := List.mem_map.mp member
    subst q
    have oldFound : (Value.fixed slots).find
        (.cons (.fixed ⟨i.val, Nat.lt_trans i.isLt m.property.2⟩) .nil) =
        some ((slots i).getD (Value.dflt E)) := by
      simp only [Value.find, Path.read, Step.get, dif_pos i.isLt, Option.bind_some]
    have newFound : (recursiveClear (Value.fixed slots)).find
        (.cons (.fixed ⟨i.val, Nat.lt_trans i.isLt m.property.2⟩) .nil) =
        some ((recursiveClearSlot (slots i)).getD (Value.dflt E)) := by
      simp only [recursiveClear, Value.find, Path.read, Step.get, dif_pos i.isLt, Option.bind_some]
    rw [Query.compatible_prefix _ _ _ _ oldFound] at before
    rw [Query.compatible_prefix _ _ _ _ newFound]
    exact listed_slot_compatible _ child inside before
  | _, .mapping _, _, member, _ => by cases member

theorem listed_slot_compatible {n : Nat} {G : Schema n} :
    {T : TypeGraph.Ty n} → (slot : Slot G T) →
    ∀ q ∈ slotDemands slot, q.compatible (slot.getD (Value.dflt _)) →
      q.compatible ((recursiveClearSlot slot).getD (Value.dflt _))
  | _, .absent, _, member, _ => by cases member
  | _, .present value, q, member, before => listed_compatible value q member before
end

/-- Complete finite-query preservation for actual clear, using OLD owner
representation. All generated words are zeroed; every other query is framed
by the proved footprint law. Only the explicit layout nonalias certificate
remains, to be combined with the owner's actual per-run numeric premises. -/
theorem represented_complete {n : Nat} {G : Schema n} {T : TypeGraph.Ty n}
    (value : Value G T) (queries : List (Query G T)) (base : Solidity.Storage.Loc) (store : Store)
    (before : Represented value (demands value ++ queries) base store)
    (separate : ∀ q ∈ queries, q ∉ demands value → ∀ d ∈ demands value,
      q.location base ≠ d.location base) :
    Represented (recursiveClear value) (demands value ++ queries) base
      ((updates value base).foldl (fun w op => write w op.1 op.2) store) := by
  have generated : Represented (recursiveClear value) (demands value) base
      ((updates value base).foldl (fun w op => write w op.1 op.2) store) := by
    apply represented_clear value base store
    · intro q member
      exact (before q (List.mem_append.mpr (Or.inl member))).1
    · intro q member
      exact listed_compatible value q member (before q (List.mem_append.mpr (Or.inl member))).2.1
  intro q member
  by_cases demanded : q ∈ demands value
  · exact generated q demanded
  · have later : q ∈ queries := (List.mem_append.mp member).resolve_left demanded
    obtain ⟨supported, compatible, represented⟩ := before q member
    have frame := outside_frame value q demanded
    refine ⟨supported, ?_, ?_⟩
    · rw [frame.2]
      exact compatible
    · intro word observed
      rw [frame.1] at observed
      simp only [updates, List.foldl_map]
      exact (fold_outside _ base _ store (separate q later demanded)).trans (represented word observed)

/-- Actual generated words plus the caller's finite observations, retaining
order and duplicates. Hash preimage/region/bound certificates must cover this
whole list, including outside queries. -/
noncomputable def coveredLocations {n : Nat} {G : Schema n} {T : TypeGraph.Ty n}
    (value : Value G T) (queries : List (Query G T)) (base : Solidity.Storage.Loc) :
    List Solidity.Storage.Loc := (demands value ++ queries).map (fun q => q.location base)

/-- Operation-generated finite clear realization consumes OLD representation
and the owner's full per-run premises, preserving all selected observations.
It does not implement emitted loops or claim Source/world preservation. -/
theorem complete_numeric {n N L R : Nat} {G : Schema n} {T : TypeGraph.Ty n}
    (value : Value G T) (queries : List (Query G T)) (base : Solidity.Storage.Loc)
    (hash : Solidity.Storage.Pre → Nat) (preimages : List Solidity.Storage.Pre)
    (run : FiniteRun N L R hash preimages (coveredLocations value queries base))
    (store : Store) (machine : WordStore)
    (before : Represented value (demands value ++ queries) base store)
    (initial : Transport N hash (coveredLocations value queries base) store machine)
    (separate : ∀ q ∈ queries, q ∉ demands value → ∀ d ∈ demands value,
      q.location base ≠ d.location base) :
    let afterStore := (updates value base).foldl (fun w op => write w op.1 op.2) store
    let afterMachine := numericClear (N := N) value base hash machine
    Represented (recursiveClear value) (demands value ++ queries) base afterStore ∧
    Transport N hash (coveredLocations value queries base) afterStore afterMachine ∧
    ∀ q ∈ demands value ++ queries, ∀ word, q.read (recursiveClear value) = some word →
      afterMachine ((q.location base).word N hash) = word := by
  have represented := represented_complete value queries base store before separate
  have transported := numeric_transport run value base store machine initial (fun q member =>
    List.mem_map.mpr ⟨q, List.mem_append.mpr (Or.inl member), rfl⟩)
  refine ⟨represented, transported, ?_⟩
  intro q member word observed
  exact represented.numeric transported q member (List.mem_map.mpr ⟨q, member, rfl⟩) word observed

/-- info: 'Solidity.Backend.StorageOps.ClearDemands.outside_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms outside_frame
/-- info: 'Solidity.Backend.StorageOps.ClearDemands.outside_slot_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms outside_slot_frame
/-- info: 'Solidity.Backend.StorageOps.ClearDemands.listed_compatible' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms listed_compatible
/-- info: 'Solidity.Backend.StorageOps.ClearDemands.listed_slot_compatible' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms listed_slot_compatible
/-- info: 'Solidity.Backend.StorageOps.ClearDemands.represented_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms represented_complete
/-- info: 'Solidity.Backend.StorageOps.ClearDemands.complete_numeric' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms complete_numeric

/-- info: 'Solidity.Backend.StorageOps.ClearDemands.demands' does not depend on any axioms -/
#guard_msgs in #print axioms demands
/-- info: 'Solidity.Backend.StorageOps.ClearDemands.slotDemands' does not depend on any axioms -/
#guard_msgs in #print axioms slotDemands
/-- info: 'Solidity.Backend.StorageOps.ClearDemands.mapping_barrier' does not depend on any axioms -/
#guard_msgs in #print axioms mapping_barrier
/-- info: 'Solidity.Backend.StorageOps.ClearDemands.absent_demands' does not depend on any axioms -/
#guard_msgs in #print axioms absent_demands
/-- info: 'Solidity.Backend.StorageOps.ClearDemands.default_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms default_zero
/-- info: 'Solidity.Backend.StorageOps.ClearDemands.listed_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms listed_zero
/-- info: 'Solidity.Backend.StorageOps.ClearDemands.listed_slot_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms listed_slot_zero
/-- info: 'Solidity.Backend.StorageOps.ClearDemands.numeric_transport' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms numeric_transport
/-- info: 'Solidity.Backend.StorageOps.ClearDemands.numeric_outside' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms numeric_outside
/-- info: 'Solidity.Backend.StorageOps.ClearDemands.represented_clear' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms represented_clear
/-- info: 'Solidity.Backend.StorageOps.ClearDemands.mapping_query_frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms mapping_query_frame
/-- info: 'Solidity.Backend.StorageOps.ClearDemands.mapping_numeric_identity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms mapping_numeric_identity
/-- info: 'Solidity.Backend.StorageOps.ClearDemands.delete_numeric' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms delete_numeric
/-- info: 'Solidity.Backend.StorageOps.ClearDemands.mapping_compatible_frame' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms mapping_compatible_frame
/-- info: 'Solidity.Backend.StorageOps.ClearDemands.mapping_represented_frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms mapping_represented_frame
/-- info: 'Solidity.Backend.StorageOps.ClearDemands.shadow_find_frame' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms shadow_find_frame
/-- info: 'Solidity.Backend.StorageOps.ClearDemands.shadow_query_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms shadow_query_frame
/-- info: 'Solidity.Backend.StorageOps.ClearDemands.shadow_compatible_frame' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms shadow_compatible_frame
/-- info: 'Solidity.Backend.StorageOps.ClearDemands.shadow_represented_frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms shadow_represented_frame
/-- info: 'Solidity.Backend.StorageOps.ClearDemands.delete_outside_frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms delete_outside_frame

/-- info: 'Solidity.Backend.StorageOps.ClearDemands.positions' does not depend on any axioms -/
#guard_msgs in #print axioms positions
/-- info: 'Solidity.Backend.StorageOps.ClearDemands.updates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms updates
/-- info: 'Solidity.Backend.StorageOps.ClearDemands.numericClear' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms numericClear
/-- info: 'Solidity.Backend.StorageOps.ClearDemands.coveredLocations' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms coveredLocations

/-- info: 'Solidity.Backend.StorageOps.ClearDemands.positions_mem' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms positions_mem
/-- info: 'Solidity.Backend.StorageOps.ClearDemands.fin_mem' depends on axioms: [propext] -/
#guard_msgs in #print axioms fin_mem
/-- info: 'Solidity.Backend.StorageOps.ClearDemands.fold_zero_member' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms fold_zero_member
/-- info: 'Solidity.Backend.StorageOps.ClearDemands.fold_outside' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms fold_outside

/-- info: 'Solidity.Backend.StorageOps.ClearDemands.prefix_find_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms prefix_find_frame

end Solidity.Backend.StorageOps.ClearDemands
