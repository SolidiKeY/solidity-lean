import Solidity.Backend.StorageOps.CopyDemands

/-! Actual finite recursive copy write generation. Reads are supplied by one
captured INITIAL numeric store at typed source query locations; zero writes
handle defaults and cleared tails. Existing owner queries annotate writes,
not another value/state/AST. Runtime target loop emission is not supplied. -/
namespace Solidity.Backend.StorageOps.CopyWrites
open TypeGraph Solidity.Storage Solidity.Storage.Representation Solidity.Storage.Representation.Graph

def zeros {n : Nat} {G : Schema n} {T : TypeGraph.Ty n}
    (queries : List (Query G T)) : List (Query G T × Semantics.Word) :=
  queries.map (fun q => (q,ClearDemands.zero))

def prefixWrites {n : Nat} {G : Schema n} {A B : TypeGraph.Ty n}
    (path : TypeGraph.Path G A B) (writes : List (Query G B × Semantics.Word)) :
    List (Query G A × Semantics.Word) :=
  writes.map (fun op => (op.1.prefix path,op.2))

mutual
/-- Present source children drive structural recursion at every demanded level.
The reader is fixed before any destination write, including overlapping copies. -/
def queryWrites {n : Nat} {G : Schema n} {T : TypeGraph.Ty n}
    (old src : Value G T) (read : Query G T → Semantics.Word) :
    List (Query G T × Semantics.Word) :=
  Value.casesOn (motive_1 := fun T _ => Value G T →
    (Query G T → Semantics.Word) → List (Query G T × Semantics.Word)) src
    (fun _ _ read => [(.word .nil,read (.word .nil))])
    (fun fields old read => (ClearDemands.positions (G.fields _)).flatMap (fun p =>
      prefixWrites (.cons (.field p.2) .nil) (queryWrites (nodeView old p.2) (fields p.2)
        (fun q => read (q.prefix (.cons (.field p.2) .nil))))))
    (fun _ length bound slots old read =>
      (List.finRange (max old.length.val length.val)).flatMap (fun i =>
        let path : TypeGraph.Path G (.array _) _ := .cons (.index ⟨i.val,by
          have h := i.isLt; have a := old.length.isLt; have b := length.isLt; omega⟩) .nil
        let child := if h : i.val < length.val then
            slotWrites (oldSlot old.extent old.slots i.val)
              (slots ⟨i.val,Nat.lt_of_lt_of_le h bound⟩) (fun q => read (q.prefix path))
          else zeros (ClearDemands.slotDemands (oldSlot old.extent old.slots i.val))
        prefixWrites path child) ++ [(.length .nil,read (.length .nil))])
    (fun {_ m} slots old read => (List.finRange m.val).flatMap (fun i =>
      let path := TypeGraph.Path.cons (.fixed ⟨i.val,Nat.lt_trans i.isLt m.property.2⟩) .nil
      prefixWrites path (slotWrites (fixedView old i) (slots i) (fun q => read (q.prefix path)))))
    (fun _ _ _ => []) old read

/-- Fresh cells initialize published default observations BEFORE present-source
copy writes; absent source clears only the old live demand footprint. -/
def slotWrites {n : Nat} {G : Schema n} {T : TypeGraph.Ty n}
    (old src : Slot G T) (read : Query G T → Semantics.Word) :
    List (Query G T × Semantics.Word) :=
  Slot.casesOn (motive_2 := fun T _ => Slot G T →
    (Query G T → Semantics.Word) → List (Query G T × Semantics.Word)) src
    (fun old _ => Slot.casesOn (motive_2 := fun T _ => List (Query G T × Semantics.Word)) old
      (zeros (CopyDefaults.demands G _)) (fun value => zeros (ClearDemands.demands value)))
    (fun value old read =>
      (Slot.casesOn (motive_2 := fun T _ => List (Query G T × Semantics.Word)) old
        (zeros (CopyDefaults.demands G _)) (fun _ => [])) ++
      queryWrites (old.getD (Value.dflt _)) value read) old read
end

private theorem queries_zeros {n : Nat} {G : Schema n} {T : TypeGraph.Ty n}
    (queries : List (Query G T)) : (zeros queries).map Prod.fst = queries := by
  simp only [zeros,List.map_map,Function.comp_def,List.map_id_fun']
  rfl

private theorem queries_prefix {n : Nat} {G : Schema n} {A B : TypeGraph.Ty n}
    (path : TypeGraph.Path G A B) (writes : List (Query G B × Semantics.Word)) :
    (prefixWrites path writes).map Prod.fst = (writes.map Prod.fst).map (Query.prefix path) := by
  simp only [prefixWrites,List.map_map,Function.comp_def]

mutual
/-- The ACTUAL write sequence has exactly the proved recursive demand footprint,
including initialization duplicates and header-last ordering. -/
theorem query_sequence {n : Nat} {G : Schema n} :
    {T : TypeGraph.Ty n} → (old src : Value G T) → (read : Query G T → Semantics.Word) →
    (queryWrites old src read).map Prod.fst = CopyDemands.demands old src
  | _, .prim old, .prim src, _ => rfl
  | _, @Value.node _ _ i old, .node src, read => by
    change ((ClearDemands.positions (G.fields i)).flatMap (fun p =>
      prefixWrites (.cons (.field p.2) .nil) (queryWrites (old p.2) (src p.2)
        (fun q => read (q.prefix (.cons (.field p.2) .nil)))))).map Prod.fst = _
    rw [List.map_flatMap]
    apply congrArg (fun f => (ClearDemands.positions (G.fields i)).flatMap f)
    funext p
    rw [queries_prefix,query_sequence]
    rfl
  | _, @Value.array _ _ E oe ol oh os, .array ne nl nh ns, read => by
    change (((List.finRange (max ol.val nl.val)).flatMap (fun (i : Fin (max ol.val nl.val)) =>
      let path : TypeGraph.Path G (.array E) E := .cons (.index ⟨i.val,by
        have h := i.isLt; have a := ol.isLt; have b := nl.isLt; omega⟩) .nil
      prefixWrites path (if h : i.val < nl.val then
        slotWrites (oldSlot oe os i.val) (ns ⟨i.val,Nat.lt_of_lt_of_le h nh⟩)
          (fun q => read (q.prefix path))
        else zeros (ClearDemands.slotDemands (oldSlot oe os i.val))))) ++
      [((.length .nil : Query G (.array E)),read (.length .nil))]).map Prod.fst = _
    rw [List.map_append,List.map_flatMap]
    change _ ++ [(.length .nil : Query G (.array E))] = _ ++ [.length .nil]
    apply congrArg (fun (xs : List (Query G (.array E))) =>
      xs ++ [(Query.length (.nil : TypeGraph.Path G (.array E) (.array E)))])
    apply congrArg (fun f => (List.finRange (max ol.val nl.val)).flatMap f)
    funext i
    rw [queries_prefix]
    by_cases live : i.val < nl.val
    · simp only [dif_pos live,slot_query_sequence,Value.extent,Value.slots]
    · simp only [dif_neg live,queries_zeros,Value.extent,Value.slots]
  | _, @Value.fixed _ _ E m old, .fixed src, read => by
    change ((List.finRange m.val).flatMap (fun i =>
      let path := TypeGraph.Path.cons (.fixed ⟨i.val,Nat.lt_trans i.isLt m.property.2⟩) .nil
      prefixWrites path (slotWrites (old i) (src i) (fun q => read (q.prefix path))))).map Prod.fst = _
    rw [List.map_flatMap]
    apply congrArg (fun f => (List.finRange m.val).flatMap f)
    funext i
    rw [queries_prefix,slot_query_sequence]
    rfl
  | _, .mapping old, .mapping src, _ => rfl

theorem slot_query_sequence {n : Nat} {G : Schema n} :
    {T : TypeGraph.Ty n} → (old src : Slot G T) → (read : Query G T → Semantics.Word) →
    (slotWrites old src read).map Prod.fst = CopyDemands.slotDemands old src
  | _, .absent, .absent, _ => queries_zeros _
  | _, .present old, .absent, _ => queries_zeros _
  | _, .absent, .present src, read => by
    change (zeros (CopyDefaults.demands G _) ++ queryWrites (Value.dflt _) src read).map Prod.fst = _
    rw [List.map_append,queries_zeros,query_sequence]
    rfl
  | _, .present old, .present src, read => query_sequence old src read
end

/-- Existing numeric storage is captured by the runtime reader, not by using
source evaluator output as a target payload oracle. -/
noncomputable def updates {n N : Nat} {G : Schema n} {T : TypeGraph.Ty n}
    (old src : Value G T) (dst source : Solidity.Storage.Loc)
    (hash : Solidity.Storage.Pre → Nat) (initial : WordStore) :
    List (Solidity.Storage.Loc × Semantics.Word) :=
  (queryWrites old src (fun q => initial ((q.location source).word N hash))).map
    (fun op => (op.1.location dst,op.2))

noncomputable def numericCopy {n N : Nat} {G : Schema n} {T : TypeGraph.Ty n}
    (old src : Value G T) (dst source : Solidity.Storage.Loc)
    (hash : Solidity.Storage.Pre → Nat) (initial : WordStore) : WordStore :=
  (updates (N := N) old src dst source hash initial).foldl
    (fun m op => writeWord m (op.1.word N hash) op.2) initial

/-- Coverage comes from the actual generator; no arbitrary write-log premise. -/
theorem generated {n N : Nat} {G : Schema n} {T : TypeGraph.Ty n}
    (old src : Value G T) (dst source : Solidity.Storage.Loc)
    (hash : Solidity.Storage.Pre → Nat) (initial : WordStore) :
    ∀ op ∈ updates (N := N) old src dst source hash initial,
      ∃ q ∈ CopyDemands.demands old src, op.1 = q.location dst := by
  intro op member
  obtain ⟨entry,inside,same⟩ := List.mem_map.mp member
  subst op
  refine ⟨entry.1,?_,rfl⟩
  rw [← query_sequence old src (fun q => initial ((q.location source).word N hash))]
  exact List.mem_map.mpr ⟨entry,inside,rfl⟩

/-- Actual snapshot write generation composes with the PUBLIC transport relation
and the C31 complete omitted-query frame. INSIDE value provenance is separate. -/
theorem outside_numeric {n N L R : Nat} {G : Schema n} {T : TypeGraph.Ty n}
    (old src : Value G T) (permit : CopyPermit G T) (queries : List (Query G T))
    (dst source : Solidity.Storage.Loc) (store : Store) (machine : WordStore)
    {hash : Solidity.Storage.Pre → Nat} {P : List Solidity.Storage.Pre}
    {locations : List Solidity.Storage.Loc} (run : FiniteRun N L R hash P locations)
    (before : Represented old queries dst store)
    (initial : Transport N hash locations store machine)
    (covered : ∀ d ∈ CopyDemands.demands old src, d.location dst ∈ locations)
    (observed : ∀ q ∈ queries, q.location dst ∈ locations)
    (separate : ∀ q ∈ queries, ∀ d ∈ CopyDemands.demands old src, q.location dst ≠ d.location dst) :
    let afterStore := (updates (N := N) old src dst source hash machine).foldl
      (fun w op => write w op.1 op.2) store
    Represented (recursiveCopy old src) queries dst afterStore ∧
    Transport N hash locations afterStore (numericCopy (N := N) old src dst source hash machine) ∧
    ∀ q ∈ queries, ∀ word, q.read (recursiveCopy old src) = some word →
      numericCopy (N := N) old src dst source hash machine ((q.location dst).word N hash) = word :=
  CopyDemands.outside_numeric old src permit queries dst store machine run before initial
    (updates (N := N) old src dst source hash machine) (generated old src dst source hash machine)
    covered observed separate

/-- Every numeric word outside the generated destination image stays unchanged. -/
theorem numeric_outside {n N : Nat} {G : Schema n} {T : TypeGraph.Ty n}
    (old src : Value G T) (dst source : Solidity.Storage.Loc)
    (hash : Solidity.Storage.Pre → Nat) (initial : WordStore) (address : Nat)
    (outside : ∀ q ∈ CopyDemands.demands old src, address ≠ (q.location dst).word N hash) :
    numericCopy (N := N) old src dst source hash initial address = initial address := by
  apply sequence_outside_frame N hash initial (updates (N := N) old src dst source hash initial) address
  intro op member
  obtain ⟨q,inside,same⟩ := generated old src dst source hash initial op member
  rw [same]
  exact outside q inside

/-- info: 'Solidity.Backend.StorageOps.CopyWrites.queryWrites' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms queryWrites
/-- info: 'Solidity.Backend.StorageOps.CopyWrites.slotWrites' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms slotWrites
/-- info: 'Solidity.Backend.StorageOps.CopyWrites.query_sequence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms query_sequence
/-- info: 'Solidity.Backend.StorageOps.CopyWrites.slot_query_sequence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms slot_query_sequence
/-- info: 'Solidity.Backend.StorageOps.CopyWrites.updates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms updates
/-- info: 'Solidity.Backend.StorageOps.CopyWrites.numericCopy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms numericCopy
/-- info: 'Solidity.Backend.StorageOps.CopyWrites.generated' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms generated
/-- info: 'Solidity.Backend.StorageOps.CopyWrites.outside_numeric' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms outside_numeric
/-- info: 'Solidity.Backend.StorageOps.CopyWrites.numeric_outside' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms numeric_outside

/-- info: 'Solidity.Backend.StorageOps.CopyWrites.zeros' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms zeros
/-- info: 'Solidity.Backend.StorageOps.CopyWrites.prefixWrites' does not depend on any axioms -/
#guard_msgs in #print axioms prefixWrites

end Solidity.Backend.StorageOps.CopyWrites
