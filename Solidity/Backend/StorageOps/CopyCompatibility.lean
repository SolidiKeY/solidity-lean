import Solidity.Backend.StorageOps.CopyReadCapture

/-! Operation-side preservation of the PUBLIC selected-query header bounds.
Old selected destination bounds and source read-footprint bounds are inputs;
post bounds are derived through the independent recursive operation. No source
admission limit or owner representation relation is changed. -/
namespace Solidity.Backend.StorageOps.CopyCompatibility
open TypeGraph Solidity.Storage Solidity.Storage.Representation Solidity.Storage.Representation.Graph

theorem default_compatible {n : Nat} {G : Schema n} {T : TypeGraph.Ty n}
    (permit : CopyPermit G T) (q : Query G T) : q.compatible (Value.dflt T) := by
  cases read : q.read (Value.dflt T) with
  | none => exact CopyDemands.read_none_compatible q _ read
  | some word => exact (CopyDefaults.listed_properties G T q
      (CopyDefaults.complete G T permit q word read)).1

theorem clear_compatible {n : Nat} {G : Schema n} {T : TypeGraph.Ty n}
    (old : Value G T) (q : Query G T) (before : q.compatible old) :
    q.compatible (recursiveClear old) := by
  by_cases inside : q ∈ ClearDemands.demands old
  · exact ClearDemands.listed_compatible old q inside before
  · rw [(ClearDemands.outside_frame old q inside).2]
    exact before

theorem clear_slot_compatible {n : Nat} {G : Schema n} {T : TypeGraph.Ty n}
    (old : Slot G T) (q : Query G T) (before : q.compatible (old.getD (Value.dflt T))) :
    q.compatible ((recursiveClearSlot old).getD (Value.dflt T)) := by
  cases old with
  | absent => exact before
  | present value => exact clear_compatible value q before

mutual
/-- Selected post header bounds derive from OLD destination observations and
ALL actual SOURCE read-header observations. No desired post relation is assumed. -/
theorem copy_compatible {n : Nat} {G : Schema n} :
    {T : TypeGraph.Ty n} → (old src : Value G T) → CopyPermit G T →
    (q : Query G T) → q.compatible old →
    (∀ d ∈ ClearDemands.demands src, d.compatible src) →
    q.compatible (recursiveCopy old src)
  | _, .prim old, .prim src, _, q, _, _ => by
    cases q with
    | word _ => exact True.intro
    | length path => cases path with | cons step rest => cases step
  | _, @Value.node _ _ i old, .node src, permit, q, before, sourceBounds => by
    cases q with
    | word _ => exact True.intro
    | length path => cases path with | cons step rest => cases step with
      | field position =>
        have childBefore : (Query.length rest).compatible (old position) := by
          exact Eq.mp (Query.compatible_prefix (Value.node old) (old position)
            (.cons (.field position) .nil) (.length rest) rfl) before
        have childBounds : ∀ d ∈ ClearDemands.demands (src position), d.compatible (src position) := by
          intro d member
          have bound := sourceBounds (d.prefix (.cons (.field position) .nil))
            (List.mem_flatMap.mpr ⟨⟨_,position⟩,ClearDemands.positions_mem position,
              List.mem_map.mpr ⟨d,member,rfl⟩⟩)
          rwa [Query.compatible_prefix (.node src) _ _ d rfl] at bound
        apply Eq.mpr (Query.compatible_prefix (recursiveCopy (.node old) (.node src))
          (recursiveCopy (old position) (src position)) (.cons (.field position) .nil) (.length rest) rfl)
        exact copy_compatible (old position) (src position) (permit.step (.field position))
          (.length rest) childBefore childBounds
  | _, @Value.array _ _ E oe ol oh os, .array ne nl nh ns, permit, q, before, sourceBounds => by
    cases q with
    | word _ => exact True.intro
    | length path => cases path with
      | nil =>
        have oldBounds : ol.val ≤ lmax ∧ oe.val ≤ lmax := before
        have srcBounds : nl.val ≤ lmax ∧ ne.val ≤ lmax := sourceBounds (.length .nil)
          (List.mem_append.mpr (Or.inr List.mem_cons_self))
        change nl.val ≤ lmax ∧ max oe.val nl.val ≤ lmax
        exact ⟨srcBounds.1,Nat.max_le.mpr ⟨oldBounds.2,srcBounds.1⟩⟩
      | cons step rest => cases step with
        | index i =>
          let child : Query G E := .length rest
          have oldChildBounds : child.compatible ((oldSlot oe os i.val).getD (Value.dflt E)) := by
            by_cases retained : i.val < oe.val
            · have found : (Value.array oe ol oh os).find (.cons (.index i) .nil) =
                  some ((oldSlot oe os i.val).getD (Value.dflt E)) := by
                simp only [Value.find,Path.read,Step.get,dif_pos retained,oldSlot,Option.bind_some]
              rw [← Query.compatible_prefix (.array oe ol oh os) _ _ child found]
              exact before
            · have absent : oldSlot oe os i.val = Slot.absent := by simp only [oldSlot,dif_neg retained]
              rw [absent]
              exact default_compatible (permit.step (.index i)) child
          by_cases live : i.val < nl.val
          · have sourceChildBounds : ∀ d ∈ ClearDemands.slotDemands (ns ⟨i.val,Nat.lt_of_lt_of_le live nh⟩),
                d.compatible ((ns ⟨i.val,Nat.lt_of_lt_of_le live nh⟩).getD (Value.dflt E)) := by
              intro d member
              have rootBound := sourceBounds (d.prefix (.cons (.index i) .nil))
                (List.mem_append.mpr (Or.inl (List.mem_flatMap.mpr
                  ⟨⟨i.val,live⟩,ClearDemands.fin_mem _,List.mem_map.mpr ⟨d,member,rfl⟩⟩)))
              have found : (Value.array ne nl nh ns).find (.cons (.index i) .nil) =
                  some ((ns ⟨i.val,Nat.lt_of_lt_of_le live nh⟩).getD (Value.dflt E)) := by
                simp only [Value.find,Path.read,Step.get,dif_pos (Nat.lt_of_lt_of_le live nh),Option.bind_some]
              rwa [Query.compatible_prefix (.array ne nl nh ns) _ _ d found] at rootBound
            have newBound : i.val < max oe.val nl.val := Nat.lt_of_lt_of_le live (Nat.le_max_right _ _)
            have visited : i.val < max ol.val nl.val := Nat.lt_of_lt_of_le live (Nat.le_max_right _ _)
            have found : (recursiveCopy (.array oe ol oh os) (.array ne nl nh ns)).find
                (.cons (.index i) .nil) = some
                ((recursiveSlot (oldSlot oe os i.val) (ns ⟨i.val,Nat.lt_of_lt_of_le live nh⟩)).getD (Value.dflt E)) := by
              simp only [recursiveCopy,Value.extent,Value.length,Value.slots,Value.find,Path.read,
                Step.get,dif_pos newBound,Option.bind_some,visit_prefix,if_pos visited,dif_pos live]
            apply Eq.mpr (Query.compatible_prefix _ _ _ child found)
            exact slot_compatible (oldSlot oe os i.val) (ns ⟨i.val,Nat.lt_of_lt_of_le live nh⟩)
              (permit.step (.index i)) child oldChildBounds sourceChildBounds
          · by_cases clearing : i.val < ol.val
            · have newBound : i.val < max oe.val nl.val :=
                Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le clearing oh) (Nat.le_max_left _ _)
              have visited : i.val < max ol.val nl.val := Nat.lt_of_lt_of_le clearing (Nat.le_max_left _ _)
              have found : (recursiveCopy (.array oe ol oh os) (.array ne nl nh ns)).find
                  (.cons (.index i) .nil) = some ((recursiveClearSlot (oldSlot oe os i.val)).getD (Value.dflt E)) := by
                simp only [recursiveCopy,Value.extent,Value.length,Value.slots,Value.find,Path.read,
                  Step.get,dif_pos newBound,Option.bind_some,visit_prefix,if_pos visited,dif_neg live,if_pos clearing]
              apply Eq.mpr (Query.compatible_prefix _ _ _ child found)
              exact clear_slot_compatible (oldSlot oe os i.val) child oldChildBounds
            · have unvisited : ¬ i.val < max ol.val nl.val := by omega
              have same : (recursiveCopy (.array oe ol oh os) (.array ne nl nh ns)).find
                  (.cons (.index i) .nil) = (Value.array oe ol oh os).find (.cons (.index i) .nil) := by
                by_cases retained : i.val < oe.val
                · have newBound : i.val < max oe.val nl.val := Nat.lt_of_lt_of_le retained (Nat.le_max_left _ _)
                  simp only [recursiveCopy,Value.extent,Value.length,Value.slots,Value.find,Path.read,
                    Step.get,dif_pos newBound,dif_pos retained,Option.bind_some,visit_prefix,if_neg unvisited,oldSlot]
                · have newBound : ¬ i.val < max oe.val nl.val := by omega
                  simp only [recursiveCopy,Value.extent,Value.length,Value.slots,Value.find,Path.read,
                    Step.get,dif_neg newBound,dif_neg retained,Option.bind_none]
              exact Eq.mpr (ClearDemands.prefix_find_frame _ _ (.cons (.index i) .nil) child same).2 before
  | _, @Value.fixed _ _ E m old, .fixed src, permit, q, before, sourceBounds => by
    cases q with
    | word _ => exact True.intro
    | length path => cases path with | cons step rest => cases step with
      | fixed i =>
        let child : Query G E := .length rest
        by_cases inside : i.val < m.val
        · have foundBefore : (Value.fixed old).find (.cons (.fixed i) .nil) =
              some ((old ⟨i.val,inside⟩).getD (Value.dflt E)) := by
            simp only [Value.find,Path.read,Step.get,dif_pos inside,Option.bind_some]
          have childBefore : child.compatible ((old ⟨i.val,inside⟩).getD (Value.dflt E)) := by
            rw [← Query.compatible_prefix (.fixed old) _ _ child foundBefore]
            exact before
          have childBounds : ∀ d ∈ ClearDemands.slotDemands (src ⟨i.val,inside⟩),
              d.compatible ((src ⟨i.val,inside⟩).getD (Value.dflt E)) := by
            intro d member
            have rootBound := sourceBounds (d.prefix (.cons (.fixed i) .nil))
              (List.mem_flatMap.mpr ⟨⟨i.val,inside⟩,ClearDemands.fin_mem _,List.mem_map.mpr ⟨d,member,rfl⟩⟩)
            have found : (Value.fixed src).find (.cons (.fixed i) .nil) =
                some ((src ⟨i.val,inside⟩).getD (Value.dflt E)) := by
              simp only [Value.find,Path.read,Step.get,dif_pos inside,Option.bind_some]
            rwa [Query.compatible_prefix (.fixed src) _ _ d found] at rootBound
          have foundAfter : (recursiveCopy (.fixed old) (.fixed src)).find (.cons (.fixed i) .nil) =
              some ((recursiveSlot (old ⟨i.val,inside⟩) (src ⟨i.val,inside⟩)).getD (Value.dflt E)) := by
            simp only [recursiveCopy,fixedView,Value.find,Path.read,Step.get,dif_pos inside,Option.bind_some]
          apply Eq.mpr (Query.compatible_prefix _ _ _ child foundAfter)
          exact slot_compatible (old ⟨i.val,inside⟩) (src ⟨i.val,inside⟩) (permit.step (.fixed i)) child childBefore childBounds
        · have missing : (recursiveCopy (.fixed old) (.fixed src)).find (.cons (.fixed i) .nil) = none := by
            simp only [recursiveCopy,Value.find,Path.read,Step.get,dif_neg inside,Option.bind_none]
          exact (CopyDemands.prefix_none _ (.cons (.fixed i) .nil) child missing).2
  | _, .mapping old, .mapping src, _, q, before, _ => before

theorem slot_compatible {n : Nat} {G : Schema n} :
    {T : TypeGraph.Ty n} → (old src : Slot G T) → CopyPermit G T →
    (q : Query G T) → q.compatible (old.getD (Value.dflt _)) →
    (∀ d ∈ ClearDemands.slotDemands src, d.compatible (src.getD (Value.dflt _))) →
    q.compatible ((recursiveSlot old src).getD (Value.dflt _))
  | _, .absent, .absent, _, _, before, _ => before
  | _, .present old, .absent, _, q, before, _ => clear_compatible old q before
  | _, old, .present src, permit, q, before, sourceBounds =>
    copy_compatible (old.getD (Value.dflt _)) src permit q before sourceBounds
end

/-- Both PUBLIC OLD relations supply all selected post metadata. Word agreement
is deliberately separate and remains the next inside-output obligation. -/
theorem represented_metadata {n : Nat} {G : Schema n} {T : TypeGraph.Ty n}
    (old src : Value G T) (permit : CopyPermit G T) (queries : List (Query G T))
    (dst source : Solidity.Storage.Loc) (store : Store)
    (beforeDst : Represented old queries dst store)
    (beforeSrc : Represented src (ClearDemands.demands src) source store) :
    ∀ q ∈ queries, q.supported ∧ q.compatible (recursiveCopy old src) := by
  intro q member
  exact ⟨(beforeDst q member).1,copy_compatible old src permit q (beforeDst q member).2.1
    (fun d inside => (beforeSrc d inside).2.1)⟩

/-- info: 'Solidity.Backend.StorageOps.CopyCompatibility.default_compatible' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms default_compatible
/-- info: 'Solidity.Backend.StorageOps.CopyCompatibility.clear_compatible' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms clear_compatible
/-- info: 'Solidity.Backend.StorageOps.CopyCompatibility.clear_slot_compatible' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms clear_slot_compatible
/-- info: 'Solidity.Backend.StorageOps.CopyCompatibility.copy_compatible' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms copy_compatible
/-- info: 'Solidity.Backend.StorageOps.CopyCompatibility.slot_compatible' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms slot_compatible
/-- info: 'Solidity.Backend.StorageOps.CopyCompatibility.represented_metadata' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms represented_metadata

end Solidity.Backend.StorageOps.CopyCompatibility
