import Solidity.Backend.StorageOps.CopyDefaults
import Solidity.Backend.StorageOps.RecursiveCopy

/-! Recursive copy-generated existing typed queries. Present source constructors
and runtime live prefixes drive enumeration. Absent OLD slots add initialization
demands before copy demands: old failed queries constrain no numeric cells.
This is a finite demand algorithm, not emitted runtime code or a new value IR. -/
namespace Solidity.Backend.StorageOps.CopyDemands
open TypeGraph Solidity.Storage Solidity.Storage.Representation Solidity.Storage.Representation.Graph

mutual
/-- Structural source recursion with runtime traversal at every dynamic level.
Older shadows are omitted, shortened old live tails use independent clear demands.
No overlay invocation or copied-output observation defines this algorithm. -/
def demands {n : Nat} {G : Schema n} {T : TypeGraph.Ty n}
    (old src : Value G T) : List (Query G T) :=
  Value.casesOn (motive_1 := fun T _ => Value G T → List (Query G T)) src
    (fun _ _ => [.word .nil])
    (fun fields old => (ClearDemands.positions (G.fields _)).flatMap (fun p =>
      (demands (nodeView old p.2) (fields p.2)).map
        (Query.prefix (.cons (.field p.2) .nil))))
    (fun _ length bound slots old =>
      (List.finRange (max old.length.val length.val)).flatMap (fun i =>
        let child := if h : i.val < length.val then
            slotDemands (oldSlot old.extent old.slots i.val)
              (slots ⟨i.val,Nat.lt_of_lt_of_le h bound⟩)
          else ClearDemands.slotDemands (oldSlot old.extent old.slots i.val)
        child.map (Query.prefix (.cons (.index ⟨i.val,by
          have h := i.isLt; have a := old.length.isLt; have b := length.isLt; omega⟩) .nil))) ++
      [.length .nil])
    (fun {_ m} slots old => (List.finRange m.val).flatMap (fun i =>
      (slotDemands (fixedView old i) (slots i)).map
        (Query.prefix (.cons (.fixed ⟨i.val,Nat.lt_trans i.isLt m.property.2⟩) .nil))))
    (fun _ _ => []) old

/-- Fresh absent slots explicitly initialize default observations before the
present-source recursion. Existing absent source slots clear old present values. -/
def slotDemands {n : Nat} {G : Schema n} {T : TypeGraph.Ty n}
    (old src : Slot G T) : List (Query G T) :=
  Slot.casesOn (motive_2 := fun T _ => Slot G T → List (Query G T)) src
    (fun old => Slot.casesOn (motive_2 := fun T _ => List (Query G T)) old
      (CopyDefaults.demands G _) (fun value => ClearDemands.demands value))
    (fun value old =>
      (Slot.casesOn (motive_2 := fun T _ => List (Query G T)) old
        (CopyDefaults.demands G _) (fun _ => [])) ++
      demands (old.getD (Value.dflt _)) value) old
end

theorem absent_absent {n : Nat} (G : Schema n) (T : TypeGraph.Ty n) :
    slotDemands (Slot.absent : Slot G T) .absent = CopyDefaults.demands G T := rfl

theorem absent_present {n : Nat} {G : Schema n} {T : TypeGraph.Ty n} (src : Value G T) :
    slotDemands Slot.absent (.present src) = CopyDefaults.demands G T ++
      demands (Value.dflt T) src := rfl

theorem present_absent {n : Nat} {G : Schema n} {T : TypeGraph.Ty n} (old : Value G T) :
    slotDemands (.present old) Slot.absent = ClearDemands.demands old := rfl

theorem present_present {n : Nat} {G : Schema n} {T : TypeGraph.Ty n} (old src : Value G T) :
    slotDemands (.present old) (.present src) = demands old src := rfl

theorem mapping_barrier {n : Nat} {G : Schema n} {K : PrimTy} {V : TypeGraph.Ty n}
    (old src : Value G (.mapping K V)) : demands old src = [] := by
  cases src
  rfl

/-- Crucial fresh-visibility invariant: an omitted query was not a successful
default read. A clear-only footprint cannot establish this statement. -/
theorem absent_outside_none {n : Nat} {G : Schema n} {T : TypeGraph.Ty n}
    (permit : CopyPermit G T) (src : Slot G T) (q : Query G T)
    (omitted : q ∉ slotDemands .absent src) : q.read (Value.dflt T) = none := by
  have outside : q ∉ CopyDefaults.demands G T := by
    cases src with
    | absent => exact omitted
    | present value => exact fun member => omitted (List.mem_append.mpr (Or.inl member))
  cases observed : q.read (Value.dflt T) with
  | none => rfl
  | some word => exact False.elim (outside (CopyDefaults.complete G T permit q word observed))

theorem read_none_compatible {n : Nat} {G : Schema n} {T : TypeGraph.Ty n}
    (q : Query G T) (value : Value G T) (missing : q.read value = none) : q.compatible value := by
  cases q with
  | word path => exact True.intro
  | length path =>
    simp only [Query.read,Option.map_eq_none_iff] at missing
    simp only [Query.compatible,missing]

theorem prefix_none {n : Nat} {G : Schema n} {A B : TypeGraph.Ty n}
    (value : Value G A) (stem : TypeGraph.Path G A B) (q : Query G B)
    (missing : value.find stem = none) :
    (q.prefix stem).read value = none ∧ (q.prefix stem).compatible value := by
  have read : (q.prefix stem).read value = none := by
    cases q <;> simp only [Query.read,Query.prefix,Value.observe_append,missing,
      Option.bind_none,Option.map_none]
  exact ⟨read,read_none_compatible _ _ read⟩

mutual
/-- Every omitted query preserves its complete Option read and terminal header
compatibility. Fresh defaults are enumerated, not assumed numerically initialized. -/
theorem outside_frame {n : Nat} {G : Schema n} :
    {T : TypeGraph.Ty n} → (old src : Value G T) → CopyPermit G T →
    (q : Query G T) → q ∉ demands old src →
    q.read (recursiveCopy old src) = q.read old ∧
      q.compatible (recursiveCopy old src) = q.compatible old
  | _, .prim old, .prim src, _, q, outside => by
    cases q with
    | word path => cases path with
      | nil => exact False.elim (outside List.mem_cons_self)
      | cons step rest => cases step
    | length path => cases path with | cons step rest => cases step
  | _, @Value.node _ _ i old, .node src, permit, q, outside => by
    have childFrame : ∀ {U : TypeGraph.Ty n} (position : Field (G.fields i) U)
        (child : Query G U),
        child.prefix (.cons (.field position) .nil) ∉ demands (.node old) (.node src) →
        (child.prefix (.cons (.field position) .nil)).read (recursiveCopy (.node old) (.node src)) =
          (child.prefix (.cons (.field position) .nil)).read (.node old) ∧
        (child.prefix (.cons (.field position) .nil)).compatible (recursiveCopy (.node old) (.node src)) =
          (child.prefix (.cons (.field position) .nil)).compatible (.node old) := by
      intro U position child omitted
      have absent : child ∉ demands (old position) (src position) := by
        intro member
        apply omitted
        exact List.mem_flatMap.mpr ⟨⟨U,position⟩,ClearDemands.positions_mem position,
          List.mem_map.mpr ⟨child,member,rfl⟩⟩
      have frame := outside_frame (old position) (src position)
        (permit.step (.field position)) child absent
      constructor
      · rw [Query.read_prefix _ _ _ _ rfl,Query.read_prefix _ _ _ _ rfl]
        exact frame.1
      · rw [Query.compatible_prefix _ _ _ _ rfl,Query.compatible_prefix _ _ _ _ rfl]
        exact frame.2
    cases q with
    | word path => cases path with | cons step rest => cases step with
      | field position => exact childFrame position (.word rest) outside
    | length path => cases path with | cons step rest => cases step with
      | field position => exact childFrame position (.length rest) outside
  | _, @Value.array _ _ E oe ol oh os, .array ne nl nh ns, permit, q, outside => by
    have childFrame : ∀ (i : Index) (child : Query G E),
        child.prefix (.cons (.index i) .nil) ∉ demands (.array oe ol oh os) (.array ne nl nh ns) →
        (child.prefix (.cons (.index i) .nil)).read
          (recursiveCopy (.array oe ol oh os) (.array ne nl nh ns)) =
          (child.prefix (.cons (.index i) .nil)).read (.array oe ol oh os) ∧
        (child.prefix (.cons (.index i) .nil)).compatible
          (recursiveCopy (.array oe ol oh os) (.array ne nl nh ns)) =
          (child.prefix (.cons (.index i) .nil)).compatible (.array oe ol oh os) := by
      intro i child omitted
      by_cases live : i.val < nl.val
      · have visited : i.val < max ol.val nl.val := Nat.lt_of_lt_of_le live (Nat.le_max_right _ _)
        have childOutside : child ∉ slotDemands (oldSlot oe os i.val)
            (ns ⟨i.val,Nat.lt_of_lt_of_le live nh⟩) := by
          intro member
          apply omitted
          exact List.mem_append.mpr (Or.inl (List.mem_flatMap.mpr
            ⟨⟨i.val,visited⟩,ClearDemands.fin_mem _,List.mem_map.mpr
              ⟨child,by simpa only [dif_pos live] using member,rfl⟩⟩))
        have frame := outside_slot_frame (oldSlot oe os i.val)
          (ns ⟨i.val,Nat.lt_of_lt_of_le live nh⟩) (permit.step (.index i)) child childOutside
        have newBound : i.val < max oe.val nl.val := Nat.lt_of_lt_of_le live (Nat.le_max_right _ _)
        have after : (recursiveCopy (.array oe ol oh os) (.array ne nl nh ns)).find
            (.cons (.index i) .nil) = some
            ((recursiveSlot (oldSlot oe os i.val) (ns ⟨i.val,Nat.lt_of_lt_of_le live nh⟩)).getD
              (Value.dflt E)) := by
          simp only [recursiveCopy,Value.extent,Value.length,Value.slots,Value.find,
            Path.read,Step.get,dif_pos newBound,Option.bind_some,visit_prefix,
            if_pos visited,dif_pos live]
        by_cases retained : i.val < oe.val
        · have before : (Value.array oe ol oh os).find (.cons (.index i) .nil) =
              some ((oldSlot oe os i.val).getD (Value.dflt E)) := by
            simp only [Value.find,Path.read,Step.get,dif_pos retained,oldSlot,Option.bind_some]
          constructor
          · rw [Query.read_prefix _ _ _ _ after,Query.read_prefix _ _ _ _ before]
            exact frame.1
          · rw [Query.compatible_prefix _ _ _ _ after,Query.compatible_prefix _ _ _ _ before]
            exact frame.2.1
        · have before : (Value.array oe ol oh os).find (.cons (.index i) .nil) = none := by
            simp only [Value.find,Path.read,Step.get,dif_neg retained,Option.bind_none]
          have oldAbsent : oldSlot oe os i.val = Slot.absent := by
            simp only [oldSlot,dif_neg retained]
          have defaultMissing := frame.2.2 oldAbsent
          have missing : (child.prefix (.cons (.index i) .nil)).read
              (recursiveCopy (.array oe ol oh os) (.array ne nl nh ns)) = none := by
            rw [Query.read_prefix _ _ _ _ after,frame.1]
            simpa only [oldAbsent,Slot.getD] using defaultMissing
          have oldMissing := prefix_none (.array oe ol oh os) (.cons (.index i) .nil) child before
          exact ⟨missing.trans oldMissing.1.symm,
            propext ⟨(fun _ => oldMissing.2),(fun _ => read_none_compatible _ _ missing)⟩⟩
      · by_cases clearing : i.val < ol.val
        · have visited : i.val < max ol.val nl.val := Nat.lt_of_lt_of_le clearing (Nat.le_max_left _ _)
          have retained : i.val < oe.val := Nat.lt_of_lt_of_le clearing oh
          have newBound : i.val < max oe.val nl.val := Nat.lt_of_lt_of_le retained (Nat.le_max_left _ _)
          have childOutside : child ∉ ClearDemands.slotDemands (oldSlot oe os i.val) := by
            intro member
            apply omitted
            exact List.mem_append.mpr (Or.inl (List.mem_flatMap.mpr
              ⟨⟨i.val,visited⟩,ClearDemands.fin_mem _,List.mem_map.mpr
                ⟨child,by simpa only [dif_neg live] using member,rfl⟩⟩))
          have frame := ClearDemands.outside_slot_frame (oldSlot oe os i.val) child childOutside
          have before : (Value.array oe ol oh os).find (.cons (.index i) .nil) =
              some ((oldSlot oe os i.val).getD (Value.dflt E)) := by
            simp only [Value.find,Path.read,Step.get,dif_pos retained,oldSlot,Option.bind_some]
          have after : (recursiveCopy (.array oe ol oh os) (.array ne nl nh ns)).find
              (.cons (.index i) .nil) = some ((recursiveClearSlot (oldSlot oe os i.val)).getD
                (Value.dflt E)) := by
            simp only [recursiveCopy,Value.extent,Value.length,Value.slots,Value.find,
              Path.read,Step.get,dif_pos newBound,Option.bind_some,visit_prefix,
              if_pos visited,dif_neg live,if_pos clearing]
          constructor
          · rw [Query.read_prefix _ _ _ _ after,Query.read_prefix _ _ _ _ before]
            exact frame.1
          · rw [Query.compatible_prefix _ _ _ _ after,Query.compatible_prefix _ _ _ _ before]
            exact frame.2
        · have unvisited : ¬ i.val < max ol.val nl.val := by omega
          apply ClearDemands.prefix_find_frame _ _ (.cons (.index i) .nil) child
          by_cases retained : i.val < oe.val
          · have newBound : i.val < max oe.val nl.val := Nat.lt_of_lt_of_le retained (Nat.le_max_left _ _)
            simp only [recursiveCopy,Value.extent,Value.length,Value.slots,Value.find,
              Path.read,Step.get,dif_pos newBound,dif_pos retained,Option.bind_some,
              visit_prefix,if_neg unvisited,oldSlot]
          · have newBound : ¬ i.val < max oe.val nl.val := by omega
            simp only [recursiveCopy,Value.extent,Value.length,Value.slots,Value.find,
              Path.read,Step.get,dif_neg newBound,dif_neg retained,Option.bind_none]
    cases q with
    | word path => cases path with | cons step rest => cases step with
      | index i => exact childFrame i (.word rest) outside
    | length path => cases path with
      | nil => exact False.elim (outside (List.mem_append.mpr (Or.inr List.mem_cons_self)))
      | cons step rest => cases step with
        | index i => exact childFrame i (.length rest) outside
  | _, @Value.fixed _ _ E m old, .fixed src, permit, q, outside => by
    have childFrame : ∀ (i : Index) (child : Query G E),
        child.prefix (.cons (.fixed i) .nil) ∉ demands (.fixed old) (.fixed src) →
        (child.prefix (.cons (.fixed i) .nil)).read (recursiveCopy (.fixed old) (.fixed src)) =
          (child.prefix (.cons (.fixed i) .nil)).read (.fixed old) ∧
        (child.prefix (.cons (.fixed i) .nil)).compatible (recursiveCopy (.fixed old) (.fixed src)) =
          (child.prefix (.cons (.fixed i) .nil)).compatible (.fixed old) := by
      intro i child omitted
      by_cases inside : i.val < m.val
      · have absent : child ∉ slotDemands (old ⟨i.val,inside⟩) (src ⟨i.val,inside⟩) := by
          intro member
          apply omitted
          exact List.mem_flatMap.mpr ⟨⟨i.val,inside⟩,ClearDemands.fin_mem _,
            List.mem_map.mpr ⟨child,member,rfl⟩⟩
        have frame := outside_slot_frame (old ⟨i.val,inside⟩) (src ⟨i.val,inside⟩)
          (permit.step (.fixed i)) child absent
        have before : (Value.fixed old).find (.cons (.fixed i) .nil) =
            some ((old ⟨i.val,inside⟩).getD (Value.dflt E)) := by
          simp only [Value.find,Path.read,Step.get,dif_pos inside,Option.bind_some]
        have after : (recursiveCopy (.fixed old) (.fixed src)).find (.cons (.fixed i) .nil) =
            some ((recursiveSlot (old ⟨i.val,inside⟩) (src ⟨i.val,inside⟩)).getD (Value.dflt E)) := by
          simp only [recursiveCopy,fixedView,Value.find,Path.read,Step.get,dif_pos inside,Option.bind_some]
        constructor
        · rw [Query.read_prefix _ _ _ _ after,Query.read_prefix _ _ _ _ before]
          exact frame.1
        · rw [Query.compatible_prefix _ _ _ _ after,Query.compatible_prefix _ _ _ _ before]
          exact frame.2.1
      · apply ClearDemands.prefix_find_frame _ _ (.cons (.fixed i) .nil) child
        simp only [recursiveCopy,Value.find,Path.read,Step.get,dif_neg inside,Option.bind_none]
    cases q with
    | word path => cases path with | cons step rest => cases step with
      | fixed i => exact childFrame i (.word rest) outside
    | length path => cases path with | cons step rest => cases step with
      | fixed i => exact childFrame i (.length rest) outside
  | _, .mapping old, .mapping src, _, _, _ => ⟨rfl,rfl⟩

/-- Slot frames additionally expose why a fresh OLD absent slot cannot hide a
successful default query. This is the needed old-None/new-Some boundary. -/
theorem outside_slot_frame {n : Nat} {G : Schema n} :
    {T : TypeGraph.Ty n} → (old src : Slot G T) → CopyPermit G T →
    (q : Query G T) → q ∉ slotDemands old src →
    (q.read ((recursiveSlot old src).getD (Value.dflt _)) = q.read (old.getD (Value.dflt _))) ∧
    (q.compatible ((recursiveSlot old src).getD (Value.dflt _)) = q.compatible (old.getD (Value.dflt _))) ∧
    (old = .absent → q.read (Value.dflt _) = none)
  | _, .absent, .absent, permit, q, outside =>
    ⟨rfl,rfl,fun _ => absent_outside_none permit .absent q outside⟩
  | _, .present old, .absent, _, q, outside =>
    let frame := ClearDemands.outside_frame old q outside
    ⟨frame.1,frame.2,fun impossible => Slot.noConfusion impossible⟩
  | _, .absent, .present src, permit, q, outside => by
    have childOutside : q ∉ demands (Value.dflt _) src := by
      intro member
      exact outside (List.mem_append.mpr (Or.inr member))
    have frame := outside_frame (Value.dflt _) src permit q childOutside
    exact ⟨frame.1,frame.2,fun _ => absent_outside_none permit (.present src) q outside⟩
  | _, .present old, .present src, permit, q, outside =>
    let frame := outside_frame old src permit q outside
    ⟨frame.1,frame.2,fun impossible => Slot.noConfusion impossible⟩
end

private theorem writes_outside (updates : List (Solidity.Storage.Loc × Semantics.Word))
    (store : Store) (location : Solidity.Storage.Loc)
    (outside : ∀ op ∈ updates, location ≠ op.1) :
    (updates.foldl (fun w op => write w op.1 op.2) store) location = store location := by
  induction updates generalizing store with
  | nil => rfl
  | cons op rest ih =>
    exact (ih (write store op.1 op.2)
      (fun next member => outside next (List.mem_cons_of_mem _ member))).trans
      (write_other store op.1 location op.2 (outside op List.mem_cons_self))

/-- Apply the recursive operation footprint to the PUBLIC owner relation.
Only omitted/separated observations are certified here; payload correctness of
writes INSIDE the footprint is a separate unfinished copy realization obligation. -/
theorem represented_outside {n : Nat} {G : Schema n} {T : TypeGraph.Ty n}
    (old src : Value G T) (permit : CopyPermit G T) (queries : List (Query G T))
    (base : Solidity.Storage.Loc) (store : Store)
    (before : Represented old queries base store)
    (updates : List (Solidity.Storage.Loc × Semantics.Word))
    (generated : ∀ op ∈ updates, ∃ d ∈ demands old src, op.1 = d.location base)
    (separate : ∀ q ∈ queries, ∀ d ∈ demands old src, q.location base ≠ d.location base) :
    Represented (recursiveCopy old src) queries base
      (updates.foldl (fun w op => write w op.1 op.2) store) := by
  intro q member
  obtain ⟨supported,compatible,related⟩ := before q member
  have omitted : q ∉ demands old src := fun inside => separate q member q inside rfl
  have frame := outside_frame old src permit q omitted
  refine ⟨supported,?_,?_⟩
  · rw [frame.2]
    exact compatible
  · intro word observed
    rw [writes_outside updates store (q.location base) (by
      intro op inside
      obtain ⟨d,inDemands,same⟩ := generated op inside
      rw [same]
      exact separate q member d inDemands)]
    exact related word (frame.1.symm.trans observed)

/-- Exact finite-run transport and read agreement for separated represented
observations under writes actually located inside the generated copy footprint.
No assumption of desired postrepresentation, numeric/global hash injection or
correct INSIDE copy payload is hidden in this outside-frame certificate. -/
theorem outside_numeric {n N L R : Nat} {G : Schema n} {T : TypeGraph.Ty n}
    (old src : Value G T) (permit : CopyPermit G T) (queries : List (Query G T))
    (base : Solidity.Storage.Loc) (store : Store) (machine : WordStore)
    {hash : Solidity.Storage.Pre → Nat} {P : List Solidity.Storage.Pre}
    {locations : List Solidity.Storage.Loc} (run : FiniteRun N L R hash P locations)
    (before : Represented old queries base store)
    (initial : Transport N hash locations store machine)
    (updates : List (Solidity.Storage.Loc × Semantics.Word))
    (generated : ∀ op ∈ updates, ∃ d ∈ demands old src, op.1 = d.location base)
    (covered : ∀ d ∈ demands old src, d.location base ∈ locations)
    (observed : ∀ q ∈ queries, q.location base ∈ locations)
    (separate : ∀ q ∈ queries, ∀ d ∈ demands old src, q.location base ≠ d.location base) :
    let afterStore := updates.foldl (fun w op => write w op.1 op.2) store
    let afterMachine := updates.foldl (fun m op => writeWord m (op.1.word N hash) op.2) machine
    Represented (recursiveCopy old src) queries base afterStore ∧
    Transport N hash locations afterStore afterMachine ∧
    ∀ q ∈ queries, ∀ word, q.read (recursiveCopy old src) = some word →
      afterMachine ((q.location base).word N hash) = word := by
  have related := represented_outside old src permit queries base store before updates generated separate
  have transported := transport_sequence run initial updates (by
    intro op member
    obtain ⟨d,inside,same⟩ := generated op member
    rw [same]
    exact covered d inside)
  refine ⟨related,transported,?_⟩
  intro q member word read
  exact related.numeric transported q member (observed q member) word read

/-- Captured actual path copy lifts the newly proved recursive footprint frame
through arbitrary existing typed prefixes using the published owner relation. -/
theorem copyAt_outside_represented {n : Nat} {G : Schema n} {A T : TypeGraph.Ty n}
    (root result : Value G A) (dst source : TypeGraph.Path G A T)
    (old snapshot : Value G T) (permit : CopyPermit G T)
    (readDst : root.find dst = some old) (readSrc : root.find source = some snapshot)
    (copied : recursiveCopyAt root dst source = some result)
    (queries : List (Query G T)) (base : Solidity.Storage.Loc) (store : Store)
    (supported : PathSupported dst)
    (before : Represented old queries (pathLoc dst base) store)
    (updates : List (Solidity.Storage.Loc × Semantics.Word))
    (generated : ∀ op ∈ updates, ∃ d ∈ demands old snapshot, op.1 = d.location (pathLoc dst base))
    (separate : ∀ q ∈ queries, ∀ d ∈ demands old snapshot,
      q.location (pathLoc dst base) ≠ d.location (pathLoc dst base)) :
    Represented result (queries.map (Query.prefix dst)) base
      (updates.foldl (fun w op => write w op.1 op.2) store) :=
  Represented.prefix dst (recursiveCopyAt_readback root result dst source old snapshot readDst readSrc copied)
    supported (represented_outside old snapshot permit queries (pathLoc dst base) store before
      updates generated separate)

/-- One demand-generation iteration at the actual old/new runtime lengths. -/
def arrayStep {n : Nat} {G : Schema n} {E : TypeGraph.Ty n}
    (oe : Extent) (ol : Index) (os : Fin oe.val → Slot G E)
    (ne : Extent) (nl : Index) (nh : nl.val ≤ ne.val) (ns : Fin ne.val → Slot G E)
    (i : Fin (max ol.val nl.val)) : List (Query G (.array E)) :=
  let child := if h : i.val < nl.val then slotDemands (oldSlot oe os i.val)
      (ns ⟨i.val,Nat.lt_of_lt_of_le h nh⟩)
    else ClearDemands.slotDemands (oldSlot oe os i.val)
  child.map (Query.prefix (.cons (.index ⟨i.val,by
    have a := ol.isLt; have b := nl.isLt; have h := i.isLt; omega⟩) .nil))

/-- Processed query prefix; this visits runtime indices, not a depth bound. -/
def arrayPrefix {n : Nat} {G : Schema n} {E : TypeGraph.Ty n}
    (oe : Extent) (ol : Index) (os : Fin oe.val → Slot G E)
    (ne : Extent) (nl : Index) (nh : nl.val ≤ ne.val) (ns : Fin ne.val → Slot G E)
    (count : Nat) : List (Query G (.array E)) :=
  ((List.finRange (max ol.val nl.val)).take count).flatMap (arrayStep oe ol os ne nl nh ns)

/-- Complete enumeration is exactly prefix plus unvisited suffix and LAST
header. Restart preserves the original captured old/source slot functions. -/
theorem array_restart {n : Nat} {G : Schema n} {E : TypeGraph.Ty n}
    (oe : Extent) (ol : Index) (oh : ol.val ≤ oe.val) (os : Fin oe.val → Slot G E)
    (ne : Extent) (nl : Index) (nh : nl.val ≤ ne.val) (ns : Fin ne.val → Slot G E)
    (count : Nat) :
    demands (.array oe ol oh os) (.array ne nl nh ns) =
      arrayPrefix oe ol os ne nl nh ns count ++
      (((List.finRange (max ol.val nl.val)).drop count).flatMap (arrayStep oe ol os ne nl nh ns) ++
        [.length .nil]) := by
  change (List.finRange (max ol.val nl.val)).flatMap (arrayStep oe ol os ne nl nh ns) ++ _ = _
  rw [← List.take_append_drop count (List.finRange (max ol.val nl.val))]
  simp only [List.flatMap_append,List.append_assoc,arrayPrefix]
  rw [List.take_append_drop]

/-- One more runtime iteration appends EXACTLY that index's demands. -/
theorem array_progress {n : Nat} {G : Schema n} {E : TypeGraph.Ty n}
    (oe : Extent) (ol : Index) (os : Fin oe.val → Slot G E)
    (ne : Extent) (nl : Index) (nh : nl.val ≤ ne.val) (ns : Fin ne.val → Slot G E)
    (count : Nat) (inside : count < max ol.val nl.val) :
    arrayPrefix oe ol os ne nl nh ns (count+1) =
      arrayPrefix oe ol os ne nl nh ns count ++ arrayStep oe ol os ne nl nh ns ⟨count,inside⟩ := by
  unfold arrayPrefix
  rw [List.take_succ_eq_append_getElem (by simpa only [List.length_finRange] using inside)]
  simp only [List.flatMap_append,List.flatMap_singleton,List.getElem_finRange]
  rfl

/-- Runtime-index membership distinguishes processed from unvisited iterations. -/
theorem prefix_indices {count total : Nat} (i : Fin total) :
    i ∈ (List.finRange total).take count ↔ i.val < count := by
  constructor
  · intro member
    obtain ⟨j,bound,same⟩ := List.mem_take_iff_getElem.mp member
    have value : i.val = j := by
      rw [← same,List.getElem_finRange]
      rfl
    omega
  · intro inside
    apply List.mem_take_iff_getElem.mpr
    refine ⟨i.val,?_,?_⟩
    · simp only [List.length_finRange]
      exact Nat.lt_min.mpr ⟨inside,i.isLt⟩
    · rw [List.getElem_finRange]
      exact Fin.ext rfl

/-- info: 'Solidity.Backend.StorageOps.CopyDemands.demands' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms demands
/-- info: 'Solidity.Backend.StorageOps.CopyDemands.slotDemands' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms slotDemands
/-- info: 'Solidity.Backend.StorageOps.CopyDemands.absent_absent' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms absent_absent
/-- info: 'Solidity.Backend.StorageOps.CopyDemands.absent_present' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms absent_present
/-- info: 'Solidity.Backend.StorageOps.CopyDemands.present_absent' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms present_absent
/-- info: 'Solidity.Backend.StorageOps.CopyDemands.present_present' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms present_present
/-- info: 'Solidity.Backend.StorageOps.CopyDemands.mapping_barrier' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms mapping_barrier
/-- info: 'Solidity.Backend.StorageOps.CopyDemands.absent_outside_none' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms absent_outside_none
/-- info: 'Solidity.Backend.StorageOps.CopyDemands.outside_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms outside_frame
/-- info: 'Solidity.Backend.StorageOps.CopyDemands.outside_slot_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms outside_slot_frame
/-- info: 'Solidity.Backend.StorageOps.CopyDemands.represented_outside' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms represented_outside
/-- info: 'Solidity.Backend.StorageOps.CopyDemands.outside_numeric' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms outside_numeric
/-- info: 'Solidity.Backend.StorageOps.CopyDemands.copyAt_outside_represented' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms copyAt_outside_represented
/-- info: 'Solidity.Backend.StorageOps.CopyDemands.arrayStep' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms arrayStep
/-- info: 'Solidity.Backend.StorageOps.CopyDemands.arrayPrefix' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms arrayPrefix
/-- info: 'Solidity.Backend.StorageOps.CopyDemands.array_restart' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms array_restart
/-- info: 'Solidity.Backend.StorageOps.CopyDemands.array_progress' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms array_progress
/-- info: 'Solidity.Backend.StorageOps.CopyDemands.prefix_indices' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms prefix_indices

/-- info: 'Solidity.Backend.StorageOps.CopyDemands.read_none_compatible' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms read_none_compatible
/-- info: 'Solidity.Backend.StorageOps.CopyDemands.prefix_none' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms prefix_none

end Solidity.Backend.StorageOps.CopyDemands
