import Solidity.Backend.StorageOps.CopyReadback

/-! Independent copied-output proof infrastructure over the actual generated
query logs. Family enumeration is operation-side; owner layouts are unchanged. -/
namespace Solidity.Backend.StorageOps.CopyOutput
open TypeGraph Solidity.Storage Solidity.Storage.Representation Solidity.Storage.Representation.Graph
open CopyReadback

private theorem family_frame {n : Nat} {G : Schema n} {T : TypeGraph.Ty n} {I : Type}
    (q : Query G T) (items : List I) (logs : I → List (Query G T × Semantics.Word))
    (initial : Semantics.Word)
    (frame : ∀ i ∈ items, ∀ word, traceWord q (logs i) word = word) :
    traceWord q (items.flatMap logs) initial = initial := by
  induction items generalizing initial with
  | nil => rfl
  | cons i rest ih =>
    rw [List.flatMap_cons,traceWord_append,frame i List.mem_cons_self initial]
    exact ih initial (fun j member => frame j (List.mem_cons_of_mem _ member))

/-- The actual child write family factors at its unique enumerated selector.
Neither child readback nor any source/representation theorem is assumed. -/
theorem family_one {n : Nat} {G : Schema n} {T : TypeGraph.Ty n} {I : Type}
    (q : Query G T) (items : List I) (logs : I → List (Query G T × Semantics.Word))
    (selected : I) (initial : Semantics.Word) (unique : items.Nodup) (member : selected ∈ items)
    (others : ∀ i ∈ items, i ≠ selected → ∀ word, traceWord q (logs i) word = word) :
    traceWord q (items.flatMap logs) initial = traceWord q (logs selected) initial := by
  classical
  induction items generalizing initial with
  | nil => cases member
  | cons i rest ih =>
    have distinct := List.nodup_cons.mp unique
    rcases List.mem_cons.mp member with same | later
    · subst i
      rw [List.flatMap_cons,traceWord_append]
      apply family_frame
      intro j inside
      exact others j (List.mem_cons_of_mem _ inside) (by
        intro same
        subst j
        exact distinct.1 inside)
    · have different : i ≠ selected := by
        intro same
        subst i
        exact distinct.1 later
      rw [List.flatMap_cons,traceWord_append,others i List.mem_cons_self different initial]
      exact ih initial distinct.2 later (fun j inside => others j (List.mem_cons_of_mem _ inside))

private theorem position_eq {n : Nat} {fs : List (Name × TypeGraph.Ty n)}
    (a b : Sigma (fun T => Field fs T)) (same : a.2.toNat = b.2.toNat) : a = b := by
  rcases a with ⟨A,a⟩
  rcases b with ⟨B,b⟩
  have types := Field.type_eq a b same
  subst B
  have fields := Field.eq_of_toNat_eq a b same
  subst b
  rfl

/-- Existing heterogeneous field enumeration has no duplicate selectors. -/
theorem positions_nodup {n : Nat} (fs : List (Name × TypeGraph.Ty n)) :
    (ClearDemands.positions fs).Nodup := by
  induction fs with
  | nil => exact List.nodup_nil
  | cons f rest ih =>
    apply List.nodup_cons.mpr
    constructor
    · intro member
      obtain ⟨p,_,same⟩ := List.mem_map.mp member
      have indexes := congrArg (fun p => p.2.toNat) same
      change p.2.toNat + 1 = 0 at indexes
      omega
    · exact List.Pairwise.map _ (fun a b different same => different (position_eq a b (by
        have indexes := congrArg (fun p => p.2.toNat) same
        change a.2.toNat + 1 = b.2.toNat + 1 at indexes
        omega))) ih

/-- Runtime index enumeration is unique for every finite intrinsic length. -/
theorem indices_nodup (count : Nat) : (List.finRange count).Nodup := by
  induction count with
  | zero => exact List.nodup_nil
  | succ count ih =>
    rw [List.finRange_succ]
    apply List.nodup_cons.mpr
    constructor
    · intro member
      obtain ⟨i,_,same⟩ := List.mem_map.mp member
      have indexes := congrArg Fin.val same
      change i.val + 1 = 0 at indexes
      omega
    · exact List.Pairwise.map Fin.succ (fun a b different same => different (Fin.ext (by
        have indexes := congrArg Fin.val same
        change a.val + 1 = b.val + 1 at indexes
        omega))) ih

/-- The actual node generator factors into the selected heterogeneous child
trace. Other members are proved frames, not assumed preservation results. -/
theorem node_trace {n : Nat} {G : Schema n} {i : Fin n} {T : TypeGraph.Ty n}
    (old src : Fields G (G.fields i)) (position : Field (G.fields i) T)
    (q : Query G T) (reader : Query G (.node i) → Semantics.Word) (initial : Semantics.Word) :
    traceWord (q.prefix (.cons (.field position) .nil))
      (CopyWrites.queryWrites (.node old) (.node src) reader) initial =
    traceWord q (CopyWrites.queryWrites (old position) (src position)
      (fun d => reader (d.prefix (.cons (.field position) .nil)))) initial := by
  let logs := fun (p : Sigma (fun T => Field (G.fields i) T)) =>
    CopyWrites.prefixWrites (.cons (.field p.2) .nil)
      (CopyWrites.queryWrites (old p.2) (src p.2) (fun d => reader (d.prefix (.cons (.field p.2) .nil))))
  have isolated := family_one (q.prefix (.cons (.field position) .nil))
    (ClearDemands.positions (G.fields i)) logs ⟨T,position⟩ initial
    (positions_nodup _) (ClearDemands.positions_mem position) (by
      intro p _ different word
      apply fields_trace position p.2
      intro same
      exact different (position_eq p ⟨T,position⟩ same.symm))
  exact isolated.trans (prefix_trace (.cons (.field position) .nil) q _ initial)

/-- The actual fixed-array generator factors at any in-extent index, for
arbitrary aggregate/recursive element types and runtime slot presence. -/
theorem fixed_trace {n : Nat} {G : Schema n} {E : TypeGraph.Ty n} {m : FixedSize}
    (old src : Fin m.val → Slot G E) (index : Fin m.val)
    (q : Query G E) (reader : Query G (.fixed E m) → Semantics.Word) (initial : Semantics.Word) :
    let step : Step G (.fixed E m) E := .fixed ⟨index.val,Nat.lt_trans index.isLt m.property.2⟩
    traceWord (q.prefix (.cons step .nil))
      (CopyWrites.queryWrites (.fixed old) (.fixed src) reader) initial =
    traceWord q (CopyWrites.slotWrites (old index) (src index)
      (fun d => reader (d.prefix (.cons step .nil)))) initial := by
  let step := fun (j : Fin m.val) => Step.fixed (G := G) (E := E) (m := m)
    ⟨j.val,Nat.lt_trans j.isLt m.property.2⟩
  let logs := fun (j : Fin m.val) => CopyWrites.prefixWrites (.cons (step j) .nil)
    (CopyWrites.slotWrites (old j) (src j) (fun d => reader (d.prefix (.cons (step j) .nil))))
  have isolated := family_one (q.prefix (.cons (step index) .nil)) (List.finRange m.val) logs index initial
    (indices_nodup _) (ClearDemands.fin_mem index) (by
      intro j _ different word
      apply CopyReadback.fixed_trace
      intro same
      exact different (Fin.ext same.symm))
  exact isolated.trans (prefix_trace (.cons (step index) .nil) q _ initial)

private theorem array_header_frame {n : Nat} {G : Schema n} {E : TypeGraph.Ty n}
    (index : Index) (q : Query G E) (header initial : Semantics.Word) :
    traceWord (q.prefix (.cons (.index index) .nil)) [(.length .nil,header)] initial = initial := by
  apply traceWord_outside
  intro op member
  have same := List.mem_singleton.mp member
  subst op
  cases q <;> intro same <;> cases same

/-- At every runtime array level, one processed index factors through the
ACTUAL live-copy or stale-tail-clear child trace. Header-last is a frame for
this nested query. No fixed length/depth cutoff or post-readback premise. -/
theorem array_trace {n : Nat} {G : Schema n} {E : TypeGraph.Ty n}
    (oe : Extent) (ol : Index) (oh : ol.val ≤ oe.val) (os : Fin oe.val → Slot G E)
    (ne : Extent) (nl : Index) (nh : nl.val ≤ ne.val) (ns : Fin ne.val → Slot G E)
    (index : Index) (processed : index.val < max ol.val nl.val)
    (q : Query G E) (reader : Query G (.array E) → Semantics.Word) (initial : Semantics.Word) :
    let path : TypeGraph.Path G (.array E) E := .cons (.index index) .nil
    traceWord (q.prefix path) (CopyWrites.queryWrites (.array oe ol oh os) (.array ne nl nh ns) reader) initial =
    traceWord q (if live : index.val < nl.val then
      CopyWrites.slotWrites (oldSlot oe os index.val) (ns ⟨index.val,Nat.lt_of_lt_of_le live nh⟩)
        (fun d => reader (d.prefix path))
      else CopyWrites.zeros (ClearDemands.slotDemands (oldSlot oe os index.val))) initial := by
  let step := fun (j : Fin (max ol.val nl.val)) => Step.index (G := G) (E := E)
    ⟨j.val,by have h := j.isLt; have a := ol.isLt; have b := nl.isLt; omega⟩
  let child := fun (j : Fin (max ol.val nl.val)) =>
    if live : j.val < nl.val then
      CopyWrites.slotWrites (oldSlot oe os j.val) (ns ⟨j.val,Nat.lt_of_lt_of_le live nh⟩)
        (fun d => reader (d.prefix (.cons (step j) .nil)))
    else CopyWrites.zeros (ClearDemands.slotDemands (oldSlot oe os j.val))
  let logs := fun j => CopyWrites.prefixWrites (.cons (step j) .nil) (child j)
  have isolated := family_one (q.prefix (.cons (.index index) .nil))
    (List.finRange (max ol.val nl.val)) logs ⟨index.val,processed⟩ initial
    (indices_nodup _) (ClearDemands.fin_mem _) (by
      intro j _ different word
      apply CopyReadback.indices_trace
      intro same
      exact different (Fin.ext same.symm))
  change traceWord (q.prefix (.cons (.index index) .nil))
    ((List.finRange (max ol.val nl.val)).flatMap logs ++ [(.length .nil,reader (.length .nil))]) initial = _
  rw [traceWord_append,array_header_frame]
  exact isolated.trans (prefix_trace (.cons (.index index) .nil) q _ initial)

/-- Every unprocessed index is a frame of the ACTUAL generated trace,
including retained older shadows and malformed out-of-extent queries. -/
theorem array_trace_outside {n : Nat} {G : Schema n} {E : TypeGraph.Ty n}
    (oe : Extent) (ol : Index) (oh : ol.val ≤ oe.val) (os : Fin oe.val → Slot G E)
    (ne : Extent) (nl : Index) (nh : nl.val ≤ ne.val) (ns : Fin ne.val → Slot G E)
    (index : Index) (outside : max ol.val nl.val ≤ index.val)
    (q : Query G E) (reader : Query G (.array E) → Semantics.Word) (initial : Semantics.Word) :
    traceWord (q.prefix (.cons (.index index) .nil))
      (CopyWrites.queryWrites (.array oe ol oh os) (.array ne nl nh ns) reader) initial = initial := by
  let step := fun (j : Fin (max ol.val nl.val)) => Step.index (G := G) (E := E)
    ⟨j.val,by have h := j.isLt; have a := ol.isLt; have b := nl.isLt; omega⟩
  let child := fun (j : Fin (max ol.val nl.val)) =>
    if live : j.val < nl.val then
      CopyWrites.slotWrites (oldSlot oe os j.val) (ns ⟨j.val,Nat.lt_of_lt_of_le live nh⟩)
        (fun d => reader (d.prefix (.cons (step j) .nil)))
    else CopyWrites.zeros (ClearDemands.slotDemands (oldSlot oe os j.val))
  let logs := fun j => CopyWrites.prefixWrites (.cons (step j) .nil) (child j)
  change traceWord (q.prefix (.cons (.index index) .nil))
    ((List.finRange (max ol.val nl.val)).flatMap logs ++ [(.length .nil,reader (.length .nil))]) initial = _
  rw [traceWord_append,array_header_frame]
  apply family_frame
  intro j _ word
  apply CopyReadback.indices_trace
  intro same
  change index.val = j.val at same
  have h := j.isLt
  omega

/-- The actual zero trace matches every successful independent clear read.
Unwritten older observations retain precisely their OLD successful word;
failed old reads impose no cell-zero premise. -/
theorem clear_output {n : Nat} {G : Schema n} {T : TypeGraph.Ty n}
    (old : Value G T) (q : Query G T) (initial : Semantics.Word)
    (before : ∀ word, q.read old = some word → initial = word)
    (word : Semantics.Word) (observed : q.read (recursiveClear old) = some word) :
    traceWord q (CopyWrites.zeros (ClearDemands.demands old)) initial = word := by
  classical
  by_cases member : q ∈ ClearDemands.demands old
  · have same := ClearDemands.listed_zero old q member
    have equal : ClearDemands.zero = word := Option.some.inj (same.symm.trans observed)
    rw [zero_member q _ initial member]
    exact equal
  · have frame := (ClearDemands.outside_frame old q member).1
    rw [frame] at observed
    have actual := traceWord_outside q (CopyWrites.zeros (ClearDemands.demands old)) initial (by
      intro op inside
      obtain ⟨d,demandMember,same⟩ := List.mem_map.mp inside
      subst op
      intro equal
      change d = q at equal
      subst d
      exact member demandMember)
    exact actual.trans (before word observed)

/-- Clearing an absent retained slot performs no writes. Its successful
DEFAULT observations therefore require OLD read agreement, unlike fresh slot
initialization. This distinction is essential for stale-tail clearing. -/
theorem clear_slot_output {n : Nat} {G : Schema n} {T : TypeGraph.Ty n}
    (old : Slot G T) (q : Query G T) (initial : Semantics.Word)
    (before : ∀ word, q.read (old.getD (Value.dflt T)) = some word → initial = word)
    (word : Semantics.Word)
    (observed : q.read ((recursiveClearSlot old).getD (Value.dflt T)) = some word) :
    traceWord q (CopyWrites.zeros (ClearDemands.slotDemands old)) initial = word := by
  cases old with
  | absent => exact before word observed
  | present value => exact clear_output value q initial before word observed

/-- info: 'Solidity.Backend.StorageOps.CopyOutput.family_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms family_one
/-- info: 'Solidity.Backend.StorageOps.CopyOutput.positions_nodup' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms positions_nodup
/-- info: 'Solidity.Backend.StorageOps.CopyOutput.indices_nodup' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms indices_nodup
/-- info: 'Solidity.Backend.StorageOps.CopyOutput.node_trace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms node_trace
/-- info: 'Solidity.Backend.StorageOps.CopyOutput.fixed_trace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms fixed_trace
/-- info: 'Solidity.Backend.StorageOps.CopyOutput.array_trace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms array_trace
/-- info: 'Solidity.Backend.StorageOps.CopyOutput.array_trace_outside' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms array_trace_outside
/-- info: 'Solidity.Backend.StorageOps.CopyOutput.clear_output' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms clear_output
/-- info: 'Solidity.Backend.StorageOps.CopyOutput.clear_slot_output' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms clear_slot_output

end Solidity.Backend.StorageOps.CopyOutput
