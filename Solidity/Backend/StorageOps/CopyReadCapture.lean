import Solidity.Backend.StorageOps.CopyWrites

/-! Finite captured SOURCE read footprint for actual recursive numeric writes.
Reuse the existing source clear-demand enumeration; no new path/value/state.
Finite capture caches use the existing numeric WordStore and original destination
state. Emitted memory/storage loops and ordinary Source are not supplied. -/
namespace Solidity.Backend.StorageOps.CopyReadCapture
open TypeGraph Solidity.Storage Solidity.Storage.Representation Solidity.Storage.Representation.Graph

mutual
/-- Every source query the numeric reader can need is an actual successful
independent graph read. Implicit absent defaults are handled as constant writes. -/
theorem source_read {n : Nat} {G : Schema n} :
    {T : TypeGraph.Ty n} → (src : Value G T) →
    ∀ q ∈ ClearDemands.demands src, ∃ word, q.read src = some word
  | _, .prim value, q, member => by
    simp only [ClearDemands.demands,List.mem_singleton] at member
    subst q
    exact ⟨PrimTy.toWord value,rfl⟩
  | _, @Value.node _ _ i fields, q, member => by
    change q ∈ (ClearDemands.positions (G.fields i)).flatMap (fun p =>
      (ClearDemands.demands (fields p.2)).map (Query.prefix (.cons (.field p.2) .nil))) at member
    obtain ⟨p,_,inside⟩ := List.mem_flatMap.mp member
    obtain ⟨child,childMember,same⟩ := List.mem_map.mp inside
    subst q
    rw [Query.read_prefix _ _ (.cons (.field p.2) .nil) child rfl]
    exact source_read (fields p.2) child childMember
  | _, @Value.array _ _ E extent length bound slots, q, member => by
    change q ∈ (List.finRange length.val).flatMap (fun i =>
      (ClearDemands.slotDemands (slots ⟨i.val,Nat.lt_of_lt_of_le i.isLt bound⟩)).map
        (Query.prefix (.cons (.index ⟨i.val,Nat.lt_trans i.isLt length.isLt⟩) .nil))) ++ [.length .nil] at member
    rcases List.mem_append.mp member with inside | header
    · obtain ⟨i,_,inside⟩ := List.mem_flatMap.mp inside
      obtain ⟨child,childMember,same⟩ := List.mem_map.mp inside
      subst q
      have found : (Value.array extent length bound slots).find
          (.cons (.index ⟨i.val,Nat.lt_trans i.isLt length.isLt⟩) .nil) =
          some ((slots ⟨i.val,Nat.lt_of_lt_of_le i.isLt bound⟩).getD (Value.dflt E)) := by
        simp only [Value.find,Path.read,Step.get,dif_pos (Nat.lt_of_lt_of_le i.isLt bound),Option.bind_some]
      rw [Query.read_prefix _ _ _ child found]
      exact source_slot_read _ child childMember
    · have same : q = .length .nil := List.mem_singleton.mp header
      subst q
      exact ⟨lengthWord length.val length.isLt,rfl⟩
  | _, @Value.fixed _ _ E m slots, q, member => by
    change q ∈ (List.finRange m.val).flatMap (fun i =>
      (ClearDemands.slotDemands (slots i)).map (Query.prefix
        (.cons (.fixed ⟨i.val,Nat.lt_trans i.isLt m.property.2⟩) .nil))) at member
    obtain ⟨i,_,inside⟩ := List.mem_flatMap.mp member
    obtain ⟨child,childMember,same⟩ := List.mem_map.mp inside
    subst q
    have found : (Value.fixed slots).find
        (.cons (.fixed ⟨i.val,Nat.lt_trans i.isLt m.property.2⟩) .nil) =
        some ((slots i).getD (Value.dflt E)) := by
      simp only [Value.find,Path.read,Step.get,dif_pos i.isLt,Option.bind_some]
    rw [Query.read_prefix _ _ _ child found]
    exact source_slot_read _ child childMember
  | _, .mapping _, _, member => by cases member

theorem source_slot_read {n : Nat} {G : Schema n} :
    {T : TypeGraph.Ty n} → (src : Slot G T) →
    ∀ q ∈ ClearDemands.slotDemands src, ∃ word, q.read (src.getD (Value.dflt _)) = some word
  | _, .absent, _, member => by cases member
  | _, .present value, q, member => source_read value q member
end

mutual
/-- Exact finite reader dependence: changing numeric words outside the EXISTING
source demand set cannot affect the generated write log, even with overlap. -/
theorem reader_congr {n : Nat} {G : Schema n} :
    {T : TypeGraph.Ty n} → (old src : Value G T) →
    (left right : Query G T → Semantics.Word) →
    (∀ q ∈ ClearDemands.demands src, left q = right q) →
    CopyWrites.queryWrites old src left = CopyWrites.queryWrites old src right
  | _, @Value.prim _ _ p old, .prim src, left, right, agree => by
    change [((.word .nil : Query G (.prim p)),left (.word .nil))] =
      [((.word .nil : Query G (.prim p)),right (.word .nil))]
    rw [agree (.word .nil) List.mem_cons_self]
  | _, @Value.node _ _ i old, .node src, left, right, agree => by
    change (ClearDemands.positions (G.fields i)).flatMap (fun p =>
      CopyWrites.prefixWrites (.cons (.field p.2) .nil) (CopyWrites.queryWrites (old p.2) (src p.2)
        (fun q => left (q.prefix (.cons (.field p.2) .nil))))) = _
    apply congrArg (fun f => (ClearDemands.positions (G.fields i)).flatMap f)
    funext p
    apply congrArg (CopyWrites.prefixWrites (.cons (.field p.2) .nil))
    apply reader_congr
    intro q member
    apply agree
    exact List.mem_flatMap.mpr ⟨p,ClearDemands.positions_mem p.2,
      List.mem_map.mpr ⟨q,member,rfl⟩⟩
  | _, @Value.array _ _ E oe ol oh os, .array ne nl nh ns, left, right, agree => by
    change (List.finRange (max ol.val nl.val)).flatMap (fun (i : Fin (max ol.val nl.val)) =>
      let path : TypeGraph.Path G (.array E) E := .cons (.index ⟨i.val,by
        have h := i.isLt; have a := ol.isLt; have b := nl.isLt; omega⟩) .nil
      CopyWrites.prefixWrites path (if h : i.val < nl.val then
        CopyWrites.slotWrites (oldSlot oe os i.val) (ns ⟨i.val,Nat.lt_of_lt_of_le h nh⟩)
          (fun q => left (q.prefix path))
        else CopyWrites.zeros (ClearDemands.slotDemands (oldSlot oe os i.val)))) ++
      [((.length .nil : Query G (.array E)),left (.length .nil))] = _
    rw [agree (.length .nil) (List.mem_append.mpr (Or.inr List.mem_cons_self))]
    apply congrArg (fun (xs : List (Query G (.array E) × Semantics.Word)) =>
      xs ++ [(Query.length (.nil : TypeGraph.Path G (.array E) (.array E)),right (.length .nil))])
    apply congrArg (fun f => (List.finRange (max ol.val nl.val)).flatMap f)
    funext i
    apply congrArg (CopyWrites.prefixWrites _)
    by_cases live : i.val < nl.val
    · simp only [dif_pos live]
      apply slot_reader_congr
      intro q member
      apply agree
      exact List.mem_append.mpr (Or.inl (List.mem_flatMap.mpr
        ⟨⟨i.val,live⟩,ClearDemands.fin_mem _,List.mem_map.mpr ⟨q,member,rfl⟩⟩))
    · simp only [dif_neg live,Value.extent,Value.slots]
  | _, @Value.fixed _ _ E m old, .fixed src, left, right, agree => by
    change (List.finRange m.val).flatMap (fun i =>
      let path := TypeGraph.Path.cons (.fixed ⟨i.val,Nat.lt_trans i.isLt m.property.2⟩) .nil
      CopyWrites.prefixWrites path (CopyWrites.slotWrites (old i) (src i) (fun q => left (q.prefix path)))) = _
    apply congrArg (fun f => (List.finRange m.val).flatMap f)
    funext i
    apply congrArg (CopyWrites.prefixWrites _)
    apply slot_reader_congr
    intro q member
    apply agree
    exact List.mem_flatMap.mpr ⟨i,ClearDemands.fin_mem _,List.mem_map.mpr ⟨q,member,rfl⟩⟩
  | _, .mapping old, .mapping src, _, _, _ => rfl

theorem slot_reader_congr {n : Nat} {G : Schema n} :
    {T : TypeGraph.Ty n} → (old src : Slot G T) →
    (left right : Query G T → Semantics.Word) →
    (∀ q ∈ ClearDemands.slotDemands src, left q = right q) →
    CopyWrites.slotWrites old src left = CopyWrites.slotWrites old src right
  | _, old, .absent, _, _, _ => rfl
  | _, old, .present src, left, right, agree => by
    change _ ++ CopyWrites.queryWrites (old.getD (Value.dflt _)) src left =
      _ ++ CopyWrites.queryWrites (old.getD (Value.dflt _)) src right
    rw [reader_congr (old.getD (Value.dflt _)) src left right agree]
end

/-- Source word provenance uses the PUBLIC independent graph relation and OLD
numeric transport, not a desired copy preservation premise. -/
theorem represented_reads {n N : Nat} {G : Schema n} {T : TypeGraph.Ty n}
    (src : Value G T) (source : Solidity.Storage.Loc) (store : Store) (machine : WordStore)
    (hash : Solidity.Storage.Pre → Nat) (locations : List Solidity.Storage.Loc)
    (before : Represented src (ClearDemands.demands src) source store)
    (initial : Transport N hash locations store machine)
    (covered : ∀ q ∈ ClearDemands.demands src, q.location source ∈ locations) :
    ∀ q ∈ ClearDemands.demands src,
      machine ((q.location source).word N hash) = (q.read src).getD ClearDemands.zero := by
  intro q member
  obtain ⟨word,read⟩ := source_read src q member
  rw [read]
  exact before.numeric initial q member (covered q member) word read

/-- This is INPUT read provenance for actual generated writes. It is not an
inside-output representation theorem or a definition of independent source semantics. -/
theorem represented_log {n N : Nat} {G : Schema n} {T : TypeGraph.Ty n}
    (old src : Value G T) (dst source : Solidity.Storage.Loc) (store : Store) (machine : WordStore)
    (hash : Solidity.Storage.Pre → Nat) (locations : List Solidity.Storage.Loc)
    (before : Represented src (ClearDemands.demands src) source store)
    (initial : Transport N hash locations store machine)
    (covered : ∀ q ∈ ClearDemands.demands src, q.location source ∈ locations) :
    CopyWrites.updates (N := N) old src dst source hash machine =
      (CopyWrites.queryWrites old src (fun q => (q.read src).getD ClearDemands.zero)).map
        (fun op => (op.1.location dst,op.2)) := by
  unfold CopyWrites.updates
  exact congrArg (List.map (fun (op : Query G T × Semantics.Word) => (op.1.location dst,op.2)))
    (reader_congr old src _ _ (represented_reads src source store machine hash locations before initial covered))

noncomputable def addresses {n N : Nat} {G : Schema n} {T : TypeGraph.Ty n}
    (src : Value G T) (source : Solidity.Storage.Loc) (hash : Solidity.Storage.Pre → Nat) : List Nat :=
  (ClearDemands.demands src).map (fun q => (q.location source).word N hash)

/-- Materialized finite source address/word pairs, before ANY destination write. -/
def entries (sourceAddresses : List Nat) (initial : WordStore) : List (Nat × Semantics.Word) :=
  sourceAddresses.map (fun address => (address,initial address))

/-- A finite captured read cache in the EXISTING numeric WordStore, with zero
elsewhere. It is distinct from the ORIGINAL destination store. No new state type. -/
def capture (sourceAddresses : List Nat) (initial : WordStore) : WordStore :=
  (entries sourceAddresses initial).foldl (fun cache op => writeWord cache op.1 op.2)
    (fun _ => ClearDemands.zero)

private theorem fill_preserves (xs : List Nat) (initial cache : WordStore) (address : Nat)
    (already : cache address = initial address) :
    (xs.foldl (fun cache a => writeWord cache a (initial a)) cache) address = initial address := by
  induction xs generalizing cache with
  | nil => exact already
  | cons first rest ih =>
    apply ih
    by_cases same : address = first
    · subst address
      exact if_pos rfl
    · exact (if_neg same).trans already

private theorem fill_member (xs : List Nat) (initial cache : WordStore) (address : Nat)
    (member : address ∈ xs) :
    (xs.foldl (fun cache a => writeWord cache a (initial a)) cache) address = initial address := by
  induction xs generalizing cache with
  | nil => cases member
  | cons first rest ih =>
    rcases List.mem_cons.mp member with same | later
    · subst first
      exact fill_preserves rest initial (writeWord cache address (initial address)) address (if_pos rfl)
    · exact ih (writeWord cache first (initial first)) later

/-- Physical aliases and duplicates need NO injectivity assumption: all cache
entries at the same address capture the same initial raw word. -/
theorem capture_read (sourceAddresses : List Nat) (initial : WordStore) (address : Nat)
    (member : address ∈ sourceAddresses) : capture sourceAddresses initial address = initial address := by
  simp only [capture,entries,List.foldl_map]
  exact fill_member sourceAddresses initial _ address member

theorem entries_length (sourceAddresses : List Nat) (initial : WordStore) :
    (entries sourceAddresses initial).length = sourceAddresses.length := by
  simp only [entries,List.length_map]

private theorem fill_outside (xs : List Nat) (initial cache : WordStore) (address : Nat)
    (outside : address ∉ xs) :
    (xs.foldl (fun cache a => writeWord cache a (initial a)) cache) address = cache address := by
  induction xs generalizing cache with
  | nil => rfl
  | cons first rest ih =>
    have different : address ≠ first := fun same => outside (List.mem_cons.mpr (Or.inl same))
    have omitted : address ∉ rest := fun member => outside (List.mem_cons_of_mem _ member)
    exact (ih (writeWord cache first (initial first)) omitted).trans (if_neg different)

theorem capture_outside (sourceAddresses : List Nat) (initial : WordStore) (address : Nat)
    (outside : address ∉ sourceAddresses) : capture sourceAddresses initial address = ClearDemands.zero := by
  simp only [capture,entries,List.foldl_map]
  exact fill_outside sourceAddresses initial _ address outside

/-- The finite cache is observationally sufficient for the COMPLETE actual
recursive write generator; no source oracle or unbounded-store capture needed. -/
theorem captured_updates {n N : Nat} {G : Schema n} {T : TypeGraph.Ty n}
    (old src : Value G T) (dst source : Solidity.Storage.Loc)
    (hash : Solidity.Storage.Pre → Nat) (initial : WordStore) :
    CopyWrites.updates (N := N) old src dst source hash
      (capture (addresses (N := N) src source hash) initial) =
    CopyWrites.updates (N := N) old src dst source hash initial := by
  unfold CopyWrites.updates
  apply congrArg (List.map (fun (op : Query G T × Semantics.Word) => (op.1.location dst,op.2)))
  apply reader_congr
  intro q member
  exact capture_read _ initial _ (List.mem_map.mpr ⟨q,member,rfl⟩)

/-- Preload only the finite source reads, THEN execute generated writes against
original destination storage. Graph shape still supplies traversal metadata;
this is not emitted memory/storage loop code. -/
noncomputable def finiteCopy {n N : Nat} {G : Schema n} {T : TypeGraph.Ty n}
    (old src : Value G T) (dst source : Solidity.Storage.Loc)
    (hash : Solidity.Storage.Pre → Nat) (initial : WordStore) : WordStore :=
  let cached := capture (addresses (N := N) src source hash) initial
  (CopyWrites.updates (N := N) old src dst source hash cached).foldl
    (fun m op => writeWord m (op.1.word N hash) op.2) initial

/-- Actual finite-source capture realizes the checked snapshot algorithm,
including defaults, tails, older shadows and overlapping source/destination. -/
theorem finiteCopy_eq {n N : Nat} {G : Schema n} {T : TypeGraph.Ty n}
    (old src : Value G T) (dst source : Solidity.Storage.Loc)
    (hash : Solidity.Storage.Pre → Nat) (initial : WordStore) :
    finiteCopy (N := N) old src dst source hash initial =
      CopyWrites.numericCopy (N := N) old src dst source hash initial := by
  dsimp only [finiteCopy]
  rw [captured_updates]
  rfl

/-- Actual generated write logs depend only on this finite physical SOURCE
read set; destination initial stores may otherwise differ. -/
theorem updates_eq_of_reads {n N : Nat} {G : Schema n} {T : TypeGraph.Ty n}
    (old src : Value G T) (dst source : Solidity.Storage.Loc)
    (hash : Solidity.Storage.Pre → Nat) (left right : WordStore)
    (agree : ∀ address ∈ addresses (N := N) src source hash, left address = right address) :
    CopyWrites.updates (N := N) old src dst source hash left =
      CopyWrites.updates (N := N) old src dst source hash right := by
  unfold CopyWrites.updates
  apply congrArg (List.map (fun (op : Query G T × Semantics.Word) => (op.1.location dst,op.2)))
  apply reader_congr
  intro q member
  exact agree _ (List.mem_map.mpr ⟨q,member,rfl⟩)

/-- Finite capture preserves every old destination word outside the operation's
actual generated image, by the already checked numeric copy frame. -/
theorem finite_outside {n N : Nat} {G : Schema n} {T : TypeGraph.Ty n}
    (old src : Value G T) (dst source : Solidity.Storage.Loc)
    (hash : Solidity.Storage.Pre → Nat) (initial : WordStore) (address : Nat)
    (outside : ∀ q ∈ CopyDemands.demands old src, address ≠ (q.location dst).word N hash) :
    finiteCopy (N := N) old src dst source hash initial address = initial address := by
  rw [finiteCopy_eq]
  exact CopyWrites.numeric_outside old src dst source hash initial address outside

/-- info: 'Solidity.Backend.StorageOps.CopyReadCapture.source_read' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms source_read
/-- info: 'Solidity.Backend.StorageOps.CopyReadCapture.source_slot_read' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms source_slot_read
/-- info: 'Solidity.Backend.StorageOps.CopyReadCapture.reader_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms reader_congr
/-- info: 'Solidity.Backend.StorageOps.CopyReadCapture.slot_reader_congr' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms slot_reader_congr
/-- info: 'Solidity.Backend.StorageOps.CopyReadCapture.represented_reads' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms represented_reads
/-- info: 'Solidity.Backend.StorageOps.CopyReadCapture.represented_log' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms represented_log
/-- info: 'Solidity.Backend.StorageOps.CopyReadCapture.addresses' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms addresses
/-- info: 'Solidity.Backend.StorageOps.CopyReadCapture.entries' does not depend on any axioms -/
#guard_msgs in #print axioms entries
/-- info: 'Solidity.Backend.StorageOps.CopyReadCapture.capture' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms capture
/-- info: 'Solidity.Backend.StorageOps.CopyReadCapture.capture_read' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms capture_read
/-- info: 'Solidity.Backend.StorageOps.CopyReadCapture.entries_length' depends on axioms: [propext] -/
#guard_msgs in #print axioms entries_length
/-- info: 'Solidity.Backend.StorageOps.CopyReadCapture.capture_outside' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms capture_outside
/-- info: 'Solidity.Backend.StorageOps.CopyReadCapture.captured_updates' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms captured_updates
/-- info: 'Solidity.Backend.StorageOps.CopyReadCapture.finiteCopy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms finiteCopy
/-- info: 'Solidity.Backend.StorageOps.CopyReadCapture.finiteCopy_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms finiteCopy_eq
/-- info: 'Solidity.Backend.StorageOps.CopyReadCapture.updates_eq_of_reads' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms updates_eq_of_reads
/-- info: 'Solidity.Backend.StorageOps.CopyReadCapture.finite_outside' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms finite_outside

end Solidity.Backend.StorageOps.CopyReadCapture
