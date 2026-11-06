import Solidity.Backend.StorageOps.CopyOutput
import Solidity.Backend.StorageOps.CopyCompatibility

/-! Independent copied-output correspondence for existing recursive generated
query traces. Ordinary Source lowering/emitted code/world execution are separate. -/
namespace Solidity.Backend.StorageOps.CopyOutput
open TypeGraph Solidity.Storage Solidity.Storage.Representation Solidity.Storage.Representation.Graph
open CopyReadback

mutual
/-- Actual generated query writes match every successful independent recursive
copy output read. OLD failed reads impose no scalar-zero condition. -/
theorem copy_output {n : Nat} {G : Schema n} :
    {T : TypeGraph.Ty n} → (old src : Value G T) → CopyPermit G T →
    (q : Query G T) → (initial : Semantics.Word) →
    (∀ word, q.read old = some word → initial = word) →
    (word : Semantics.Word) → q.read (recursiveCopy old src) = some word →
    traceWord q (CopyWrites.queryWrites old src (fun d => (d.read src).getD ClearDemands.zero)) initial = word
  | _, .prim old, .prim src, _, q, initial, _, word, observed => by
    cases q with
    | word path => cases path with
      | nil =>
        change some (PrimTy.toWord src) = some word at observed
        cases observed
        change traceWord (.word .nil) [(.word .nil,PrimTy.toWord src)] initial = _
        simp only [traceWord,List.foldl_cons,List.foldl_nil,ite_true]
      | cons step rest => cases step
    | length path => cases path with | cons step rest => cases step
  | _, @Value.node _ _ i old, .node src, permit, q, initial, before, word, observed => by
    have handle : ∀ {U : TypeGraph.Ty n} (p : Field (G.fields i) U) (child : Query G U)
        (first : Semantics.Word),
        (∀ w, (child.prefix (.cons (.field p) .nil)).read (.node old) = some w → first = w) →
        ∀ w, (child.prefix (.cons (.field p) .nil)).read (recursiveCopy (.node old) (.node src)) = some w →
        traceWord (child.prefix (.cons (.field p) .nil))
          (CopyWrites.queryWrites (.node old) (.node src) (fun d => (d.read (.node src)).getD ClearDemands.zero)) first = w := by
      intro U p child first oldRead w postRead
      rw [node_trace]
      have readers : (fun d => ((d.prefix (.cons (.field p) .nil)).read (.node src)).getD ClearDemands.zero) =
          (fun d : Query G U => (d.read (src p)).getD ClearDemands.zero) := by
        funext d
        rw [Query.read_prefix (.node src) (src p) (.cons (.field p) .nil) d rfl]
      rw [readers]
      apply copy_output (old p) (src p) (permit.step (.field p)) child first
      · intro oldWord oldObserved
        apply oldRead oldWord
        rwa [Query.read_prefix (.node old) (old p) (.cons (.field p) .nil) child rfl]
      · rwa [Query.read_prefix (recursiveCopy (.node old) (.node src))
          (recursiveCopy (old p) (src p)) (.cons (.field p) .nil) child rfl] at postRead
    cases q with
    | word path => cases path with | cons step rest => cases step with
      | field p => exact handle p (.word rest) initial before word observed
    | length path => cases path with | cons step rest => cases step with
      | field p => exact handle p (.length rest) initial before word observed
  | _, @Value.fixed _ _ E m old, .fixed src, permit, q, initial, before, word, observed => by
    have handle : ∀ (i : Index) (child : Query G E) (first : Semantics.Word),
        (∀ w, (child.prefix (.cons (.fixed (m := m) i) .nil)).read (.fixed old) = some w → first = w) →
        ∀ w, (child.prefix (.cons (.fixed (m := m) i) .nil)).read (recursiveCopy (.fixed old) (.fixed src)) = some w →
        traceWord (child.prefix (.cons (.fixed (m := m) i) .nil))
          (CopyWrites.queryWrites (.fixed old) (.fixed src) (fun d => (d.read (.fixed src)).getD ClearDemands.zero)) first = w := by
      intro i child first oldRead w postRead
      by_cases inside : i.val < m.val
      · have foundSrc : (Value.fixed src).find (.cons (.fixed i) .nil) =
            some ((src ⟨i.val,inside⟩).getD (Value.dflt E)) := by
          simp only [Value.find,Path.read,Step.get,dif_pos inside,Option.bind_some]
        have foundPost : (recursiveCopy (.fixed old) (.fixed src)).find (.cons (.fixed i) .nil) =
            some ((recursiveSlot (old ⟨i.val,inside⟩) (src ⟨i.val,inside⟩)).getD (Value.dflt E)) := by
          simp only [recursiveCopy,fixedView,Value.find,Path.read,Step.get,dif_pos inside,Option.bind_some]
        rw [fixed_trace old src ⟨i.val,inside⟩]
        have readers : (fun d => ((d.prefix (.cons (.fixed (m := m) i) .nil)).read (.fixed src)).getD ClearDemands.zero) =
            (fun d : Query G E => (d.read ((src ⟨i.val,inside⟩).getD (Value.dflt E))).getD ClearDemands.zero) := by
          funext d
          rw [Query.read_prefix (.fixed src) _ _ d foundSrc]
        rw [readers]
        apply slot_output (old ⟨i.val,inside⟩) (src ⟨i.val,inside⟩) (permit.step (.fixed i)) child first
        · intro value same oldWord oldObserved
          have foundOld : (Value.fixed old).find (.cons (.fixed i) .nil) = some value := by
            simp only [Value.find,Path.read,Step.get,dif_pos inside,Option.bind_some,same,Slot.getD]
          apply oldRead oldWord
          rwa [Query.read_prefix (.fixed old) value _ child foundOld]
        · rwa [Query.read_prefix _ _ _ child foundPost] at postRead
      · have missing : (recursiveCopy (.fixed old) (.fixed src)).find (.cons (.fixed i) .nil) = none := by
          simp only [recursiveCopy,Value.find,Path.read,Step.get,dif_neg inside,Option.bind_none]
        rw [(CopyDemands.prefix_none _ _ child missing).1] at postRead
        cases postRead
    cases q with
    | word path => cases path with | cons step rest => cases step with
      | fixed i => exact handle i (.word rest) initial before word observed
    | length path => cases path with | cons step rest => cases step with
      | fixed i => exact handle i (.length rest) initial before word observed
  | _, @Value.array _ _ E oe ol oh os, .array ne nl nh ns, permit, q, initial, before, word, observed => by
    have handle : ∀ (i : Index) (child : Query G E) (first : Semantics.Word),
        (∀ w, (child.prefix (.cons (.index i) .nil)).read (.array oe ol oh os) = some w → first = w) →
        ∀ w, (child.prefix (.cons (.index i) .nil)).read
          (recursiveCopy (.array oe ol oh os) (.array ne nl nh ns)) = some w →
        traceWord (child.prefix (.cons (.index i) .nil))
          (CopyWrites.queryWrites (.array oe ol oh os) (.array ne nl nh ns)
            (fun d => (d.read (.array ne nl nh ns)).getD ClearDemands.zero)) first = w := by
      intro i child first oldRead w postRead
      by_cases live : i.val < nl.val
      · have retainedNew : i.val < max oe.val nl.val := Nat.lt_of_lt_of_le live (Nat.le_max_right _ _)
        have processed : i.val < max ol.val nl.val := Nat.lt_of_lt_of_le live (Nat.le_max_right _ _)
        have foundSrc : (Value.array ne nl nh ns).find (.cons (.index i) .nil) =
            some ((ns ⟨i.val,Nat.lt_of_lt_of_le live nh⟩).getD (Value.dflt E)) := by
          simp only [Value.find,Path.read,Step.get,dif_pos (Nat.lt_of_lt_of_le live nh),Option.bind_some]
        have foundPost : (recursiveCopy (.array oe ol oh os) (.array ne nl nh ns)).find (.cons (.index i) .nil) =
            some ((recursiveSlot (oldSlot oe os i.val) (ns ⟨i.val,Nat.lt_of_lt_of_le live nh⟩)).getD (Value.dflt E)) := by
          simp only [recursiveCopy,Value.extent,Value.length,Value.slots,Value.find,Path.read,
            Step.get,dif_pos retainedNew,Option.bind_some,visit_prefix,if_pos processed,dif_pos live]
        rw [array_trace oe ol oh os ne nl nh ns i processed,dif_pos live]
        have readers : (fun d => ((d.prefix (.cons (.index i) .nil)).read (.array ne nl nh ns)).getD ClearDemands.zero) =
            (fun d : Query G E => (d.read ((ns ⟨i.val,Nat.lt_of_lt_of_le live nh⟩).getD (Value.dflt E))).getD ClearDemands.zero) := by
          funext d
          rw [Query.read_prefix (.array ne nl nh ns) _ _ d foundSrc]
        rw [readers]
        apply slot_output (oldSlot oe os i.val) (ns ⟨i.val,Nat.lt_of_lt_of_le live nh⟩)
          (permit.step (.index i)) child first
        · intro value same oldWord oldObserved
          by_cases retained : i.val < oe.val
          · have foundOld : (Value.array oe ol oh os).find (.cons (.index i) .nil) = some value := by
              simp only [Value.find,Path.read,Step.get,dif_pos retained,Option.bind_some]
              have slotSame : os ⟨i.val,retained⟩ = Slot.present value := by
                simpa only [oldSlot,dif_pos retained] using same
              rw [slotSame]
              rfl
            apply oldRead oldWord
            rwa [Query.read_prefix (.array oe ol oh os) value _ child foundOld]
          · simp only [oldSlot,dif_neg retained] at same
            cases same
        · rwa [Query.read_prefix _ _ _ child foundPost] at postRead
      · by_cases clearing : i.val < ol.val
        · have retainedOld : i.val < oe.val := Nat.lt_of_lt_of_le clearing oh
          have retainedNew : i.val < max oe.val nl.val := Nat.lt_of_lt_of_le retainedOld (Nat.le_max_left _ _)
          have processed : i.val < max ol.val nl.val := Nat.lt_of_lt_of_le clearing (Nat.le_max_left _ _)
          have foundOld : (Value.array oe ol oh os).find (.cons (.index i) .nil) =
              some ((oldSlot oe os i.val).getD (Value.dflt E)) := by
            simp only [Value.find,Path.read,Step.get,dif_pos retainedOld,Option.bind_some,oldSlot]
          have foundPost : (recursiveCopy (.array oe ol oh os) (.array ne nl nh ns)).find (.cons (.index i) .nil) =
              some ((recursiveClearSlot (oldSlot oe os i.val)).getD (Value.dflt E)) := by
            simp only [recursiveCopy,Value.extent,Value.length,Value.slots,Value.find,Path.read,
              Step.get,dif_pos retainedNew,Option.bind_some,visit_prefix,if_pos processed,dif_neg live,if_pos clearing]
          rw [array_trace oe ol oh os ne nl nh ns i processed,dif_neg live]
          apply clear_slot_output (oldSlot oe os i.val) child first
          · intro oldWord oldObserved
            apply oldRead oldWord
            rwa [Query.read_prefix (.array oe ol oh os) _ _ child foundOld]
          · rwa [Query.read_prefix _ _ _ child foundPost] at postRead
        · have unprocessed : max ol.val nl.val ≤ i.val := by omega
          have unvisited : ¬ i.val < max ol.val nl.val := by omega
          have same : (recursiveCopy (.array oe ol oh os) (.array ne nl nh ns)).find (.cons (.index i) .nil) =
              (Value.array oe ol oh os).find (.cons (.index i) .nil) := by
            by_cases retained : i.val < oe.val
            · have retainedNew : i.val < max oe.val nl.val := Nat.lt_of_lt_of_le retained (Nat.le_max_left _ _)
              simp only [recursiveCopy,Value.extent,Value.length,Value.slots,Value.find,Path.read,
                Step.get,dif_pos retainedNew,dif_pos retained,Option.bind_some,visit_prefix,if_neg unvisited,oldSlot]
            · have retainedNew : ¬ i.val < max oe.val nl.val := by omega
              simp only [recursiveCopy,Value.extent,Value.length,Value.slots,Value.find,Path.read,
                Step.get,dif_neg retainedNew,dif_neg retained,Option.bind_none]
          rw [array_trace_outside oe ol oh os ne nl nh ns i unprocessed]
          apply oldRead w
          rwa [(ClearDemands.prefix_find_frame _ _ (.cons (.index i) .nil) child same).1] at postRead
    cases q with
    | word path => cases path with | cons step rest => cases step with
      | index i => exact handle i (.word rest) initial before word observed
    | length path => cases path with
      | nil =>
        change some (lengthWord nl.val nl.isLt) = some word at observed
        cases observed
        change traceWord (.length .nil : Query G (.array E))
          (_ ++ [(.length .nil,lengthWord nl.val nl.isLt)]) initial = _
        rw [traceWord_append]
        simp only [traceWord,List.foldl_cons,List.foldl_nil,ite_true]
      | cons step rest => cases step with
        | index i => exact handle i (.length rest) initial before word observed
  | _, .mapping old, .mapping src, permit, q, initial, before, word, observed =>
    False.elim permit.no_mapping

/-- Fresh absent slots need no OLD word premise because initialization is
actual. Retained present slots use their OLD successful read agreement. -/
theorem slot_output {n : Nat} {G : Schema n} :
    {T : TypeGraph.Ty n} → (old src : Slot G T) → CopyPermit G T →
    (q : Query G T) → (initial : Semantics.Word) →
    (∀ value, old = .present value → ∀ word, q.read value = some word → initial = word) →
    (word : Semantics.Word) → q.read ((recursiveSlot old src).getD (Value.dflt T)) = some word →
    traceWord q (CopyWrites.slotWrites old src
      (fun d => (d.read (src.getD (Value.dflt T))).getD ClearDemands.zero)) initial = word
  | _, .absent, .absent, permit, q, initial, _, word, observed =>
    default_readback permit q initial word observed
  | _, .present old, .absent, _, q, initial, before, word, observed =>
    clear_output old q initial (before old rfl) word observed
  | _, .absent, .present src, permit, q, initial, _, word, observed => by
    change traceWord q (CopyWrites.zeros (CopyDefaults.demands G _) ++
      CopyWrites.queryWrites (Value.dflt _) src (fun d => (d.read src).getD ClearDemands.zero)) initial = word
    rw [traceWord_append]
    apply copy_output (Value.dflt _) src permit q
    · intro oldWord oldObserved
      exact default_readback permit q initial oldWord oldObserved
    · exact observed
  | _, .present old, .present src, permit, q, initial, before, word, observed =>
    copy_output old src permit q initial (before old rfl) word observed
end

/-- GENERAL selected recursive copied-output numeric readback, derived from
OLD independent owner relations and actual generated writes. Source metadata
and finite layout/query separation remain explicit prerequisites. -/
theorem numeric_readback {n N L R : Nat} {G : Schema n} {T : TypeGraph.Ty n}
    (old src : Value G T) (permit : CopyPermit G T) (queries : List (Query G T))
    (dst source : Solidity.Storage.Loc) (store : Store) (initial : WordStore)
    {hash : Solidity.Storage.Pre → Nat} {P : List Solidity.Storage.Pre}
    {locations : List Solidity.Storage.Loc} (run : FiniteRun N L R hash P locations)
    (beforeDst : Represented old queries dst store)
    (beforeSrc : Represented src (ClearDemands.demands src) source store)
    (before : Transport N hash locations store initial)
    (sourceCovered : ∀ d ∈ ClearDemands.demands src, d.location source ∈ locations)
    (queriesCovered : ∀ q ∈ queries, q.location dst ∈ locations)
    (writesCovered : ∀ d ∈ CopyDemands.demands old src, d.location dst ∈ locations)
    (separate : ∀ q ∈ queries, ∀ d ∈ CopyDemands.demands old src, d.location dst = q.location dst → d = q) :
    ∀ q ∈ queries, ∀ word, q.read (recursiveCopy old src) = some word →
      CopyWrites.numericCopy (N := N) old src dst source hash initial ((q.location dst).word N hash) = word := by
  intro q member word observed
  rw [represented_copy_trace old src q dst source store initial run beforeSrc before
    sourceCovered (queriesCovered q member) writesCovered (separate q member)]
  apply copy_output old src permit q _ _ word observed
  intro oldWord oldObserved
  rw [before _ (queriesCovered q member)]
  exact (beforeDst q member).2.2 oldWord oldObserved

/-- FULL selected PUBLIC recursive copy representation and ACTUAL generated
numeric Transport, with no desired post-representation premise. This is graph-
guided execution, not ordinary Source lowering or emitted runtime traversal. -/
theorem represented_copy {n N L R : Nat} {G : Schema n} {T : TypeGraph.Ty n}
    (old src : Value G T) (permit : CopyPermit G T) (queries : List (Query G T))
    (dst source : Solidity.Storage.Loc) (store : Store) (initial : WordStore)
    {hash : Solidity.Storage.Pre → Nat} {P : List Solidity.Storage.Pre}
    {locations : List Solidity.Storage.Loc} (run : FiniteRun N L R hash P locations)
    (beforeDst : Represented old queries dst store)
    (beforeSrc : Represented src (ClearDemands.demands src) source store)
    (before : Transport N hash locations store initial)
    (sourceCovered : ∀ d ∈ ClearDemands.demands src, d.location source ∈ locations)
    (queriesCovered : ∀ q ∈ queries, q.location dst ∈ locations)
    (writesCovered : ∀ d ∈ CopyDemands.demands old src, d.location dst ∈ locations)
    (separate : ∀ q ∈ queries, ∀ d ∈ CopyDemands.demands old src, d.location dst = q.location dst → d = q) :
    let log := CopyWrites.updates (N := N) old src dst source hash initial
    let after := log.foldl (fun w op => write w op.1 op.2) store
    Represented (recursiveCopy old src) queries dst after ∧
    Transport N hash locations after (CopyWrites.numericCopy (N := N) old src dst source hash initial) := by
  dsimp only
  have transported := transport_sequence run before
    (CopyWrites.updates (N := N) old src dst source hash initial) (by
      intro op inside
      obtain ⟨q,member,same⟩ := CopyWrites.generated old src dst source hash initial op inside
      rw [same]
      exact writesCovered q member)
  refine ⟨?_,transported⟩
  intro q member
  obtain ⟨supported,compatible⟩ := CopyCompatibility.represented_metadata old src permit queries dst source store beforeDst beforeSrc q member
  refine ⟨supported,compatible,?_⟩
  intro word observed
  exact (transported _ (queriesCovered q member)).symm.trans
    (numeric_readback old src permit queries dst source store initial run beforeDst beforeSrc before
      sourceCovered queriesCovered writesCovered separate q member word observed)

/-- info: 'Solidity.Backend.StorageOps.CopyOutput.copy_output' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms copy_output
/-- info: 'Solidity.Backend.StorageOps.CopyOutput.slot_output' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms slot_output
/-- info: 'Solidity.Backend.StorageOps.CopyOutput.numeric_readback' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms numeric_readback
/-- info: 'Solidity.Backend.StorageOps.CopyOutput.represented_copy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms represented_copy

end Solidity.Backend.StorageOps.CopyOutput
