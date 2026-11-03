import Solidity.Backend.StorageOps.RetainedPush

/-! Fresh primitive mapping defaults derived from actual zero-origin write
histories. Old failed reads impose no numeric value. Only explicitly covered
finite per-run separation transports the history; no global hash premise. -/
namespace Solidity.Backend.StorageOps.FreshMappingHistory
open TypeGraph Solidity.Storage Solidity.Storage.Representation Solidity.Storage.Representation.Graph

def symbolic (history : List (Solidity.Storage.Loc × Semantics.Word)) : Store :=
  history.foldl (fun s op => write s op.1 op.2) (fun _ => ClearDemands.zero)
def numeric (N : Nat) (hash : Solidity.Storage.Pre → Nat)
    (history : List (Solidity.Storage.Loc × Semantics.Word)) : WordStore :=
  history.foldl (fun s op => writeWord s (op.1.word N hash) op.2) (fun _ => ClearDemands.zero)

theorem history_transport {N L R : Nat} {hash : Solidity.Storage.Pre → Nat}
    {P : List Solidity.Storage.Pre} {locations : List Solidity.Storage.Loc}
    (run : FiniteRun N L R hash P locations) (history : List (Solidity.Storage.Loc × Semantics.Word))
    (covered : ∀ op ∈ history, op.1 ∈ locations) :
    Transport N hash locations (symbolic history) (numeric N hash history) :=
  transport_sequence run (fun _ _ => rfl) history covered

/-- The desired zero is a consequence of the executed history and finite
separation, not an assumed default representation of old None reads. -/
theorem untouched_zero {N L R : Nat} {hash : Solidity.Storage.Pre → Nat}
    {P : List Solidity.Storage.Pre} {locations : List Solidity.Storage.Loc}
    (run : FiniteRun N L R hash P locations) (history : List (Solidity.Storage.Loc × Semantics.Word))
    (covered : ∀ op ∈ history, op.1 ∈ locations) (fresh : Solidity.Storage.Loc) (member : fresh ∈ locations)
    (apart : ∀ op ∈ history, fresh ≠ op.1) : numeric N hash history (fresh.word N hash) = ClearDemands.zero :=
  sequence_outside_frame N hash (fun _ => ClearDemands.zero) history (fresh.word N hash)
    (fun op inside equal => apart op inside (run.word_inj member (covered op inside) equal))

def keyQuery {n : Nat} {G : Schema n} {K p : PrimTy} (i : Index) (key : K.Denote) :
    Query G (.array (.mapping K (.prim p))) := .word (.cons (.index i) (.cons (.key key) .nil))

/-- Exact old failure is distinct from the newly readable default. -/
theorem fresh_before {n : Nat} {G : Schema n} {K p : PrimTy}
    (old : Value G (.array (.mapping K (.prim p)))) (fresh : old.extent.val = old.length.val) (key : K.Denote) :
    (keyQuery old.length key).read old = none := by
  cases old with
  | array extent length bound slots =>
    change extent.val = length.val at fresh
    have outside : ¬ length.val < extent.val := by omega
    simp only [keyQuery,Query.read,Value.observe,Value.find,Value.length,TypeGraph.Path.read,Step.get,
      dif_neg outside,Option.bind_none,Option.map_none]

theorem fresh_read {n : Nat} {G : Schema n} {K p : PrimTy}
    (old result : Value G (.array (.mapping K (.prim p))))
    (fresh : old.extent.val = old.length.val) (pushed : operationPush old = some result) (key : K.Denote) :
    (keyQuery old.length key).read result = some ClearDemands.zero := by
  have found := operationPush_fresh old result fresh pushed
  simp only [keyQuery,Query.read,Value.observe,Value.find,TypeGraph.Path.read,found,Option.bind_some]
  exact congrArg some (ClearDemands.default_zero p)

/-- Selected fresh mapping words acquire the PUBLIC owner relation after the
actual header write. Requested keys are arbitrary finite inputs, not a key cap.
Header/other-index observations are separate composition obligations. -/
theorem represented_keys {n N L R : Nat} {G : Schema n} {K p : PrimTy}
    (old result : Value G (.array (.mapping K (.prim p))))
    (fresh : old.extent.val = old.length.val) (pushed : operationPush old = some result)
    (keys : List K.Denote) (base : Solidity.Storage.Loc)
    {hash : Solidity.Storage.Pre → Nat} {P : List Solidity.Storage.Pre} {locations : List Solidity.Storage.Loc}
    (run : FiniteRun N L R hash P locations) (history : List (Solidity.Storage.Loc × Semantics.Word))
    (historyCovered : ∀ op ∈ history, op.1 ∈ locations)
    (queryCovered : ∀ key ∈ keys, (keyQuery (G := G) (p := p) old.length key).location base ∈ locations)
    (apart : ∀ key ∈ keys, ∀ op ∈ history, (keyQuery (G := G) (p := p) old.length key).location base ≠ op.1)
    (support : old.length.val < lmax) :
    Represented result (keys.map (keyQuery old.length)) base
      (write (symbolic history) base (lengthWord result.length.val result.length.isLt)) := by
  intro q member
  obtain ⟨key,inside,rfl⟩ := List.mem_map.mp member
  refine ⟨?_,True.intro,?_⟩
  · exact ⟨support,True.intro,True.intro⟩
  · intro value observed
    have same : ClearDemands.zero = value := Option.some.inj ((fresh_read old result fresh pushed key).symm.trans observed)
    rw [← same]
    have initial := history_transport run history historyCovered
    have zero := untouched_zero run history historyCovered _ (queryCovered key inside) (apart key inside)
    have different : (keyQuery (G := G) (p := p) old.length key).location base ≠ base :=
      OperationDepth.indexed_ne_header (.word (.cons (.key key) .nil)) old.length base
    exact (write_other _ base _ _ different).trans
      ((initial _ (queryCovered key inside)).symm.trans zero)

/-- Actual CURRENT-header push, with newly readable defaults proved from history.
The explicit bound is PUBLIC observation coverage, not a source admission cap.
Only the selected root header and finite fresh keys are claimed here. -/
theorem complete_numeric {n N L R : Nat} {G : Schema n} {K p : PrimTy}
    (old result : Value G (.array (.mapping K (.prim p))))
    (fresh : old.extent.val = old.length.val) (pushed : operationPush old = some result)
    (keys : List K.Denote) (base : Solidity.Storage.Loc)
    {hash : Solidity.Storage.Pre → Nat} {P : List Solidity.Storage.Pre} {locations : List Solidity.Storage.Loc}
    (run : FiniteRun N L R hash P locations) (history : List (Solidity.Storage.Loc × Semantics.Word))
    (historyCovered : ∀ op ∈ history, op.1 ∈ locations) (headerCovered : base ∈ locations)
    (queryCovered : ∀ key ∈ keys, (keyQuery (G := G) (p := p) old.length key).location base ∈ locations)
    (apart : ∀ key ∈ keys, ∀ op ∈ history, (keyQuery (G := G) (p := p) old.length key).location base ≠ op.1)
    (coverage : old.length.val + 1 ≤ lmax)
    (before : Represented old [.length .nil] base (symbolic history)) :
    ∃ final, LifecycleNumeric.pushHeader N hash base (numeric N hash history) = some final ∧
      let after := write (symbolic history) base (lengthWord result.length.val result.length.isLt)
      Represented result (.length .nil :: keys.map (keyQuery old.length)) base after ∧
      Transport N hash locations after final ∧
      (∀ q ∈ (.length .nil :: keys.map (keyQuery (G := G) (p := p) old.length)),
        ∀ value, q.read result = some value → final ((q.location base).word N hash) = value) ∧
      (∀ address, address ≠ base.word N hash → final address = numeric N hash history address) := by
  have initial := history_transport run history historyCovered
  have header := LifecycleNumeric.array_header_numeric old base (symbolic history) (numeric N hash history)
    hash locations before initial headerCovered
  have headers := operationPush_header old result pushed
  have room : old.length.val + 1 < 2 ^ 256 := by have bound := result.length.isLt; omega
  let final := writeWord (numeric N hash history) (base.word N hash) (lengthWord result.length.val result.length.isLt)
  have executed : LifecycleNumeric.pushHeader N hash base (numeric N hash history) = some final := by
    rw [LifecycleNumeric.pushHeader_known hash base _ old.length header,dif_pos room]
    apply congrArg some
    apply congrArg (writeWord _ (base.word N hash))
    apply Subtype.ext
    exact congrArg Int.ofNat headers.1.symm
  have keysOwner := represented_keys old result fresh pushed keys base run history historyCovered queryCovered apart (by omega)
  have owner : Represented result (.length .nil :: keys.map (keyQuery old.length)) base
      (write (symbolic history) base (lengthWord result.length.val result.length.isLt)) := by
    intro q member
    rcases List.mem_cons.mp member with same | inside
    · subst q
      refine ⟨True.intro,?_,?_⟩
      · have extent : result.extent.val = old.length.val + 1 := by rw [headers.2,fresh]; omega
        cases result with
        | array newExtent newLength bound slots =>
          change newLength.val = old.length.val + 1 ∧ _ at headers
          change newExtent.val = old.length.val + 1 at extent
          change newLength.val ≤ lmax ∧ newExtent.val ≤ lmax
          constructor <;> omega
      · intro value observed
        have same : lengthWord result.length.val result.length.isLt = value := by cases result; exact Option.some.inj observed
        rw [← same]
        exact write_same _ base _
    · exact keysOwner q inside
  have transported := transport_write run initial base headerCovered (lengthWord result.length.val result.length.isLt)
  refine ⟨final,executed,owner,transported,?_,?_⟩
  · intro q member value observed
    apply owner.numeric transported q member _ value observed
    rcases List.mem_cons.mp member with same | inside
    · subst q; exact headerCovered
    · obtain ⟨key,keyInside,rfl⟩ := List.mem_map.mp inside
      exact queryCovered key keyInside
  · intro address different
    exact if_neg different

/-- info: 'Solidity.Backend.StorageOps.FreshMappingHistory.history_transport' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms history_transport
/-- info: 'Solidity.Backend.StorageOps.FreshMappingHistory.untouched_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms untouched_zero
/-- info: 'Solidity.Backend.StorageOps.FreshMappingHistory.fresh_before' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms fresh_before
/-- info: 'Solidity.Backend.StorageOps.FreshMappingHistory.fresh_read' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms fresh_read
/-- info: 'Solidity.Backend.StorageOps.FreshMappingHistory.represented_keys' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms represented_keys
/-- info: 'Solidity.Backend.StorageOps.FreshMappingHistory.complete_numeric' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms complete_numeric

end Solidity.Backend.StorageOps.FreshMappingHistory
