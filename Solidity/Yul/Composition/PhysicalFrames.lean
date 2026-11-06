import Solidity.Yul.Composition.Interface
import Solidity.Yul.Views.OwnedBoolFrame

/-! Actual VY2 source actions and their VY4 execution projection.
VY4 Effects has no complement/owned-byte journals or EMState locals/heap.
Those remain in the original VY2 carriers; projecting execution never claims
that VY4 rollback restores discarded physical data or source log encodings. -/
namespace Solidity.Yul.Composition
open Solidity.Roadmap (Address Word Bytes)
open Solidity.Yul.Views
variable {E : Source.Env} {Γ : Source.RCtx}

/-- Only execution is projected. VY4 log logPrefix/buffer are explicit inputs;
Source.St.logs has a different representation and is NOT silently converted. -/
def physicalExecution (s : Source.EMState E Γ) (logPrefix : List Solidity.Yul.World.Log)
    (buffer : Bytes) : Solidity.Yul.World.Effects E.layout E.lay E.lay :=
  ⟨s.2.ex,logPrefix,buffer⟩

/-- Public frame API and successful concrete preparation agree only at the
same account/request. The source caller is F.sender, not an invented account. -/
theorem prepared_frame_action
    (ps ts : (a : Address) → List (ScalarPath E.layout (E.lay a)))
    (q : PackedSlotRequest) (before : BoolEncodingJournal) (F : Source.Fr)
    (p : RepresentedSlotPlan ps ts q before)
    (prepared : prepareRepresentedSlot ps ts q before = some p)
    (owner : q.address = F.this) (s : Source.EMState E Γ)
    (r : ResidualJournal complementCarrierOwnership) :
    representedFrameWrite? ps ts F q.transient q.slot q.raw before s r =
      some (representedSourceStep ps ts q before F p s r) := by
  have bound : (⟨q.transient,F.this,q.slot,q.raw⟩ : PackedSlotRequest) = q := by
    cases q with
    | mk bank address slot raw => cases owner; rfl
  unfold representedFrameWrite?
  rw [bound]
  dsimp only
  rw [prepared,Option.map_some]

/-- This is the SAME source operation used by VY2, not a separately supplied
world operation list. Full physical journals remain separately coupled. -/
theorem physical_success_projection
    (ps ts : (a : Address) → List (ScalarPath E.layout (E.lay a)))
    (q : PackedSlotRequest) (before : BoolEncodingJournal) (F : Source.Fr)
    (p : RepresentedSlotPlan ps ts q before) (s : Source.EMState E Γ)
    (r : ResidualJournal complementCarrierOwnership) (static : F.static = false)
    (logPrefix : List Solidity.Yul.World.Log) (stale input data : Bytes) :
    Solidity.Yul.World.complete (physicalExecution s logPrefix stale)
      F.this F.sender F.value input F.static [p.packed.sourceOp] [] (.success data) =
      ⟨(representedSourceStep ps ts q before F p s r).1.1.2.2.ex,logPrefix,data⟩ := by
  rw [representedSourceStep_nonstatic F p s r static]
  simp only [Solidity.Yul.World.complete,physicalExecution,List.append_nil]
  rfl

/-- Current-frame preparation, actual source MemOK, complete physical raw-word
reconstruction and VY4 execution agree under their real separate premises. -/
theorem prepared_persistent_source
    (ps ts : (a : Address) → List (ScalarPath E.layout (E.lay a)))
    (q : PackedSlotRequest) (before : BoolEncodingJournal) (F : Source.Fr)
    (p : RepresentedSlotPlan ps ts q before)
    (prepared : prepareRepresentedSlot ps ts q before = some p)
    (owner : q.address = F.this) (s : Source.EMState E Γ)
    (r : ResidualJournal complementCarrierOwnership) (H : Source.HeapTy)
    (ok : Source.MemOK E H s) (static : F.static = false)
    (bank : q.transient = false) (separated : finiteSeparated (ps q.address)) :
    let result := representedSourceStep ps ts q before F p s r
    representedFrameWrite? ps ts F q.transient q.slot q.raw before s r = some result ∧
    Source.MemOK E H result.1.1.2 ∧
    reencodePersistentSlot (representedBanks ps false result.2)
      ⟨result.1.1.2.2.ex,result.1.2⟩ F.this q.slot = some q.raw := by
  refine ⟨prepared_frame_action ps ts q before F p prepared owner s r,
    representedSourceStep_MemOK H F p s r ok, ?_⟩
  rw [← owner]
  exact represented_step_persistent_at_request F p s r static bank separated

/-- A real represented action may be followed by a bounded target copy. The
bytes are supplied completion bytes, not a RETURNDATACOPY lowering theorem. -/
theorem physical_success_copy
    (ps ts : (a : Address) → List (ScalarPath E.layout (E.lay a)))
    (q : PackedSlotRequest) (before : BoolEncodingJournal) (F : Source.Fr)
    (p : RepresentedSlotPlan ps ts q before) (s : Source.EMState E Γ)
    (r : ResidualJournal complementCarrierOwnership) (static : F.static = false)
    (logPrefix : List Solidity.Yul.World.Log) (stale input data bytes : Bytes)
    (offset size destination : Nat) (caller : Solidity.Backend.Environment.Slice)
    (window : Solidity.Yul.World.returnWindow data offset size = some bytes)
    (fits : destination + bytes.length ≤ 2^256) :
    completeAndCopy (physicalExecution s logPrefix stale) F.this F.sender F.value input F.static
      [p.packed.sourceOp] [] (.success data) offset size destination caller =
      some (⟨(representedSourceStep ps ts q before F p s r).1.1.2.2.ex,logPrefix,data⟩,
        {caller with memory := Solidity.Backend.Environment.writeBytes caller.memory destination bytes}) := by
  unfold completeAndCopy
  rw [physical_success_projection ps ts q before F p s r static logPrefix stale input data]
  dsimp only
  rw [window]
  simp only [Option.bind_some,Solidity.Backend.Environment.materialize_correct bytes destination caller fits,Option.map_some]

/-- Committed child source/complement journals AND both owned-byte updates are
rolled back to the SAME parent entry. Caller identity/value are kept explicit.
No VY4 Effects field is invented for the physical journals. -/
theorem physical_child_outer_rollback
    (ps ts : (a : Address) → List (ScalarPath E.layout (E.lay a)))
    (q : PackedSlotRequest) (before : BoolEncodingJournal) (F : Source.Fr)
    (p : RepresentedSlotPlan ps ts q before) (s : Source.EMState E Γ)
    (r : ResidualJournal complementCarrierOwnership) (next : PackedSlotRequest)
    (child : RepresentedSlotPlan ps ts next (requestEncoding ps ts q before))
    (static : F.static = false) (input : Bytes) :
    let first := representedSourceStep ps ts q before F p s r
    let second := representedSourceStep ps ts next (requestEncoding ps ts q before) F child first.1.1.2 first.1.2
    companionRollback (companionEnter ⟨s.2.ex,r⟩ F.this F.sender F.value input F.static)
      (companionCommit (companionEnter ⟨first.1.1.2.2.ex,first.1.2⟩ F.this F.sender F.value input F.static)
        ⟨second.1.1.2.2.ex,second.1.2⟩) = ⟨s.2.ex,r⟩ ∧
    boolEncodingRollback before.journal.length second.2 = before := by
  have owned := (represented_two_outer_rollback F p s r next child static).2
  refine ⟨?_,owned⟩
  rw [representedSourceStep_nonstatic F p s r static]
  dsimp only
  rw [representedSourceStep_nonstatic F child _ _ static]
  exact companionRollback_outer_commit ⟨s.2.ex,r⟩ [p.packed.sourceOp] [child.packed.sourceOp]
    [p.packed.residualUpdate] [child.packed.residualUpdate] F.this F.sender F.value input F.static

/-- Nested successful world completions project the SAME two represented
source actions. The second completion replaces the first returndata. -/
theorem physical_two_success_projection
    (ps ts : (a : Address) → List (ScalarPath E.layout (E.lay a)))
    (q : PackedSlotRequest) (before : BoolEncodingJournal) (F : Source.Fr)
    (p : RepresentedSlotPlan ps ts q before) (s : Source.EMState E Γ)
    (r : ResidualJournal complementCarrierOwnership) (next : PackedSlotRequest)
    (child : RepresentedSlotPlan ps ts next (requestEncoding ps ts q before))
    (static : F.static = false) (logPrefix : List Solidity.Yul.World.Log)
    (stale input firstData lastData : Bytes) :
    let first := representedSourceStep ps ts q before F p s r
    let second := representedSourceStep ps ts next (requestEncoding ps ts q before) F child first.1.1.2 first.1.2
    Solidity.Yul.World.complete
      (Solidity.Yul.World.complete (physicalExecution s logPrefix stale)
        F.this F.sender F.value input F.static [p.packed.sourceOp] [] (.success firstData))
      F.this F.sender F.value input F.static [child.packed.sourceOp] [] (.success lastData) =
      ⟨second.1.1.2.2.ex,logPrefix,lastData⟩ := by
  dsimp only
  rw [physical_success_projection ps ts q before F p s r static logPrefix stale input firstData]
  exact physical_success_projection ps ts next (requestEncoding ps ts q before) F child
    (representedSourceStep ps ts q before F p s r).1.1.2
    (representedSourceStep ps ts q before F p s r).1.2 static logPrefix firstData input lastData

/-- Restore the actual EMState too: these source operations leave locals,
heap, source events/logs and function locals unchanged before journal rollback. -/
theorem physical_child_state_rollback
    (ps ts : (a : Address) → List (ScalarPath E.layout (E.lay a)))
    (q : PackedSlotRequest) (before : BoolEncodingJournal) (F : Source.Fr)
    (p : RepresentedSlotPlan ps ts q before) (s : Source.EMState E Γ)
    (r : ResidualJournal complementCarrierOwnership) (next : PackedSlotRequest)
    (child : RepresentedSlotPlan ps ts next (requestEncoding ps ts q before))
    (static : F.static = false) (input : Bytes) :
    let first := representedSourceStep ps ts q before F p s r
    let second := representedSourceStep ps ts next (requestEncoding ps ts q before) F child first.1.1.2 first.1.2
    let restored := companionRollback (companionEnter ⟨s.2.ex,r⟩ F.this F.sender F.value input F.static)
      (companionCommit (companionEnter ⟨first.1.1.2.2.ex,first.1.2⟩ F.this F.sender F.value input F.static)
        ⟨second.1.1.2.2.ex,second.1.2⟩)
    (second.1.1.2.1,{second.1.1.2.2 with ex := restored.source}) = s := by
  have restored := (physical_child_outer_rollback ps ts q before F p s r next child static input).1
  dsimp only at restored ⊢
  rw [restored]
  rw [representedSourceStep_nonstatic F p s r static]
  dsimp only
  rw [representedSourceStep_nonstatic F child _ _ static]


#print axioms prepared_frame_action
#print axioms physical_success_projection
#print axioms prepared_persistent_source
#print axioms physical_success_copy
#print axioms physical_child_outer_rollback
#print axioms physical_two_success_projection
#print axioms physical_child_state_rollback
end Solidity.Yul.Composition
