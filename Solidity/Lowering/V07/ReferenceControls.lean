import Solidity.Lowering.V07.ReferenceEffects
import Solidity.Source.SemanticsExamples
import Solidity.Theory.Typed.Mem
import Solidity.Semantics.AllocBytes

namespace Solidity.Lowering.V07.ReferenceControls
open Source.SemanticsExamples
abbrev C := (default : Contract)
abbrev SrcCtx : Source.RCtx := [.bytes .memory,.bytes .memory]
abbrev TgtCtx : Ctx := [.mem bytesR,.mem bytesR]

def heap : Source.Heap E0.layout :=
  (((Source.Heap.empty : Source.Heap E0.layout).alloc ⟨.bytes .memory,.bytes [0,0]⟩).1.alloc
    ⟨.bytes .memory,.bytes [0,0,0]⟩).1
def source : Source.EMState E0 SrcCtx :=
  (.cons (.memRef rfl 1) (.cons (.memRef rfl 0) .nil),{s0 with heap := heap})
def first : State C [.mem bytesR] :=
  (State.init C).allocPush (zerosObj [] 2 (by decide))
def target : State C TgtCtx := first.allocPush (zerosObj first.H 3 (by decide))
def old : HRef target.H bytesR := ⟨0,rfl⟩
def assigned : HRef target.H bytesR := ⟨1,rfl⟩
def sourcePost : Source.EMState E0 SrcCtx :=
  (source.1.set (.there .here) (.memRef rfl 1),source.2)
def reached (p : Roadmap.Pipeline) : State C (.mem bytesR :: .mem bytesR :: TgtCtx) :=
  ((target.setLocal (.there .here) (some assigned)).push (t := .mem bytesR)
    (some (if p = .legacy then old else assigned))).push (t := .mem bytesR) (some assigned)

theorem source_cells_live :
    source.2.heap.get 0 = some ⟨.bytes .memory,.bytes [0,0]⟩ ∧
    source.2.heap.get 1 = some ⟨.bytes .memory,.bytes [0,0,0]⟩ := ⟨rfl,rfl⟩

theorem distinct_references : old ≠ assigned := by
  intro same
  have id := congrArg HRef.id same
  change (0 : Nat) = 1 at id
  omega

theorem old_length : target.heap.len old .dyn = 2 := by
  change (MObj.elems .dyn (target.heap.get old)).length = 2
  rw [MObj.elems_dyn]
  rfl

theorem assigned_length : target.heap.len assigned .dyn = 3 := by
  change (MObj.elems .dyn (target.heap.get (first.alloc (zerosObj first.H 3 (by decide))).2)).length = 3
  unfold target
  rw [State.allocPush_get]
  simp only [MObj.elems_dyn,MObj.wk,List.length_map,zerosObj,List.length_replicate]

theorem initial_aliases : (0 : Nat) = 1 ↔ old = assigned := by
  constructor
  · intro impossible; omega
  · intro same; exact False.elim (distinct_references same)

theorem actual_source_pair (p : Roadmap.Pipeline) (fuel : Nat) :
    (Source.evalPair (G0 p) F0 (fuel+3)
      (.assign (.local (.there .here)) (.local .here)) (.local (.there .here))).run source =
      (.ok (.val (.memRef rfl 1),.val (.memRef rfl (if p = .legacy then 0 else 1))),sourcePost) :=
  (reference_assignment_pair_transport (G0 p) F0 fuel source target (.there .here) .here
    (.there .here) .here 0 1 old assigned rfl rfl rfl rfl
    (fun address ref => address = ref.id) rfl rfl initial_aliases).1

theorem actual_target_prefix (p : Roadmap.Pipeline) :
    (memoryAssignReadPrefix p (.there .here) .here rfl).run target =
      .ok (⟨reached p,List.prefix_refl _⟩) :=
  memory_assign_read_prefix_run p target (.there .here) .here rfl old assigned rfl rfl

theorem captured_old_after_rebind :
    (MPath.var (.there .here) rfl : MPath C (.mem bytesR :: .mem bytesR :: TgtCtx) (.ref bytesR)).mvalT
      (reached .legacy) = .ok old ∧
    (MPath.var (.there (.there (.there .here))) rfl :
      MPath C (.mem bytesR :: .mem bytesR :: TgtCtx) (.ref bytesR)).mvalT
        (reached .legacy) = .ok assigned := ⟨rfl,rfl⟩

theorem wrong_deferred_alias_rejected :
    (MPath.var (.there .here) rfl : MPath C (.mem bytesR :: .mem bytesR :: TgtCtx) (.ref bytesR)).mvalT
      (reached .legacy) ≠
    (MPath.var (.there (.there (.there .here))) rfl :
      MPath C (.mem bytesR :: .mem bytesR :: TgtCtx) (.ref bytesR)).mvalT (reached .legacy) := by
  rw [captured_old_after_rebind.1,captured_old_after_rebind.2]
  intro same
  exact distinct_references (Except.ok.inj same)

def capturedSnapshot : TRes (SVal (.ref bytesR)) :=
  (Src.copyMem (.var (.there .here) rfl)).valueT (reached .legacy)
def lateSnapshot : TRes (SVal (.ref bytesR)) :=
  (Src.copyMem (.var (.there (.there (.there .here))) rfl)).valueT (reached .legacy)

theorem captured_snapshot_length :
    capturedSnapshot.map (fun v => (v.view : ArrView (.prim .uint)).n) = .ok 2 := by
  unfold capturedSnapshot
  rw [Src.valueT,captured_old_after_rebind.1]
  change Except.ok ((MVal.copyMToSt target.heap (T := .ref bytesR) old).view : ArrView (.prim .uint)).n = _
  rw [MVal.copyMToSt_len,old_length]

theorem late_snapshot_length :
    lateSnapshot.map (fun v => (v.view : ArrView (.prim .uint)).n) = .ok 3 := by
  unfold lateSnapshot
  rw [Src.valueT,captured_old_after_rebind.2]
  change Except.ok ((MVal.copyMToSt target.heap (T := .ref bytesR) assigned).view : ArrView (.prim .uint)).n = _
  rw [MVal.copyMToSt_len,assigned_length]

theorem wrong_snapshot_time_rejected : capturedSnapshot ≠ lateSnapshot := by
  intro same
  have lengths := congrArg (fun result : TRes (SVal (.ref bytesR)) =>
    result.map (fun v => (v.view : ArrView (.prim .uint)).n)) same
  change capturedSnapshot.map (fun v => (v.view : ArrView (.prim .uint)).n) =
    lateSnapshot.map (fun v => (v.view : ArrView (.prim .uint)).n) at lengths
  rw [captured_snapshot_length,late_snapshot_length] at lengths
  cases lengths

theorem complete_pointer_observations :
    TEnv.get (.here : Idx (.mem bytesR :: .mem bytesR :: TgtCtx) (.mem bytesR)) (reached .legacy).env = some assigned ∧
    TEnv.get (.there .here) (reached .legacy).env = some old ∧
    TEnv.get (.there (.there .here)) (reached .legacy).env = some assigned ∧
    TEnv.get (.there (.there (.there .here))) (reached .legacy).env = some assigned ∧
    TEnv.get (.there .here) (reached .viaIR).env = some assigned ∧
    (reached .legacy).glob = target.glob ∧ (reached .viaIR).glob = target.glob ∧ sourcePost.2 = source.2 :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

/-- Equal byte contents still inhabit two distinct allocated identities. -/
def twinHeap : Source.Heap E0.layout :=
  (((Source.Heap.empty : Source.Heap E0.layout).alloc ⟨.bytes .memory,.bytes [0,0]⟩).1.alloc
    ⟨.bytes .memory,.bytes [0,0]⟩).1
def twinTarget : State C TgtCtx := first.allocPush (zerosObj first.H 2 (by decide))
def twinOld : HRef twinTarget.H bytesR := ⟨0,rfl⟩
def twinNew : HRef twinTarget.H bytesR := ⟨1,rfl⟩

theorem equal_content_distinct_identities :
    twinHeap.get 0 = twinHeap.get 1 ∧ twinOld ≠ twinNew ∧
    twinTarget.heap.get twinOld = twinTarget.heap.get twinNew := by
  refine ⟨rfl,?_,rfl⟩
  intro same
  have id := congrArg HRef.id same
  change (0 : Nat) = 1 at id
  omega

end Solidity.Lowering.V07.ReferenceControls
