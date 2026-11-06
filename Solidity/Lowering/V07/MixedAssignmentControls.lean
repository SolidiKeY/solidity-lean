import Solidity.Lowering.V07.AssignmentControls
import Solidity.Semantics.AllocBytes

namespace Solidity.Lowering.V07.MixedAssignmentControls
open Source.SemanticsExamples

def C : Contract := { vars := [("live",.ref bytesR)] }
def storageRef : SRef C (.ref bytesR) := SRef.ofRoot "live" rfl
def base : State C [.alias bytesR] := (State.init C).push (t := .alias bytesR) (some storageRef)
def memory : State C [.mem bytesR,.alias bytesR] := base.allocPush (zerosObj base.H 2 (by decide))
def target : State C [.val .uint,.val .uint,.mem bytesR,.alias bytesR] :=
  (memory.push (integerValue .u8 3 (by decide))).push (integerValue .u8 7 (by decide))
def post : State C [.val .uint,.val .uint,.mem bytesR,.alias bytesR] :=
  target.setLocal (.there .here) (integerValue .u8 7 (by decide))

theorem live_memory : ∃ r : HRef target.H bytesR,
    TEnv.get (.there (.there .here)) target.env = some r ∧ target.heap.len r .dyn = 2 :=
  by
    refine ⟨(base.alloc (zerosObj base.H 2 (by decide))).2,rfl,?_⟩
    change (MObj.elems .dyn (memory.heap.get (base.alloc (zerosObj base.H 2 (by decide))).2)).length = 2
    unfold memory
    rw [State.allocPush_get]
    simp only [MObj.elems_dyn,MObj.wk,List.length_map,zerosObj,List.length_replicate]

theorem live_storage :
    TEnv.get (.there (.there (.there .here))) target.env = some storageRef := rfl

theorem live_references_preserved :
    (∃ r : HRef post.H bytesR,
      TEnv.get (.there (.there .here)) post.env = some r ∧ post.heap.len r .dyn = 2) ∧
    TEnv.get (.there (.there (.there .here))) post.env = some storageRef ∧
    post.glob = target.glob := ⟨live_memory,rfl,rfl⟩

theorem effectful_operand_frame (p : Roadmap.Pipeline)
    (hz : Source.IntTy.u8.lo ≤ 7-(if p = .legacy then 3 else 7) ∧
      7-(if p = .legacy then 3 else 7) ≤ Source.IntTy.u8.hi) :
    (assignReadSubOperand p .u8 (.there .here) .here).run target =
      .ok (⟨post,List.prefix_refl _⟩,.prim (integerValue .u8 (7-(if p = .legacy then 3 else 7)) hz)) :=
  assign_read_sub_operand_run p target .u8 (.there .here) .here 7 3 (by decide) (by decide) rfl rfl hz

/-- A real Source allocation supports the caller memory reference. Local
assignment does not replace the independent Source heap/world semantics. -/
def E : Source.Env := ⟨[⟨.stateVar,"live",some "C",false,
  .stateVar (.elem .bytes) none none none false "live" .none⟩]⟩
def path : Source.SPath := ⟨⟨some "C","live"⟩,[]⟩
def heap : Source.Heap E.layout :=
  ((Source.Heap.empty : Source.Heap E.layout).alloc ⟨.bytes .memory,.bytes [0,0]⟩).1
def source : Source.EMState E [.int .u8,.int .u8,.bytes .memory,.bytes .storage] :=
  (.cons (.int 7 (by decide)) (.cons (.int 3 (by decide))
    (.cons (.memRef rfl 0) (.cons (.storRef rfl path) .nil))),{s0 with heap := heap})
def sourcePost : Source.EMState E [.int .u8,.int .u8,.bytes .memory,.bytes .storage] :=
  (source.1.set (.there .here) (.int 7 (by decide)),source.2)

theorem source_memory_live : source.2.heap.get 0 = some ⟨.bytes .memory,.bytes [0,0]⟩ := rfl

theorem source_storage_typed : E.pathTy path = some (.bytes .storage) := rfl

theorem source_references_preserved :
    sourcePost.1.get (.there (.there .here)) = .memRef rfl 0 ∧
    sourcePost.1.get (.there (.there (.there .here))) = .storRef rfl path ∧
    sourcePost.2 = source.2 := ⟨rfl,rfl,rfl⟩

theorem source_assignment_frame (G : Source.Glob E) (fuel : Nat) :
    (Source.evalE G F0 (fuel+2) (.assign (.local (.there .here)) (.local .here))).run source =
      (.ok (.val (.int 7 (by decide))),sourcePost) :=
  source_assign_local_run G F0 fuel source (.there .here) .here _ rfl

def program : Source.Program E where
  body _ := none
  consts _ := none
  inits _ := []
  ctor _ := none
  ctorLocals _ := []
  baseArgs _ := []
  contracts := []
def globals (p : Roadmap.Pipeline) : Source.Glob E :=
  ⟨program,p,toyFixed,fun _ => word 0,fun _ _ => false,fun _ => .answer (.success []),word 0⟩

theorem mixed_actual_transport (p : Roadmap.Pipeline) (fuel : Nat)
    (hz : Source.IntTy.u8.lo ≤ 7-(if p = .legacy then 3 else 7) ∧
      7-(if p = .legacy then 3 else 7) ≤ Source.IntTy.u8.hi) :
    (Source.evalE (globals p) F0 (fuel+4)
      (.binary .sub (.assign (.local (.there .here)) (.local .here)) (.local (.there .here)))).run source =
      (.ok (.val (.int (7-(if p = .legacy then 3 else 7)) hz)),sourcePost) ∧
    (assignReadSubOperand p .u8 (.there .here) .here).run target =
      .ok (⟨post,List.prefix_refl _⟩,.prim (integerValue .u8 (7-(if p = .legacy then 3 else 7)) hz)) ∧
    IntValueRel .u8 (.int (7-(if p = .legacy then 3 else 7)) hz : Source.Val E.layout (.int .u8))
      (integerValue .u8 (7-(if p = .legacy then 3 else 7)) hz) :=
  assignment_subtraction_transport (globals p) F0 fuel source target .u8 (.there .here) .here
    (.there .here) .here 7 3 (by decide) (by decide) rfl rfl rfl rfl hz

end Solidity.Lowering.V07.MixedAssignmentControls
