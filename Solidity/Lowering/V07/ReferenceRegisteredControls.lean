import Solidity.Lowering.V07.ReferenceCaptureRelated
import Solidity.Lowering.V07.P12Controls
import Solidity.Lowering.V07.ReferenceControls
import Solidity.Lowering.V07.ReferenceOrderRelated
import Solidity.Lowering.V07.ContextMapWrite

namespace Solidity.Lowering.V07.RegisteredCaptureClients
open Source.SemanticsExamples P12Controls
abbrev mi : Source.Idx SrcCtx (.bytes .memory) := .there (.there (.there (.there .here)))
abbrev mj : Idx TgtCtx (.mem bytesR) := .there (.there (.there (.there .here)))
abbrev si : Source.Idx SrcCtx (.bytes .storage) := .there (.there (.there (.there (.there .here))))
abbrev sj : Idx TgtCtx (.alias bytesR) := .there (.there (.there (.there (.there .here))))
def memoryPost := target.push (t := .mem bytesR) (some memoryRef)
def storagePost := target.push (t := .alias bytesR) (some MixedAssignmentControls.storageRef)

def memoryWitness (p : Roadmap.Pipeline) (fuel : Nat) :=
  related_memory_capture (MixedAssignmentControls.globals p) F0 fuel source target
    mapping BindingRel initial mi mj 0 memoryRef rfl rfl rfl

def storageWitness (p : Roadmap.Pipeline) (fuel : Nat) :=
  related_storage_capture (MixedAssignmentControls.globals p) F0 fuel source target
    mapping BindingRel initial si sj MixedAssignmentControls.path
    MixedAssignmentControls.storageRef rfl rfl rfl

-- Both actual pipeline runs and fresh getter observations are inhabited.
example (p : Roadmap.Pipeline) (fuel : Nat) :
    (Source.evalE (MixedAssignmentControls.globals p) F0 (fuel+1) (.local mi)).run source =
      (.ok (.val (.memRef rfl 0)),source) := (memoryWitness p fuel).1
example (p : Roadmap.Pipeline) :
    (memoryCapture mj rfl).run target = .ok (⟨memoryPost,List.prefix_refl _⟩) :=
  (memoryWitness p 0).2.1
example (p : Roadmap.Pipeline) :
    (SPath.alias .here : SPath C (.alias bytesR :: TgtCtx) (.ref bytesR)).resolveT storagePost =
      .ok MixedAssignmentControls.storageRef := (storageWitness p 0).2.2.1
example : BindingRel (.bytes .memory) (.mem bytesR) (.memRef rfl 0) (some memoryRef) :=
  (memoryWitness .legacy 0).2.2.2.1
example : (mapping.cons (.bytes .memory) (.mem bytesR)).Related BindingRel
    (.cons (.memRef rfl 0) source.1) memoryPost.env := (memoryWitness .viaIR 0).2.2.2.2.1
example : (mapping.wk (Thin.drop (t := .alias bytesR) .refl)).Related BindingRel
    source.1 storagePost.env := (storageWitness .viaIR 0).2.2.2.2.2.1
example : memoryPost.drop (.push .refl) = target := (memoryWitness .legacy 0).2.2.2.2.2.2
example : storagePost.drop (.push .refl) = target := (storageWitness .viaIR 0).2.2.2.2.2.2
example : ((mapping.wk (Thin.drop (t := .mem bytesR) .refl)).slot mi).2.toNat ≠ 0 :=
  capture_fresh_position mapping mi (.mem bytesR)
example : source.2.heap.get 0 = some ⟨.bytes .memory,.bytes [0,0]⟩ ∧
    target.heap.len memoryRef .dyn = 2 ∧
    E.pathTy MixedAssignmentControls.path = some (.bytes .storage) := live_memory_and_storage

end Solidity.Lowering.V07.RegisteredCaptureClients

namespace Solidity.Lowering.V07.RegisteredReferenceOrderClients
open Source.SemanticsExamples
abbrev E := P12Controls.E
abbrev C := P12Controls.C
abbrev SrcCtx := Source.STy.bytes .memory :: P12Controls.SrcCtx
abbrev TgtCtx := LTy.mem bytesR :: P12Controls.TgtCtx

def source : Source.EMState E SrcCtx :=
  (.cons (.memRef rfl 1) P12Controls.source.1,
    {P12Controls.source.2 with heap :=
      (P12Controls.source.2.heap.alloc ⟨.bytes .memory,.bytes [0,0,0]⟩).1})
def target : State C TgtCtx :=
  P12Controls.target.allocPush (zerosObj P12Controls.target.H 3 (by decide))
def old : HRef target.H bytesR := ⟨0,rfl⟩
def assigned : HRef target.H bytesR := ⟨1,rfl⟩
def mapping : ContextMap SrcCtx TgtCtx :=
  P12Controls.mapping.cons (.bytes .memory) (.mem bytesR)
def Rel : (τ : Source.STy) → (u : LTy) → Source.Val E.layout τ → u.TDenote C target.H → Prop
  | .bool,.val .bool,v,b => v = .bool b
  | .int t,.val .uint,v,n => t.signed = false ∧ v.key = PrimTy.num? n
  | .bytes .memory,.mem (.array (.prim .uint)),.memRef _ address,some ref => address = ref.id
  | .bytes .storage,.alias (.array (.prim .uint)),v,r =>
    v = .storRef rfl MixedAssignmentControls.path ∧ r = some MixedAssignmentControls.storageRef
  | _,_,_,_ => False

def Alignment : Prop := mapping.Related Rel source.1 target.env

def initial : Alignment := by
  refine ContextMap.related_cons _ _ _ _ ?_ _ _ _ _ rfl
  refine ContextMap.related_cons _ _ _ _ ?_ _ _ _ _ rfl
  refine ContextMap.related_cons _ _ _ _ ?_ _ _ _ _ rfl
  refine ContextMap.related_cons _ _ _ _ ?_ _ _ _ _ ⟨rfl,rfl⟩
  refine ContextMap.related_cons _ _ _ _ ?_ _ _ _ _ ⟨rfl,rfl⟩
  refine ContextMap.related_cons _ _ _ _ ?_ _ _ _ _ rfl
  refine ContextMap.related_cons _ _ _ _ ?_ _ _ _ _ ⟨rfl,rfl⟩
  exact fun {_} i => nomatch i

abbrev i : Source.Idx SrcCtx (.bytes .memory) :=
  .there (.there (.there (.there (.there .here))))
abbrev j : Idx TgtCtx (.mem bytesR) :=
  .there (.there (.there (.there (.there .here))))
abbrev storageIndex : Idx TgtCtx (.alias bytesR) :=
  .there (.there (.there (.there (.there (.there .here)))))

def sourcePost : Source.EMState E SrcCtx := (source.1.set i (.memRef rfl 1),source.2)
def reached (p : Roadmap.Pipeline) : State C (.mem bytesR :: .mem bytesR :: TgtCtx) :=
  ((target.setLocal j (some assigned)).push (t := .mem bytesR)
    (some (if p = .legacy then old else assigned))).push (t := .mem bytesR) (some assigned)

def witness (p : Roadmap.Pipeline) (fuel : Nat) :=
  related_reference_assignment_pair (MixedAssignmentControls.globals p) F0 fuel source target mapping Rel initial
    i .here j .here 0 1 old assigned rfl rfl rfl rfl rfl rfl

example (p : Roadmap.Pipeline) (fuel : Nat) :
    (Source.evalPair (MixedAssignmentControls.globals p) F0 (fuel+3)
      (.assign (.local i) (.local .here)) (.local i)).run source =
    (.ok (.val (.memRef rfl 1),.val (.memRef rfl (if p = .legacy then 0 else 1))),sourcePost) :=
  (witness p fuel).1
example (p : Roadmap.Pipeline) :
    (memoryAssignReadPrefix p j .here rfl).run target = .ok (⟨reached p,List.prefix_refl _⟩) :=
  (witness p 0).2.1
example (p : Roadmap.Pipeline) :
    ((mapping.wk (Thin.drop (t := .mem bytesR) .refl)).wk
      (Thin.drop (t := .mem bytesR) .refl)).Related Rel sourcePost.1 (reached p).env :=
  (witness p 0).2.2.2.2.1
example (p : Roadmap.Pipeline) :
    (reached p).drop (.push (.push .refl)) = target.setLocal j (some assigned) :=
  (witness p 0).2.2.2.2.2.1
example (p : Roadmap.Pipeline) : (reached p).glob = target.glob := (witness p 0).2.2.2.2.2.2

example : source.2.heap.get 0 = some ⟨.bytes .memory,.bytes [0,0]⟩ ∧
    source.2.heap.get 1 = some ⟨.bytes .memory,.bytes [0,0,0]⟩ := ⟨rfl,rfl⟩
example : E.pathTy MixedAssignmentControls.path = some (.bytes .storage) := rfl
example : TEnv.get storageIndex target.env = some MixedAssignmentControls.storageRef := rfl
example (p : Roadmap.Pipeline) :
    TEnv.get (.there (.there storageIndex)) (reached p).env = some MixedAssignmentControls.storageRef := rfl
example : sourcePost.2 = source.2 := rfl

end Solidity.Lowering.V07.RegisteredReferenceOrderClients
