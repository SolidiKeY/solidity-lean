import Solidity.Lowering.V07.ReferenceCaptureRelated
import Solidity.Lowering.V07.P12Controls
import Solidity.Lowering.V07.ReferenceControls

namespace Solidity.Lowering.V07.ReferenceCaptureRelatedChecks
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

-- A predicate over existing values/references, not a new state/value semantics.
def PointerRel : (τ : Source.STy) → (u : LTy) → Source.Val E0.layout τ →
    u.TDenote ReferenceControls.C ReferenceControls.twinTarget.H → Prop
  | .bytes .memory,.mem (.array (.prim .uint)),.memRef _ address,some ref => address = ref.id
  | _,_,_,_ => False

local instance (address : Nat) (ref : Option (HRef ReferenceControls.twinTarget.H bytesR)) :
    Decidable (PointerRel (.bytes .memory) (.mem bytesR) (.memRef rfl address) ref) :=
  match ref with
  | none => inferInstanceAs (Decidable False)
  | some r => inferInstanceAs (Decidable (address = r.id))

example : PointerRel (.bytes .memory) (.mem bytesR) (.memRef rfl 0)
    (some ReferenceControls.twinOld) := by decide
example : ¬ PointerRel (.bytes .memory) (.mem bytesR) (.memRef rfl 0)
    (some ReferenceControls.twinNew) := by decide
example : ¬ PointerRel (.bytes .memory) (.mem bytesR) (.memRef rfl 0) none := by decide
example : ReferenceControls.twinHeap.get 0 = ReferenceControls.twinHeap.get 1 ∧
    ReferenceControls.twinOld ≠ ReferenceControls.twinNew ∧
    ReferenceControls.twinTarget.heap.get ReferenceControls.twinOld =
      ReferenceControls.twinTarget.heap.get ReferenceControls.twinNew :=
  ReferenceControls.equal_content_distinct_identities

-- Position-valid metadata can still select the wrong live, equal-content object.
def wrongMap : ContextMap [.bytes .memory] ReferenceControls.TgtCtx :=
  (ContextMap.empty.wk (Thin.drop (t := .mem bytesR) .refl)).cons
    (.bytes .memory) (.mem bytesR)
example : ¬ wrongMap.Related PointerRel (.cons (.memRef rfl 0) .nil)
    ReferenceControls.twinTarget.env := by
  intro aligned
  have bad := aligned (Source.Idx.here)
  change (0 : Nat) = 1 at bad
  omega

-- Complete mixed caller observations BEFORE the temporary drops.
example : TEnv.get (.there mj) memoryPost.env = some memoryRef := rfl
example : TEnv.get (.there sj) memoryPost.env = some MixedAssignmentControls.storageRef := rfl
example : TEnv.get (.there (.here : Idx TgtCtx (.val .bool))) memoryPost.env = false := by decide
example : memoryPost.glob = target.glob := rfl

def actualMemoryId : Option Nat := match (memoryCapture mj rfl).run target with
  | .ok out => (TEnv.get .here out.st.env).map HRef.id
  | .error _ => none

def actualStoragePresent : Bool := match (storageCapture sj).run target with
  | .ok out => (TEnv.get .here out.st.env).isSome
  | .error _ => false

def actualSourceId (p : Roadmap.Pipeline) (fuel : Nat) : Option Nat :=
  match (Source.evalE (MixedAssignmentControls.globals p) F0 fuel (.local mi)).run source with
  | (.ok (.val (.memRef _ address)),_) => some address
  | _ => none

/-- info: [true, true, true, true, true, true, true, false, false] -/
#guard_msgs in
#eval IO.println (reprStr [actualMemoryId == some 0, actualStoragePresent,
  actualSourceId .legacy 1 == some 0, actualSourceId .viaIR 1 == some 0,
  actualSourceId .legacy 0 == none,
  TEnv.get (.there (.here : Idx TgtCtx (.val .bool))) memoryPost.env == false,
  decide (ReferenceControls.twinOld.id ≠ ReferenceControls.twinNew.id),
  decide (PointerRel (.bytes .memory) (.mem bytesR) (.memRef rfl 0) (some ReferenceControls.twinNew)),
  decide (PointerRel (.bytes .memory) (.mem bytesR) (.memRef rfl 0) none)])
end Solidity.Lowering.V07.ReferenceCaptureRelatedChecks
