import Solidity.Lowering.V07.EffectfulCondition
import Solidity.Lowering.V07.ReferenceCapture
import Solidity.Lowering.V07.MixedAssignmentControls

/-! Inhabited P12 interfaces, not an admitted-profile producer. BindingRel is
one discriminating witness relation on actual scalar/ref bindings. It is not
a replacement Source value/world semantics and has no compiler/run premise. -/
namespace Solidity.Lowering.V07.P12Controls
open Source.SemanticsExamples
abbrev C := MixedAssignmentControls.C
abbrev E := MixedAssignmentControls.E
abbrev SrcCtx : Source.RCtx := [.bool,.bool,.int .u8,.int .u8,.bytes .memory,.bytes .storage]
abbrev TgtCtx : Ctx := [.val .bool,.val .bool,.val .uint,.val .uint,.mem bytesR,.alias bytesR]

def source : Source.EMState E SrcCtx :=
  (.cons (.bool false) (.cons (.bool true) MixedAssignmentControls.source.1),MixedAssignmentControls.source.2)
def target : State C TgtCtx :=
  (MixedAssignmentControls.target.push (t := .val .bool) true).push (t := .val .bool) false

def mapping : ContextMap SrcCtx TgtCtx :=
  (((((ContextMap.empty.cons (.bytes .storage) (.alias bytesR)).cons
    (.bytes .memory) (.mem bytesR)).cons (.int .u8) (.val .uint)).cons
    (.int .u8) (.val .uint)).cons .bool (.val .bool)).cons .bool (.val .bool)

def memoryRef : HRef target.H bytesR :=
  (MixedAssignmentControls.base.alloc (zerosObj MixedAssignmentControls.base.H 2 (by decide))).2

/-- Only the actual witness's initial reference identity pairs are related.
In particular this is not a rule that arbitrary equal-content objects alias. -/
def BindingRel : (τ : Source.STy) → (u : LTy) → Source.Val E.layout τ → u.TDenote C target.H → Prop
  | .bool,.val .bool,v,b => v = .bool b
  | .int t,.val .uint,v,n => t.signed = false ∧ v.key = PrimTy.num? n
  | .bytes .memory,.mem (.array (.prim .uint)),v,r =>
    v = .memRef rfl 0 ∧ r = some memoryRef
  | .bytes .storage,.alias (.array (.prim .uint)),v,r =>
    v = .storRef rfl MixedAssignmentControls.path ∧ r = some MixedAssignmentControls.storageRef
  | _,_,_,_ => False

theorem initial : mapping.Related BindingRel source.1 target.env := by
  intro τ i
  cases i with
  | here => rfl
  | there i => cases i with
    | here => rfl
    | there i => cases i with
      | here => exact ⟨rfl,rfl⟩
      | there i => cases i with
        | here => exact ⟨rfl,rfl⟩
        | there i => cases i with
          | here => exact ⟨rfl,rfl⟩
          | there i => cases i with
            | here => exact ⟨rfl,rfl⟩
            | there i => nomatch i

theorem bool_reflect (v : Source.Val E.layout .bool) (b : Bool)
    (related : BindingRel .bool (.val .bool) v b) : v = .bool b := related

theorem reference_positions :
    mapping.slot (Source.Idx.there (.there (.there (.there .here))) : Source.Idx SrcCtx (.bytes .memory)) =
      ⟨.mem bytesR,.there (.there (.there (.there .here)))⟩ ∧
    mapping.slot (Source.Idx.there (.there (.there (.there (.there .here)))) : Source.Idx SrcCtx (.bytes .storage)) =
      ⟨.alias bytesR,.there (.there (.there (.there (.there .here))))⟩ := ⟨rfl,rfl⟩

theorem live_memory_and_storage :
    source.2.heap.get 0 = some ⟨.bytes .memory,.bytes [0,0]⟩ ∧
    target.heap.len memoryRef .dyn = 2 ∧
    E.pathTy MixedAssignmentControls.path = some (.bytes .storage) := by
  refine ⟨MixedAssignmentControls.source_memory_live,?_,MixedAssignmentControls.source_storage_typed⟩
  obtain ⟨r,read,length⟩ := MixedAssignmentControls.live_memory
  change some memoryRef = some r at read
  have same := Option.some.inj read
  rw [same]
  exact length

def sourcePost : Source.EMState E SrcCtx := (source.1.set .here (.bool true),source.2)
def targetPost : State C (.val .bool :: TgtCtx) :=
  (target.setLocal .here true).push (t := .val .bool) true

theorem actual_effectful_condition (p : Roadmap.Pipeline) (fuel : Nat) (checked : Bool) :
    (Source.evalE (MixedAssignmentControls.globals p) {F0 with checked := checked} (fuel+2)
      (.assign (.local .here) (.local (.there .here)))).run source =
        (.ok (.val (.bool true)),sourcePost) ∧
    (assignLocalOperand (.here : Idx TgtCtx (.val .bool)) (.there .here)).code.run target =
      .ok (⟨targetPost,List.prefix_refl _⟩) ∧
    (.simple (.local .here) : Val C (.val .bool :: TgtCtx) .bool).evalT targetPost = .ok true ∧
    (mapping.wk (Thin.drop (t := .val .bool) .refl)).Related BindingRel sourcePost.1 targetPost.env ∧
    targetPost.glob = target.glob :=
  condition_assignment_transport (MixedAssignmentControls.globals p) {F0 with checked := checked}
    fuel source target mapping BindingRel initial bool_reflect .here (.there .here)
      .here (.there .here) rfl rfl

theorem actual_condition_operand :
    (assignLocalOperand (.here : Idx TgtCtx (.val .bool)) (.there .here)).run target =
      .ok (⟨target.setLocal .here true,List.prefix_refl _⟩,.prim true) :=
  assigned_condition_operand_run target .here (.there .here)

def prefixChoice : Bool :=
  match (assignLocalOperand (.here : Idx TgtCtx (.val .bool)) (.there .here)).code.run target with
  | .ok out => TEnv.get .here out.st.env
  | .error _ => false

theorem captured_choice : prefixChoice = true := by
  unfold prefixChoice
  rw [(actual_effectful_condition .legacy 0 true).2.1]
  rfl

theorem stale_initial_choice_rejected : TEnv.get (.here : Idx TgtCtx (.val .bool)) target.env ≠ prefixChoice := by
  rw [captured_choice]
  decide

theorem nonlocal_frames :
    sourcePost.2 = source.2 ∧ targetPost.glob = target.glob ∧
    TEnv.get (.there (.there (.there (.there (.there .here))))) targetPost.env = some memoryRef ∧
    TEnv.get (.there (.there (.there (.there (.there (.there .here)))))) targetPost.env =
      some MixedAssignmentControls.storageRef := ⟨rfl,rfl,rfl,rfl⟩

theorem memory_capture_actual (p : Roadmap.Pipeline) (fuel : Nat) :
    (Source.evalE (MixedAssignmentControls.globals p) F0 (fuel+1)
      (.local (.there (.there (.there (.there .here)))))).run source =
        (.ok (.val (.memRef rfl 0)),source) ∧
    (memoryCapture (.there (.there (.there (.there .here)))) rfl).run target =
      .ok (⟨target.push (t := .mem bytesR) (some memoryRef),List.prefix_refl _⟩) ∧
    (MPath.var .here rfl : MPath C (.mem bytesR :: TgtCtx) (.ref bytesR)).mvalT
      (target.push (t := .mem bytesR) (some memoryRef)) = .ok memoryRef :=
  capture_memory_transport (MixedAssignmentControls.globals p) F0 fuel source target
    (.there (.there (.there (.there .here)))) (.there (.there (.there (.there .here))))
    0 memoryRef rfl rfl

theorem storage_capture_actual (p : Roadmap.Pipeline) (fuel : Nat) :
    (Source.evalE (MixedAssignmentControls.globals p) F0 (fuel+1)
      (.local (.there (.there (.there (.there (.there .here))))))).run source =
        (.ok (.val (.storRef rfl MixedAssignmentControls.path)),source) ∧
    (storageCapture (.there (.there (.there (.there (.there .here)))))).run target =
      .ok (⟨target.push (t := .alias bytesR) (some MixedAssignmentControls.storageRef),List.prefix_refl _⟩) ∧
    (SPath.alias .here : SPath C (.alias bytesR :: TgtCtx) (.ref bytesR)).resolveT
      (target.push (t := .alias bytesR) (some MixedAssignmentControls.storageRef)) =
        .ok MixedAssignmentControls.storageRef :=
  capture_storage_transport (MixedAssignmentControls.globals p) F0 fuel source target
    (.there (.there (.there (.there (.there .here))))) (.there (.there (.there (.there (.there .here)))))
    MixedAssignmentControls.path MixedAssignmentControls.storageRef rfl rfl

/-- Equal scalar contents do not make two differently typed Source bindings
one local. The complete context certificate rejects this collapse. -/
theorem collapsed_width_positions_rejected :
    ¬ ∃ m : ContextMap [.int .u8,.int .u256] [.val .uint,.val .uint],
      m.slot (Source.Idx.here : Source.Idx [.int .u8,.int .u256] (.int .u8)) = ⟨.val .uint,.here⟩ ∧
      m.slot (Source.Idx.there .here : Source.Idx [.int .u8,.int .u256] (.int .u256)) = ⟨.val .uint,.here⟩ := by
  rintro ⟨m,first,second⟩
  have impossible : (0 : Nat) = 1 := (m.positions
    (Source.Idx.here : Source.Idx [.int .u8,.int .u256] (.int .u8))
    (Source.Idx.there .here : Source.Idx [.int .u8,.int .u256] (.int .u256))).mpr (by rw [first,second])
  omega

end Solidity.Lowering.V07.P12Controls
