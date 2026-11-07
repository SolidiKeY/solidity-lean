import Solidity.Yul.Adapters.SelectedPhysicalStore
import Solidity.Yul.Views.ResidualMemoryWriteback

/-! The existing computed residual-window check supplies byte geometry and
reserved-word separation to the existing physical-store compiler consumer.
No new planner, state, admission predicate or allocator is introduced. Current
image padding is not a promise about future regrowth or memory resources. -/
namespace Solidity.Yul.Adapters.CheckedResidualStore
open Solidity.Yul.Views Solidity.Yul.Views.NominalInventory
open Solidity.Backend Solidity.Yul.Compilation

/-- One actual copied byte is the existing low-byte store on the WHOLE map. -/
theorem copy_one (m : ByteView) (destination : Nat) (value : Roadmap.Word) :
    copyBytes m (fun _ => UInt8.ofNat value.val) destination 0 1=mstore8 m destination value := by
  first
  | solve | rfl
  | solve | simp only
  | funext a
    by_cases same : a=destination
    · subst a
      simp only [copyBytes,Nat.le_refl,Nat.lt_add_one,and_self,if_true,mstore8,saveByte]
    · have outside : ¬(destination≤a ∧ a<destination+1) := by omega
      simp only [copyBytes,if_neg outside,mstore8,saveByte,if_neg same]

/-- This is derived from actual checked intervals, including zero-span images. -/
theorem byte_outside {D : Source.Layout} {h : Source.Heap D} {p : Placement h}
    (plan : ResidualWindowPlan p) (one : plan.size.val=1) :
    ∀ e ∈ plan.entries,plan.destination.val<p.address e.id ∨
      p.address e.id+e.image.span≤plan.destination.val := by
  intro e member
  have checked := plan.facts.2.2 e member
  rw [one] at checked
  rcases checked with empty | zero | before | after <;> omega

/-- Exact updated complement representation, without zeroing padding or gaps. -/
theorem byte_map {D : Source.Layout} {h : Source.Heap D} {p : Placement h}
    (plan : ResidualWindowPlan p) (one : plan.size.val=1)
    (residual : ByteView) (value : Roadmap.Word) :
    mstore8 (encodeMixedHeap p plan.entries residual) plan.destination.val value=
      encodeMixedHeap p plan.entries (mstore8 residual plan.destination.val value) := by
  have actual := plan.whole_map residual (fun _ => UInt8.ofNat value.val) 0
  rw [one,copy_one,copy_one] at actual
  exact actual

/-- Reserved validity starts on the residual carrier. Encoding and the checked
byte update derive validity of BOTH reserved words on the complete output map. -/
theorem byte_reserved {D : Source.Layout} {h : Source.Heap D} {p : Placement h}
    (plan : ResidualWindowPlan p) (one : plan.size.val=1)
    (residual : ByteView) (value : Roadmap.Word) (reserved : ReservedOK residual p.free) :
    ReservedOK (mstore8 (encodeMixedHeap p plan.entries residual) plan.destination.val value) p.free := by
  have preserved := plan.reserved residual (fun _ => UInt8.ofNat value.val) 0 reserved
  rw [one,copy_one] at preserved
  rw [byte_map plan one residual value]
  exact encodeMixedHeap_reserved p plan.entries _ preserved

/-- Actual successful preparation computes the inventory and all byte geometry.
The compiled byte instruction changes only the raw complement, preserves the
WHOLE Source state and both reserved words, and retains every initial H.
This is a checked canonical component, not a language refusal or allocation law. -/
theorem prepared_byte {E : Source.Env} {Γ : Source.RCtx} {origin : Source.Heap E.layout}
    (allocated : Placement origin) (s : Source.EMState E Γ) (p : Placement s.2.heap)
    (history : RetainedAllocation allocated p) (destination value : Roadmap.Word)
    (plan : ResidualWindowPlan p)
    (ready : prepareResidualWindow p destination 1=.ok (some plan))
    (supported : ∀ a ty d,s.2.heap.get a=some ⟨ty,d⟩ → TypeSupported E ty)
    (residual : ByteView) (reserved : ReservedOK residual p.free)
    (F : Environment.Frame) (tail : List Environment.Word) :
    let raw := encodeMixedHeap p plan.entries residual
    let after := mstore8 raw destination.val value
    ∃ next,PhysicalSnapshotSlice.applySlice allocated s ⟨p,history,plan.entries⟩ F
      (PhysicalStore.byteCode destination value) ⟨tail,raw⟩=some (⟨tail,after⟩,some next) ∧
      next.1=s ∧ after=encodeMixedHeap p plan.entries (mstore8 residual destination.val value) ∧
      ReservedOK raw p.free ∧ ReservedOK after p.free ∧
      (∀ H : Source.HeapTy,Source.MemOK E H s → Source.MemOK E H next.1) := by
  first
  | solve | simp only
  | have metadata := prepareResidualWindow_metadata p destination 1 plan ready
    have one : plan.size.val=1 := congrArg Fin.val metadata.2
    have sameDestination := metadata.1
    subst destination
    obtain ⟨next,actual,same⟩ := SelectedPhysicalStore.byte_residual_identity allocated s p history plan.entries
      plan.inventory.2.1 plan.inventory.2.2 (fun e _ => supported e.id e.ty e.data e.found)
      residual F plan.destination value tail (byte_outside plan one)
    exact ⟨next,actual,same,byte_map plan one residual value,
      encodeMixedHeap_reserved p plan.entries residual reserved,byte_reserved plan one residual value reserved,
      fun H ok => same.symm ▸ ok⟩

end Solidity.Yul.Adapters.CheckedResidualStore
