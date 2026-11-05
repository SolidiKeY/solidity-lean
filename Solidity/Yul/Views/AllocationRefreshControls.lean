import Solidity.Yul.Views.AllocationRefresh
import Solidity.Source.Semantics

/-! Two actual allocations resume from a refreshed computed placement, deriving
second-input agreement. Future unused coordinates differ, while real objects,
padding, residual tail and complete unchanged Source writeback are retained. -/
namespace Solidity.Yul.Views.AllocationRefresh.Controls

def E : Source.Env := ⟨[]⟩
def initial : Source.EMState E [] := (.nil,Source.St.init E)
def first : Source.Data E.layout (.bytes .memory) := .bytes [255,0,128]
def second : Source.Data E.layout (.string .memory) := .string [17]
def p : Placement initial.2.heap := ComputedPlacement.build _ rfl (by decide)
def input : ByteView := mstore (fun i => if i=191 then 99 else if i=255 then 77 else if i=319 then 170 else 0) 64 128
def rawOne := (ComputedAllocationWrite.prepare initial.2.heap p rfl first (.bytes 3) rfl (by decide) input).getD input
def one := objectAllocatedState initial first
def q : Placement one.2.heap := placement initial.2.heap p rfl first (.bytes 3) rfl (by decide)
def incremental : Placement one.2.heap := ComputedAllocationWrite.placement initial.2.heap p rfl first (.bytes 3) rfl (by decide)
theorem q_ready : ComputedPlacement.prepare one.2.heap=.ok q := prepared _ _ _ _ _ _ _
def rawTwo := (ComputedAllocationWrite.prepare one.2.heap q q_ready second (.bytes 1) rfl (by decide) rawOne).getD rawOne

theorem first_step : ComputedAllocationWrite.prepare initial.2.heap p rfl first (.bytes 3) rfl (by decide) input=some rawOne := rfl
theorem second_step : ComputedAllocationWrite.prepare one.2.heap q q_ready second (.bytes 1) rfl (by decide) rawOne=some rawTwo := rfl

/-- Whole function equality would be false on an unoccupied future ID. -/
theorem future_coordinates : incremental.address 2=128 ∧ q.address 2=192 ∧
    incremental.address 0=q.address 0 ∧ q.free.val=192 ∧ incremental.address≠q.address := by
  first | (simp only;done) | decide | omega | rfl | skip
  refine ⟨rfl,rfl,rfl,rfl,?_⟩
  intro same
  have impossible := congrFun same 2
  change 128=192 at impossible
  contradiction

theorem physical_bytes : (mload rawTwo 64).val=256 ∧
    (mload rawTwo 128).val=3 ∧ readBytes rawTwo 160 3=[255,0,128] ∧
    (mload rawTwo 192).val=1 ∧ rawTwo 224=17 ∧ rawTwo 191=99 ∧
    rawTwo 255=77 ∧ rawTwo 319=170 := by decide

theorem whole_source_writeback :
    let finalPlacement := ComputedAllocationWrite.placement one.2.heap q q_ready second (.bytes 1) rfl (by decide)
    let after := objectAllocatedState one second
    encodeMixedHeap finalPlacement (generatedHeapEntries finalPlacement) rawTwo=rawTwo ∧
    enumeratedMemoryWriteback after finalPlacement finalPlacement (retainInitial _ _) rawTwo=.ok (some (.ok (),after)) := by
  have ok : Source.MemOK E initial.2.heap.ty initial :=
    ⟨⟨⟨Source.HeapOK.empty,Source.HeapTy.Le.refl _⟩,trivial⟩,Source.HeapShaped.empty,Source.HeapInner.empty⟩
  have supported : ∀ a τ d,initial.2.heap.get a=some ⟨τ,d⟩ → InventoryTypeSupported E τ := by
    intro a τ d found
    cases found
  have oldReads : ∀ e∈generatedHeapEntries p,e.image.Reads input (p.address e.id) := by
    intro e member
    cases member
  obtain ⟨finalRaw,next,actual,safe,encoded,writeback⟩ := resume initial.2.heap.ty initial p rfl first (.bytes 3) rfl
    (by decide) input rawOne first_step ok trivial (.bytes _) trivial supported oldReads
    second (.bytes 1) rfl (by decide) trivial (.string _) trivial
  have same : finalRaw=rawTwo := Option.some.inj (next.symm.trans second_step)
  subst finalRaw
  exact ⟨encoded,writeback⟩
theorem actual_retained_reads :
    let after := objectAllocatedState one second
    (Source.heapBytes (E:=E) (Γ:=[]) 0).run after=(.ok [255,0,128],after) ∧
    (Source.heapBytes (E:=E) (Γ:=[]) 1).run after=(.ok [17],after) := ⟨rfl,rfl⟩

def zero : Source.Data E.layout (.array .memory .bool (some 0)) :=
  .array 0 (fun _ equal => (Option.some.inj equal).symm) Fin.elim0

def zeroPlacement := placement initial.2.heap p rfl zero (.array false 0) rfl (by decide)

/-- Zero-footprint mathematical objects still use the existing max-one stride;
this is not a claim about a target allocator's address selection. -/
theorem zero_extent : zeroPlacement.address 0=128 ∧ zeroPlacement.free.val=129 ∧
    zeroPlacement.address 1=129 := ⟨rfl,rfl,rfl⟩
end Solidity.Yul.Views.AllocationRefresh.Controls
