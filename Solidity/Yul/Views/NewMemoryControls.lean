import Solidity.Yul.Views.NewMemory
import Solidity.Source.Semantics

/-! Actual new bytes/bool[] producers, static allocation, exact allocation panic
and timeout. Physical witness preserves nonzero padding and unknown bytes;
none of these seeded kernel controls asserts a target allocation policy. -/
namespace Solidity.Yul.Views.NewMemory.Controls

def E : Source.Env := ⟨[]⟩
def F : Source.Fr := {this:=1,sender:=2,value:=0,static:=true,contract:="NewMemory",cd:=[]}
def state (length : Nat) (fits : Source.IntTy.u256.lo≤(length : Int) ∧ (length : Int)≤Source.IntTy.u256.hi) :
    Source.EMState E [.int Source.IntTy.u256] := (.cons (.int length fits) .nil,Source.St.init E)
def initial := state 3 (by decide)
def bytes : Source.Data E.layout (.bytes .memory) := .bytes [0,0,0]
def bools : Source.Data E.layout (.array .memory .bool none) :=
  .array 3 (fun _ impossible => nomatch impossible) (fun _ => .val (.bool false))
def p : Placement initial.2.heap := ComputedPlacement.build _ rfl (by decide)
def input : ByteView := mstore (fun i=>if i=191 then 99 else if i=319 then 170 else 0) 64 128
def raw := (ComputedAllocationWrite.prepare initial.2.heap p rfl bytes (.bytes 3) rfl (by decide) input).getD input

theorem source_bytes (G : Source.Glob E) (n : Nat) :
    (Source.evalE G F (n+2) (expr (τ:=.bytes .memory) rfl .here)).run initial=
      (.ok (.val (.memRef rfl 0)),objectAllocatedState initial bytes) :=
  run G F n initial rfl .here 3 (by decide) rfl (by decide) bytes rfl rfl

theorem source_bools (G : Source.Glob E) (n : Nat) :
    (Source.evalE G F (n+2) (expr (τ:=.array .memory .bool none) rfl .here)).run initial=
      (.ok (.val (.memRef rfl 0)),objectAllocatedState initial bools) :=
  run G F n initial rfl .here 3 (by decide) rfl (by decide) bools rfl rfl

theorem exact_panic (G : Source.Glob E) (n : Nat) :
    (Source.evalE G F (n+2) (expr (τ:=.bytes .memory) rfl .here)).run (state (2^64) (by decide))=
      (.error (.revert (Source.panicData .alloc)),state (2^64) (by decide)) :=
  panic G F n _ rfl .here (2^64) (by decide) rfl (by decide)

theorem timeout (G : Source.Glob E) :
    (Source.evalE G F 1 (expr (τ:=.bytes .memory) rfl .here)).run initial=(.error .timeout,initial) :=
  (low G F initial rfl .here).2

theorem physical_bytes : (mload raw 64).val=192 ∧ (mload raw 128).val=3 ∧
    readBytes raw 160 3=[0,0,0] ∧ raw 191=99 ∧ raw 319=170 := by decide

theorem actual_physical (G : Source.Glob E) (n : Nat) :
    let q := ComputedAllocationWrite.placement initial.2.heap p rfl bytes (.bytes 3) rfl (by decide)
    let after := objectAllocatedState initial bytes
    encodeMixedHeap q (generatedHeapEntries q) raw=raw ∧
    enumeratedMemoryWriteback after q q (retainInitial _ _) raw=.ok (some (.ok (),after)) := by
  have ok : Source.MemOK E initial.2.heap.ty initial :=
    ⟨⟨⟨Source.HeapOK.empty,Source.HeapTy.Le.refl _⟩,⟨trivial,trivial⟩⟩,Source.HeapShaped.empty,Source.HeapInner.empty⟩
  have supported : ∀ a τ d,initial.2.heap.get a=some ⟨τ,d⟩ → InventoryTypeSupported E τ := by
    intro a τ d found
    cases found
  have reads : ∀ e∈generatedHeapEntries p,e.image.Reads input (p.address e.id) := by
    intro e member
    cases member
  have reserved : ReservedOK input p.free := by
    constructor
    · exact congrArg Fin.val (mload_mstore (fun i=>if i=191 then 99 else if i=319 then 170 else 0) 64 128)
    · intro i
      rw [input,mstore_outside _ _ _ _ (by have hi:=i.isLt;omega)]
      have hi:=i.isLt
      rw [if_neg (by omega),if_neg (by omega)]
  obtain ⟨output,step,actual,safe,whole,writeback,finalReserved⟩ :=
    physical G F n initial rfl .here 3 (by decide) rfl (by decide) bytes rfl (.bytes 3) rfl p rfl
      (by decide) _ ok trivial (.bytes _) trivial supported input reads reserved
  have prepared : ComputedAllocationWrite.prepare initial.2.heap p rfl bytes (.bytes 3) rfl (by decide) input=some raw := rfl
  have same : output=raw := Option.some.inj (step.symm.trans prepared)
  subst output
  exact ⟨whole,writeback⟩
end Solidity.Yul.Views.NewMemory.Controls
