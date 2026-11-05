import Solidity.Yul.Views.NewMemoryOperand
import Solidity.Yul.Views.NewMemoryControls

/-! Real effectful length expressions: postincrement determines the old length
but preserves the new local, size panic retains that prefix, and a later halt
retains a changed condition. Physical writeback uses the same reached state. -/
namespace Solidity.Yul.Views.NewMemoryOperand.Controls
open NewMemory.Controls

def post : Source.RExpr E [.int Source.IntTy.u256] (.int Source.IntTy.u256) := .incDec true false (.local .here)
def reached := state 4 (by decide)

theorem actual_post (G : Source.Glob E) (n : Nat) :
    (Source.evalE G F (n+3) post).run initial=(.ok (.val (Source.Val.int 3 (by decide))),reached) := rfl

theorem allocated_post (G : Source.Glob E) (n : Nat) :
    (Source.evalE G F (n+4) (.newArray (τ:=.bytes .memory) rfl post rfl)).run initial=
      (.ok (.val (.memRef rfl 0)),objectAllocatedState reached bytes) :=
  run G F (n+3) initial reached rfl post rfl _ (actual_post G n) 3 rfl (by decide) bytes rfl rfl

theorem panic_prefix (G : Source.Glob E) (n : Nat) :
    (Source.evalE G F (n+4) (.newArray (τ:=.bytes .memory) rfl post rfl)).run (state (2^64) (by decide))=
      (.error (.revert (Source.panicData .alloc)),state (2^64+1) (by decide)) :=
  panic G F (n+3) _ _ rfl post rfl (.val (Source.Val.int (2^64) (by decide))) rfl (2^64) rfl (by decide)

def lateInitial : Source.EMState E [.bool,.int Source.IntTy.u256] :=
  (.cons (.bool false) initial.1,initial.2)
def lateAfter : Source.EMState E [.bool,.int Source.IntTy.u256] :=
  (.cons (.bool true) initial.1,initial.2)
def late : Source.RExpr E [.bool,.int Source.IntTy.u256] (.int Source.IntTy.u256) :=
  .cond (.assign (.local .here) (.bool true))
    (.assign (.local (.there .here)) (.assign (.local (.there .here)) (.assign (.local (.there .here)) (.local (.there .here)))))
    (.local (.there .here))

theorem late_prefix (G : Source.Glob E) :
    (Source.evalE G F 5 (.newArray (τ:=.bytes .memory) rfl late rfl)).run lateInitial=(.error .timeout,lateAfter) :=
  halt G F 4 lateInitial lateAfter rfl late rfl .timeout rfl

/-- Resetting the reached length local would lose a real successful prefix. -/
theorem changed_local : reached.1.get Source.Idx.here≠initial.1.get Source.Idx.here := by
  intro same
  have words := congrArg Source.Val.word same
  exact (by decide : (some (4 : Roadmap.Word))≠some (3 : Roadmap.Word)) words

theorem physical_post (G : Source.Glob E) (n : Nat) :
    let q := ComputedAllocationWrite.placement reached.2.heap p rfl bytes (.bytes 3) rfl (by decide)
    let after := objectAllocatedState reached bytes
    encodeMixedHeap q (generatedHeapEntries q) raw=raw ∧
    enumeratedMemoryWriteback after q q (retainInitial _ _) raw=.ok (some (.ok (),after)) := by
  have ok : Source.MemOK E reached.2.heap.ty reached :=
    ⟨⟨⟨Source.HeapOK.empty,Source.HeapTy.Le.refl _⟩,⟨trivial,trivial⟩⟩,Source.HeapShaped.empty,Source.HeapInner.empty⟩
  have supported : ∀ a τ d,reached.2.heap.get a=some ⟨τ,d⟩ → InventoryTypeSupported E τ := by
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
  obtain ⟨output,step,actual,safe,whole,writeback,finalReserved⟩ := physical G F (n+3) initial reached rfl post rfl _
    (actual_post G n) 3 rfl (by decide) bytes rfl (.bytes 3) rfl p rfl (by decide) _ ok trivial (.bytes _)
    trivial supported input reads reserved
  have prepared : ComputedAllocationWrite.prepare reached.2.heap p rfl bytes (.bytes 3) rfl (by decide) input=some raw := rfl
  have same : output=raw := Option.some.inj (step.symm.trans prepared)
  subst output
  exact ⟨whole,writeback⟩
end Solidity.Yul.Views.NewMemoryOperand.Controls
