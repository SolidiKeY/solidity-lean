import Solidity.Backend.InternalFlow.RuntimeFrameFootprint
import Solidity.Evm.MemoryCapture

/-! Runtime word restoration into the ORIGINAL caller cell, using only the
existing instruction semantics. Local restoration does not restore heap
contents, create a failed State or provide an unbounded call dispatcher. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.Restore
open Evm Evm.Memory
variable {C : Contract}

def code (destination pointerCell : Nat) : List Instr :=
 Stack.popCode pointerCell ++ [.mstore destination]

def restored (m : Machine) (destination pointerCell : Nat) (address : Fin W) : Machine :=
 {m with mem := upd (upd m.mem pointerCell (.val (wmod (address.val - 1)))) destination (m.mem (address.val - 1))}

/-- Consume the popped word into its genuine caller destination. The entire
previous evaluation stack survives; only pointer and destination memory cells
change. Separation is about the actual pointer and payload, not a type cast. -/
theorem run (m : Machine) (destination pointerCell : Nat) (address : Fin W)
 (pointer : m.mem pointerCell = .val address) (positive : 0 < address.val)
 (separate : pointerCell ≠ address.val - 1) :
 Evm.run (code destination pointerCell) m = .ok (restored m destination pointerCell address) 0 := by
 rw [code,Evm.run_append_ok (Stack.pop_run m pointerCell address pointer positive separate)]
 rfl

theorem stack (m : Machine) (destination pointerCell : Nat) (address : Fin W) :
 (restored m destination pointerCell address).stack = m.stack := rfl

theorem destination (m : Machine) (destination pointerCell : Nat) (address : Fin W) :
 (restored m destination pointerCell address).mem destination = m.mem (address.val - 1) :=
 upd_same _ _ _

theorem outside (m : Machine) (destination pointerCell : Nat) (address : Fin W)
 (x : Nat) (notPointer : x ≠ pointerCell) (notDestination : x ≠ destination) :
 (restored m destination pointerCell address).mem x = m.mem x := by
 simp only [restored,upd,if_neg notDestination,if_neg notPointer]

/-- A temporary clobber followed by writing the ACTUAL recovered top word.
This models physical local-cell reuse; it is not a new source assignment. -/
def consumeCode (destination : Nat) (temporary : Word) : List Instr :=
 [.push temporary,.mstore destination,.mstore destination]

theorem consume_run (m : Machine) (destination : Nat) (temporary value : Word)
 (tail : List Word) (top : m.stack = value :: tail) (same : m.mem destination = value) :
 Evm.run (consumeCode destination temporary) m = .ok {m with stack := tail} 0 := by
 have memory : upd (upd m.mem destination temporary) destination value = m.mem := by
  funext x
  by_cases equal : x = destination
  · subst x
    simp only [upd,↓reduceIte,same]
  · simp only [upd,if_neg equal]
 simp only [consumeCode,Evm.run,exec_cons_zero,Instr.step,Machine.next,
   Out.ok_bind,exec_nil,top]
 rw [memory]

/-- Consuming a stack word that equals the caller cell's current content keeps
the reached `StateRepr`. Both the representation and the cell content are
premises; recovery after a clobber is `restore_context` in
`RuntimeFrameContext`. -/
theorem local_repr {L b frame : Nat} {Γ : Ctx} {F : Frag Γ}
 {σ : State C Γ} {base : Nat → Fin W} {m : Machine}
 (repr : StateRepr L b frame F σ base m) {t : LTy} (index : Idx Γ t)
 (temporary value : Word) (tail : List Word)
 (top : m.stack = value :: tail) (same : m.mem (cellOf b index) = value) :
 Evm.run (consumeCode (cellOf b index) temporary) m = .ok {m with stack := tail} 0 ∧
 StateRepr L b frame F σ base {m with stack := tail} :=
 ⟨consume_run m _ temporary value tail top same,repr.stack tail⟩

theorem uint_unique {v : PrimTy.uint.Denote} {a b : Word}
 (left : ReprV .uint v a) (right : ReprV .uint v b) : a = b := by
 obtain ⟨x,hax,hx⟩ := left
 obtain ⟨y,hby,hy⟩ := right
 rw [hax,hby]
 congr 1
 apply Fin.ext
 exact Int.ofNat_inj.mp (hx.symm.trans hy)

/-- Actual successful fragment composition; its Words proof must be derived
from the checked producer. No failed machine/rollback conclusion is supplied. -/
theorem after_fragment {lo hi : Nat} {before after : Machine} {body : List Instr}
 (executed : Evm.run body before = .ok after 0) (words : Footprint.Words lo hi before after)
 (destination pointerCell : Nat) (address : Fin W)
 (pointer : before.mem pointerCell = .val address) (positive : 0 < address.val)
 (separate : pointerCell ≠ address.val - 1)
 (headerLower : lo ≤ pointerCell) (headerUpper : pointerCell < hi)
 (payloadLower : lo ≤ address.val - 1) (payloadUpper : address.val - 1 < hi) :
 Evm.run (body ++ code destination pointerCell) before =
   .ok (restored after destination pointerCell address) 0 ∧
 (restored after destination pointerCell address).mem destination = before.mem (address.val - 1) ∧
 (restored after destination pointerCell address).stack = after.stack := by
 refine ⟨?_,?_,rfl⟩
 · rw [Evm.run_append_ok executed]
   exact run after destination pointerCell address
     ((words pointerCell headerLower headerUpper).trans pointer) positive separate
 · exact (Restore.destination after destination pointerCell address).trans
     (words (address.val - 1) payloadLower payloadUpper)

/-- Physical caller cells are derived from the original intrinsic context,
including memory references, primitive values and storage-alias words. -/
def contextCells (b : Nat) (Γ : Ctx) : List Nat :=
 (List.range Γ.length).map (fun n => b + n)

theorem cell_member (b : Nat) {Γ : Ctx} {t : LTy} (index : Idx Γ t) :
 cellOf b index ∈ contextCells b Γ := by
 have lower := le_lvl b index
 have upper := lvl_lt b index
 apply List.mem_map.mpr
 refine ⟨lvl b index - b,List.mem_range.mpr (by omega),?_⟩
 change b + (lvl b index - b) = lvl b index
 omega

/-- Only emit existing save/restore slices; no state evaluator is defined. -/
def saveCells (pointerCell : Nat) : List Nat → List Instr
 | [] => []
 | source :: rest => saveCode source pointerCell ++ saveCells pointerCell rest

def restoreCells (pointerCell : Nat) : List Nat → List Instr
 | [] => []
 | source :: rest => restoreCells pointerCell rest ++ code source pointerCell

end Solidity.Backend.InternalFlow.RuntimeFrame.Restore
