import Solidity.Backend.InternalFlow.RuntimeFrameStack
import Solidity.Evm.MemoryScope
import Solidity.Evm.MemoryLocals

/-! A runtime frame word saved outside all caller locals and below all heap
objects preserves the FULL existing typed memory representation. Scalar and
reference captures read actual represented caller cells. No callee footprint
or recursive-call simulation is assumed or claimed here. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame
open Evm Evm.Memory
variable {C : Contract} {Γ : Ctx} {L b frame : Nat} {F : Frag Γ}
  {σ : State C Γ} {base : Nat → Fin W} {m : Machine}

/-- Input invariant for ONE runtime frame-word operation. This is a proof
relation over the existing typed state and target machine, not another state.
A later push must establish its next payload bounds and separation anew. -/
structure Arena (L b frame : Nat) {Γ : Ctx} (F : Frag Γ) (σ : State C Γ)
    (base : Nat → Fin W) (m : Machine) (pointerCell : Nat) (address : Fin W) : Prop where
  state : StateRepr L b frame F σ base m
  pointer : m.mem pointerCell = .val address
  pointerAbove : b + Γ.length ≤ pointerCell
  pointerBelow : pointerCell < frame
  payloadAbove : b + Γ.length ≤ address.val
  payloadBelow : address.val < frame
  separate : pointerCell ≠ address.val
  noWrap : 1 + address.val < W

/-- Reserve an actual scratch/frame cell without changing any represented
local, scalar/storage alias, array/struct/reference field, root or environment. -/
theorem reserved_write (repr : StateRepr L b frame F σ base m)
    (address : Nat) (above : b + Γ.length ≤ address) (below : address < frame) (value : Word) :
    StateRepr L b frame F σ base (writeMachine m address value) := by
  have unchanged {t : LTy} (i : Idx Γ t) :
      (writeMachine m address value).memAt (lvl b i) = m.memAt (lvl b i) :=
    upd_other m.mem value (by change lvl b i ≠ address; have bound := lvl_lt b i; omega)
  constructor
  · refine ⟨repr.core.store,?_,?_,repr.core.net,repr.core.netSelf,repr.core.bound,
      ?_,repr.core.env,repr.core.funds,repr.core.oracle⟩
    · intro p i
      rw [unchanged i]
      exact repr.core.vals i
    · intro R i flag
      obtain ⟨r,slot,hr,hm,path⟩ := repr.core.aliases i flag
      exact ⟨r,slot,hr,(unchanged i).trans hm,path⟩
    · intro R i flag
      obtain ⟨r,slot,hr,hm,path,live⟩ := repr.core.fragile i flag
      exact ⟨r,slot,hr,(unchanged i).trans hm,path,live⟩
  · exact repr.heap.localWrite address below value
  · intro R i
    obtain ⟨r,hr,hm⟩ := repr.pointers i
    exact ⟨r,hr,(unchanged i).trans hm⟩
  · exact repr.locals
  · exact repr.structs.localWrite address below value
  · exact repr.separated
  · exact RefFieldsRepr.localWrite repr.refs repr.structs address below value

theorem pushed_repr (repr : StateRepr L b frame F σ base m)
    (pointerCell : Nat) (address : Fin W) (value : Word)
    (pointerAbove : b + Γ.length ≤ pointerCell) (pointerBelow : pointerCell < frame)
    (payloadAbove : b + Γ.length ≤ address.val) (payloadBelow : address.val < frame) :
    StateRepr L b frame F σ base (Stack.pushed m pointerCell address value) :=
  reserved_write (reserved_write repr address.val payloadAbove payloadBelow value)
    pointerCell pointerAbove pointerBelow (.val (wmod (1 + address.val)))

/-- Frame saves below the heap consume ZERO allocation cells. The allocator
cell itself is excluded by the genuine positive-base and slot bounds. -/
theorem pushed_allocator (pointerCell : Nat) (address : Fin W) (value : Word)
    (pointerAbove : b + Γ.length ≤ pointerCell) (pointerBelow : pointerCell < frame)
    (payloadAbove : b + Γ.length ≤ address.val) (payloadBelow : address.val < frame) :
    GrowsAllocator b frame 0 σ base m σ base (Stack.pushed m pointerCell address value) := by
  intro cursor positive alloc space
  simpa only [Nat.add_zero] using
    (alloc.localWrite address.val (by omega) payloadBelow value).localWrite
      pointerCell (by omega) pointerBelow (.val (wmod (1 + address.val)))

def saveCode (source pointerCell : Nat) : List Instr := [.mload source] ++ Stack.pushCode pointerCell

theorem save_word_run (m : Machine) (source pointerCell : Nat) (address : Fin W)
    (pointer : m.mem pointerCell = .val address) (separate : pointerCell ≠ address.val) :
    Evm.run (saveCode source pointerCell) m = .ok (Stack.pushed m pointerCell address (m.mem source)) 0 := by
  have load : Evm.run [.mload source] m = .ok (m.push (m.mem source)) 0 := rfl
  rw [saveCode,Evm.run_append_ok load]
  exact Stack.push_run m pointerCell address _ pointer separate

/-- Popping changes only the reserved pointer cell and evaluation stack, not
any typed caller binding, root or represented heap object. -/
theorem popped_repr (repr : StateRepr L b frame F σ base m)
    (pointerCell : Nat) (address : Fin W)
    (pointerAbove : b + Γ.length ≤ pointerCell) (pointerBelow : pointerCell < frame) :
    StateRepr L b frame F σ base (Stack.popped m pointerCell address) :=
  (reserved_write repr pointerCell pointerAbove pointerBelow (.val (wmod (address.val - 1)))).push
    (m.mem (address.val - 1))

/-- Save the REAL caller memory identity, including two aliases of the same
object. No reference content or alias-liveness conclusion is inferred for a
subsequent arbitrary mutating callee. -/
theorem save_reference (repr : StateRepr L b frame F σ base m)
    {R : RefTy} (index : Idx Γ (.mem R)) (pointerCell : Nat) (address : Fin W)
    (pointer : m.mem pointerCell = .val address) (separate : pointerCell ≠ address.val)
    (pointerAbove : b + Γ.length ≤ pointerCell) (pointerBelow : pointerCell < frame)
    (payloadAbove : b + Γ.length ≤ address.val) (payloadBelow : address.val < frame) :
    ∃ ref : HRef σ.H R, TEnv.get index σ.env = some ref ∧
      Evm.run (saveCode (cellOf b index) pointerCell) m =
        .ok (Stack.pushed m pointerCell address (.val (base ref.id))) 0 ∧
      StateRepr L b frame F σ base (Stack.pushed m pointerCell address (.val (base ref.id))) ∧
      (Stack.pushed m pointerCell address (.val (base ref.id))).mem address.val = .val (base ref.id) ∧
      GrowsAllocator b frame 0 σ base m σ base (Stack.pushed m pointerCell address (.val (base ref.id))) := by
  obtain ⟨ref,hasRef,pointerValue⟩ := repr.pointers index
  refine ⟨ref,hasRef,?_,pushed_repr repr pointerCell address _ pointerAbove pointerBelow payloadAbove payloadBelow,?_,
    pushed_allocator pointerCell address _ pointerAbove pointerBelow payloadAbove payloadBelow⟩
  · have load : Evm.run [.mload (cellOf b index)] m = .ok (m.push (.val (base ref.id))) 0 := by
      simp only [Evm.run,exec_cons_zero,Instr.step,Machine.next,pointerValue,Out.ok_bind,exec_nil,Machine.push]
    rw [saveCode,Evm.run_append_ok load]
    exact Stack.push_run m pointerCell address _ pointer separate
  · simp only [Stack.pushed,upd,if_neg (Ne.symm separate),↓reduceIte]

/-- Primitive values are saved with their actual ReprV proof, not a
same-typed value selected independently of the caller destination. -/
theorem save_scalar (repr : StateRepr L b frame F σ base m)
    {p : PrimTy} (index : Idx Γ (.val p)) (pointerCell : Nat) (address : Fin W)
    (pointer : m.mem pointerCell = .val address) (separate : pointerCell ≠ address.val)
    (pointerAbove : b + Γ.length ≤ pointerCell) (pointerBelow : pointerCell < frame)
    (payloadAbove : b + Γ.length ≤ address.val) (payloadBelow : address.val < frame) :
    ∃ word : Word, ReprV p (TEnv.get index σ.env) word ∧
      Evm.run (saveCode (cellOf b index) pointerCell) m = .ok (Stack.pushed m pointerCell address word) 0 ∧
      StateRepr L b frame F σ base (Stack.pushed m pointerCell address word) ∧
      (Stack.pushed m pointerCell address word).mem address.val = word := by
  let word := m.mem (cellOf b index)
  refine ⟨word,repr.core.vals index,?_,pushed_repr repr pointerCell address word pointerAbove pointerBelow payloadAbove payloadBelow,?_⟩
  · have load : Evm.run [.mload (cellOf b index)] m = .ok (m.push word) 0 := rfl
    rw [saveCode,Evm.run_append_ok load]
    exact Stack.push_run m pointerCell address word pointer separate
  · simp only [Stack.pushed,upd,if_neg (Ne.symm separate),↓reduceIte]
end Solidity.Backend.InternalFlow.RuntimeFrame
