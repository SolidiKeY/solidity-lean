import Solidity.Backend.InternalFlow.RuntimeFrameSaved
import Solidity.Evm.MemoryAllocSource
import Solidity.Evm.MemoryCompile

/-! Reserved runtime words survive actual published allocation, private pointer
rebinding and represented array mutation. These exact emitter leaves are not a
scratch theorem for arbitrary compiled callees. No heap-content preservation is
assumed: the array write changes the old object. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.Footprint
open Evm Evm.Memory
variable {C : Contract} {Γ : Ctx} {L b frame : Nat} {F : Frag Γ}
  {σ : State C Γ} {base : Nat → Fin W} {m : Machine}

/-- Equality only on a reserved half-open interval of the existing word memory. -/
def Words (lo hi : Nat) (before after : Machine) : Prop :=
  ∀ address, lo ≤ address → address < hi → after.mem address = before.mem address

theorem words_refl (lo hi : Nat) (m : Machine) : Words lo hi m m := fun _ _ _ => rfl

theorem words_trans {lo hi : Nat} {a b c : Machine}
    (first : Words lo hi a b) (second : Words lo hi b c) : Words lo hi a c :=
  fun address lower upper => (second address lower upper).trans (first address lower upper)

theorem write_below {lo hi : Nat} (m : Machine) (address : Nat) (value : Word)
    (below : address < lo) : Words lo hi m (writeMachine m address value) := by
  intro a lower upper
  exact upd_other _ _ (by omega)

theorem write_above {lo hi : Nat} (m : Machine) (address : Nat) (value : Word)
    (above : hi ≤ address) : Words lo hi m (writeMachine m address value) := by
  intro a lower upper
  exact upd_other _ _ (by omega)

/-- Derive the footprint from the two genuine allocator writes, not from
source Heap.Keeps or an arbitrary machine-preservation premise. -/
theorem allocation_words {lo : Nat} (positive : 0 < lo)
    (cursor size : Fin W) (above : frame ≤ cursor.val) :
    Words lo frame m (allocateMachine m cursor size) :=
  words_trans (write_above m cursor.val (.val size) above)
    (write_below _ 0 (.val (wmod (cursor.val + size.val + 1))) positive)

/-- A checked allocating declaration retains every reserved runtime word,
while returning its ACTUAL source extension, target, representation and cursor. -/
theorem declare (repr : StateRepr L b frame F σ base m)
    {cursor : Fin W} (allocator : StructAllocatorRepr σ.heap base frame cursor m)
    (positive : 0 < b) (p : PrimTy) (n : Simple C Γ .uint)
    (admitted : simpleIn n = true) (size : Fin W)
    (evaluated : n.evalT σ = indexValue size)
    (capacity : cursor.val + size.val + 1 < W)
    {lo : Nat} (locals : b + Γ.length < lo) (room : b + (Γ.length + 1) ≤ frame) :
    let next := σ.allocPush (defaultArray p size)
    let addresses := upd base σ.H.length cursor
    let target := writeMachine (allocateMachine m cursor size) (cell (b + Γ.length)) (.val cursor)
    TRun.declMem (.array (.prim p)) (some (.newArr n rfl)) rfl σ =
      .ok ⟨next, List.prefix_append _ _⟩ ∧
    run (declareNewCode b n) m = .ok target 0 ∧
    StateRepr L b frame (F.push (.mem (.array (.prim p))) .ok) next addresses target ∧
    StructAllocatorRepr next.heap addresses frame ⟨cursor.val + size.val + 1,capacity⟩ target ∧
    target.stack = m.stack ∧ Words lo frame m target := by
  obtain ⟨hs,ht,hr,ha,hk⟩ := newArray_correct repr allocator positive p n admitted size evaluated capacity room
  exact ⟨hs,ht,hr,ha,hk,words_trans
    (allocation_words (by omega) cursor size allocator.arrays.free.above)
    (write_below _ _ _ locals)⟩

/-- Allocating PRIVATE rebinding has the same footprint; the old alias may
still name an object whose contents are mutated by other admitted leaves. -/
theorem rebind (repr : StateRepr L b frame F σ base m)
    {cursor : Fin W} (allocator : StructAllocatorRepr σ.heap base frame cursor m)
    (positive : 0 < b) (p : PrimTy) (dst : Idx Γ (.mem (.array (.prim p))))
    (n : Simple C Γ .uint) (admitted : simpleIn n = true) (size : Fin W)
    (evaluated : n.evalT σ = indexValue size) (capacity : cursor.val + size.val + 1 < W)
    {lo : Nat} (locals : b + Γ.length ≤ lo) :
    let next := (σ.alloc (defaultArray p size)).1.setLocal dst (some (σ.alloc (defaultArray p size)).2)
    let addresses := upd base σ.H.length cursor
    let target := writeMachine (allocateMachine m cursor size) (cellOf b dst) (.val cursor)
    TRun.rebindMem dst (.newArr n rfl) σ = .ok ⟨next,List.prefix_append _ _⟩ ∧
    run (rebindNewCode b dst n) m = .ok target 0 ∧
    StateRepr L b frame F next addresses target ∧
    StructAllocatorRepr next.heap addresses frame ⟨cursor.val + size.val + 1,capacity⟩ target ∧
    target.stack = m.stack ∧ Words lo frame m target := by
  obtain ⟨hs,ht,hr,ha,hk⟩ := rebindNew_correct repr allocator positive p dst n admitted size evaluated capacity
  exact ⟨hs,ht,hr,ha,hk,words_trans
    (allocation_words (by have bound := le_lvl b dst; omega) cursor size allocator.arrays.free.above)
    (write_below _ _ _ (Nat.lt_of_lt_of_le (lvl_lt b dst) locals))⟩

/-- An ACTUAL represented old-object write, including exact source update,
retains the reserved words although heap contents change. -/
theorem array_write (repr : StateRepr L b frame F σ base m)
    {p : PrimTy} (ref : HRef σ.H (.array (.prim p))) (index : Fin W)
    (live : index.val < σ.heap.len ref .dyn) (value : p.Denote) (word : Word)
    (represented : ReprV p value word) (lo : Nat) :
    let next := σ.withHeap (σ.heap.set ref (MObj.setElem .dyn (σ.heap.get ref) index.val value))
    let target := writeMachine m ((base ref.id).val + 1 + index.val) word
    σ.heap.writeAddr (.index ref .dyn (indexValue index)) value = some next.heap ∧
    run (writeArrayCode (base ref.id)) ((m.push word).push (.val index)) = .ok target 0 ∧
    StateRepr L b frame F next base target ∧ Words lo frame m target := by
  obtain ⟨hp,hsource,htarget,hr⟩ | ⟨hsource,htarget⟩ :=
    writeArray_correct (repr.heap.arrays ref) index value word represented
  · have actual : σ.heap.writeAddr (.index ref .dyn (indexValue index)) value =
        some (σ.heap.set ref (MObj.setElem .dyn (σ.heap.get ref) index.val value)) := by
      simp only [Heap.writeAddr,Heap.setIndex,indexValue,Int.toNat_natCast]
      exact ite_eq_left live
    exact ⟨actual,htarget,repr.set ref index.val live value word represented,
      write_above m _ word (by have bound := repr.heap.above ref;omega)⟩
  · have impossible : σ.heap.writeAddr (.index ref .dyn (indexValue index)) value ≠ none := by
      simp only [Heap.writeAddr,Heap.setIndex,indexValue,Int.toNat_natCast]
      exact fun absent =>
        Option.some_ne_none _ ((ite_eq_left
          (show index.val < (MObj.elems .dyn (σ.heap.get ref)).length from live)).symm.trans absent)
    exact (impossible hsource).elim

/-- Full expression/receiver/index pipeline of the published local-array
write. The argument order and exact resulting machine come from genuine
compiled value certificates and the represented pointer, not an assumed
footprint. This leaf also permits reads of memory in either expression. -/
theorem write_local (repr : StateRepr L b frame F σ base m)
    {p : PrimTy} (destination : Idx Γ (.mem (.array (.prim p))))
    (ref : HRef σ.H (.array (.prim p)))
    (binding : TEnv.get destination σ.env = some ref)
    (index : Val C Γ .uint) (value : Val C Γ p)
    (indexCode : CompiledVal b F index) (valueCode : CompiledVal b F value)
    (ix : Fin W) (evaluatedIndex : index.evalT σ = .ok (indexValue ix))
    (x : p.Denote) (evaluatedValue : value.evalT σ = .ok x)
    (live : ix.val < σ.heap.len ref .dyn) (lo : Nat) :
    ∃ word : Word,
      let next := σ.withHeap (σ.heap.set ref (MObj.setElem .dyn (σ.heap.get ref) ix.val x))
      let target := writeMachine m ((base ref.id).val + 1 + ix.val) word
      ReprV p x word ∧
      TRun.assignMem (.index .dyn (.var destination rfl) index) (.val value) σ =
        .ok ⟨next,List.prefix_refl _⟩ ∧
      run (writeLocalValueCode b destination indexCode.code valueCode.code) m = .ok target 0 ∧
      StateRepr L b frame F next base target ∧ Words lo frame m target := by
  obtain ⟨r,hr,hm⟩ := repr.pointers destination
  have same := Option.some.inj (hr.symm.trans binding)
  subst r
  rcases valueCode.cert.correct repr with ⟨v,w,hv,hw,hcode⟩ | ⟨hv,hcode⟩
  · have same := Except.ok.inj (hv.symm.trans evaluatedValue)
    subst v
    rcases indexCode.cert.correct ((repr.push w).push (.val (base ref.id))) with
      ⟨iv,iw,hiv,hiw,hic⟩ | ⟨hiv,hic⟩
    · have same := Except.ok.inj (hiv.symm.trans evaluatedIndex)
      subst iv
      obtain ⟨a,ha,hva,rfl⟩ := hiw.uint_inv
      have equal : (⟨a,ha⟩ : Fin W) = ix := by
        apply Fin.ext
        have numeric : (ix.val : Int) = (a : Int) := hva
        exact (Int.ofNat_inj.mp numeric).symm
      cases equal
      obtain ⟨hs,ht,hn,hwords⟩ := array_write repr ref ⟨a,ha⟩ live x w hw lo
      refine ⟨w,hw,?_,?_,hn,hwords⟩
      · simp only [TRun.assignMem,MSrc.mvalT,MLoc.addrT,MPath.mvalT,binding,
          evaluatedValue,evaluatedIndex,bind,Except.bind,pure,Except.pure]
        rw [hs]
        rfl
      · rw [writeLocalValueCode,List.append_assoc,List.append_assoc,run_append_ok hcode]
        have pointer : run [.mload (cellOf b destination)] (m.push w) =
            .ok ((m.push w).push (.val (base ref.id))) 0 := by
          change Out.ok ((m.push w).push (m.mem (cellOf b destination))) 0 = _
          rw [hm]
        rw [run_append_ok pointer,run_append_ok hic,writeArrayStackCode,
          arrayStack_append_eq (m.push w) (base ref.id) ⟨a,ha⟩ _
            (σ.heap.len_dyn_lt ref) (repr.heap.arrays ref).length,← writeArrayCode]
        exact ht
    · rw [evaluatedIndex] at hiv
      contradiction
  · rw [evaluatedValue] at hv
    contradiction

/-- Restoring the pointer below the heap consumes no allocation cells; the
recovered evaluation-stack word does not change allocator ownership. -/
theorem popped_allocator (pointerCell : Nat) (address : Fin W)
    (above : b + Γ.length ≤ pointerCell) (below : pointerCell < frame) :
    GrowsAllocator b frame 0 σ base m σ base (Stack.popped m pointerCell address) := by
  intro cursor positive allocator space
  simpa only [Nat.add_zero] using
    (allocator.localWrite pointerCell (by omega) below (.val (wmod (address.val - 1)))).mem_eq
      (m' := Stack.popped m pointerCell address) rfl

/-- Compose an ACTUAL successful fragment with the existing runtime pop.
The footprint obligation is explicit here and discharged by the emitter
leaves in the inhabited client; it is not an arbitrary-callee theorem. -/
theorem restore {lo hi : Nat} {before after : Machine} {code : List Instr}
    (executed : run code before = .ok after 0)
    (words : Words lo hi before after) (pointerCell : Nat) (address : Fin W)
    (pointer : before.mem pointerCell = .val address)
    (positive : 0 < address.val) (separate : pointerCell ≠ address.val - 1)
    (headerLower : lo ≤ pointerCell) (headerUpper : pointerCell < hi)
    (payloadLower : lo ≤ address.val - 1) (payloadUpper : address.val - 1 < hi) :
    run (code ++ Stack.popCode pointerCell) before = .ok (Stack.popped after pointerCell address) 0 ∧
    (Stack.popped after pointerCell address).stack = before.mem (address.val - 1) :: after.stack := by
  constructor
  · rw [run_append_ok executed]
    exact Stack.pop_run after pointerCell address
      ((words pointerCell headerLower headerUpper).trans pointer) positive separate
  · exact congrArg (· :: after.stack) (words (address.val - 1) payloadLower payloadUpper)
/-- A source-typed mutation/private-allocation fragment, using only the
published compiler's actual emitter snippets. Its selector link is proved
separately for each checked client, not assumed as a simulation premise. -/
def fragmentCode {Γ : Ctx} (b : Nat) (destination : Idx Γ (.mem (.array (.prim .uint)))) : List Instr :=
  writeLocalValueCode b destination [.push w[0]] [.push w[37]] ++
  declareNewCode (C := C) (Γ := Γ) b (.lit 2 rfl) ++
  rebindNewCode (C := C) (Γ := .mem (.array (.prim .uint)) :: Γ) b .here (.lit 1 rfl)

/-- Imported abstract proof boundary: all write/allocation/frame obligations
are discharged by the actual typed emitter laws. Only the genuine represented
input, old live alias and capacity remain as premises. -/
theorem fragment (repr : StateRepr L b frame F σ base m)
    {cursor : Fin W} (allocator : StructAllocatorRepr σ.heap base frame cursor m)
    (positive : 0 < b) (destination : Idx Γ (.mem (.array (.prim .uint))))
    (ref : HRef σ.H (.array (.prim .uint)))
    (binding : TEnv.get destination σ.env = some ref)
    (live : 0 < σ.heap.len ref .dyn) (capacity : cursor.val + 5 < W)
    {lo : Nat} (locals : b + Γ.length < lo) (room : b + (Γ.length + 1) ≤ frame) :
    ∃ target, run (fragmentCode (C := C) b destination) m = .ok target 0 ∧ Words lo frame m target := by
  let indexCode : CompiledVal b F (.simple (.lit 0 rfl) : Val C Γ .uint) :=
    ⟨[.push w[0]],.core _ rfl⟩
  let valueCode : CompiledVal b F (.simple (.lit 37 rfl) : Val C Γ .uint) :=
    ⟨[.push w[37]],.core _ rfl⟩
  obtain ⟨w,hw,source₁,run₁,repr₁,words₁⟩ := write_local repr destination ref binding
    (.simple (.lit 0 rfl)) (.simple (.lit 37 rfl)) indexCode valueCode
    (wmod 0) rfl (indexValue (wmod 37)) rfl live lo
  let changed := σ.withHeap (σ.heap.set ref (MObj.setElem .dyn (σ.heap.get ref) 0 (indexValue (wmod 37))))
  let firstTarget := writeMachine m ((base ref.id).val + 1) w
  have allocator₁ : StructAllocatorRepr changed.heap base frame cursor firstTarget :=
    allocator.setArray ref 0 live (indexValue (wmod 37)) w hw
  have cap₂ : cursor.val + (wmod 2).val + 1 < W := by
    have two : (wmod 2).val = 2 := by decide +kernel
    rw [two];omega
  obtain ⟨source₂,run₂,repr₂,allocator₂,stack₂,words₂⟩ := declare
    repr₁ allocator₁ positive .uint (.lit 2 rfl) rfl (wmod 2) rfl cap₂ (lo := lo) locals room
  have cap₃ : (cursor.val + (wmod 2).val + 1) + (wmod 1).val + 1 < W := by
    have two : (wmod 2).val = 2 := by decide +kernel
    have one : (wmod 1).val = 1 := by decide +kernel
    rw [two,one];omega
  obtain ⟨source₃,run₃,repr₃,allocator₃,stack₃,words₃⟩ := rebind
    repr₂ allocator₂ positive .uint .here (.lit 1 rfl) rfl (wmod 1) rfl cap₃
    (lo := lo) (by simp only [List.length_cons];omega)
  refine ⟨_,?_,words_trans words₁ (words_trans words₂ words₃)⟩
  rw [fragmentCode,List.append_assoc,run_append_ok run₁,run_append_ok run₂]
  exact run₃
end Solidity.Backend.InternalFlow.RuntimeFrame.Footprint
