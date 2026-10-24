import Solidity.Evm.MemoryStructCopyAlloc

/-!
# Storage-to-memory primitive struct simulation

Member loads precede the fresh reservation, and initialization consumes the
loaded words without disturbing the caller's stack. The resulting typed
object, old aliases, allocator cursor and reserved local frame are represented
together before the declaration/rebinding stores its new pointer.
-/
namespace Solidity.Evm.Memory
open Semantics
variable {C : Contract}

def copyStructCode (s : Name) (loads : List Instr) : List Instr :=
  loads ++ allocateStructCode (structAllocationSize s) ++
    copyStoreCode s ((structDef s).map Prod.fst)

/-- The emitted copy body creates the actual populated source object. -/
theorem copiedStruct_body_correct {L b frame : Nat} {Γ : Ctx} {F : Frag Γ}
    {σ : State C Γ} {base : Nat → Fin W} {cursor : Fin W} {m : Machine}
    (h : StateRepr L b frame F σ base m)
    (ha : StructAllocatorRepr σ.heap base frame cursor m) (hb : 0 < b)
    {s : Name} {root : Name} {hr : C.rootType root = some (.ref (.struct s))}
    {loads : List Instr} (plan : CopyLoads b F root hr (structDef s) loads)
    (v : SFields (structDef s)) (hv : σ.storage.get hr = .struct v)
    (hp : primitiveMembers (structDef s) = true) (hm : (Ty.ref (.struct s)).mapFree = true)
    (hspace : cursor.val + structAllocationSize s < W) :
    ∃ m',
      run (copyStructCode s loads) m = .ok (m'.push (.val cursor)) 0 ∧
      StateRepr L b frame F (σ.alloc (R := .struct s) (copiedFields (structDef s) hp v)).1
        (upd base σ.H.length cursor) m' ∧
      StructAllocatorRepr (σ.alloc (R := .struct s) (copiedFields (structDef s) hp v)).1.heap
        (upd base σ.H.length cursor) frame ⟨cursor.val + structAllocationSize s, hspace⟩ m' ∧
      m'.stack = m.stack := by
  obtain ⟨cells, hn, hg, hloads⟩ := plan.correct h.core v hv
  let reserved := allocateStructMachine m cursor (structAllocationSize s)
  let filled := copyStoreMachine s cursor cells reserved
  have hshape : filled = {m with mem := filled.mem} :=
    copyStore_shape s cursor cells reserved
  have hz : 0 < cursor.val := Nat.lt_of_lt_of_le ha.arrays.free.reserved ha.arrays.free.above
  have hlen : (structDef s).length ≤ structAllocationSize s := Nat.le_max_right _ _
  have hfields : cursor.val + (structDef s).length < W := by omega
  have hold : ∀ addr, 0 < addr → addr < cursor.val → filled.mem addr = m.mem addr := by
    intro a ha' hb'
    rw [copyStore_other s cursor cells reserved a (by intro f w _; omega)]
    exact allocateStructMachine_other m cursor _ a (by omega)
  have hcell : filled.mem 0 = .val ⟨cursor.val + structAllocationSize s, hspace⟩ := by
    rw [copyStore_other s cursor cells reserved 0 (by intro f w _; omega)]
    simp only [reserved, allocateStructMachine, writeMachine, upd_same, wmod_of_lt hspace]
  have hzero : ∀ addr, cursor.val + structAllocationSize s ≤ addr → filled.mem addr = w[0] := by
    intro a ha'
    rw [copyStore_other s cursor cells reserved a (by
      intro f w hw
      have hn' : f ∈ (structDef s).map Prod.fst := hn ▸ List.mem_map_of_mem hw
      obtain ⟨p, hf⟩ := plan.member hn'
      have ho := fieldOffset_bound hf
      omega)]
    rw [allocateStructMachine_other m cursor _ a (by omega)]
    exact ha.arrays.free.zero a (by omega)
  have hfresh : StructRepr (σ.heap.alloc (R := .struct s) (copiedFields (structDef s) hp v)).1
      (σ.heap.alloc (R := .struct s) (copiedFields (structDef s) hp v)).2 cursor filled :=
    copyStore_fields plan σ.heap v hp hm cursor cells reserved hn hg hfields
  rw [hshape] at hfresh
  have hall := h.reserveFilledStruct ha hb (copiedFields (structDef s) hp v)
    (by change cursor.val + (structDef s).length ≤ cursor.val + structAllocationSize s; omega)
    (fun hf => primitiveMembers_noRef hp hf) filled.mem hold hcell hzero hfresh
  refine ⟨filled, ?_, ?_, ?_, ?_⟩
  · rw [copyStructCode, List.append_assoc, run_append_ok hloads]
    have halloc := allocateStruct_run
      {m with stack := cells.map Prod.snd ++ m.stack} cursor (structAllocationSize s) ha.arrays.free.cell
    rw [run_append_ok halloc, ← hn]
    exact copyStore_run s cursor cells reserved (by
      intro f w hw
      obtain ⟨p, hf⟩ := plan.member (hn ▸ List.mem_map_of_mem hw)
      have ho : fieldOffset (structDef s) f < (structDef s).length := fieldOffset_bound hf
      omega)
  · rw [hshape]; exact hall.1
  · rw [hshape]; exact hall.2
  · rw [hshape]

def declareCopyStructCode {Γ : Ctx} (b : Nat) (s : Name) (loads : List Instr) : List Instr :=
  copyStructCode s loads ++ [.mstore (cell (b + Γ.length))]

/-- A copied source declaration and emitted loads/allocation/stores agree. -/
theorem copiedStruct_correct {L b frame : Nat} {Γ : Ctx} {F : Frag Γ}
    {σ : State C Γ} {base : Nat → Fin W} {cursor : Fin W} {m : Machine}
    (h : StateRepr L b frame F σ base m)
    (ha : StructAllocatorRepr σ.heap base frame cursor m) (hb : 0 < b)
    {s : Name} (root : Name) (hr : C.rootType root = some (.ref (.struct s)))
    {loads : List Instr} (plan : CopyLoads b F root hr (structDef s) loads)
    (v : SFields (structDef s)) (hv : σ.storage.get hr = .struct v)
    (hp : primitiveMembers (structDef s) = true) (hm : (Ty.ref (.struct s)).mapFree = true)
    (hspace : cursor.val + structAllocationSize s < W) (hcap : b + (Γ.length + 1) ≤ frame) :
    ∃ m',
      TRun.declMem (.struct s) (some (.copy (.loc (.root root hr)) hm)) hm σ =
        .ok ⟨σ.allocPush (R := .struct s) (copiedFields (structDef s) hp v), List.prefix_append _ _⟩ ∧
      run (declareCopyStructCode (Γ := Γ) b s loads) m = .ok m' 0 ∧
      StateRepr L b frame (F.push (.mem (.struct s)) .ok)
        (σ.allocPush (R := .struct s) (copiedFields (structDef s) hp v))
        (upd base σ.H.length cursor) m' ∧
      StructAllocatorRepr (σ.allocPush (R := .struct s) (copiedFields (structDef s) hp v)).heap
        (upd base σ.H.length cursor) frame ⟨cursor.val + structAllocationSize s, hspace⟩ m' ∧
      m'.stack = m.stack := by
  obtain ⟨m', hc, hs, hal, hstack⟩ := copiedStruct_body_correct h ha hb plan v hv hp hm hspace
  let out := writeMachine m' (cell (b + Γ.length)) (.val cursor)
  refine ⟨out, copiedStruct_decl σ _ (SRef.ofRoot root hr) rfl v ?_ hp hm, ?_, ?_, ?_, hstack⟩
  · simp only [Storage.find, SRef.ofRoot, hv, SVal.find_nil]
  · rw [declareCopyStructCode, run_append_ok hc]; rfl
  · have hid : (σ.alloc (R := .struct s) (copiedFields (structDef s) hp v)).2.id = σ.H.length := rfl
    simpa only [hid, upd_same] using
      hs.consMem (σ.alloc (R := .struct s) (copiedFields (structDef s) hp v)).2 hcap
  · exact hal.localWrite _ (by change 0 < b + Γ.length; omega)
      (by change b + Γ.length < frame; omega) _

def rebindCopyStructCode {Γ : Ctx} {s : Name} (b : Nat)
    (dst : Idx Γ (.mem (.struct s))) (loads : List Instr) : List Instr :=
  copyStructCode s loads ++ [.mstore (cellOf b dst)]

/-- Rebinding installs a new populated identity while preserving earlier aliases. -/
theorem copiedStruct_rebind_correct {L b frame : Nat} {Γ : Ctx} {F : Frag Γ}
    {σ : State C Γ} {base : Nat → Fin W} {cursor : Fin W} {m : Machine}
    (h : StateRepr L b frame F σ base m)
    (ha : StructAllocatorRepr σ.heap base frame cursor m) (hb : 0 < b)
    {s : Name} (dst : Idx Γ (.mem (.struct s)))
    (root : Name) (hr : C.rootType root = some (.ref (.struct s)))
    {loads : List Instr} (plan : CopyLoads b F root hr (structDef s) loads)
    (v : SFields (structDef s)) (hv : σ.storage.get hr = .struct v)
    (hp : primitiveMembers (structDef s) = true) (hm : (Ty.ref (.struct s)).mapFree = true)
    (hspace : cursor.val + structAllocationSize s < W) :
    let σ' := (σ.alloc (R := .struct s) (copiedFields (structDef s) hp v)).1.setLocal dst
      (some (σ.alloc (R := .struct s) (copiedFields (structDef s) hp v)).2)
    ∃ m',
      TRun.rebindMem dst (.copy (.loc (.root root hr)) hm) σ =
        .ok ⟨σ', List.prefix_append _ _⟩ ∧
      run (rebindCopyStructCode b dst loads) m = .ok m' 0 ∧
      StateRepr L b frame F σ' (upd base σ.H.length cursor) m' ∧
      StructAllocatorRepr σ'.heap (upd base σ.H.length cursor) frame
        ⟨cursor.val + structAllocationSize s, hspace⟩ m' ∧
      m'.stack = m.stack := by
  obtain ⟨m', hc, hs, hal, hstack⟩ := copiedStruct_body_correct h ha hb plan v hv hp hm hspace
  let out := writeMachine m' (cellOf b dst) (.val cursor)
  refine ⟨out, copiedStruct_rebind σ dst _ (SRef.ofRoot root hr) rfl v ?_ hp hm, ?_, ?_, ?_, hstack⟩
  · simp only [Storage.find, SRef.ofRoot, hv, SVal.find_nil]
  · rw [rebindCopyStructCode, run_append_ok hc]; rfl
  · have hid : (σ.alloc (R := .struct s) (copiedFields (structDef s) hp v)).2.id = σ.H.length := rfl
    simpa only [hid, upd_same] using
      hs.setMem dst (σ.alloc (R := .struct s) (copiedFields (structDef s) hp v)).2
  · exact hal.localWrite _ (Nat.lt_of_lt_of_le hb (le_lvl b dst))
      (Nat.lt_of_lt_of_le (lvl_lt b dst) h.locals) _

end Solidity.Evm.Memory
