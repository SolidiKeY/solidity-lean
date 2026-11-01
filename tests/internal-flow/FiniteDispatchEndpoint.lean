import Solidity.Backend.InternalFlow.CallerView
import Solidity.Backend.InternalFlow.CallerTail
import Solidity.Backend.InternalFlow.CallerFrame
import tests.«internal-flow».FiniteDispatchFacts
import tests.«internal-flow».MemoryDispatchFacts
namespace Solidity.Backend.InternalFlow.DispatchChecks
open Evm Evm.Memory FiniteDispatch PublishedDirectCalls

theorem capacity : AllocationInput 1 64 (seed.cost (State.init C) + checked.cost mid.st)
    (State.init C) bases machine := by
  refine .inr ⟨by decide,wmod 128,(initial_repr C).2,?_⟩
  rw [seed_cost,reached_cost]
  decide +kernel

/-- Closed prefix-to-selected-arm target: every midpoint/input is derived. -/
theorem endpoint : ∃ m₁ base₁ m₂ base₂,
    run seed.code machine = .ok m₁ 0 ∧ run checked.code m₁ = .ok m₂ 0 ∧
    run (seed.code ++ checked.code) machine = .ok m₂ 0 ∧
    StateRepr 1 1 64 seed.frag mid.st base₁ m₁ ∧
    StateRepr 1 1 64 checked.frag chosen.st base₂ m₂ ∧
    BaseExtends mid.st.H base₁ base₂ ∧
    GrowsAllocator 1 64 9 (State.init C) bases machine chosen.st base₂ m₂ ∧
    m₂.stack = [w[77]] ∧ m₂.mem 0 = w[137] := by
  obtain ⟨m₁,base₁,hp,hr₁,stack₁,he₁,hg₁⟩ := program_endpoint seed (initial_repr C).1 seed_frame
    (capacity.of_le (Nat.le_add_right _ _)) mid seed_run
  have hi := hg₁.nextInput capacity
  obtain ⟨m₂,base₂,hc,hr₂,stack₂,he₂,hg₂⟩ := selected_endpoint [actualFirst] actualSecond []
    .revert checked mid.st (by
      intro a h; have ha := List.mem_singleton.mp h; subst a; exact first_miss)
    second_hit armOut body_run hr₁ room hi
  have whole : run (seed.code ++ checked.code) machine = .ok m₂ 0 := by rw [run_append_ok hp,hc]
  have grows := hg₁.comp hg₂
  rw [seed_cost,reached_cost] at grows
  have cursor := (grows (wmod 128) (by decide) (initial_repr C).2 (by decide +kernel)).arrays.free.cell
  change m₂.mem 0 = w[137] at cursor
  exact ⟨m₁,base₁,m₂,base₂,hp,hc,whole,hr₁,hr₂,he₂,grows,stack₂.trans stack₁,cursor⟩

private theorem uint_word {v : PrimTy.uint.Denote} {w : Word} {n : Fin W}
    (repr : ReprV .uint v w) (value : v.1 = (n.val : Int)) : w = .val n := by
  obtain ⟨a,hw,ha⟩ := repr
  have he : a = n := Fin.ext (Int.ofNat_inj.mp (ha.symm.trans value))
  exact hw.trans (congrArg Word.val he)

def afterCells (base : Nat → Fin W) (m : Machine) : List Word :=
 [m.mem 1,m.mem 2,m.mem 3,m.mem 4,m.mem 5,m.mem 6,m.mem 7,m.mem 8,
  m.mem (base 0).val,m.mem ((base 0).val+1),m.mem ((base 0).val+2),
  m.mem (base 1).val,m.mem ((base 1).val+1),m.mem ((base 1).val+2),
  m.mem (base 2).val,m.mem ((base 2).val+1),m.mem ((base 2).val+2),
  .val (m.store.cells (.root 0)),m.mem 0]

theorem observe_after {base₁ base₂ : Nat → Fin W} {m : Machine}
 (hr : StateRepr 1 1 64 checked.frag chosen.st base₂ m)
 (he : BaseExtends mid.st.H base₁ base₂) (cursor : m.mem 0 = w[137]) :
 afterCells base₂ m = [w[42],.val (base₁ 0),.val (base₁ 0),.val (base₁ 1),w[2],w[16],
  .val (base₁ 0),w[5],w[2],w[7],w[16],w[2],w[23],w[29],w[2],w[70],w[71],w[10],w[137]] := by
 obtain ⟨ac,asame,axs,ao⟩ := aliases
 have c := old_alias_at_entry_address (σ := mid.st) chosen hr he old (.there .here) ac
 have same := old_alias_at_entry_address (σ := mid.st) chosen hr he old _ asame
 have xs := old_alias_at_entry_address (σ := mid.st) chosen hr he old _ axs
 have otherCell := old_alias_at_entry_address (σ := mid.st) chosen hr he other _ ao
 change m.mem 7 = .val (base₁ 0) at c
 change m.mem 3 = .val (base₁ 0) at same
 change m.mem 2 = .val (base₁ 0) at xs
 change m.mem 4 = .val (base₁ 1) at otherCell
 have cap := uint_word (n := wmod 5) (hr.core.vals (.here : Idx Caller (.val .uint))) (by decide +kernel)
 have result := uint_word (n := wmod 16) (hr.core.vals (.there (.there .here) : Idx Caller (.val .uint))) (by decide +kernel)
 have tag := uint_word (n := wmod 2) (hr.core.vals (.there (.there (.there .here)) : Idx Caller (.val .uint))) (by decide +kernel)
 have marker := uint_word (n := wmod 42) (hr.core.vals (.there (.there (.there (.there (.there (.there (.there .here)))))) : Idx Caller (.val .uint))) (by decide +kernel)
 change m.mem 8 = w[5] at cap
 change m.mem 6 = w[16] at result
 change m.mem 5 = w[2] at tag
 change m.mem 1 = w[42] at marker
 obtain ⟨l0,l1,l2,e00,e01,e10,e11,e20,e21⟩ := heap_values
 have h0 := (hr.heap.arrays (old.wk chosen.ext)).length
 have h1 := (hr.heap.arrays (other.wk chosen.ext)).length
 have h2 := (hr.heap.arrays fresh).length
 rw [l0] at h0; rw [l1] at h1; rw [l2] at h2
 change m.mem (base₂ 0).val = w[2] at h0
 change m.mem (base₂ 1).val = w[2] at h1
 change m.mem (base₂ 2).val = w[2] at h2
 have a := uint_word ((hr.heap.arrays (old.wk chosen.ext)).elements 0 _ e00) rfl
 have b := uint_word ((hr.heap.arrays (old.wk chosen.ext)).elements 1 _ e01) rfl
 have d := uint_word ((hr.heap.arrays (other.wk chosen.ext)).elements 0 _ e10) rfl
 have e := uint_word ((hr.heap.arrays (other.wk chosen.ext)).elements 1 _ e11) rfl
 have f := uint_word ((hr.heap.arrays fresh).elements 0 _ e20) rfl
 have g := uint_word ((hr.heap.arrays fresh).elements 1 _ e21) rfl
 change m.mem ((base₂ 0).val+1) = w[7] at a
 change m.mem ((base₂ 0).val+2) = w[16] at b
 change m.mem ((base₂ 1).val+1) = w[23] at d
 change m.mem ((base₂ 1).val+2) = w[29] at e
 change m.mem ((base₂ 2).val+1) = w[70] at f
 change m.mem ((base₂ 2).val+2) = w[71] at g
 have storage := hr.core.store "count" (.prim .uint) rfl
 change ReprAt m.store 1 (.prim .uint) (rootSlot C "count")
   (chosen.st.storage.get (rfl : C.rootType "count" = some (.prim .uint))) at storage
 have sv : chosen.st.storage.get (rfl : C.rootType "count" = some (.prim .uint)) = .prim (indexValue (wmod 10)) := by decide +kernel
 rw [sv] at storage
 have rootCell : (.val (m.store.cells (.root 0)) : Word) = w[10] := by
   cases storage with | prim h => exact uint_word h rfl
 simp only [afterCells,marker,xs,same,otherCell,tag,result,c,cap,h0,h1,h2,a,b,d,e,f,g,rootCell,cursor]

theorem complete_endpoint : ∃ (m₁ : Machine) (base₁ : Nat → Fin W) (m₂ : Machine) (base₂ : Nat → Fin W),
 run seed.code machine = .ok m₁ 0 ∧ run checked.code m₁ = .ok m₂ 0 ∧
 run (seed.code ++ checked.code) machine = .ok m₂ 0 ∧
 StateRepr 1 1 64 checked.frag chosen.st base₂ m₂ ∧
 GrowsAllocator 1 64 9 (State.init C) bases machine chosen.st base₂ m₂ ∧ m₂.stack = [w[77]] ∧
 afterCells base₂ m₂ = [w[42],.val (base₁ 0),.val (base₁ 0),.val (base₁ 1),w[2],w[16],.val (base₁ 0),w[5],
  w[2],w[7],w[16],w[2],w[23],w[29],w[2],w[70],w[71],w[10],w[137]] := by
 obtain ⟨m₁,base₁,m₂,base₂,hp,hc,whole,hr₁,hr₂,he,hg,stack,cursor⟩ := endpoint
 exact ⟨m₁,base₁,m₂,base₂,hp,hc,whole,hr₂,hg,stack,observe_after hr₂ he cursor⟩

theorem exact_fallback : run (seed.code ++ clearCert.code ++ checked.code) machine = .revert := by
 obtain ⟨m₁,base₁,m₂,base₂,hp,hc,whole,hr₁,rest⟩ := endpoint
 obtain ⟨mf,bf,hclear,hrf,hsf,hef,hgf⟩ := statement_endpoint clearCert hr₁ clear_room
   (.inl clear_cost) cleared clear_run
 rw [clear_frag] at hrf
 have failed := fallback_revert [actualFirst,actualSecond] (.revert : Stmt C Caller Caller)
   checked cleared.st all_miss rfl hrf room (.inl no_match_cost)
 rw [List.append_assoc,run_append_ok hp,run_append_ok hclear,failed]

theorem negative_controls : ∃ (m : Machine) (base : Nat → Fin W),
 run (seed.code ++ checked.code) machine = .ok m 0 ∧
 m.mem 6 ≠ w[42] ∧ m.mem 1 ≠ w[16] ∧ m.mem 0 ≠ w[142] ∧
 m.mem ((base 0).val+2) ≠ w[11] ∧ (.val (m.store.cells (.root 0)) : Word) ≠ w[1000] ∧
 m.mem 2 ≠ .val (base fresh.id) := by
 obtain ⟨m₁,base₁,m₂,base₂,hp,hc,whole,hr,hg,stack,obs⟩ := complete_endpoint
 have r := congrArg (fun xs : List Word => xs[5]?) obs
 have mark := congrArg (fun xs : List Word => xs[0]?) obs
 have free := congrArg (fun xs : List Word => xs[18]?) obs
 have elem := congrArg (fun xs : List Word => xs[10]?) obs
 have root := congrArg (fun xs : List Word => xs[17]?) obs
 change some (m₂.mem 6) = some w[16] at r
 change some (m₂.mem 1) = some w[42] at mark
 change some (m₂.mem 0) = some w[137] at free
 change some (m₂.mem ((base₂ 0).val+2)) = some w[16] at elem
 change some (.val (m₂.store.cells (.root 0))) = some w[10] at root
 have gap := hr.heap.separated (old.wk chosen.ext) fresh (by decide +kernel)
 have different : base₂ old.id ≠ base₂ fresh.id := by
   intro eq
   change (base₂ old.id).val + 1 + _ ≤ (base₂ fresh.id).val ∨
     (base₂ fresh.id).val + 1 + _ ≤ (base₂ old.id).val at gap
   rw [eq] at gap
   rcases gap with h | h <;> omega
 have ptr := old_alias_at_entry_address (σ := mid.st) chosen hr (BaseExtends.refl base₂) old _ aliases.2.2.1
 change m₂.mem 2 = .val (base₂ old.id) at ptr
 refine ⟨m₂,base₂,whole,?_,?_,?_,?_,?_,?_⟩
 · rw [Option.some.inj r]; decide +kernel
 · rw [Option.some.inj mark]; decide +kernel
 · rw [Option.some.inj free]; decide +kernel
 · rw [Option.some.inj elem]; decide +kernel
 · rw [Option.some.inj root]; decide +kernel
 · rw [ptr]; exact fun h => different (Word.val.inj h)

theorem fallback_not_fault : run (seed.code ++ clearCert.code ++ checked.code) machine ≠ .fault := by
 rw [exact_fallback]; intro h; cases h
#print axioms negative_controls
#print axioms fallback_not_fault
#print axioms observe_after
#print axioms complete_endpoint
#print axioms exact_fallback
#print axioms capacity
#print axioms endpoint
end Solidity.Backend.InternalFlow.DispatchChecks

namespace Solidity.Backend.InternalFlow.MemoryDispatchChecks
open Evm Evm.Memory FiniteDispatch PublishedDirectCalls

theorem capacity : AllocationInput 1 64 (seed.cost (State.init C) + checked.cost mid.st)
 (State.init C) bases machine := by
 refine .inr ⟨by decide,wmod 128,initial_repr.2,?_⟩
 rw [seed_cost,reached_cost]
 decide +kernel

theorem endpoint : ∃ (m₁ : Machine) (base₁ : Nat → Fin W) (m₂ : Machine) (base₂ : Nat → Fin W)
 (m₃ : Machine) (base₃ : Nat → Fin W),
 run seed.code machine = .ok m₁ 0 ∧ run checked.code m₁ = .ok m₂ 0 ∧
 run postCert.code m₂ = .ok m₃ 0 ∧ run (seed.code ++ checked.code ++ postCert.code) machine = .ok m₃ 0 ∧
 StateRepr 1 1 64 seed.frag mid.st base₁ m₁ ∧ StateRepr 1 1 64 checked.frag chosen.st base₂ m₂ ∧
 StateRepr 1 1 64 postCert.frag finished.st base₃ m₃ ∧
 BaseExtends mid.st.H base₁ base₂ ∧ BaseExtends chosen.st.H base₂ base₃ ∧
 GrowsAllocator 1 64 11 (State.init C) bases machine finished.st base₃ m₃ ∧
 m₃.stack = [w[77]] ∧ m₃.mem 0 = w[139] := by
 obtain ⟨m₁,base₁,hp,hr₁,stack₁,he₁,hg₁⟩ := program_endpoint seed initial_repr.1 seed_frame
   (capacity.of_le (Nat.le_add_right _ _)) mid seed_run
 obtain ⟨m₂,base₂,hc,hr₂,stack₂,he₂,hg₂⟩ := selected_endpoint [actualFirst] actualSecond []
   .revert checked mid.st (by intro a h; have ha := List.mem_singleton.mp h; subst a; exact first_miss)
   second_hit armOut body_run hr₁ room (hg₁.nextInput capacity)
 obtain ⟨m₃,base₃,ht,hr₃,stack₃,he₃,hg₃⟩ := program_endpoint postCert hr₂ post_room
   (.inl post_cost) finished post_run
 have whole : run (seed.code ++ checked.code ++ postCert.code) machine = .ok m₃ 0 := by
   rw [List.append_assoc,run_append_ok hp,run_append_ok hc,ht]
 have grow := (hg₁.comp hg₂).comp hg₃
 change GrowsAllocator 1 64 (seed.cost (State.init C) + checked.cost mid.st + postCert.cost chosen.st)
   (State.init C) bases machine finished.st base₃ m₃ at grow
 rw [seed_cost,reached_cost,post_cost] at grow
 have cursor := (grow (wmod 128) (by decide) initial_repr.2 (by decide +kernel)).arrays.free.cell
 change m₃.mem 0 = w[139] at cursor
 exact ⟨m₁,base₁,m₂,base₂,m₃,base₃,hp,hc,ht,whole,hr₁,hr₂,hr₃,he₂,he₃,grow,
   stack₃.trans (stack₂.trans stack₁),cursor⟩

private theorem uint_word {v : PrimTy.uint.Denote} {w : Word} {n : Fin W}
 (repr : ReprV .uint v w) (value : v.1 = (n.val : Int)) : w = .val n := by
 obtain ⟨a,hw,ha⟩ := repr
 have he : a = n := Fin.ext (Int.ofNat_inj.mp (ha.symm.trans value))
 exact hw.trans (congrArg Word.val he)
def total : Solidity.Out C mid.st.H Final := ⟨finished.st,chosen.ext.trans finished.ext⟩
def afterCells (base : Nat → Fin W) (m : Machine) : List Word :=
 [m.mem 1,m.mem 2,m.mem 3,m.mem 4,m.mem 5,m.mem 6,m.mem 7,m.mem 8,m.mem 9,
  m.mem (base 0).val,m.mem ((base 0).val+1),m.mem ((base 0).val+2),
  m.mem (base 1).val,m.mem ((base 1).val+1),m.mem ((base 1).val+2),
  m.mem (base 2).val,m.mem (base 3).val,m.mem (base 4).val,
  m.mem ((base 4).val+1),m.mem ((base 4).val+2),.val (m.store.cells (.root 0)),m.mem 0]

theorem observe_after {base₁ base₃ : Nat → Fin W} {m : Machine}
 (hr : StateRepr 1 1 64 postCert.frag finished.st base₃ m)
 (he : BaseExtends mid.st.H base₁ base₃) (cursor : m.mem 0 = w[139]) :
 afterCells base₃ m = [w[42],.val (base₁ 0),.val (base₁ 0),.val (base₁ 1),w[2],
  .val (base₁ 0),w[5],.val (base₁ 0),.val (base₁ 0),w[2],w[12],w[11],w[2],w[23],w[29],
  w[0],w[0],w[2],w[99],w[101],w[11],w[139]] := by
 obtain ⟨ar,ad,ac,asame,axs,ao⟩ := final_aliases
 have ret := old_alias_at_entry_address (σ := mid.st) total hr he old (.here : Idx Final (.mem A)) ar
 have dest := old_alias_at_entry_address (σ := mid.st) total hr he old _ ad
 have capref := old_alias_at_entry_address (σ := mid.st) total hr he old _ ac
 have same := old_alias_at_entry_address (σ := mid.st) total hr he old _ asame
 have xs := old_alias_at_entry_address (σ := mid.st) total hr he old _ axs
 have otherCell := old_alias_at_entry_address (σ := mid.st) total hr he other _ ao
 change m.mem 9 = .val (base₁ 0) at ret
 change m.mem 8 = .val (base₁ 0) at dest
 change m.mem 6 = .val (base₁ 0) at capref
 change m.mem 3 = .val (base₁ 0) at same
 change m.mem 2 = .val (base₁ 0) at xs
 change m.mem 4 = .val (base₁ 1) at otherCell
 have cap := uint_word (n := wmod 5) (hr.core.vals (.there (.there .here) : Idx Final (.val .uint))) (by decide +kernel)
 have tag := uint_word (n := wmod 2) (hr.core.vals (.there (.there (.there (.there .here))) : Idx Final (.val .uint))) (by decide +kernel)
 have marker := uint_word (n := wmod 42) (hr.core.vals (.there (.there (.there (.there (.there (.there (.there (.there .here))))))) : Idx Final (.val .uint))) (by decide +kernel)
 change m.mem 7 = w[5] at cap
 change m.mem 5 = w[2] at tag
 change m.mem 1 = w[42] at marker
 obtain ⟨l0,l1,ld,lc,lp,e00,e01,e10,e11,ep0,ep1⟩ := heap_values
 have h0 := (hr.heap.arrays exported).length
 have h1 := (hr.heap.arrays ((other.wk chosen.ext).wk finished.ext)).length
 have hd := (hr.heap.arrays ((sharedDefault.wk chosen.ext).wk finished.ext)).length
 have hc := (hr.heap.arrays (callDefault.wk finished.ext)).length
 have hp := (hr.heap.arrays (privateNew.wk finished.ext)).length
 rw [l0] at h0; rw [l1] at h1; rw [ld] at hd; rw [lc] at hc; rw [lp] at hp
 change m.mem (base₃ 0).val = w[2] at h0
 change m.mem (base₃ 1).val = w[2] at h1
 change m.mem (base₃ 2).val = w[0] at hd
 change m.mem (base₃ 3).val = w[0] at hc
 change m.mem (base₃ 4).val = w[2] at hp
 have a := uint_word ((hr.heap.arrays exported).elements 0 _ e00) rfl
 have b := uint_word ((hr.heap.arrays exported).elements 1 _ e01) rfl
 have c := uint_word ((hr.heap.arrays ((other.wk chosen.ext).wk finished.ext)).elements 0 _ e10) rfl
 have d := uint_word ((hr.heap.arrays ((other.wk chosen.ext).wk finished.ext)).elements 1 _ e11) rfl
 have e := uint_word ((hr.heap.arrays (privateNew.wk finished.ext)).elements 0 _ ep0) rfl
 have f := uint_word ((hr.heap.arrays (privateNew.wk finished.ext)).elements 1 _ ep1) rfl
 change m.mem ((base₃ 0).val+1) = w[12] at a
 change m.mem ((base₃ 0).val+2) = w[11] at b
 change m.mem ((base₃ 1).val+1) = w[23] at c
 change m.mem ((base₃ 1).val+2) = w[29] at d
 change m.mem ((base₃ 4).val+1) = w[99] at e
 change m.mem ((base₃ 4).val+2) = w[101] at f
 have storage := hr.core.store "count" (.prim .uint) rfl
 change ReprAt m.store 1 (.prim .uint) (rootSlot C "count")
   (finished.st.storage.get (rfl : C.rootType "count" = some (.prim .uint))) at storage
 have sv : finished.st.storage.get (rfl : C.rootType "count" = some (.prim .uint)) = .prim (indexValue (wmod 11)) := by decide +kernel
 rw [sv] at storage
 have rootCell : (.val (m.store.cells (.root 0)) : Word) = w[11] := by
   cases storage with | prim h => exact uint_word h rfl
 simp only [afterCells,marker,xs,same,otherCell,tag,capref,cap,dest,ret,h0,h1,hd,hc,hp,a,b,c,d,e,f,rootCell,cursor]

theorem complete_endpoint : ∃ (m₁ : Machine) (base₁ : Nat → Fin W) (m₂ : Machine) (base₂ : Nat → Fin W)
 (m₃ : Machine) (base₃ : Nat → Fin W),
 run seed.code machine = .ok m₁ 0 ∧ run checked.code m₁ = .ok m₂ 0 ∧ run postCert.code m₂ = .ok m₃ 0 ∧
 run (seed.code ++ checked.code ++ postCert.code) machine = .ok m₃ 0 ∧
 StateRepr 1 1 64 postCert.frag finished.st base₃ m₃ ∧
 GrowsAllocator 1 64 11 (State.init C) bases machine finished.st base₃ m₃ ∧ m₃.stack = [w[77]] ∧
 afterCells base₃ m₃ = [w[42],.val (base₁ 0),.val (base₁ 0),.val (base₁ 1),w[2],.val (base₁ 0),w[5],
  .val (base₁ 0),.val (base₁ 0),w[2],w[12],w[11],w[2],w[23],w[29],w[0],w[0],w[2],w[99],w[101],w[11],w[139]] := by
 obtain ⟨m₁,base₁,m₂,base₂,m₃,base₃,hp,hc,ht,whole,hr₁,hr₂,hr₃,he₂,he₃,hg,stack,cursor⟩ := endpoint
 exact ⟨m₁,base₁,m₂,base₂,m₃,base₃,hp,hc,ht,whole,hr₃,hg,stack,observe_after hr₃ (he₂.trans chosen.ext he₃) cursor⟩

private theorem distinct_pointer {m : Machine} {base : Nat → Fin W}
 (hr : StateRepr 1 1 64 postCert.frag finished.st base m) (r : HRef finished.st.H A)
 (different : exported.id ≠ r.id) : m.mem 9 ≠ .val (base r.id) := by
 have gap := hr.heap.separated exported r different
 have addr : base exported.id ≠ base r.id := by
   intro eq
   change (base exported.id).val + 1 + _ ≤ (base r.id).val ∨
     (base r.id).val + 1 + _ ≤ (base exported.id).val at gap
   rw [eq] at gap
   rcases gap with h | h <;> omega
 obtain ⟨q,hq,ptr⟩ := hr.pointers (.here : Idx Final (.mem A))
 have eq : q = exported := Option.some.inj (hq.symm.trans final_aliases.1)
 subst q
 change m.mem 9 = .val (base exported.id) at ptr
 rw [ptr]
 exact fun h => addr (Word.val.inj h)

theorem negative_escape : ∃ (m : Machine) (base : Nat → Fin W),
 run (seed.code ++ checked.code ++ postCert.code) machine = .ok m 0 ∧
 m.mem 9 ≠ .val (base other.id) ∧ m.mem 9 ≠ .val (base sharedDefault.id) ∧
 m.mem 9 ≠ .val (base callDefault.id) ∧ m.mem 9 ≠ .val (base privateNew.id) ∧
 m.mem 0 ≠ w[137] ∧ m.mem ((base 0).val+1) ≠ w[7] := by
 obtain ⟨m₁,base₁,m₂,base₂,m₃,base₃,hp,hc,ht,whole,hr,hg,stack,obs⟩ := complete_endpoint
 have cursor := congrArg (fun xs : List Word => xs[21]?) obs
 have elem := congrArg (fun xs : List Word => xs[10]?) obs
 change some (m₃.mem 0) = some w[139] at cursor
 change some (m₃.mem ((base₃ 0).val+1)) = some w[12] at elem
 refine ⟨m₃,base₃,whole,
  distinct_pointer hr ((other.wk chosen.ext).wk finished.ext) (by decide +kernel),
  distinct_pointer hr ((sharedDefault.wk chosen.ext).wk finished.ext) (by decide +kernel),
  distinct_pointer hr (callDefault.wk finished.ext) (by decide +kernel),
  distinct_pointer hr (privateNew.wk finished.ext) (by decide +kernel),?_,?_⟩
 · rw [Option.some.inj cursor]; decide +kernel
 · rw [Option.some.inj elem]; decide +kernel

#print axioms negative_escape
#print axioms observe_after
#print axioms complete_endpoint
#print axioms capacity
#print axioms endpoint
end Solidity.Backend.InternalFlow.MemoryDispatchChecks

namespace Solidity.Backend.InternalFlow.DispatchRuntimeChecks
open Evm Evm.Memory
private def trace (code : List Instr) (addresses : List Nat) : Option (List Word × List Word × Nat) :=
 match Evm.run code DispatchChecks.machine with
 | .ok m _ => some (m.stack,addresses.map m.mem,(m.store.cells (.root 0)).val)
 | _ => none
/-- info: true -/
#guard_msgs in #eval decide (trace (DispatchChecks.seed.code ++ DispatchChecks.checked.code)
 [0,1,2,3,4,5,6,7,8,63,128,129,130,131,132,133,134,135,136] =
 some ([w[77]],[w[137],w[42],w[128],w[128],w[131],w[2],w[16],w[128],w[5],w[99],
  w[2],w[7],w[16],w[2],w[23],w[29],w[2],w[70],w[71]],10))
/-- info: true -/
#guard_msgs in #eval decide (trace
 (MemoryDispatchChecks.seed.code ++ MemoryDispatchChecks.checked.code ++ MemoryDispatchChecks.postCert.code)
 [0,1,2,3,4,5,6,7,8,9,63,128,129,130,131,132,133,134,135,136,137,138] =
 some ([w[77]],[w[139],w[42],w[128],w[128],w[131],w[2],w[128],w[5],w[128],w[128],w[99],
  w[2],w[12],w[11],w[2],w[23],w[29],w[0],w[0],w[2],w[99],w[101]],11))
end Solidity.Backend.InternalFlow.DispatchRuntimeChecks

namespace Solidity.Backend.InternalFlow.DispatchChecks.ProtectedCaller
open Evm Evm.Memory
abbrev View : Ctx := [.val .uint,.mem A,.val .uint,.mem A,.mem A,.mem A,.val .uint]
def projection : Thin View Caller := .keep (.keep (.drop .refl))
def destination : Idx Caller (.val .uint) := .there (.there .here)

theorem separated (name : Var) :
    CallerFrame.Disjoint projection (.val .uint name (some destination)) := by
  intro t i
  cases i with
  | here => decide
  | there i =>
    cases i with
    | here => decide
    | there i =>
      change 2 ≠ i.toNat + 3
      omega

theorem complete_caller_frame :
    TEnv.thin projection chosen.st.env =
      TEnv.wk chosen.ext View (TEnv.thin projection mid.st.env) := by
  exact CallerFrame.single_call_environment projection (separated _) body_run

def wrongProjection : Thin [.mem A,.val .uint,.val .uint,.mem A,.mem A,.mem A,.val .uint] Caller :=
  .drop .refl

theorem wrong_destination (name : Var) :
    ¬ CallerFrame.Disjoint wrongProjection (.val .uint name (some destination)) := by
  intro separate
  exact separate (.val .uint) (.there .here) rfl

theorem full_frame_changes : chosen.st.env ≠ TEnv.wk chosen.ext Caller mid.st.env := by
  intro same
  have before : (locals mid.st)[2]! = some 0 := congrArg (fun x => x.2.2.1[2]!) before_values
  have after : (locals chosen.st)[2]! = some 16 := congrArg (fun x => x.2.2.1[2]!) after_values
  have value := congrArg (fun env => some ((TEnv.get destination env).1.toNat)) same
  change (locals chosen.st)[2]! = (locals mid.st)[2]! at value
  rw [after,before] at value
  cases value

theorem no_heap_frame : ¬ Heap.Keeps chosen.ext mid.st.heap chosen.st.heap := by
  intro kept
  have changed := congrArg (fun obj => (MObj.elems .dyn obj)[1]?) (kept old)
  have before : (MObj.elems .dyn (MObj.wk chosen.ext A (mid.st.heap.get old)))[1]? =
      some (indexValue (wmod 11)) := by decide +kernel
  dsimp only at changed
  rw [heap_values.2.2.2.2.1,before] at changed
  have impossible := congrArg (fun v : PrimTy.uint.Denote => v.1) (Option.some.inj changed)
  cases impossible

theorem fallback_no_success (out : Solidity.Out C cleared.st.H Caller) :
    actualDispatch.run cleared.st ≠ .ok out := by
  rw [no_match_run]
  intro impossible
  cases impossible

theorem protected_alias_id : (locals chosen.st)[1]! = some 0 := by
  have same := congrArg (fun env =>
    (TEnv.get (.there .here : Idx View (.mem A)) env).map HRef.id) complete_caller_frame
  dsimp only at same
  rw [CallerFrame.read_thin,TEnv.get_wk,CallerFrame.read_thin] at same
  simp only [LTy.TDenote.wk,Option.map_map,Function.comp_def] at same
  change (locals chosen.st)[1]! = (locals mid.st)[1]! at same
  exact same.trans (congrArg (fun x => x.2.2.1[1]!) before_values)

theorem wrong_private_escape :
    TEnv.get (.there .here : Idx Caller (.mem A)) chosen.st.env ≠ some fresh := by
  intro wrong
  have ids := congrArg (fun v => v.map HRef.id) wrong
  change (locals chosen.st)[1]! = some 2 at ids
  rw [protected_alias_id] at ids
  cases ids

theorem protected_target : ∃ (m₁ : Machine) (base₁ : Nat → Fin W) (m₂ : Machine) (base₂ : Nat → Fin W),
    run seed.code machine = .ok m₁ 0 ∧ run checked.code m₁ = .ok m₂ 0 ∧
    run (seed.code ++ checked.code) machine = .ok m₂ 0 ∧
    StateRepr 1 1 64 seed.frag mid.st base₁ m₁ ∧
    StateRepr 1 1 64 checked.frag chosen.st base₂ m₂ ∧
    BaseExtends mid.st.H base₁ base₂ ∧
    GrowsAllocator 1 64 9 (State.init C) bases machine chosen.st base₂ m₂ ∧
    m₂.stack = [w[77]] ∧ m₂.mem 0 = w[137] ∧
    afterCells base₂ m₂ = [w[42],.val (base₁ 0),.val (base₁ 0),.val (base₁ 1),w[2],w[16],
      .val (base₁ 0),w[5],w[2],w[7],w[16],w[2],w[23],w[29],w[2],w[70],w[71],w[10],w[137]] ∧
    TEnv.thin projection chosen.st.env =
      TEnv.wk chosen.ext View (TEnv.thin projection mid.st.env) ∧
    ∀ (R : RefTy) (i : Idx View (.mem R)) (r : HRef mid.st.H R),
      TEnv.get (i.wk projection) mid.st.env = some r →
        m₂.mem (cellOf 1 (i.wk projection)) = .val (base₁ r.id) := by
  obtain ⟨m₁,base₁,hp,hr₁,stack₁,he₁,hg₁⟩ := PublishedDirectCalls.program_endpoint
    seed (initial_repr C).1 seed_frame (capacity.of_le (Nat.le_add_right _ _)) mid seed_run
  have input := hg₁.nextInput capacity
  obtain ⟨m₂,base₂,hc,hr₂,stack₂,he₂,hg₂,view,pointers⟩ :=
    CallerFrame.selected_target projection (separated _)
      actualSecond.cond [actualFirst] [] .revert checked mid.st (by
        intro a h; have ha := List.mem_singleton.mp h; subst a; exact first_miss)
      second_hit armOut body_run hr₁ room input
  have whole := (run_append_ok hp).trans hc
  have grows := hg₁.comp hg₂
  rw [seed_cost,reached_cost] at grows
  have cursor := (grows (wmod 128) (by decide) (initial_repr C).2 (by decide +kernel)).arrays.free.cell
  change m₂.mem 0 = w[137] at cursor
  exact ⟨m₁,base₁,m₂,base₂,hp,hc,whole,hr₁,hr₂,he₂,grows,stack₂.trans stack₁,cursor,
    observe_after hr₂ he₂ cursor,view,pointers⟩

/-- info: 'Solidity.Backend.InternalFlow.DispatchChecks.ProtectedCaller.separated' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms separated

/-- info: 'Solidity.Backend.InternalFlow.DispatchChecks.ProtectedCaller.complete_caller_frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms complete_caller_frame

/-- info: 'Solidity.Backend.InternalFlow.DispatchChecks.ProtectedCaller.wrong_destination' depends on axioms: [propext] -/
#guard_msgs in #print axioms wrong_destination

/-- info: 'Solidity.Backend.InternalFlow.DispatchChecks.ProtectedCaller.full_frame_changes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms full_frame_changes

/-- info: 'Solidity.Backend.InternalFlow.DispatchChecks.ProtectedCaller.no_heap_frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms no_heap_frame

/-- info: 'Solidity.Backend.InternalFlow.DispatchChecks.ProtectedCaller.fallback_no_success' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms fallback_no_success

/-- info: 'Solidity.Backend.InternalFlow.DispatchChecks.ProtectedCaller.protected_alias_id' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms protected_alias_id

/-- info: 'Solidity.Backend.InternalFlow.DispatchChecks.ProtectedCaller.wrong_private_escape' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms wrong_private_escape

/-- info: 'Solidity.Backend.InternalFlow.DispatchChecks.ProtectedCaller.protected_target' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms protected_target

end Solidity.Backend.InternalFlow.DispatchChecks.ProtectedCaller

namespace Solidity.Backend.InternalFlow.MemoryDispatchChecks.ProtectedTail
open Evm Evm.Memory
abbrev View : Ctx := [.val .uint,.mem A,.val .uint,.mem A,.mem A,.mem A,.val .uint]
def projection : Thin View Caller := .drop .refl

def tail : Prog C (.mem A :: Caller) (.mem A :: Caller) :=
  .cons (.rebindMem (.there .here) (.alias (.var .here rfl))) .nil

theorem tail_within : Prog.withinM .nonpayable tail = true := rfl

theorem tail_unwritten (t : LTy) (i : Idx View t) :
    (t,((i.wk projection).ext (.push (t := .mem A) .refl)).toNat) ∉ Prog.writesAt 0 tail := by
  intro member
  change (t,i.toNat + 2) ∈ [(.mem A,1)] at member
  have index := congrArg Prod.snd (List.mem_singleton.mp member)
  omega

theorem complete_caller_frame :
    TEnv.thin projection chosen.st.env =
      TEnv.wk chosen.ext View (TEnv.thin projection mid.st.env) :=
  CallerTail.environment (executed := body_run) projection (by trivial) tail_within (by exact tail_unwritten)

theorem whole_body_guard_stays_false : Prog.withinM .nonpayable actualSecond.body = false := by decide +kernel

theorem wrong_destination : ¬ ∀ (t : LTy) (i : Idx Caller t),
    (t,(i.ext (.push (t := .mem A) .refl)).toNat) ∉ Prog.writesAt 0 tail := by
  intro unwritten
  exact unwritten (.mem A) .here (by decide +kernel)

theorem reference_ids_wk {H H' : HTy} (e : H <+: H') (v : Option (HRef H A)) :
    (LTy.TDenote.wk (C := C) e (.mem A) v).map HRef.id = v.map HRef.id := by
  cases v <;> rfl

theorem full_frame_changes : chosen.st.env ≠ TEnv.wk chosen.ext Caller mid.st.env := by
  intro same
  have before : (locals mid.st)[0]! = some 2 := congrArg (fun x => x.2.2.1[0]!) before_values
  have after : (locals chosen.st)[0]! = some 0 := congrArg (fun x => x.2.2.1[0]!) after_values
  have ids := congrArg (fun env => (TEnv.get (.here : Idx Caller (.mem A)) env).map HRef.id) same
  dsimp only at ids
  rw [TEnv.get_wk,reference_ids_wk] at ids
  change (locals chosen.st)[0]! = (locals mid.st)[0]! at ids
  rw [after,before] at ids
  cases ids

theorem protected_alias_id : (locals chosen.st)[2]! = some 0 := by
  have same := congrArg (fun env =>
    (TEnv.get (.there .here : Idx View (.mem A)) env).map HRef.id) complete_caller_frame
  dsimp only at same
  rw [CallerFrame.read_thin,TEnv.get_wk,CallerFrame.read_thin] at same
  rw [reference_ids_wk] at same
  change (locals chosen.st)[2]! = (locals mid.st)[2]! at same
  exact same.trans (congrArg (fun x => x.2.2.1[2]!) before_values)

theorem post_step :
    TEnv.thin projection (TEnv.drop post.ext finished.st.env) =
      TEnv.wk finished.ext View (TEnv.thin projection chosen.st.env) := by
  exact CallerTail.program_environment (P := post) (σ := chosen.st) (out := finished)
    projection (by decide +kernel) (by
      intro t i member
      change (t,(i.wk projection).toNat) ∈ [] at member
      exact List.not_mem_nil member) post_run
theorem protected_final_frame :
    TEnv.thin projection (TEnv.drop post.ext finished.st.env) =
      TEnv.wk total.ext View (TEnv.thin projection mid.st.env) :=
  post_step.trans ((congrArg (TEnv.wk finished.ext View) complete_caller_frame).trans
    (TEnv.wk_trans chosen.ext finished.ext View (TEnv.thin projection mid.st.env)))


/-- info: 'Solidity.Backend.InternalFlow.MemoryDispatchChecks.ProtectedTail.tail_within' depends on axioms: [propext] -/
#guard_msgs in #print axioms tail_within

/-- info: 'Solidity.Backend.InternalFlow.MemoryDispatchChecks.ProtectedTail.tail_unwritten' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in #print axioms tail_unwritten

/-- info: 'Solidity.Backend.InternalFlow.MemoryDispatchChecks.ProtectedTail.complete_caller_frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms complete_caller_frame

/-- info: 'Solidity.Backend.InternalFlow.MemoryDispatchChecks.ProtectedTail.whole_body_guard_stays_false' depends on axioms: [propext] -/
#guard_msgs in #print axioms whole_body_guard_stays_false

/-- info: 'Solidity.Backend.InternalFlow.MemoryDispatchChecks.ProtectedTail.wrong_destination' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in #print axioms wrong_destination

/-- info: 'Solidity.Backend.InternalFlow.MemoryDispatchChecks.ProtectedTail.reference_ids_wk' depends on axioms: [propext] -/
#guard_msgs in #print axioms reference_ids_wk

/-- info: 'Solidity.Backend.InternalFlow.MemoryDispatchChecks.ProtectedTail.full_frame_changes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms full_frame_changes

/-- info: 'Solidity.Backend.InternalFlow.MemoryDispatchChecks.ProtectedTail.protected_alias_id' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms protected_alias_id

/-- info: 'Solidity.Backend.InternalFlow.MemoryDispatchChecks.ProtectedTail.post_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms post_step

/-- info: 'Solidity.Backend.InternalFlow.MemoryDispatchChecks.ProtectedTail.protected_final_frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms protected_final_frame

end Solidity.Backend.InternalFlow.MemoryDispatchChecks.ProtectedTail

namespace Solidity.Backend.InternalFlow.MemoryDispatchChecks.ProtectedTail
open Evm Evm.Memory

theorem middle_pointers {base₁ base₂ : Nat → Fin W} {m₂ : Machine}
    (repr : StateRepr 1 1 64 checked.frag chosen.st base₂ m₂)
    (addresses : BaseExtends mid.st.H base₁ base₂) :
    ∀ (R : RefTy) (i : Idx View (.mem R)) (r : HRef mid.st.H R),
      TEnv.get (i.wk projection) mid.st.env = some r →
        m₂.mem (cellOf 1 (i.wk projection)) = .val (base₁ r.id) :=
  CallerView.represented (σ := mid.st) chosen projection complete_caller_frame repr addresses

theorem middle_endpoint : ∃ (m₁ : Machine) (base₁ : Nat → Fin W) (m₂ : Machine) (base₂ : Nat → Fin W),
    run seed.code machine = .ok m₁ 0 ∧ run checked.code m₁ = .ok m₂ 0 ∧
    StateRepr 1 1 64 seed.frag mid.st base₁ m₁ ∧
    StateRepr 1 1 64 checked.frag chosen.st base₂ m₂ ∧
    BaseExtends mid.st.H base₁ base₂ ∧
    ∀ (R : RefTy) (i : Idx View (.mem R)) (r : HRef mid.st.H R),
      TEnv.get (i.wk projection) mid.st.env = some r →
        m₂.mem (cellOf 1 (i.wk projection)) = .val (base₁ r.id) := by
  obtain ⟨m₁,base₁,m₂,base₂,m₃,base₃,hp,hc,ht,whole,hr₁,hr₂,hr₃,he₂,he₃,grows,stack,cursor⟩ := endpoint
  exact ⟨m₁,base₁,m₂,base₂,hp,hc,hr₁,hr₂,he₂,
    middle_pointers (base₁ := base₁) (base₂ := base₂) (m₂ := m₂) hr₂ he₂⟩

def capIndex : Idx View (.mem A) := .there .here
def otherIndex : Idx View (.mem A) := .there (.there (.there .here))
def sameIndex : Idx View (.mem A) := .there (.there (.there (.there .here)))
def xsIndex : Idx View (.mem A) := .there (.there (.there (.there (.there .here))))

theorem old_inputs :
    TEnv.get (capIndex.wk projection) mid.st.env = some old ∧
    TEnv.get (otherIndex.wk projection) mid.st.env = some other ∧
    TEnv.get (sameIndex.wk projection) mid.st.env = some old ∧
    TEnv.get (xsIndex.wk projection) mid.st.env = some old := by
  refine ⟨CallerView.by_id _ _ ?_,CallerView.by_id _ _ ?_,CallerView.by_id _ _ ?_,CallerView.by_id _ _ ?_⟩
  · change (locals mid.st)[2]! = some 0
    exact congrArg (fun x => x.2.2.1[2]!) before_values
  · change (locals mid.st)[4]! = some 1
    exact congrArg (fun x => x.2.2.1[4]!) before_values
  · change (locals mid.st)[5]! = some 0
    exact congrArg (fun x => x.2.2.1[5]!) before_values
  · change (locals mid.st)[6]! = some 0
    exact congrArg (fun x => x.2.2.1[6]!) before_values

theorem middle_snapshot : ∃ (m₁ : Machine) (base₁ : Nat → Fin W) (m₂ : Machine) (base₂ : Nat → Fin W),
    run seed.code machine = .ok m₁ 0 ∧ run checked.code m₁ = .ok m₂ 0 ∧
    StateRepr 1 1 64 checked.frag chosen.st base₂ m₂ ∧
    [m₂.mem 6,m₂.mem 4,m₂.mem 3,m₂.mem 2] =
      [.val (base₁ 0),.val (base₁ 1),.val (base₁ 0),.val (base₁ 0)] ∧
    m₂.mem 6 ≠ .val (base₂ privateNew.id) ∧
    m₂.mem 6 ≠ .val (base₂ other.id) ∧
    m₂.mem 6 ≠ .val (base₂ sharedDefault.id) := by
  obtain ⟨m₁,base₁,m₂,base₂,hp,hc,hr₁,hr₂,addresses,capturedRefs⟩ := middle_endpoint
  have cap := capturedRefs A capIndex old old_inputs.1
  have otherPtr := capturedRefs A otherIndex other old_inputs.2.1
  have same := capturedRefs A sameIndex old old_inputs.2.2.1
  have xs := capturedRefs A xsIndex old old_inputs.2.2.2
  change m₂.mem 6 = .val (base₁ 0) at cap
  change m₂.mem 4 = .val (base₁ 1) at otherPtr
  change m₂.mem 3 = .val (base₁ 0) at same
  change m₂.mem 2 = .val (base₁ 0) at xs
  have privateWrong := CallerView.different_array (σ := mid.st) chosen projection
    complete_caller_frame hr₂ capIndex old old_inputs.1 privateNew (by decide +kernel)
  have otherWrong := CallerView.different_array (σ := mid.st) chosen projection
    complete_caller_frame hr₂ capIndex old old_inputs.1 (other.wk chosen.ext) (by decide +kernel)
  have defaultWrong := CallerView.different_array (σ := mid.st) chosen projection
    complete_caller_frame hr₂ capIndex old old_inputs.1 (sharedDefault.wk chosen.ext) (by decide +kernel)
  refine ⟨m₁,base₁,m₂,base₂,hp,hc,hr₂,?_,privateWrong,otherWrong,defaultWrong⟩
  rw [cap,otherPtr,same,xs]

/-- info: 'Solidity.Backend.InternalFlow.MemoryDispatchChecks.ProtectedTail.middle_pointers' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms middle_pointers

/-- info: 'Solidity.Backend.InternalFlow.MemoryDispatchChecks.ProtectedTail.middle_endpoint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms middle_endpoint

/-- info: 'Solidity.Backend.InternalFlow.MemoryDispatchChecks.ProtectedTail.old_inputs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms old_inputs

/-- info: 'Solidity.Backend.InternalFlow.MemoryDispatchChecks.ProtectedTail.middle_snapshot' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms middle_snapshot

end Solidity.Backend.InternalFlow.MemoryDispatchChecks.ProtectedTail

namespace Solidity.Backend.InternalFlow.MemoryDispatchChecks.ProtectedTail
open Evm Evm.Memory

/-- The actual allocating suffix keeps the captured old alias after dropping
its result/local prefix; the callee's old-object mutation is not hidden. -/
theorem final_alias_after_drop :
    TEnv.get ((capIndex.wk projection).ext post.ext) total.st.env =
      some (old.wk total.ext) :=
  CallerView.reference_drop total post.ext projection protected_final_frame
    capIndex old old_inputs.1

theorem final_other_is_not_old :
    TEnv.get ((capIndex.wk projection).ext post.ext) total.st.env ≠
      some (other.wk total.ext) := by
  rw [final_alias_after_drop]
  intro impossible
  have ids := congrArg (fun x => x.map HRef.id) impossible
  change (some 0 : Option Nat) = some 1 at ids
  cases ids

/-- Genuine reached representation and composed entry-address extension,
not a requested simulation or a heap-content invariant. -/
theorem final_pointers {base₁ base₃ : Nat → Fin W} {m₃ : Machine}
    (repr : StateRepr 1 1 64 postCert.frag total.st base₃ m₃)
    (addresses : BaseExtends mid.st.H base₁ base₃) :
    ∀ (R : RefTy) (i : Idx View (.mem R)) (r : HRef mid.st.H R),
      TEnv.get (i.wk projection) mid.st.env = some r →
        m₃.mem (cellOf 1 ((i.wk projection).ext post.ext)) = .val (base₁ r.id) :=
  CallerView.represented_drop total post.ext projection protected_final_frame repr addresses

/-- The existing checked prefix/selected-call/suffix endpoint discharges the
reached representation and composed address premises for every protected alias. -/
theorem final_target_pointers :
    ∃ (m₁ : Machine) (base₁ : Nat → Fin W) (m₃ : Machine) (base₃ : Nat → Fin W),
      run seed.code machine = .ok m₁ 0 ∧
      run (seed.code ++ checked.code ++ postCert.code) machine = .ok m₃ 0 ∧
      StateRepr 1 1 64 seed.frag mid.st base₁ m₁ ∧
      StateRepr 1 1 64 postCert.frag total.st base₃ m₃ ∧
      BaseExtends mid.st.H base₁ base₃ ∧
      GrowsAllocator 1 64 11 (State.init C) bases machine total.st base₃ m₃ ∧
      m₃.stack = [w[77]] ∧ m₃.mem 0 = w[139] ∧
      ∀ (R : RefTy) (i : Idx View (.mem R)) (r : HRef mid.st.H R),
        TEnv.get (i.wk projection) mid.st.env = some r →
          m₃.mem (cellOf 1 ((i.wk projection).ext post.ext)) = .val (base₁ r.id) := by
  obtain ⟨m₁,base₁,m₂,base₂,m₃,base₃,hp,hc,ht,whole,hr₁,hr₂,hr₃,he₂,he₃,grows,stack,cursor⟩ := endpoint
  have addresses : BaseExtends mid.st.H base₁ base₃ := BaseExtends.trans chosen.ext he₂ he₃
  exact ⟨m₁,base₁,m₃,base₃,hp,whole,hr₁,hr₃,addresses,grows,stack,cursor,
    final_pointers hr₃ addresses⟩

/-- Complete original ordered observations and the actual captured final caller
view coexist with the newly proved protected target addresses. -/
theorem final_target_observed :
    ∃ (m₁ : Machine) (base₁ : Nat → Fin W) (m₃ : Machine) (base₃ : Nat → Fin W),
      run seed.code machine = .ok m₁ 0 ∧
      run (seed.code ++ checked.code ++ postCert.code) machine = .ok m₃ 0 ∧
      StateRepr 1 1 64 seed.frag mid.st base₁ m₁ ∧
      StateRepr 1 1 64 postCert.frag total.st base₃ m₃ ∧
      BaseExtends mid.st.H base₁ base₃ ∧
      GrowsAllocator 1 64 11 (State.init C) bases machine total.st base₃ m₃ ∧
      m₃.stack = [w[77]] ∧ m₃.mem 0 = w[139] ∧
      afterCells base₃ m₃ = [w[42],.val (base₁ 0),.val (base₁ 0),.val (base₁ 1),w[2],
        .val (base₁ 0),w[5],.val (base₁ 0),.val (base₁ 0),w[2],w[12],w[11],w[2],w[23],w[29],
        w[0],w[0],w[2],w[99],w[101],w[11],w[139]] ∧
      TEnv.thin projection (TEnv.drop post.ext total.st.env) =
        TEnv.wk total.ext View (TEnv.thin projection mid.st.env) ∧
      ∀ (R : RefTy) (i : Idx View (.mem R)) (r : HRef mid.st.H R),
        TEnv.get (i.wk projection) mid.st.env = some r →
          m₃.mem (cellOf 1 ((i.wk projection).ext post.ext)) = .val (base₁ r.id) := by
  obtain ⟨m₁,base₁,m₃,base₃,hp,whole,hr₁,hr₃,addresses,grows,stack,cursor,pointers⟩ := final_target_pointers
  exact ⟨m₁,base₁,m₃,base₃,hp,whole,hr₁,hr₃,addresses,grows,stack,cursor,
    observe_after hr₃ addresses cursor,protected_final_frame,pointers⟩

end Solidity.Backend.InternalFlow.MemoryDispatchChecks.ProtectedTail
