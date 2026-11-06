import Solidity.Backend.Aggregates.G18ReferenceSequence
import Solidity.Backend.Aggregates.G18MemoryClient

/-! Three genuine objects: two distinct Boolean children and an aliased parent.
This is a fixture for real Source/typed/word certificates, not new semantics. -/
namespace Solidity.Backend.Aggregates.DistinctClient
open MemoryOps

def C : Contract := MemoryClient.C
def child : RefTy := .array (.prim .bool)
def parent : RefTy := BoolRefsRef
def H : HTy := [child,child,parent]
def q : HRef H child := ⟨0,rfl⟩
def other : HRef H child := ⟨1,rfl⟩
def r : HRef H parent := ⟨2,rfl⟩
def hp : Heap H := (⟨[false,false],by decide +kernel⟩,⟨[true,false],by decide +kernel⟩,
  ⟨[q,other,q],by decide +kernel⟩,())
def state : State C [] := {State.init C with H := H,heap := hp}
def base (id : Nat) : Fin Evm.W := Evm.wmod (if id=0 then 16 else if id=1 then 24 else 32)
def machine : Evm.Machine := {Evm.Machine.init with
  stack := [.val (Evm.wmod 77)]
  mem := fun a => if a=16 ∨ a=24 then .val (Evm.wmod 2)
    else if a=25 then .val (Evm.bword true)
    else if a=32 then .val (Evm.wmod 3)
    else if a=33 ∨ a=35 then .val (Evm.wmod 16)
    else if a=34 then .val (Evm.wmod 24)
    else .val (Evm.wmod 0)}

theorem ref_cases {R : RefTy} (t : HRef H R) :
    (R=child ∧ t.id=0) ∨ (R=child ∧ t.id=1) ∨ (R=parent ∧ t.id=2) := by
  rcases t with ⟨i,hi⟩
  match i with
  | 0 => exact .inl ⟨(Option.some.inj hi).symm,rfl⟩
  | 1 => exact .inr (.inl ⟨(Option.some.inj hi).symm,rfl⟩)
  | 2 => exact .inr (.inr ⟨(Option.some.inj hi).symm,rfl⟩)
  | i+3 => simp only [H,List.getElem?_cons_succ,List.getElem?_nil] at hi;cases hi

theorem primitive_info {p : PrimTy} (t : HRef H (.array (.prim p))) : p=.bool := by
  obtain ⟨ht,_⟩ | ⟨ht,_⟩ | ⟨ht,_⟩ := ref_cases t
  · exact Ty.prim.inj (RefTy.array.inj ht)
  · exact Ty.prim.inj (RefTy.array.inj ht)
  · cases RefTy.array.inj ht

theorem bool_cases (t : HRef H child) : t=q ∨ t=other := by
  obtain ⟨_,hi⟩ | ⟨_,hi⟩ | ⟨ht,_⟩ := ref_cases t
  · exact .inl (eq_of_heq (HRef.heq_of_id t q hi).2)
  · exact .inr (eq_of_heq (HRef.heq_of_id t other hi).2)
  · cases RefTy.array.inj ht

theorem reference_info {R : RefTy} (t : HRef H (.array (.ref R))) : R=child ∧ t.id=2 := by
  obtain ⟨ht,_⟩ | ⟨ht,_⟩ | ⟨ht,hi⟩ := ref_cases t
  · cases RefTy.array.inj ht
  · cases RefTy.array.inj ht
  · exact ⟨Ty.ref.inj (RefTy.array.inj ht),hi⟩

theorem no_struct {s : Name} (t : HRef H (.struct s)) : False := by
  obtain ⟨ht,_⟩ | ⟨ht,_⟩ | ⟨ht,_⟩ := ref_cases t <;> cases ht

theorem q_elems : MObj.elems .dyn (hp.get q)=[false,false] := by
  simp only [MObj.elems_dyn,Heap.get,H,hp,q,Objs.get]
theorem other_elems : MObj.elems .dyn (hp.get other)=[true,false] := by
  simp only [MObj.elems_dyn,Heap.get,H,hp,other,Objs.get]
theorem parent_elems : MObj.elems .dyn (hp.get r)=[q,other,q] := by
  simp only [MObj.elems_dyn,Heap.get,H,hp,r,Objs.get]

theorem q_repr : Evm.Memory.ArrayRepr hp q (base 0) machine := by
  refine ⟨by decide +kernel,by decide +kernel,?_⟩
  intro i v hv
  rw [q_elems] at hv
  match i with
  | 0 => cases hv;rfl
  | 1 => cases hv;rfl
  | i+2 => cases hv

theorem other_repr : Evm.Memory.ArrayRepr hp other (base 1) machine := by
  refine ⟨by decide +kernel,by decide +kernel,?_⟩
  intro i v hv
  rw [other_elems] at hv
  match i with
  | 0 => cases hv;rfl
  | 1 => cases hv;rfl
  | i+2 => cases hv

theorem parent_repr : Evm.Memory.RefArrayRepr hp r base machine := by
  refine ⟨by decide +kernel,by decide +kernel,?_⟩
  intro i v hv
  rw [parent_elems] at hv
  match i with
  | 0 => cases hv;rfl
  | 1 => cases hv;rfl
  | 2 => cases hv;rfl
  | i+3 => cases hv

theorem initial_word : Evm.Memory.RefArrayStateRepr 1 1 8 (Evm.Frag.init []) state base machine := by
  have hc := Evm.Sim.init C 0 Evm.W_pos (fun _ => 0) ⟨0,Evm.W_pos⟩ rfl
  have hprim : Evm.Memory.HeapRepr hp base 8 machine := by
    refine ⟨?_,?_,?_⟩
    · intro p t
      have he := primitive_info t
      subst p
      rcases bool_cases t with rfl | rfl
      · exact q_repr
      · exact other_repr
    · intro p t
      have he := primitive_info t
      subst p
      rcases bool_cases t with rfl | rfl <;> decide +kernel
    · intro p p' t u hn
      have he := primitive_info t
      have he' := primitive_info u
      subst p
      subst p'
      rcases bool_cases t with rfl | rfl <;> rcases bool_cases u with rfl | rfl
      · exact (hn rfl).elim
      · exact .inl (by decide +kernel)
      · exact .inr (by decide +kernel)
      · exact (hn rfl).elim
  have hs : Evm.Memory.StateRepr 1 1 8 (Evm.Frag.init []) state base machine := by
    refine ⟨⟨hc.store,?_,?_,hc.net,hc.netSelf,hc.bound,?_,hc.env,hc.funds,hc.oracle⟩,
      hprim,?_,by decide +kernel,⟨?_,?_,?_⟩,?_,?_⟩
    · intro p i;nomatch i
    · intro R i;nomatch i
    · intro R i;nomatch i
    · intro R i;nomatch i
    · intro s t;exact (no_struct t).elim
    · intro s t;exact (no_struct t).elim
    · intro s s' t u _;exact (no_struct t).elim
    · intro p s t u;exact (no_struct u).elim
    · exact Evm.Memory.RefFieldsRepr.withoutStructs hp base machine no_struct
  refine ⟨hs,⟨?_,?_,?_,?_,?_⟩⟩
  · intro R t
    obtain ⟨he,hi⟩ := reference_info t
    subst R
    have ht : t=r := eq_of_heq (HRef.heq_of_id t r hi).2
    subst t
    exact parent_repr
  · intro R t
    rw [(reference_info t).2]
    decide +kernel
  · intro R Q t u hn
    exact (hn ((reference_info t).2.trans (reference_info u).2.symm)).elim
  · intro R p t u
    obtain ⟨he,hi⟩ := reference_info t
    have he' := primitive_info u
    subst R
    subst p
    have ht : t=r := eq_of_heq (HRef.heq_of_id t r hi).2
    subst t
    rcases bool_cases u with rfl | rfl <;> exact .inr (by decide +kernel)
  · intro R s t u;exact (no_struct u).elim

def E : Source.Env := MemoryClient.E
def address (id : Nat) : Nat := id
def child0 : Source.Data E.layout (.array .memory .bool none) := sourceBoolMemory [false,false]
def child1 : Source.Data E.layout (.array .memory .bool none) := sourceBoolMemory [true,false]
def table : Source.Data E.layout SourceBoolRefsTy := sourceBoolRefMemory address [q,other,q]
def heap1 : Source.Heap E.layout := (Source.Heap.empty.alloc ⟨_,child0⟩).1
def heap2 : Source.Heap E.layout := (heap1.alloc ⟨_,child1⟩).1
def heap3 : Source.Heap E.layout := (heap2.alloc ⟨_,table⟩).1
def sourceState : Source.EMState E [] := (.nil,{Source.St.init E with heap := heap3})

/-- Inhabited construction uses the EXISTING Source allocator at each step.
The word image below is independently represented, not an allocation-code claim. -/
theorem source_allocations :
    (Source.allocRef (E := E) (Γ := []) child0).run (.nil,Source.St.init E)=
      (.ok (.memRef rfl 0),(.nil,{Source.St.init E with heap := heap1})) ∧
    (Source.allocRef (E := E) (Γ := []) child1).run (.nil,{Source.St.init E with heap := heap1})=
      (.ok (.memRef rfl 1),(.nil,{Source.St.init E with heap := heap2})) ∧
    (Source.allocRef (E := E) (Γ := []) table).run (.nil,{Source.St.init E with heap := heap2})=
      (.ok (.memRef rfl 2),sourceState) := ⟨rfl,rfl,rfl⟩

theorem initial_source : SourceBoolRefsAt sourceState 2 hp r address := by
  refine ⟨?_,?_⟩
  · rw [parent_elems]
    rfl
  · intro t ht
    rw [parent_elems] at ht
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ht
    rcases ht with rfl | rfl | rfl
    · unfold SourceBoolMemoryAt;rw [q_elems];rfl
    · unfold SourceBoolMemoryAt;rw [other_elems];rfl
    · unfold SourceBoolMemoryAt;rw [q_elems];rfl

theorem initial_memOK : Source.MemOK E heap3.ty sourceState := by
  have h0 : Source.HeapOK (E := E) (Source.Heap.empty : Source.Heap E.layout) := by
    intro a x hx;cases hx
  have h1 : Source.HeapOK (E := E) heap1 := h0.alloc (.array (fun _ => .val trivial))
  have h2 : Source.HeapOK (E := E) heap2 := h1.alloc (.array (fun _ => .val trivial))
  have h3 : Source.HeapOK (E := E) heap3 := by
    apply h2.alloc
    apply Source.DataOK.array
    rintro ⟨i,hi⟩
    match i with
    | 0 => exact .val ⟨_,rfl,rfl⟩
    | 1 => exact .val ⟨_,rfl,rfl⟩
    | 2 => exact .val ⟨_,rfl,rfl⟩
    | i+3 => change i+3<3 at hi;omega
  have shaped : Source.HeapShaped (E := E) heap3 := by
    have h0 : Source.HeapShaped (E := E) (Source.Heap.empty : Source.Heap E.layout) := by
      intro a x hx;cases hx
    exact ((h0.alloc (x := ⟨_,child0⟩) trivial).alloc (x := ⟨_,child1⟩) trivial).alloc trivial
  have inner : Source.HeapInner (E := E) heap3 := by
    have h0 : Source.HeapInner (E := E) (Source.Heap.empty : Source.Heap E.layout) := by
      intro a x hx;cases hx
    exact ((h0.alloc (x := ⟨_,child0⟩) (fun _ => ⟨_,rfl⟩)).alloc (x := ⟨_,child1⟩) (fun _ => ⟨_,rfl⟩)).alloc (fun _ => ⟨_,rfl⟩)
  exact ⟨⟨⟨h3,Source.HeapTy.Le.refl _⟩,trivial⟩,shaped,inner⟩
def marker : PrimTy.uint.Denote := MemoryClient.marker
def caller : State C [.val .uint] := state.push marker
def callerMachine : Evm.Machine := Evm.Memory.writeMachine machine 1 (.val (Evm.wmod 42))
def callerSource : Source.EMState E [.int .u8] :=
  (.cons (.int 42 (by decide +kernel)) .nil,sourceState.2)
def F : Evm.Frag [.val .uint] := MemoryClient.F
def frame : Source.Fr := MemoryClient.frame

theorem marker_related : Lowering.V07.IntValueRel .u8 (callerSource.1.get .here) marker :=
  MemoryClient.marker_related

theorem caller_word : Evm.Memory.RefArrayStateRepr 1 1 8 F caller base callerMachine :=
  ⟨initial_word.state.consVal marker (.val (Evm.wmod 42))
      ⟨Evm.wmod 42,rfl,by decide +kernel⟩ (by decide +kernel),
    initial_word.arrays.localWrite 1 (by decide +kernel) _⟩

theorem caller_source : SourceBoolRefsAt callerSource 2 caller.heap r address :=
  initial_source.same_heaps rfl rfl

theorem caller_memOK : Source.MemOK E heap3.ty callerSource :=
  ⟨⟨initial_memOK.1.1,⟨trivial,trivial⟩⟩,initial_memOK.2⟩

theorem other_source : SourceBoolMemoryAt callerSource (address other.id) caller.heap other .dyn := by
  apply caller_source.children
  change other ∈ MObj.elems .dyn (hp.get r)
  rw [parent_elems]
  exact List.mem_cons_of_mem _ (List.mem_cons_self ..)

theorem separation : ∀ t ∈ MObj.elems .dyn (caller.heap.get r),
    t.id≠other.id → address t.id≠address other.id := by
  intro t _ hn
  exact hn

/-- The separation premise is exercised by a real distinct selected child. -/
theorem separation_nonvacuous : q ∈ MObj.elems .dyn (caller.heap.get r) ∧
    q.id≠other.id ∧ address q.id≠address other.id := by
  constructor
  · change q ∈ MObj.elems .dyn (hp.get r)
    rw [parent_elems]
    exact List.mem_cons_self ..
  · exact ⟨by decide +kernel,by decide +kernel⟩

def midHeap : Heap H := hp.set r (MObj.setElem .dyn (hp.get r) 2 other)
def outHeap : Heap H := midHeap.set other (MObj.setElem .dyn (midHeap.get other) 0 false)
def midSource : Source.EMState E [.int .u8] :=
  (callerSource.1,{callerSource.2 with heap := heap3.write 2 (sourceBoolRefMemory address [q,other,other]) rfl})
def outSource : Source.EMState E [.int .u8] :=
  (midSource.1,{midSource.2 with heap := midSource.2.heap.write 1 (sourceBoolMemory [false,false]) rfl})
def midMachine : Evm.Machine := Evm.Memory.writeMachine callerMachine 35 (.val (base other.id))
def outMachine : Evm.Machine := Evm.Memory.writeMachine midMachine 25 (.val (Evm.bword false))

theorem source_rebind :
    (Source.writeLoc (E := E) (Γ := [.int .u8]) frame 0
      (.mem (τ := .array .memory .bool none) 2 2) (.memRef rfl 1)).run callerSource=(.ok (),midSource) := by
  obtain ⟨ht,hs⟩ := source_refs_write callerSource 2 address [q,other,q] rfl 2 (by decide +kernel) other
  exact hs

theorem source_mutate :
    (Source.writeLoc (E := E) (Γ := [.int .u8]) frame 0
      (.mem 1 0) (.bool false)).run midSource=(.ok (),outSource) := by
  obtain ⟨ht,hs⟩ := source_bool_write midSource 1 [true,false] rfl 0 (by decide +kernel) false
  exact hs

theorem actual_sequence :
    (Source.writeLoc (E := E) (Γ := [.int .u8]) frame 0
      (.mem (τ := .array .memory .bool none) 2 2) (.memRef rfl 1)).run callerSource=(.ok (),midSource) ∧
    (Source.writeLoc (E := E) (Γ := [.int .u8]) frame 0
      (.mem 1 0) (.bool false)).run midSource=(.ok (),outSource) ∧
    Evm.run (Evm.Memory.writeArrayCode (base r.id))
      ((callerMachine.push (.val (base other.id))).push (.val (Evm.wmod 2)))=.ok midMachine 0 ∧
    Evm.run (Evm.Memory.writeArrayCode (base other.id))
      ((midMachine.push (.val (Evm.bword false))).push (.val (Evm.wmod 0)))=.ok outMachine 0 ∧
    SourceBoolRefsAt outSource 2 outHeap r address ∧ Source.MemOK E heap3.ty outSource ∧
    Evm.Memory.RefArrayStateRepr 1 1 8 F (caller.withHeap outHeap) base outMachine ∧
    outHeap.get q=hp.get q := by
  obtain ⟨mid,out,z,w,ht,ht₂,hs,hs₂,hw,hw₂,hr,hm,hmw,_,_,_,hother,_⟩ :=
    rebind_then_mutate caller r address caller_source other other_source separation frame 0
      (Evm.wmod 2) (Evm.wmod 0) false (by decide +kernel) (by decide +kernel) heap3.ty caller_memOK caller_word
  have hmid : mid=midHeap := by
    have hk : caller.heap.writeAddr (.index r .dyn (Evm.Memory.indexValue (Evm.wmod 2))) other=some midHeap := by
      simp only [Heap.writeAddr,Heap.setIndex]
      exact if_pos (by decide +kernel)
    exact Option.some.inj (ht.symm.trans hk)
  subst mid
  have hout : out=outHeap := by
    have hk : midHeap.writeAddr (.index other .dyn (Evm.Memory.indexValue (Evm.wmod 0))) false=some outHeap := by
      simp only [Heap.writeAddr,Heap.setIndex]
      exact if_pos (by decide +kernel)
    exact Option.some.inj (ht₂.symm.trans hk)
  subst out
  have hz : z=midSource := congrArg Prod.snd (hs.symm.trans source_rebind)
  subst z
  have hw' : w=outSource := congrArg Prod.snd (hs₂.symm.trans source_mutate)
  subst w
  exact ⟨source_rebind,source_mutate,hw,hw₂,hr,hm,hmw,hother q (by decide +kernel)⟩

def cells : List Nat := [1,16,17,18,24,25,26,32,33,34,35]
def observe (m : Evm.Machine) : List Evm.Word := cells.map m.mem

theorem complete_observers : observe outMachine=
    [.val (Evm.wmod 42),.val (Evm.wmod 2),.val (Evm.wmod 0),.val (Evm.wmod 0),
     .val (Evm.wmod 2),.val (Evm.wmod 0),.val (Evm.wmod 0),.val (Evm.wmod 3),
     .val (Evm.wmod 16),.val (Evm.wmod 24),.val (Evm.wmod 24)] ∧
    outMachine.stack=[.val (Evm.wmod 77)] ∧ outSource.1.get .here=.int 42 (by decide +kernel) := by
  exact ⟨by decide +kernel,rfl,rfl⟩

/-- The escaped reference at the UPDATED slot is the old distinct child1,
not child0 or the parent. Both actual read machines use the final state. -/
theorem escaped_other :
    (Source.readLoc (E := E) (Γ := [.int .u8]) frame (τ := .array .memory .bool none)
      (.mem 2 2)).run outSource=(.ok (.memRef rfl 1),outSource) ∧
    (Source.readLoc (E := E) (Γ := [.int .u8]) frame (τ := .bool)
      (.mem 1 0)).run outSource=(.ok (.bool false),outSource) ∧
    Evm.run (Evm.Memory.readArrayCode (base r.id)) (outMachine.push (.val (Evm.wmod 2)))=
      .ok (outMachine.push (.val (base other.id))) 0 ∧
    Evm.run (Evm.Memory.readArrayCode (base other.id)) (outMachine.push (.val (Evm.wmod 0)))=
      .ok (outMachine.push (.val (Evm.bword false))) 0 := by
  have hr := actual_sequence.2.2.2.2.1
  have hw := actual_sequence.2.2.2.2.2.2.1
  have hparent : outHeap.index r .dyn (Evm.Memory.indexValue (Evm.wmod 2))=some other := by
    unfold Heap.index outHeap
    rw [Heap.get_set_ne midHeap other r (by decide +kernel)]
    unfold midHeap
    rw [Heap.get_set_same,MObj.elems_setElem,parent_elems]
    rfl
  have hc : outHeap.index other .dyn (Evm.Memory.indexValue (Evm.wmod 0))=some false := by
    unfold Heap.index outHeap
    rw [Heap.get_set_same,MObj.elems_setElem]
    unfold midHeap
    rw [Heap.get_set_ne hp r other (by decide +kernel),other_elems]
    rfl
  have obs := hr.word_observe hw frame (Evm.wmod 2) (Evm.wmod 0) other false hparent hc
  exact ⟨obs.1,obs.2.1,obs.2.2.2.2.1,obs.2.2.2.2.2⟩

theorem out_parent_elems : MObj.elems .dyn (outHeap.get r)=[q,other,other] := by
  unfold outHeap
  rw [Heap.get_set_ne midHeap other r (by decide +kernel)]
  unfold midHeap
  rw [Heap.get_set_same,MObj.elems_setElem,parent_elems]
  rfl

/-- The genuinely distinct unmodified child keeps both its Source observation
and the old pointer in the first slot, through the reached consumer result. -/
theorem retained_first_child :
    (Source.readLoc (E := E) (Γ := [.int .u8]) frame (τ := .array .memory .bool none)
      (.mem 2 0)).run outSource=(.ok (.memRef rfl 0),outSource) ∧
    (Source.readLoc (E := E) (Γ := [.int .u8]) frame (τ := .bool)
      (.mem 0 0)).run outSource=(.ok (.bool false),outSource) ∧
    Evm.run (Evm.Memory.readArrayCode (base q.id)) (outMachine.push (.val (Evm.wmod 0)))=
      .ok (outMachine.push (.val (Evm.bword false))) 0 := by
  have hr := actual_sequence.2.2.2.2.1
  have hw := actual_sequence.2.2.2.2.2.2.1
  have hq := actual_sequence.2.2.2.2.2.2.2
  have ha : outHeap.index r .dyn (Evm.Memory.indexValue (Evm.wmod 0))=some q := by
    unfold Heap.index
    rw [out_parent_elems]
    rfl
  have hv : outHeap.index q .dyn (Evm.Memory.indexValue (Evm.wmod 0))=some false := by
    unfold Heap.index
    rw [hq,q_elems]
    rfl
  have obs := hr.word_observe hw frame (Evm.wmod 0) (Evm.wmod 0) q false ha hv
  exact ⟨obs.1,obs.2.1,obs.2.2.2.2.2⟩

end Solidity.Backend.Aggregates.DistinctClient
