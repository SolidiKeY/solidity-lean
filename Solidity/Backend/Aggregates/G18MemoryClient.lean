import Solidity.Backend.Aggregates.G18Memory
import Solidity.Backend.Aggregates.G18GraphRootControls
import Solidity.Source.Semantics
import Solidity.Evm.Correct

/-! A real nonempty initial source/intrinsic/word client for G18.03.
Both parent elements alias the same child. No source admission or physical
byte-EVM theorem is inferred from these scoped initial representations. -/
namespace Solidity.Backend.Aggregates.MemoryClient
open MemoryOps

def C : Contract := { vars := [] }
def child : RefTy := .array (.prim .bool)
def parent : RefTy := BoolRefsRef
def H : HTy := [child, parent]
def q : HRef H child := ⟨0, rfl⟩
def r : HRef H parent := ⟨1, rfl⟩
def hp : Heap H := (⟨[false, false], by decide +kernel⟩, (⟨[q, q], by decide +kernel⟩, ()))
def state : State C [] := { State.init C with H := H, heap := hp }
def base (id : Nat) : Fin Evm.W := Evm.wmod (if id = 0 then 16 else 24)
def machine : Evm.Machine := { Evm.Machine.init with
  stack := [.val (Evm.wmod 77)]
  mem := fun a => if a = 16 then .val (Evm.wmod 2)
    else if a = 24 then .val (Evm.wmod 2)
    else if a = 25 ∨ a = 26 then .val (Evm.wmod 16)
    else .val (Evm.wmod 0) }

theorem ref_cases {R : RefTy} (t : HRef H R) :
    (R = child ∧ t.id = 0) ∨ (R = parent ∧ t.id = 1) := by
  rcases t with ⟨i, hi⟩
  match i with
  | 0 => exact .inl ⟨(Option.some.inj hi).symm, rfl⟩
  | 1 => exact .inr ⟨(Option.some.inj hi).symm, rfl⟩
  | i+2 => simp only [H, List.getElem?_cons_succ, List.getElem?_nil] at hi
           cases hi

theorem primitive_info {p : PrimTy} (t : HRef H (.array (.prim p))) : p = .bool ∧ t.id = 0 := by
  obtain ⟨ht, hi⟩ | ⟨ht, hi⟩ := ref_cases t
  · exact ⟨Ty.prim.inj (RefTy.array.inj ht), hi⟩
  · cases RefTy.array.inj ht

theorem reference_info {R : RefTy} (t : HRef H (.array (.ref R))) : R = child ∧ t.id = 1 := by
  obtain ⟨ht, hi⟩ | ⟨ht, hi⟩ := ref_cases t
  · cases RefTy.array.inj ht
  · exact ⟨Ty.ref.inj (RefTy.array.inj ht), hi⟩

theorem no_struct {s : Name} (t : HRef H (.struct s)) : False := by
  obtain ⟨ht, _⟩ | ⟨ht, _⟩ := ref_cases t <;> cases ht

theorem child_elems : MObj.elems .dyn (hp.get q) = [false, false] := by
  simp only [MObj.elems_dyn, Heap.get, H, hp, q, Objs.get]

theorem parent_elems : MObj.elems .dyn (hp.get r) = [q, q] := by
  simp only [MObj.elems_dyn, Heap.get, H, hp, r, Objs.get]

theorem primitive_repr : Evm.Memory.ArrayRepr hp q (base 0) machine := by
  refine ⟨by decide +kernel, by decide +kernel, ?_⟩
  intro i v hv
  rw [child_elems] at hv
  match i with
  | 0 => cases hv; rfl
  | 1 => cases hv; rfl
  | i+2 => cases hv

theorem parent_repr : Evm.Memory.RefArrayRepr hp r base machine := by
  refine ⟨by decide +kernel, by decide +kernel, ?_⟩
  intro i v hv
  rw [parent_elems] at hv
  match i with
  | 0 => cases hv; rfl
  | 1 => cases hv; rfl
  | i+2 => cases hv

theorem initial_word : Evm.Memory.RefArrayStateRepr 1 1 8 (Evm.Frag.init []) state base machine := by
  have hc := Evm.Sim.init C 0 Evm.W_pos (fun _ => 0) ⟨0, Evm.W_pos⟩ rfl
  have hprim : Evm.Memory.HeapRepr hp base 8 machine := by
    refine ⟨?_, ?_, ?_⟩
    · intro p t
      obtain ⟨he, hi⟩ := primitive_info t
      subst p
      have heq : t = q := eq_of_heq (HRef.heq_of_id t q hi).2
      subst t
      exact primitive_repr
    · intro p t
      obtain ⟨he, hi⟩ := primitive_info t
      rw [hi]
      decide
    · intro p p' t u hne
      exact (hne ((primitive_info t).2.trans (primitive_info u).2.symm)).elim
  have hstate : Evm.Memory.StateRepr 1 1 8 (Evm.Frag.init []) state base machine := by
    refine ⟨⟨hc.store, ?_, ?_, hc.net, hc.netSelf, hc.bound, ?_, hc.env, hc.funds, hc.oracle⟩,
      hprim, ?_, by decide +kernel, ⟨?_, ?_, ?_⟩, ?_, ?_⟩
    · intro p i; nomatch i
    · intro R i; nomatch i
    · intro R i; nomatch i
    · intro R i; nomatch i
    · intro s t; exact (no_struct t).elim
    · intro s t; exact (no_struct t).elim
    · intro s s' t u _; exact (no_struct t).elim
    · intro p s t u; exact (no_struct u).elim
    · exact Evm.Memory.RefFieldsRepr.withoutStructs hp base machine no_struct
  refine ⟨hstate, ⟨?_, ?_, ?_, ?_, ?_⟩⟩
  · intro R t
    obtain ⟨he, hi⟩ := reference_info t
    subst R
    have heq : t = r := eq_of_heq (HRef.heq_of_id t r hi).2
    subst t
    exact parent_repr
  · intro R t
    rw [(reference_info t).2]
    decide
  · intro R Q t u hne
    exact (hne ((reference_info t).2.trans (reference_info u).2.symm)).elim
  · intro R p t u
    obtain ⟨he, hi⟩ := reference_info t
    obtain ⟨he', hi'⟩ := primitive_info u
    subst R
    subst p
    have ht : t = r := eq_of_heq (HRef.heq_of_id t r hi).2
    have hu : u = q := eq_of_heq (HRef.heq_of_id u q hi').2
    subst t
    subst u
    exact .inr (by decide +kernel)
  · intro R s t u; exact (no_struct u).elim

def E : Source.Env := GraphRootControls.env
def sourceAddress (id : Nat) : Nat := id
def sourceChild : Source.Data E.layout (.array .memory .bool none) := sourceBoolMemory [false, false]
def sourceParent : Source.Data E.layout SourceBoolRefsTy := sourceBoolRefMemory sourceAddress [q, q]
def sourceHeap1 : Source.Heap E.layout := (Source.Heap.empty.alloc ⟨_, sourceChild⟩).1
def sourceHeap : Source.Heap E.layout := (sourceHeap1.alloc ⟨_, sourceParent⟩).1
def sourceState : Source.EMState E [] := (.nil, {Source.St.init E with heap := sourceHeap})

theorem initial_source : SourceBoolRefsAt sourceState 1 hp r sourceAddress := by
  refine ⟨?_, ?_⟩
  · simpa only [MObj.elems_dyn, Heap.get, H, hp, r, Objs.get] using
      (show sourceState.2.heap.get 1 = some ⟨SourceBoolRefsTy, sourceParent⟩ from rfl)
  intro t ht
  rw [parent_elems] at ht
  have he : t = q := by simpa only [List.mem_cons, List.not_mem_nil, or_false, or_self] using ht
  subst t
  unfold SourceBoolMemoryAt
  rw [child_elems]
  exact (show sourceState.2.heap.get 0 = some ⟨.array .memory .bool none, sourceChild⟩ from rfl)

theorem initial_memOK : Source.MemOK E sourceHeap.ty sourceState := by
  have he : Source.HeapOK (E := E) (Source.Heap.empty : Source.Heap E.layout) := by
    intro a x hx; cases hx
  have h1 : Source.HeapOK (E := E) sourceHeap1 := he.alloc (.array (fun _ => .val trivial))
  have h2 : Source.HeapOK (E := E) sourceHeap := by
    apply h1.alloc
    apply Source.DataOK.array
    rintro ⟨i, hi⟩
    match i with
    | 0 => exact .val ⟨_, rfl, rfl⟩
    | 1 => exact .val ⟨_, rfl, rfl⟩
    | i+2 => change i+2 < 2 at hi; omega
  have hs : Source.HeapShaped (E := E) sourceHeap := by
    have h0 : Source.HeapShaped (E := E) (Source.Heap.empty : Source.Heap E.layout) := by
      intro a x hx; cases hx
    exact (h0.alloc (x := ⟨_, sourceChild⟩) trivial).alloc trivial
  have hin : Source.HeapInner (E := E) sourceHeap := by
    have h0 : Source.HeapInner (E := E) (Source.Heap.empty : Source.Heap E.layout) := by
      intro a x hx; cases hx
    exact (h0.alloc (x := ⟨_, sourceChild⟩) (fun _ => ⟨_, rfl⟩)).alloc (fun _ => ⟨_, rfl⟩)
  exact ⟨⟨⟨h2, Source.HeapTy.Le.refl _⟩, trivial⟩, hs, hin⟩

#print axioms initial_word
#print axioms initial_source
#print axioms initial_memOK

/-- A populated caller on both sides; the narrow source value is the existing
V07 integer embedding, not a guessed word observation. -/
def marker : PrimTy.uint.Denote := ⟨42, by decide +kernel⟩
def caller : State C [.val .uint] := state.push marker
def callerMachine : Evm.Machine := Evm.Memory.writeMachine machine 1 (.val (Evm.wmod 42))
def callerSource : Source.EMState E [.int .u8] :=
  (.cons (.int 42 (by decide +kernel)) .nil, sourceState.2)
def F : Evm.Frag [.val .uint] := (Evm.Frag.init []).push (.val .uint) .ok

theorem marker_related : Lowering.V07.IntValueRel .u8
    (callerSource.1.get .here) marker :=
  Lowering.V07.integer_related .u8 42 (by decide +kernel)

theorem caller_word : Evm.Memory.RefArrayStateRepr 1 1 8 F caller base callerMachine :=
  ⟨initial_word.state.consVal marker (.val (Evm.wmod 42)) ⟨Evm.wmod 42, rfl, by decide +kernel⟩ (by decide +kernel),
    initial_word.arrays.localWrite 1 (by decide +kernel) _⟩

theorem caller_source : SourceBoolRefsAt callerSource 1 caller.heap r sourceAddress :=
  initial_source.same_heaps rfl rfl

theorem caller_memOK : Source.MemOK E sourceHeap.ty callerSource :=
  ⟨⟨initial_memOK.1.1, ⟨trivial, trivial⟩⟩, initial_memOK.2⟩

def frame : Source.Fr := { this := ⟨1, by decide +kernel⟩, sender := ⟨2, by decide +kernel⟩, value := ⟨0, by decide +kernel⟩, static := false, contract := "Cell" }
def zero : Fin Evm.W := Evm.wmod 0
def one : Fin Evm.W := Evm.wmod 1
def updatedHeap : Heap H := hp.set q (MObj.setElem .dyn (hp.get q) 0 true)
def afterMachine : Evm.Machine := Evm.Memory.writeMachine callerMachine
  ((base q.id).val+1+zero.val) (.val (Evm.bword true))
def sourceAfter : Source.EMState E [.int .u8] :=
  (callerSource.1, {callerSource.2 with heap := sourceHeap.write 0 (sourceBoolMemory [true, false]) rfl})
def output : Evm.Out := Evm.run (Evm.Memory.writeArrayCode (base q.id))
  ((callerMachine.push (.val (Evm.bword true))).push (.val zero))
def observations (m : Evm.Machine) : List Evm.Word :=
  [m.mem 1, m.mem 16, m.mem 17, m.mem 18, m.mem 24, m.mem 25, m.mem 26]

theorem source_after_run :
    (Source.writeLoc (E := E) (Γ := [.int .u8]) frame 0 (.mem 0 0) (.bool true)).run callerSource =
      (.ok (), sourceAfter) := by
  obtain ⟨ht, hs⟩ := source_bool_write callerSource 0 [false, false] rfl 0 (by decide +kernel) true
  exact hs

/-- The NEW transport theorem is actually instantiated with all its initial
premises discharged. Exact complete target state and complete Source result are
retained alongside both parent aliases and the actual reached representation. -/
theorem actual_client :
    (Source.writeLoc (E := E) (Γ := [.int .u8]) frame 0 (.mem 0 0) (.bool true)).run callerSource =
      (.ok (), sourceAfter) ∧
    output = .ok afterMachine 0 ∧
    SourceBoolRefsAt sourceAfter 1 updatedHeap r sourceAddress ∧
    Source.MemOK E sourceHeap.ty sourceAfter ∧
    Evm.Memory.RefArrayStateRepr 1 1 8 F (caller.withHeap updatedHeap) base afterMachine ∧
    sourceAfter.1.get .here = .int 42 (by decide +kernel) ∧
    (Source.readLoc (E := E) (Γ := [.int .u8]) frame
      (τ := .array .memory .bool none) (.mem 1 0)).run sourceAfter = (.ok (.memRef rfl 0), sourceAfter) ∧
    (Source.readLoc (E := E) (Γ := [.int .u8]) frame
      (τ := .array .memory .bool none) (.mem 1 1)).run sourceAfter = (.ok (.memRef rfl 0), sourceAfter) ∧
    (Source.readLoc (E := E) (Γ := [.int .u8]) frame (τ := .bool) (.mem 0 0)).run sourceAfter =
      (.ok (.bool true), sourceAfter) ∧
    Evm.run (Evm.Memory.readArrayCode (base q.id)) (afterMachine.push (.val zero)) =
      .ok (afterMachine.push (.val (Evm.bword true))) 0 := by
  have hq : q ∈ MObj.elems .dyn (caller.heap.get r) := by
    simp only [caller, State.push, state, parent_elems, List.mem_cons, List.not_mem_nil, or_false, or_self]
  have hsep : ∀ t ∈ MObj.elems .dyn (caller.heap.get r), t.id ≠ q.id → sourceAddress t.id ≠ sourceAddress q.id := by
    intro t ht hn
    change t ∈ MObj.elems .dyn (hp.get r) at ht
    rw [parent_elems] at ht
    have he : t = q := by simpa only [List.mem_cons, List.not_mem_nil, or_false, or_self] using ht
    subst t
    exact (hn rfl).elim
  obtain ⟨out, z, ho, hs, hc, hr, hm, hw, hl, hp', obs⟩ := nested_write_observe caller r sourceAddress
    caller_source q hq hsep frame 0 zero true (by decide +kernel) sourceHeap.ty caller_memOK caller_word
  have hh : caller.heap.writeAddr (.index q .dyn (Evm.Memory.indexValue zero)) true = some updatedHeap := by
    simp only [Heap.writeAddr, Heap.setIndex]
    exact if_pos (by decide +kernel)
  have hout : out = updatedHeap := Option.some.inj (ho.symm.trans hh)
  subst out
  have hz : z = sourceAfter := congrArg Prod.snd (hs.symm.trans source_after_run)
  subst z
  have hparent0 : updatedHeap.index r .dyn (Evm.Memory.indexValue zero) = some q := by
    simp only [Heap.index, hp', caller, State.push, state, parent_elems]
    rfl
  have hparent1 : updatedHeap.index r .dyn (Evm.Memory.indexValue one) = some q := by
    simp only [Heap.index, hp', caller, State.push, state, parent_elems]
    rfl
  have hchild : updatedHeap.index q .dyn (Evm.Memory.indexValue zero) = some true := by
    simp only [updatedHeap, Heap.index, Heap.get_set_same, MObj.elems_setElem, child_elems]
    rfl
  have o0 := hr.word_observe hw frame zero zero q true hparent0 hchild
  have o1 := hr.word_observe hw frame one zero q true hparent1 hchild
  exact ⟨source_after_run, hc, hr, hm, hw, rfl, o0.1, o1.1, o0.2.1, o0.2.2.2.2.2⟩

theorem complete_word_observations : observations afterMachine =
    [.val (Evm.wmod 42), .val (Evm.wmod 2), .val (Evm.bword true), .val (Evm.bword false),
      .val (Evm.wmod 2), .val (Evm.wmod 16), .val (Evm.wmod 16)] ∧
    afterMachine.stack = [.val (Evm.wmod 77)] := by decide +kernel

#print axioms caller_word
#print axioms marker_related
#print axioms actual_client
#print axioms complete_word_observations

def cellOfResult (address : Nat) : Evm.Out → Option Evm.Word
  | .ok m _ => some (m.mem address)
  | _ => none

theorem wrong_value : output ≠ .ok (Evm.Memory.writeMachine callerMachine 17 (.val (Evm.wmod 0))) 0 := by
  intro he
  have hx := congrArg (cellOfResult 17) (actual_client.2.1.symm.trans he)
  exact (by decide +kernel : some (.val (Evm.bword true) : Evm.Word) ≠ some (.val (Evm.wmod 0))) hx

/-- Reuses the cell-17 observation of `wrong_value`; cell 25 itself is not checked. -/
theorem wrong_alias_address : output ≠ .ok (Evm.Memory.writeMachine callerMachine 25 (.val (Evm.bword true))) 0 := by
  intro he
  have hx := congrArg (cellOfResult 17) (actual_client.2.1.symm.trans he)
  exact (by decide +kernel : some (.val (Evm.bword true) : Evm.Word) ≠ some (.val (Evm.wmod 0))) hx

theorem wrong_stack_tail : output ≠ .ok {afterMachine with stack := [.val (Evm.wmod 78)]} 0 := by
  intro he
  have hx := congrArg (fun x : Evm.Out => match x with | .ok m _ => some m.stack | _ => none)
    (actual_client.2.1.symm.trans he)
  exact (by decide +kernel : some ([.val (Evm.wmod 77)] : List Evm.Word) ≠ some ([.val (Evm.wmod 78)] : List Evm.Word)) hx

theorem not_revert : output ≠ .revert := by
  rw [actual_client.2.1]
  intro he
  cases he

theorem wrong_frame : ¬ Evm.Memory.RefArrayStateRepr 1 1 20 F caller base callerMachine := by
  intro h
  have hb := h.state.heap.above q
  exact (by decide +kernel : ¬ 20 ≤ (base q.id).val) hb

/-- The returned reference is the OLD child, including the second alias. -/
theorem escaped_alias :
    Evm.run (Evm.Memory.readArrayCode (base r.id)) (afterMachine.push (.val one)) =
      .ok (afterMachine.push (.val (base q.id))) 0 := by
  have hr := actual_client.2.2.1
  have hw := actual_client.2.2.2.2.1
  have hp' : updatedHeap.get r = hp.get r := Heap.get_set_ne hp q r (by decide +kernel) _
  have hparent : updatedHeap.index r .dyn (Evm.Memory.indexValue one) = some q := by
    simp only [Heap.index, hp', parent_elems]
    rfl
  have hchild : updatedHeap.index q .dyn (Evm.Memory.indexValue zero) = some true := by
    simp only [updatedHeap, Heap.index, Heap.get_set_same, MObj.elems_setElem, child_elems]
    rfl
  exact (hr.word_observe hw frame one zero q true hparent hchild).2.2.2.2.1

theorem wrong_escape :
    Evm.run (Evm.Memory.readArrayCode (base r.id)) (afterMachine.push (.val one)) ≠
      .ok (afterMachine.push (.val (base r.id))) 0 := by
  intro he
  have hx := congrArg (fun x : Evm.Out => match x with | .ok m _ => m.stack.head? | _ => none)
    (escaped_alias.symm.trans he)
  exact (by decide +kernel : some (.val (base q.id) : Evm.Word) ≠ some (.val (base r.id))) hx

theorem source_bad_index :
    (Source.writeLoc (E := E) (Γ := [.int .u8]) frame 0 (.mem 0 2) (.bool true)).run callerSource =
      (.error (.revert (Source.panicData .index)), callerSource) :=
  source_bool_write_bounds callerSource 0 [false, false] rfl 2 (by decide +kernel) true

/-- Exact local word-IR failure. It does not carry the source panic bytes, so
this control is NOT a proof of physical observable failure preservation. -/
theorem target_bad_index :
    Evm.run (Evm.Memory.writeArrayCode (base q.id))
      ((callerMachine.push (.val (Evm.bword true))).push (.val (Evm.wmod 2))) = .revert := by
  have hn : caller.heap.writeAddr (.index q .dyn (Evm.Memory.indexValue (Evm.wmod 2))) true = none := by
    simp only [Heap.writeAddr, Heap.setIndex]
    exact if_neg (by decide +kernel)
  obtain ⟨out, ho, _⟩ | ⟨_, ht⟩ := Evm.Memory.writeArray_correct (caller_word.state.heap.arrays q)
    (Evm.wmod 2) true (.val (Evm.bword true)) rfl
  · rw [hn] at ho
    cases ho
  · exact ht

theorem bad_index_not_timeout :
    (Source.writeLoc (E := E) (Γ := [.int .u8]) frame 0 (.mem 0 2) (.bool true)).run callerSource ≠
      (.error .timeout, callerSource) := by
  rw [source_bad_index]
  intro he
  cases he

theorem wrong_panic_data :
    (Source.writeLoc (E := E) (Γ := [.int .u8]) frame 0 (.mem 0 2) (.bool true)).run callerSource ≠
      (.error (.revert (Source.panicData .arithmetic)), callerSource) := by
  intro he
  have hx := congrArg (fun x : Source.R Unit × Source.EMState E [.int .u8] => match x.1 with
    | .error (.revert bytes) => some bytes | _ => none) (source_bad_index.symm.trans he)
  exact (by decide +kernel : some (Source.panicData .index) ≠ some (Source.panicData .arithmetic)) hx

#print axioms wrong_value
#print axioms wrong_alias_address
#print axioms wrong_stack_tail
#print axioms wrong_frame
#print axioms escaped_alias
#print axioms wrong_escape
#print axioms source_bad_index
#print axioms target_bad_index
#print axioms bad_index_not_timeout
#print axioms wrong_panic_data
end Solidity.Backend.Aggregates.MemoryClient
