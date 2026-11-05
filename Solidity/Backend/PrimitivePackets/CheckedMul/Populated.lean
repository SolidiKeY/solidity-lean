import Solidity.Evm.MemoryCompile

/-! Inhabited populated memory fixture with two aliases and an independent array.
Only expression compiler imports are needed; no statement correctness import. -/
namespace Solidity.Backend.PrimitivePackets.CheckedMul.Populated
open Evm Evm.Memory
def C : Contract := contract!{ }
def H : HTy := [.array (.prim .uint), .array (.prim .uint)]
def r0 : HRef H (.array (.prim .uint)) := ⟨0, rfl⟩
def r1 : HRef H (.array (.prim .uint)) := ⟨1, rfl⟩
def base (id : Nat) : Fin W := if id = 0 then ⟨16, by decide⟩ else ⟨20, by decide⟩
def uint (n : Nat) (h : n < W) : PrimTy.uint.Denote := indexValue ⟨n, h⟩
def hp : Heap H :=
  (⟨[uint 7 (by decide), uint 9 (by decide)], by decide⟩,
    ⟨[uint 4 (by decide)], by decide⟩, ())
def Γ : Ctx := [.val .uint, .mem (.array (.prim .uint)),
  .mem (.array (.prim .uint)), .mem (.array (.prim .uint))]
def σ : State C Γ :=
  { storage := Storage.init C, H := H, heap := hp,
    env := (uint 0 W_pos, some r0, some r0, some r1, ()) }
def machine : Machine :=
  { Machine.init with mem := fun a =>
    if a = 0 then w[20] else if a = 1 then w[16] else if a = 2 then w[16]
    else if a = 16 then w[2] else if a = 17 then w[7] else if a = 18 then w[9]
    else if a = 20 then w[1] else if a = 21 then w[4] else w[0] }

theorem array0_repr : ArrayRepr hp r0 (base 0) machine := by
  constructor
  · change 16 + 1 + hp.len r0 .dyn ≤ W
    simp only [Heap.len, hp, r0, H, Heap.get, Objs.get, MObj.elems_dyn,
      List.length_cons, List.length_nil]
    decide +kernel
  · change machine.mem 16 = .val (wmod (hp.len r0 .dyn))
    simp only [Heap.len, hp, r0, H, Heap.get, Objs.get, MObj.elems_dyn,
      List.length_cons, List.length_nil]
    rfl
  · intro i v hv
    simp only [hp, r0, H, Heap.get, Objs.get, MObj.elems_dyn] at hv
    cases i with
    | zero => cases hv; exact ⟨⟨7, by decide⟩, rfl, rfl⟩
    | succ i =>
      cases i with
      | zero => cases hv; exact ⟨⟨9, by decide⟩, rfl, rfl⟩
      | succ i => cases hv

theorem array1_repr : ArrayRepr hp r1 (base 1) machine := by
  constructor
  · change 20 + 1 + hp.len r1 .dyn ≤ W
    simp only [Heap.len, hp, r1, H, Heap.get, Objs.get, MObj.elems_dyn,
      List.length_cons, List.length_nil]
    decide +kernel
  · simp only [Heap.len, hp, r1, H, Heap.get, Objs.get, MObj.elems_dyn,
      List.length_cons, List.length_nil]
    rfl
  · intro i v hv
    simp only [hp, r1, H, Heap.get, Objs.get, MObj.elems_dyn] at hv
    cases i with
    | zero => cases hv; exact ⟨⟨4, by decide⟩, rfl, rfl⟩
    | succ i => cases hv

private theorem ref_cases {p : PrimTy} (r : HRef H (.array (.prim p))) :
    p = .uint ∧ (HEq r r0 ∨ HEq r r1) := by
  rcases r with ⟨i, hi⟩
  cases i with
  | zero => cases hi; exact ⟨rfl, .inl HEq.rfl⟩
  | succ i =>
    cases i with
    | zero => cases hi; exact ⟨rfl, .inr HEq.rfl⟩
    | succ i => cases hi

theorem heap_repr : HeapRepr hp base 4 machine := by
  constructor
  · intro p r
    rcases ref_cases r with ⟨rfl, hr | hr⟩ <;> cases hr
    · exact array0_repr
    · exact array1_repr
  · intro p r
    rcases ref_cases r with ⟨rfl, hr | hr⟩ <;> cases hr <;> decide +kernel
  · intro p q r s hne
    rcases ref_cases r with ⟨rfl, hr | hr⟩ <;> cases hr <;>
      rcases ref_cases s with ⟨rfl, hs | hs⟩ <;> cases hs
    · exact False.elim (hne rfl)
    · exact .inl (by decide +kernel)
    · exact .inr (by decide +kernel)
    · exact False.elim (hne rfl)

private theorem noStructs {s : Name} (r : HRef H (.struct s)) : False := by
  rcases r with ⟨i, hi⟩
  cases i with
  | zero => cases hi
  | succ i => cases i with
    | zero => cases hi
    | succ i => cases hi

theorem fixture_repr : StateRepr 1 0 4 (Frag.init Γ) σ base machine := by
  have hc : Sim C 1 0 (Frag.init []) ({storage:=Storage.init C,H:=[],heap:=Heap.empty,env:=()} : State C [])
      (Machine.init (fun _=>0) ⟨0,W_pos⟩) :=
    ⟨initStorage_repr C Nat.one_pos,(fun i=>nomatch i),(fun i=>nomatch i),
      (fun _ _=>by simp only [netAt,Machine.init,Int.sub_self];rfl),
      rfl,(by unfold Lmax;decide),(fun i=>nomatch i),⟨rfl,rfl,rfl,rfl⟩,
      rfl,(fun _ _ _ _ _ _=>rfl)⟩
  constructor
  · refine ⟨hc.store, ?_, ?_, hc.net, hc.netSelf, hc.bound, ?_, hc.env, hc.funds, hc.oracle⟩
    · intro p i
      cases i with
      | here => exact ⟨⟨0, W_pos⟩, rfl, rfl⟩
      | there i => cases i with | there i => cases i with | there i => cases i with | there i => nomatch i
    · intro R i
      cases i with | there i => cases i with | there i => cases i with | there i => cases i with | there i => nomatch i
    · intro R i
      cases i with | there i => cases i with | there i => cases i with | there i => cases i with | there i => nomatch i
  · exact heap_repr
  · intro p i
    cases i with
    | there i =>
      cases i with
      | here => exact ⟨r0, rfl, rfl⟩
      | there i =>
        cases i with
        | here => exact ⟨r0, rfl, rfl⟩
        | there i =>
          cases i with
          | here => exact ⟨r1, rfl, rfl⟩
          | there i => nomatch i
  · exact Nat.le_refl _
  · exact ⟨fun r => (noStructs r).elim, fun r => (noStructs r).elim, fun r => (noStructs r).elim⟩
  · exact fun _ r => (noStructs r).elim
  · exact RefFieldsRepr.withoutStructs _ _ _ (fun r => noStructs r)


#print axioms array0_repr
#print axioms array1_repr
#print axioms ref_cases
#print axioms heap_repr
#print axioms noStructs
#print axioms fixture_repr
end Solidity.Backend.PrimitivePackets.CheckedMul.Populated
