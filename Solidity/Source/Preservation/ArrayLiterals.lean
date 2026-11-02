import Solidity.Source.Preservation.AllocationSites

/-! Memory preservation at the existing inline-array literal allocation site.
The one-word element boundary and argument-preservation premise are retained.
-/
namespace Solidity.Source.Preservation
open EM
variable {E : Env} {H : HeapTy}

theorem nthRep_ok {s : STy} : ∀ {m : Nat} (vs : Vals E.layout (List.replicate m s)) (i : Fin m),
    RValsOK E H vs.toR → (vs.nthRep i).RefOK E H
  | 0, _, i, _ => i.elim0
  | m + 1, .cons v vs, ⟨0, hi⟩, h => h.1
  | m + 1, .cons v vs, ⟨j + 1, hi⟩, h => nthRep_ok vs ⟨j, Nat.lt_of_succ_lt_succ hi⟩ h.2

theorem inlineData_ok {s : STy} {m : Nat} (vs : Vals E.layout (List.replicate m s))
    (h : RValsOK E H vs.toR) : DataOK E H (inlineData vs) :=
  .array fun i => .val (nthRep_ok vs i h)

theorem evalE_inlineArray_mem {Γ : RCtx} (G : Glob E) (F : Fr) (n : Nat) {H : HeapTy}
    {s : STy} {m : Nat} (args : RConvArgs E Γ (List.replicate m s)) (hs : s.oneWord = true)
    (ha : Hoare (MemOK E H) (evalConvArgs G F n args)
      (fun vs y => MemOK E H y ∧ RValsOK E y.2.heap.ty vs.toR) (fun _ y => MemOK E H y)) :
    Hoare (MemOK E H) (evalE G F (n + 1) (.inlineArray args hs))
      (fun v y => MemOK E H y ∧ RValOK E y.2.heap.ty v) (fun _ y => MemOK E H y) := by
  simp only [evalE]
  refine Hoare.bind ha fun vs => ?_
  intro y h
  exact (Hoare.bind (allocRef_mem (inlineData vs) rfl trivial (fun i => ⟨_, rfl⟩))
    (fun v => Hoare.pure' (a := RVal.val v)
      (Q := fun w y => MemOK E H y ∧ RValOK E y.2.heap.ty w)
      (X := fun _ y => MemOK E H y) (fun _ h => h))) y ⟨h.1, inlineData_ok vs h.2⟩

#print axioms evalE_inlineArray_mem
end Solidity.Source.Preservation
