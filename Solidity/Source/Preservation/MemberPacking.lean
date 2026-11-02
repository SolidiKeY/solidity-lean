import Solidity.Source.Preservation.AllocationSites

/-! Actual struct member packing and allocation. The original member count and
member type checks are retained, and only agreeing bare values are admitted.
-/
namespace Solidity.Source.Preservation
open EM
variable {E : Env} {Γ : RCtx}

theorem fieldsOf_pres : ∀ {ps : List STy} (vs : Vals E.layout ps) (ts : List STy)
    (P : EMState E Γ → Prop),
    Hoare (fun y => P y ∧ RValsOK E y.2.heap.ty vs.toR)
      (fieldsOf vs ts : EM E Γ (DataList E.layout ts))
      (fun fs y => P y ∧ DataListOK E y.2.heap.ty fs ∧ fs.AllVal)
      (fun _ y => P y) := by
  intro ps vs
  induction vs with
  | nil =>
    intro ts P
    cases ts with
    | nil => exact Hoare.pure' fun _ h => ⟨h.1, .nil, trivial⟩
    | cons t ts => exact Hoare.halt' fun _ h => h.1
  | @cons t ts v vs ih =>
    intro us P
    cases us with
    | nil => exact Hoare.halt' fun _ h => h.1
    | cons u us =>
      simp only [fieldsOf]
      split
      next he =>
        subst u
        have ht : Hoare (fun y => P y ∧ RValsOK E y.2.heap.ty (Vals.cons v vs).toR)
            (fieldsOf vs us : EM E Γ _)
            (fun fs y => P y ∧ v.RefOK E y.2.heap.ty ∧ DataListOK E y.2.heap.ty fs ∧ fs.AllVal)
            (fun _ y => P y) :=
          Hoare.conseq (ih us (fun y => P y ∧ v.RefOK E y.2.heap.ty))
            (fun _ h => ⟨⟨h.1, h.2.1⟩, h.2.2⟩)
            (fun _ _ h => ⟨h.1.1, h.1.2, h.2⟩) (fun _ _ h => h.1)
        exact Hoare.bind ht fun fs => Hoare.pure' fun _ h =>
          ⟨h.1, .cons (.val h.2.1) h.2.2.1, ⟨⟨v, rfl⟩, h.2.2.2⟩⟩
      next he => exact Hoare.halt' fun _ h => h.1

theorem structAlloc_mem {H : HeapTy} {ps : List STy} (vs : Vals E.layout ps) (dn : DeclName) :
    Hoare (fun y => MemOK E H y ∧ RValsOK E y.2.heap.ty vs.toR)
      (do let fs ← fieldsOf vs (E.layout.fields dn)
          allocRef (Data.struct (l := .memory) (d := dn) fs) : EM E Γ _)
      (fun v y => MemOK E H y ∧ v.RefOK E y.2.heap.ty) (fun _ y => MemOK E H y) := by
  refine Hoare.bind (fieldsOf_pres vs _ (MemOK E H)) fun fs => ?_
  intro y h
  exact (allocRef_mem (Data.struct (l := .memory) (d := dn) fs) rfl trivial h.2.2) y ⟨h.1, .struct h.2.1⟩

theorem evalE_structNew_mem (G : Glob E) (F : Fr) (n : Nat) {H : HeapTy}
    {dn : DeclName} {ps : List STy}
    (hs : (E.structFields dn .memory).map (·.map Prod.snd) = some ps)
    (args : RConvArgs E Γ ps)
    (ha : Hoare (MemOK E H) (evalConvArgs G F n args)
      (fun vs y => MemOK E H y ∧ RValsOK E y.2.heap.ty vs.toR) (fun _ y => MemOK E H y)) :
    Hoare (MemOK E H) (evalE G F (n + 1) (.structNew hs args))
      (fun v y => MemOK E H y ∧ RValOK E y.2.heap.ty v) (fun _ y => MemOK E H y) := by
  simp only [evalE]
  refine Hoare.bind ha fun vs => Hoare.bind (fieldsOf_pres vs _ (MemOK E H)) fun fs => ?_
  intro y h
  exact (Hoare.bind (allocRef_mem (Data.struct (l := .memory) (d := dn) fs) rfl trivial h.2.2)
    (fun v => Hoare.pure' (a := RVal.val v)
      (Q := fun w y => MemOK E H y ∧ RValOK E y.2.heap.ty w)
      (X := fun _ y => MemOK E H y) (fun _ h => h))) y ⟨h.1, .struct h.2.1⟩

#print axioms fieldsOf_pres
#print axioms structAlloc_mem
#print axioms evalE_structNew_mem
end Solidity.Source.Preservation
