import Solidity.Source.Preservation.AllocationSites

/-! Preservation through the real ABI encoder, including storage-byte reads.
This proves memory preservation, not absence of the encoder's named refusals.
-/
namespace Solidity.Source.Preservation
open EM
variable {E : Env} {Γ : RCtx}

theorem heapBytes_keep {P : EMState E Γ → Prop} (a : Nat) :
    Hoare P (heapBytes a) (fun _ y => P y) (fun _ y => P y) := by
  unfold heapBytes
  refine Hoare.bind (heapObj_get (a := a) fun y h _ => h) fun ⟨t, d⟩ => ?_
  cases d <;> first
    | exact Hoare.pure' fun _ h => h.1
    | exact Hoare.halt' fun _ h => h.1

theorem bytesOfRV_mem {H : HeapTy} (F : Fr) (n : Nat) {t : STy} (v : RVal E.layout t) :
    Hoare (MemOK E H) (bytesOfRV F n v : EM E Γ _)
      (fun _ y => MemOK E H y) (fun _ y => MemOK E H y) := by
  unfold bytesOfRV
  split
  · exact Hoare.pure' fun _ h => h
  · exact heapBytes_keep _
  · refine Hoare.bind ((loadOK F n).mem H _ _) fun d => ?_
    cases d <;> first
      | exact Hoare.pure' fun _ h => h.1
      | exact Hoare.halt' fun _ h => h.1
  · exact Hoare.pure' fun _ h => h
  · exact Hoare.halt' fun _ h => h

theorem encodeOne_mem {H : HeapTy} (F : Fr) (n : Nat) (packed : Bool)
    {t : STy} (v : RVal E.layout t) :
    Hoare (MemOK E H) (encodeOne F n packed v : EM E Γ _)
      (fun _ y => MemOK E H y) (fun _ y => MemOK E H y) := by
  unfold encodeOne
  split
  · split <;> exact Hoare.pure' fun _ h => h
  · split <;> exact Hoare.pure' fun _ h => h
  · exact Hoare.bind (bytesOfRV_mem F n _) fun _ => Hoare.pure' fun _ h => h
  · exact Hoare.bind (bytesOfRV_mem F n _) fun _ => Hoare.pure' fun _ h => h
  · exact Hoare.bind (bytesOfRV_mem F n _) fun _ => Hoare.pure' fun _ h => h
  · split
    · split
      · split <;> exact Hoare.pure' fun _ h => h
      · exact Hoare.pure' fun _ h => h
    · exact Hoare.halt' fun _ h => h
  · exact Hoare.halt' fun _ h => h

theorem encodeParts_mem {H : HeapTy} (F : Fr) (n : Nat) (packed : Bool) :
    ∀ {ts : List STy} (vs : RVals E.layout ts),
    Hoare (MemOK E H) (encodeParts F n packed vs : EM E Γ _)
      (fun _ y => MemOK E H y) (fun _ y => MemOK E H y)
  | _, .nil => Hoare.pure' fun _ h => h
  | _, .cons v vs => Hoare.bind (encodeOne_mem F n packed v) fun _ =>
      Hoare.bind (encodeParts_mem F n packed vs) fun _ => Hoare.pure' fun _ h => h

theorem encodeVals_mem {H : HeapTy} (F : Fr) (n : Nat) (packed : Bool)
    {ts : List STy} (vs : RVals E.layout ts) :
    Hoare (MemOK E H) (encodeVals F n packed vs : EM E Γ _)
      (fun _ y => MemOK E H y) (fun _ y => MemOK E H y) := by
  unfold encodeVals
  exact Hoare.bind (encodeParts_mem F n packed vs) fun _ =>
    Hoare.ite' (fun _ => Hoare.pure' fun _ h => h) (fun _ => Hoare.pure' fun _ h => h)

theorem evalE_abiEncode_mem (G : Glob E) (F : Fr) (n : Nat) {H : HeapTy}
    {ts : List STy} (args : RArgs E Γ ts)
    (ha : Hoare (MemOK E H) (evalArgs G F n args)
      (fun _ y => MemOK E H y) (fun _ y => MemOK E H y)) :
    Hoare (MemOK E H) (evalE G F (n + 1) (.abiEncode .encode args))
      (fun v y => MemOK E H y ∧ RValOK E y.2.heap.ty v) (fun _ y => MemOK E H y) := by
  simp only [evalE]
  exact Hoare.bind ha fun vs => Hoare.bind (encodeVals_mem F n false vs) fun bs =>
    Hoare.bind (allocBytes_mem bs) fun v => Hoare.pure' fun _ h => h

#print axioms bytesOfRV_mem
#print axioms encodeVals_mem
#print axioms evalE_abiEncode_mem
end Solidity.Source.Preservation
