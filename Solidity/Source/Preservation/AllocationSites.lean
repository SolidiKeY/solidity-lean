import Solidity.Source.Decode
import Solidity.Source.Preservation.Frames

/-! Actual allocation-site bridges. Raw string/hex literals do not allocate;
string materialization, struct member packing and byte encoding allocate through
`allocRef`. Decoder preservation is reused from the published source theorem.
All triples retain every halt and the full existing `MemOK` invariant.
-/
namespace Solidity.Source.Preservation
open EM
variable {E : Env} {Γ : RCtx}

theorem allocBytes_mem {H : HeapTy} (bs : Roadmap.Bytes) :
    Hoare (MemOK E H) (allocRef (Data.bytes (l := .memory) bs) : EM E Γ (Val E.layout (.bytes .memory)))
      (fun v y => MemOK E H y ∧ v.RefOK E y.2.heap.ty) (fun _ y => MemOK E H y) :=
  Hoare.conseq (allocRef_mem _ rfl trivial trivial) (fun _ h => ⟨h, .bytes bs⟩)
    (fun _ _ h => h) (fun _ _ h => h)

theorem allocString_mem {H : HeapTy} (bs : Roadmap.Bytes) :
    Hoare (MemOK E H) (allocRef (Data.string (l := .memory) bs) : EM E Γ (Val E.layout (.string .memory)))
      (fun v y => MemOK E H y ∧ v.RefOK E y.2.heap.ty) (fun _ y => MemOK E H y) :=
  Hoare.conseq (allocRef_mem _ rfl trivial trivial) (fun _ h => ⟨h, .string bs⟩)
    (fun _ _ h => h) (fun _ _ h => h)

theorem literalBytes_mem {H : HeapTy} (F : Fr) (n : Nat) (bs : Roadmap.Bytes) :
    Hoare (MemOK E H) (convRV F n (.bytes .memory) (.strLit bs) : EM E Γ _)
      (fun v y => MemOK E H y ∧ RValOK E y.2.heap.ty v) (fun _ y => MemOK E H y) := by
  simp only [convRV, reduceCtorEq, ↓reduceDIte, pure_bind]
  exact Hoare.bind (allocBytes_mem bs) fun v => Hoare.pure' fun _ h => h

theorem literalString_mem {H : HeapTy} (F : Fr) (n : Nat) (bs : Roadmap.Bytes) :
    Hoare (MemOK E H) (convRV F n (.string .memory) (.strLit bs) : EM E Γ _)
      (fun v y => MemOK E H y ∧ RValOK E y.2.heap.ty v) (fun _ y => MemOK E H y) := by
  simp only [convRV, reduceCtorEq, ↓reduceDIte, pure_bind]
  exact Hoare.bind (allocString_mem bs) fun v => Hoare.pure' fun _ h => h

#print axioms literalBytes_mem
#print axioms literalString_mem
end Solidity.Source.Preservation
