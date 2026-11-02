import Solidity.Source.WellTyped

/-! Heap-growing frame preservation for the actual `EM.sub`. The callee's
preservation theorem remains an explicit premise; this is the restoration
bridge, not an assumption that all interpreter computations preserve memory.
Caller locals are restored on success and every halt, including revert/stuck.
-/
namespace Solidity.Source.Preservation
open EM
variable {E : Env} {Γ Δ : RCtx} {α : Type}

theorem relocalize {H : HeapTy} {l : Locals E.layout Γ} {s : St E}
    (h : MemOK E H (l, s)) (l' : Locals E.layout Δ)
    (hl : LocalsOK E s.heap.ty l') : MemOK E H (l', s) :=
  ⟨⟨h.1.1, hl⟩, h.2⟩

theorem sub_locals (l : Locals E.layout Γ) (s : St E)
    (l' : Locals E.layout Δ) (m : EM E Δ α) :
    ((sub l' m : EM E Γ (α × Locals E.layout Δ)).run (l, s)).2.1 = l := by
  unfold EM.sub
  rcases h : m.run (l', s) with ⟨r, ⟨l'', s'⟩⟩
  have h' : m (l', s) = (r, (l'', s')) := h
  cases r <;> simp only [ExceptT.run, ExceptT.mk, h']

theorem sub_mem {H : HeapTy} (l' : Locals E.layout Δ) (m : EM E Δ α)
    (hm : ∀ H', Hoare (MemOK E H') m (fun _ y => MemOK E H' y)
      (fun _ y => MemOK E H' y)) :
    Hoare (fun y => MemOK E H y ∧ LocalsOK E y.2.heap.ty l')
      (sub l' m : EM E Γ (α × Locals E.layout Δ))
      (fun _ y => MemOK E H y) (fun _ y => MemOK E H y) := by
  intro ⟨l, s⟩ ⟨ho, hi⟩
  have hrun := hm s.heap.ty (l', s) (relocalize ho.self l' hi)
  unfold EM.sub
  rcases he : m.run (l', s) with ⟨r, ⟨l'', s'⟩⟩
  rw [he] at hrun
  have finish (h : MemOK E s.heap.ty (l'', s')) : MemOK E H (l, s') :=
    relocalize (h.weaken ho.le) l (LocalsOK.mono h.le l ho.1.2)
  have he' : m (l', s) = (r, (l'', s')) := he
  cases r with
  | ok a => simp only [ExceptT.run, ExceptT.mk, he']; exact finish hrun
  | error e => simp only [ExceptT.run, ExceptT.mk, he']; exact finish hrun

#print axioms sub_mem
#print axioms sub_locals
end Solidity.Source.Preservation
