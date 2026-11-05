import Solidity.Source.Progress.AggregateDefaults
import Solidity.Source.Progress.StructParentControls

/-! Reference-bearing struct defaults: actual nested empty-byte allocations,
inhabited memory preservation, and a timeout after the first child allocation.
The original default/readiness policies and heap observations are unchanged. -/
namespace Solidity.Source.Progress.AggregateDefaultControls
open EM StructParentControls
abbrev Pty : STy := .struct .memory dn

theorem shape : FiniteDefault E Pty := .structNew dn (by
  intro τ member
  change τ ∈ [Bty,Bty] at member
  simp only [List.mem_cons,List.not_mem_nil,or_false,or_self] at member
  subst τ
  exact .ready (.memory .bytes))
def child : St E := {initial with heap:=(seed.alloc ⟨Bty,.bytes []⟩).1}
def second : St E := {initial with heap:=(child.heap.alloc ⟨Bty,.bytes []⟩).1}
def data : Data E.layout Pty :=
  .struct (.cons (.val (.memRef rfl 1)) (.cons (.val (.memRef rfl 2)) .nil))
def reached : St E := {initial with heap:=(second.heap.alloc ⟨Pty,data⟩).1}

theorem run :
    (zeroVal (E:=E) (Γ:=Γ) 6 Pty).run (small,initial) =
      (.ok (.memRef rfl 3),(small,reached)) := rfl
theorem late_timeout :
    (zeroVal (E:=E) (Γ:=Γ) 5 Pty).run (small,initial) =
      (.error .timeout,(small,child)) := rfl
theorem preserved :
    NS (zeroVal (E:=E) (Γ:=Γ) 6 Pty) ∧ MemOK E seed.ty (small,reached) ∧
    (Val.memRef (τ:=Pty) rfl 3).RefOK E reached.heap.ty ∧ MemOK E seed.ty (small,child) := by
  have success := finite_default_progress_and_memory (Γ:=Γ) shape 6 seed.ty
  have timed :=  finite_default_progress_and_memory (Γ:=Γ) shape 5 seed.ty
  have hs := success.2 (small,initial) initial_mem.1
  have ht := timed.2 (small,initial) initial_mem.1
  rw [run] at hs
  rw [late_timeout] at ht
  exact ⟨success.1,hs.1,hs.2,ht⟩
theorem heap_and_frame :
    reached.heap.get 0 = seed.get 0 ∧ reached.heap.get 1 = some ⟨Bty,.bytes []⟩ ∧
    reached.heap.get 2 = some ⟨Bty,.bytes []⟩ ∧ reached.heap.get 3 = some ⟨Pty,data⟩ ∧
    reached.heap.next = 4 ∧ reached.logs = initial.logs ∧ reached.fnLocals = initial.fnLocals ∧
    child.heap.next = 2 ∧ child.heap.get 2 = none := ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
theorem old_default_refused : ¬ZeroReady E Pty := by
  intro ready
  cases ready with
  | value absent => cases absent
  | memory empty => cases empty

#print axioms shape
#print axioms run
#print axioms late_timeout
#print axioms preserved
#print axioms heap_and_frame
#print axioms old_default_refused
end Solidity.Source.Progress.AggregateDefaultControls
