import Solidity.Backend.Passes.Stack

/-!
# Independent frame reservation and fresh typed locals

A larger frame is valid only while every represented heap object stays above
it. This theorem exposes that necessary slack rather than treating frame
growth as an unconditional weakening. No heap, pointer or source value is
replaced by an unconstrained word.
-/
namespace Solidity.Backend.Passes

open Solidity.Evm
variable {C : Contract} {L b frame frame' : Nat} {Γ : Ctx} {F : Frag Γ}
  {σ : State C Γ} {base : Nat → Fin W} {m : Machine}

/-- Reserve a different frame with independently checked heap separation.
The old representation, pointer identities and complete typed heap survive. -/
theorem memory_frame
    (h : Memory.StateRepr L b frame F σ base m)
    (locals : b + Γ.length ≤ frame')
    (arrays : ∀ {p : PrimTy} (r : HRef σ.H (.array (.prim p))),
      frame' ≤ (base r.id).val)
    (structs : ∀ {s : Name} (r : HRef σ.H (.struct s)),
      frame' ≤ (base r.id).val) :
    Memory.StateRepr L b frame' F σ base m :=
  ⟨h.core, ⟨h.heap.arrays, arrays, h.heap.separated⟩,
    h.pointers, locals, ⟨h.structs.objects, structs, h.structs.separated⟩,
    h.separated, h.refs⟩

/-- A fresh value local and an arbitrary saved stack are independent:
first reserve sufficient separated frame space, then write the new typed
local. The previous locals and every actual heap object stay represented. -/
theorem memory_extend_value
    (h : Memory.StateRepr L b frame F σ base m)
    {p : PrimTy} (value : p.Denote) (word : Word) (hw : ReprV p value word)
    (capacity : b + (Γ.length + 1) ≤ frame')
    (arrays : ∀ {q : PrimTy} (r : HRef σ.H (.array (.prim q))),
      frame' ≤ (base r.id).val)
    (structs : ∀ {s : Name} (r : HRef σ.H (.struct s)),
      frame' ≤ (base r.id).val) (tail : List Word) :
    Memory.StateRepr L b frame' (F.push (.val p) .ok)
      (σ.push (t := .val p) value) base
      (Memory.writeMachine {m with stack := tail} (cell (b + Γ.length)) word) := by
  have hlocal : b + Γ.length ≤ frame' := by omega
  exact ((memory_frame h hlocal arrays structs).stack tail).consVal value word hw capacity

end Solidity.Backend.Passes
