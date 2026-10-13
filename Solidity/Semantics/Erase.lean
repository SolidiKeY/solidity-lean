import Solidity.Semantics.State
import Solidity.Semantics.HeapErase

/-!
# The typed state's operations, erased

Each operation of the typed state (`Semantics/State.lean`) read on its
erasure (`State.globE`, `Semantics.lean`'s state with no locals): an
allocation, a copy either way, the deployment's state.  Split out of
`Semantics/State.lean` at W10.5.1 (`docs/intrinsic.md`), so the typed core
(`State`, `Run`, `Heap`, `Signature.lean`) imports no erasure module; the
readers are the Typing chain and the tools, which `Semantics/TypedErase.lean`
serves, and they go with them (W10.5.2–6); the EVM simulation (W10.5.3)
and the memory laws (W10.5.4) read none.
-/

namespace Solidity

variable {C : Contract}

namespace State

variable {Γ : Ctx}

theorem init_globE (C : Contract) : (State.init C).globE = { storage := C.initStorage } := by
  simp only [globE, init, Storage.init_erase]
  rfl

theorem globE_heap (σ : State C Γ) : σ.globE.heap = σ.heap.erase := rfl

theorem globE_nextId (σ : State C Γ) : σ.globE.nextId = σ.H.length := rfl

/-- The adopted state's global part is the old one with the grown heap. -/
theorem adopt_globE {α : HTy → Type} (σ : State C Γ) (g : Grown σ.H α) :
    (σ.adopt g).1.globE = Heap.into σ.globE g.heap := rfl

theorem alloc_erase {R : RefTy} (σ : State C Γ) (o : MObj σ.H R) :
    σ.globE.alloc (MObj.erase R o) =
      ((σ.alloc o).1.globE, ((σ.alloc o).2 : HRef _ R).id) := by
  rw [Heap.alloc_erase (globE_heap σ) (globE_nextId σ) o, alloc, adopt_globE]
  rfl

theorem copyStToM_erase {T : Ty} (σ : State C Γ) (v : SVal T) (h : T.mapFree = true) :
    Semantics.copyStToM σ.globE v.erase =
      .ok ((σ.copyStToM v h).1.globE, MVal.erase T (σ.copyStToM v h).2) := by
  rw [SVal.copyStToM_erase v h σ.heap σ.globE (globE_heap σ) (globE_nextId σ), copyStToM,
    adopt_globE]
  rfl

theorem copyMem_erase {T : Ty} (σ : State C Γ) (v : MVal σ.H T) :
    Semantics.copyMem σ.globE (MVal.erase T v) = .ok (σ.copyMToSt v).erase :=
  MVal.copyMem_erase (globE_heap σ) v

end State

end Solidity
