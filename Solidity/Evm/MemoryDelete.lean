import Solidity.Evm.MemoryStatements

/-!
# Primitive memory deletion

Deleting an element writes its typed default through the existing checked
index code. Deleting an array local instead allocates a fresh empty object;
older aliases retain the previous object. These equalities use the typed run,
so the compiler can reuse its write and allocating-rebind certificates.
-/

namespace Solidity.Evm.Memory

variable {C : Contract} {Γ : Ctx}

/-- A primitive default expressed in the existing value language. -/
def deleteDefaultValue : (p : PrimTy) → Val C Γ p
  | .uint => .simple (.lit 0 rfl)
  | .int => .simple (.lit 0 rfl)
  | .bool => .simple (.bool false)

theorem deleteDefaultValue_eval (σ : State C Γ) (p : PrimTy) :
    (deleteDefaultValue p).evalT σ = .ok (PrimTy.dflt p) := by
  cases p <;> rfl

/-- Primitive deletion has exactly the failure and update behavior of a default write. -/
theorem deleteMem_primitive_eq_assign (σ : State C Γ) {p : PrimTy}
    (l : MLoc C Γ (.prim p)) :
    TRun.deleteMem (.loc l) σ = TRun.assignMem l (.val (deleteDefaultValue p)) σ := by
  cases p <;> rfl

/-- The index runs once before the default word is written. -/
def deleteLocalCode {Γ : Ctx} {p : PrimTy} (b : Nat)
    (j : Idx Γ (.mem (.array (.prim p)))) (index : List Instr) : List Instr :=
  writeLocalValueCode b j index [.push w[0]]

/-- Element deletion preserves the complete heap relation, including aliases. -/
theorem deleteLocalValue_correct {L b frame : Nat} {F : Frag Γ}
    {σ : State C Γ} {base : Nat → Fin W} {m : Machine}
    (h : StateRepr L b frame F σ base m) {p : PrimTy}
    (j : Idx Γ (.mem (.array (.prim p)))) (i : Val C Γ .uint) (index : List Instr)
    (hi : ∀ {m' : Machine}, StateRepr L b frame F σ base m' →
      ValOutT .uint (i.evalT σ) (run index m') m') :
    ResultRepr L b frame F σ base m
      (TRun.deleteMem (.loc (.index .dyn (.var j rfl) i)) σ)
      (run (deleteLocalCode b j index) m) := by
  rw [deleteMem_primitive_eq_assign]
  exact writeLocalValue_correct h j i (deleteDefaultValue p) index [.push w[0]] hi
    (.inl ⟨_, _, deleteDefaultValue_eval σ p, ReprV.dflt_zero p, rfl⟩)

/-- Deleting the local rebinds it to a fresh empty array. -/
theorem deleteMem_array_eq_reallocate (σ : State C Γ) (p : PrimTy)
    (j : Idx Γ (.mem (.array (.prim p)))) :
    TRun.deleteMem (.var j rfl) σ =
      TRun.rebindMem j (.newArr (.lit 0 rfl) rfl) σ := by
  rfl

/-- A default primitive-array declaration allocates the same fresh empty object. -/
theorem defaultArray_eq_allocate (σ : State C Γ) (p : PrimTy) :
    TRun.declMem (.array (.prim p)) none rfl σ =
      TRun.declMem (.array (.prim p)) (some (.newArr (.lit 0 rfl) rfl)) rfl σ := by
  rfl

end Solidity.Evm.Memory
