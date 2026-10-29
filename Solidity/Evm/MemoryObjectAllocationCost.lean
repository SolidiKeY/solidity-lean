import Solidity.Evm.MemoryObjectPrimitive

/-! Reached capacity and growing certificates for reference-array construction. -/
namespace Solidity.Evm.Memory.Objects
variable {C : Contract}

def GrowingResult {Γ Δ : Ctx} (L b frame cost : Nat) (F : Frag Δ) (σ : State C Γ)
    (base : Nat → Fin W) (m : Machine) (res : TRes (Solidity.Out C σ.H Δ)) (out : Out) : Prop :=
  (∃ o m' base', res = .ok o ∧ out = .ok m' 0 ∧ StateRepr L b frame F o.st base' m' ∧
    m'.stack = m.stack ∧ BaseExtends σ.H base base' ∧
    GrowsAllocator b frame cost σ base m o.st base' m') ∨
      (res = .error .revert ∧ out = .revert)

theorem ResultRepr.growing {Γ Δ : Ctx} {L b frame : Nat} {F : Frag Δ} {σ : State C Γ}
    {base : Nat → Fin W} {m : Machine} {res : TRes (Solidity.Out C σ.H Δ)} {out : Out}
    (h : ResultRepr L b frame F σ base m res out) :
    GrowingResult L b frame 0 F σ base m res out := by
  rcases h with ⟨o, m', hs, ht, hr, hk, ha⟩ | ⟨hs, ht⟩
  · refine .inl ⟨o, m', base, hs, ht, hr, hk, BaseExtends.refl base, ?_⟩
    intro c hb hc hspace
    exact ha c hb hc
  · exact .inr ⟨hs, ht⟩

end Solidity.Evm.Memory.Objects

namespace Solidity.Evm.Memory.Construction
variable {C : Contract}

/-- A typed child default contributes its actual separate reservation.
Other nonempty child constructors are refused by the compiler. -/
def arrayCost (E : Ty) (n : Nat) : Nat :=
  n + 1 + (match E with | .ref (.array _) => n | _ => 0)

theorem arrayCost_zero (E : Ty) : arrayCost E 0 = 1 := by
  cases E with
  | prim p => rfl
  | ref R => cases R <;> rfl

def hasAllocationStmt {Γ Δ : Ctx} : Stmt C Γ Δ → Bool
  | .declMem (.array _) _ none _ _ => true
  | .declMem _ _ (some (.newArr ..)) _ _ => true
  | .rebindMem _ (.newArr ..) => true
  | _ => false

def hasAllocation {Γ Δ : Ctx} : Prog C Γ Δ → Bool
  | .nil => false
  | .cons s P => hasAllocationStmt s || hasAllocation P

def rawAllocationCostStmt {Γ Δ : Ctx} (s : Stmt C Γ Δ) (σ : State C Γ) : Nat :=
  match s with
  | .declMem (.array _) _ none _ _ => 1
  | .declMem (.array E) _ (some (.newArr n _)) _ _ => arrayCost E (n.evalT σ).word.val
  | .rebindMem (R := .array E) _ (.newArr n _) => arrayCost E (n.evalT σ).word.val
  | _ => 0

def allocationCostStmt {Γ Δ : Ctx} (s : Stmt C Γ Δ) (σ : State C Γ) : Nat :=
  if hasAllocationStmt s then rawAllocationCostStmt s σ else 0

/-- Nonallocating suffixes do not evaluate their source interpreter for capacity. -/
def allocationCostProg {Γ Δ : Ctx} (P : Prog C Γ Δ) (σ : State C Γ) : Nat :=
  match P with
  | .nil => 0
  | .cons s tail =>
    if hasAllocationStmt s || hasAllocation tail then
      allocationCostStmt s σ + if hasAllocation tail then
        match s.run σ with
        | .ok o => allocationCostProg tail o.st
        | .error _ => 0
      else 0
    else 0

theorem allocationCostStmt_zero {Γ Δ : Ctx} (s : Stmt C Γ Δ)
    (h : hasAllocationStmt s = false) (σ : State C Γ) : allocationCostStmt s σ = 0 := by
  rw [allocationCostStmt, h]
  rfl

theorem allocationCostProg_zero {Γ Δ : Ctx} (P : Prog C Γ Δ)
    (h : hasAllocation P = false) (σ : State C Γ) : allocationCostProg P σ = 0 := by
  cases P with
  | nil => rfl
  | cons s P =>
    have hh : hasAllocationStmt s = false ∧ hasAllocation P = false := Bool.or_eq_false_iff.mp h
    simp only [allocationCostProg, hh.1, hh.2, Bool.false_or, Bool.false_eq_true, if_false]

theorem allocationCostProg_cons {Γ Δ Ξ : Ctx} (s : Stmt C Γ Δ) (P : Prog C Δ Ξ)
    (σ : State C Γ) :
    allocationCostProg (.cons s P) σ = allocationCostStmt s σ +
      match s.run σ with | .ok o => allocationCostProg P o.st | .error _ => 0 := by
  rw [allocationCostProg]
  cases ht : hasAllocation P with
  | true => simp only [Bool.or_true, if_true]; cases s.run σ <;> rfl
  | false =>
    simp only [Bool.or_false, Bool.false_eq_true, if_false]
    have htail : (match s.run σ with | .ok o => allocationCostProg P o.st | .error _ => 0) = 0 := by
      cases s.run σ with
      | ok o => exact allocationCostProg_zero P ht o.st
      | error _ => rfl
    rw [htail, Nat.add_zero]
    cases hs : hasAllocationStmt s with
    | true => rfl
    | false => exact (allocationCostStmt_zero s hs σ).symm

end Solidity.Evm.Memory.Construction
