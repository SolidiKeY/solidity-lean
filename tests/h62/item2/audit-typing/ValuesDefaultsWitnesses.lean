import Solidity.Typing.Values

namespace H62.AuditTyping.ValuesDefaultsWitnesses
open Solidity
open Solidity.Semantics

-- A single global predicate makes ALL three default-node conditions hold.
def truthH : Hered where
  arr := fun _ _ => True
  fix := fun _ _ => True
  map := fun _ {_} _ _ => True

theorem below_irrel : ∃ (k k' : Nat) (T : Ty),
    ∃ (_h : tyRank T < k) (_h' : tyRank T < k'), True :=
  ⟨1, 1, .prim .bool, by decide, by decide, True.intro⟩

theorem below_default : ∃ (k : Nat) (T : Ty), ∃ (_h : tyRank T < k), True :=
  ⟨1, .prim .bool, by decide, True.intro⟩

theorem fields_below : ∃ (k : Nat) (fs : List (Solidity.Name × Ty)),
    ∃ (_h : fieldsRank fs < k), True :=
  ⟨1, [], by decide, True.intro⟩

theorem default_value : ∃ (P : Hered),
    ∃ (_harr : ∀ E : Ty, P.arr (E := E) SVec.nil SList.nil)
      (_hfix : ∀ E n, P.fix E n)
      (_hmap : ∀ (K : PrimTy) (V : Ty), P.map K SMap.nil (SVal.dflt V))
      (_T : Ty), True :=
  ⟨truthH, fun _ => True.intro, fun _ _ => True.intro,
    fun _ _ => True.intro, .prim .bool, True.intro⟩

theorem default_fields : ∃ (P : Hered),
    ∃ (_harr : ∀ E : Ty, P.arr (E := E) SVec.nil SList.nil)
      (_hfix : ∀ E n, P.fix E n)
      (_hmap : ∀ (K : PrimTy) (V : Ty), P.map K SMap.nil (SVal.dflt V))
      (_fs : List (Solidity.Name × Ty)), True :=
  ⟨truthH, fun _ => True.intro, fun _ _ => True.intro,
    fun _ _ => True.intro, [], True.intro⟩

theorem default_below : ∃ (P : Hered),
    ∃ (_harr : ∀ E : Ty, P.arr (E := E) SVec.nil SList.nil)
      (_hfix : ∀ E n, P.fix E n)
      (_hmap : ∀ (K : PrimTy) (V : Ty), P.map K SMap.nil (SVal.dflt V))
      (k : Nat) (T : Ty), ∃ (_h : tyRank T < k), True :=
  ⟨truthH, fun _ => True.intro, fun _ _ => True.intro,
    fun _ _ => True.intro, 1, .prim .bool, by decide, True.intro⟩

-- Feasibility boundary: the global predicate cannot inhabit a false rank bound.
theorem zero_rank_rejected : ¬ (∃ (_h : tyRank (.prim .bool) < 0), True) := by
  intro h
  obtain ⟨h, _⟩ := h
  exact Nat.not_lt_zero _ h

end H62.AuditTyping.ValuesDefaultsWitnesses
