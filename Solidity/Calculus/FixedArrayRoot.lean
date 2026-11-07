import Solidity.Calculus.FixedArrayFloor

/-!
# Fixed-array flooring at a typed storage root

Lift the vector reconstruction to the actual storage update. Other roots
are unchanged; optional reads along typed element continuations agree.
This additive interface does not alter the APF classifier or decision.
-/
namespace Solidity.Decide

/-- Rebuild a fixed storage value using its intrinsic view, without an indexed match. -/
def fixedFloorValue {E : Ty} {n : Nat} (B : List Int)
    (v : SVal (.ref (.fixed E n))) : SVal (.ref (.fixed E n)) :=
  .fixed (fixedFloorVec B v.view)

theorem fixedFloorValue_find {E U : Ty} {n : Nat} (B : List Int)
    (v : SVal (.ref (.fixed E n))) (hn : (n : Int) ∈ B)
    (i : PrimTy.uint.Denote) (q : Path E U) :
    (fixedFloorValue B v).findM (.atF i q) =
      v.findM (.atF (fixedFloorIndex B i) q) := by
  cases v with
  | fixed v => exact fixedFloorVec_find B v hn i q

/-- Replace precisely one intrinsically typed fixed-array root. -/
def fixedFloorRoot {C : Contract} {a : Name} {E : Ty} {n : Nat}
    (h : C.rootType a = some (.ref (.fixed E n))) (B : List Int)
    (st : Storage C) : Storage C :=
  st.set h (fixedFloorValue B (st.get h))

theorem fixedFloorRoot_get {C : Contract} {a : Name} {E : Ty} {n : Nat}
    (h : C.rootType a = some (.ref (.fixed E n))) (B : List Int) (st : Storage C) :
    (fixedFloorRoot h B st).get h = fixedFloorValue B (st.get h) := by
  exact SFields.get_set_same st h _

theorem fixedFloorRoot_get_ne {C : Contract} {a b : Name} {E T : Ty} {n : Nat}
    (h : C.rootType a = some (.ref (.fixed E n))) (B : List Int) (st : Storage C)
    (hb : C.rootType b = some T) (ha : b ≠ a) :
    (fixedFloorRoot h B st).get hb = st.get hb :=
  SFields.get_set_ne st h hb (Ne.symm ha) _

theorem fixedFloorRoot_find {C : Contract} {a : Name} {E U : Ty} {n : Nat}
    (h : C.rootType a = some (.ref (.fixed E n))) (B : List Int) (st : Storage C)
    (hn : (n : Int) ∈ B) (i : PrimTy.uint.Denote) (q : Path E U) :
    ((fixedFloorRoot h B st).get h).findM (.atF i q) =
      (st.get h).findM (.atF (fixedFloorIndex B i) q) := by
  rw [fixedFloorRoot_get]
  exact fixedFloorValue_find B _ hn i q

/-- Every retained uint index is unchanged, including indices outside the array. -/
theorem fixedFloorIndex_fix (B : List Int) (i : PrimTy.uint.Denote)
    (hi : (i.1.toNat : Int) ∈ B) : fixedFloorIndex B i = i := by
  rw [fixedFloorIndex, mxFloorIndex_fix B hi, uintOfNat_toNatA]

theorem fixedFloorRoot_retained {C : Contract} {a : Name} {E U : Ty} {n : Nat}
    (h : C.rootType a = some (.ref (.fixed E n))) (B : List Int) (st : Storage C)
    (hn : (n : Int) ∈ B) (i : PrimTy.uint.Denote) (hi : (i.1.toNat : Int) ∈ B)
    (q : Path E U) :
    ((fixedFloorRoot h B st).get h).findM (.atF i q) = (st.get h).findM (.atF i q) := by
  rw [fixedFloorRoot_find h B st hn, fixedFloorIndex_fix B i hi]

/-- Actual word observations at the rebuilt root read their floored indices. -/
theorem fixedFloorRoot_word {C : Contract} {a : Name} {E : Ty} {p : PrimTy} {n : Nat}
    (h : C.rootType a = some (.ref (.fixed E n))) (B : List Int) (st : Storage C)
    (hn : (n : Int) ∈ B) (i : PrimTy.uint.Denote) (q : Path E (.prim p)) :
    (fixedFloorRoot h B st).obs.word (.ref ⟨a, h, .atF i q⟩) =
      st.obs.word (.ref ⟨a, h, .atF (fixedFloorIndex B i) q⟩) := by
  simp only [Storage.obs_word_ref]
  exact congrArg SVal.wordOf (fixedFloorRoot_find h B st hn i q)

/-- Actual presence observations preserve halted paths as well as successful paths. -/
theorem fixedFloorRoot_has {C : Contract} {a : Name} {E U : Ty} {n : Nat}
    (h : C.rootType a = some (.ref (.fixed E n))) (B : List Int) (st : Storage C)
    (hn : (n : Int) ∈ B) (i : PrimTy.uint.Denote) (q : Path E U) :
    (fixedFloorRoot h B st).obs.has (.ref ⟨a, h, .atF i q⟩) =
      st.obs.has (.ref ⟨a, h, .atF (fixedFloorIndex B i) q⟩) := by
  simp only [Storage.obs_has_ref]
  exact congrArg Option.isSome (fixedFloorRoot_find h B st hn i q)

/-- Word observations through every other root are unchanged. -/
theorem fixedFloorRoot_other_word {C : Contract} {a : Name} {E : Ty} {p : PrimTy} {n : Nat}
    (h : C.rootType a = some (.ref (.fixed E n))) (B : List Int) (st : Storage C)
    (r : SRef C (.prim p)) (ha : r.root ≠ a) :
    (fixedFloorRoot h B st).obs.word (.ref r) = st.obs.word (.ref r) := by
  rw [Storage.obs_word_ref, Storage.obs_word_ref, fixedFloorRoot_get_ne h B st r.hroot ha]

/-- Presence observations through every other root are unchanged. -/
theorem fixedFloorRoot_other_has {C : Contract} {a : Name} {E U : Ty} {n : Nat}
    (h : C.rootType a = some (.ref (.fixed E n))) (B : List Int) (st : Storage C)
    (r : SRef C U) (ha : r.root ≠ a) :
    (fixedFloorRoot h B st).obs.has (.ref r) = st.obs.has (.ref r) := by
  rw [Storage.obs_has_ref, Storage.obs_has_ref, fixedFloorRoot_get_ne h B st r.hroot ha]

/-- A typed state changed only at the selected storage root. -/
def fixedFloorState {C : Contract} {Γ : Ctx} {a : Name} {E : Ty} {n : Nat}
    (h : C.rootType a = some (.ref (.fixed E n))) (B : List Int)
    (σ : State C Γ) : State C Γ :=
  σ.withStorage (fixedFloorRoot h B σ.storage)

/-- The entire non-storage frame is retained for every contract/context/heap. -/
theorem fixedFloorState_frame {C : Contract} {Γ : Ctx} {a : Name} {E : Ty} {n : Nat}
    (h : C.rootType a = some (.ref (.fixed E n))) (B : List Int) (σ : State C Γ) :
    (fixedFloorState h B σ).H = σ.H ∧
    (fixedFloorState h B σ).heap = σ.heap ∧
    (fixedFloorState h B σ).env = σ.env ∧
    (fixedFloorState h B σ).net = σ.net ∧
    (fixedFloorState h B σ).selfBalance = σ.selfBalance ∧
    (fixedFloorState h B σ).tx = σ.tx := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

end Solidity.Decide
