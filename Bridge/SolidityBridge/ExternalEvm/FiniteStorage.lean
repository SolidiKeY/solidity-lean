import Solidity.Evm.Machine

/-! Finite observations of symbolic storage with arbitrary numeric aliases. -/
namespace Solidity.Evm.StorageSlots

/-- A finite set of observed cells; values at numeric aliases must agree. -/
def Represents {α : Type} (domain : List Slot) (ρ : Slot → α)
    (store : WordStore) (read : α → Fin W) : Prop :=
  ∀ a ∈ domain, store.cells a = read (ρ a)

/-- Collisions are legal for reads only when the represented values agree. -/
theorem aliases_read {α : Type} {domain : List Slot} {ρ : Slot → α}
    {store : WordStore} {read : α → Fin W}
    (h : Represents domain ρ store read) {a b : Slot}
    (ha : a ∈ domain) (hb : b ∈ domain) (he : ρ a = ρ b) :
    store.cells a = store.cells b := by
  rw [h a ha, h b hb, he]

/-- Exact local write condition: every distinct observed symbolic alias
already has the value being written. This permits collisions and zero writes;
it does not silently demand collision freedom on the finite domain. -/
def WriteCompatible {α : Type} (domain : List Slot) (ρ : Slot → α)
    (store : WordStore) (a : Slot) (v : Fin W) : Prop :=
  ∀ b ∈ domain, b ≠ a → ρ b = ρ a → store.cells b = v

/-- A numeric write implements the symbolic write on the observed domain
exactly under WriteCompatible. This is a representation lemma, not yet a
claim about upstream SSTORE's account-map update. -/
theorem write_iff {α : Type} [DecidableEq α] {domain : List Slot} {ρ : Slot → α}
    {store : WordStore} {read : α → Fin W}
    (h : Represents domain ρ store read) (a : Slot) (v : Fin W) :
    Represents domain ρ (store.write a v.val)
      (fun n => if n = ρ a then v else read n) ↔
      WriteCompatible domain ρ store a v := by
  constructor
  · intro hw b hb hba he
    have hh := hw b hb
    dsimp only at hh
    have hc : (store.write a v.val).cells b = store.cells b := by
      apply Fin.ext
      exact WordStore.write_other store v.val hba
    rw [hc, if_pos he] at hh
    exact hh
  · intro hw b hb
    change (store.write a v.val).cells b = if ρ b = ρ a then v else read (ρ b)
    by_cases hba : b = a
    · subst b
      rw [WordStore.write_cells_same, if_pos rfl]
    · have hc : (store.write a v.val).cells b = store.cells b := by
        apply Fin.ext
        exact WordStore.write_other store v.val hba
      rw [hc]
      by_cases he : ρ b = ρ a
      · rw [if_pos he]
        exact hw b hb hba he
      · rw [if_neg he]
        exact h b hb

/-- A collision with unequal values is refused, rather than assumed away. -/
theorem collision_refused {α : Type} {domain : List Slot} {ρ : Slot → α}
    {store : WordStore} {read : α → Fin W} {a b : Slot}
    (ha : a ∈ domain) (hb : b ∈ domain) (he : ρ a = ρ b)
    (hv : store.cells a ≠ store.cells b) : ¬ Represents domain ρ store read := by
  intro h
  exact hv (aliases_read h ha hb he)

/-- Two distinct symbolic addresses may alias when their read values agree. -/
theorem zero_aliases : Represents [.root 0, .root W] (fun _ => (0 : Nat))
    WordStore.zero (fun _ => wmod 0) := by
  intro a _
  rfl

/-- A nonzero write cannot preserve a distinct zero-valued observed alias. -/
theorem nonzero_alias_write_refused :
    ¬ WriteCompatible [.root 0, .root W] (fun _ => (0 : Nat))
      WordStore.zero (.root 0) (wmod 7) := by
  intro h
  have hn : Slot.root W ≠ Slot.root 0 := by
    intro he
    have hh := Slot.root.inj he
    have hp := W_pos
    omega
  have hv := h (.root W) (by simp only [List.mem_cons]; exact Or.inr (Or.inl True.intro)) hn rfl
  have hx := congrArg Fin.val hv
  change 0 = 7 at hx
  omega

end Solidity.Evm.StorageSlots

/-- info: 'Solidity.Evm.StorageSlots.write_iff' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Evm.StorageSlots.write_iff
/-- info: 'Solidity.Evm.StorageSlots.nonzero_alias_write_refused' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Evm.StorageSlots.nonzero_alias_write_refused
