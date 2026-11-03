import Solidity.Yul.Static

/-! Catalog and lookup bridges used by independent static relations. -/
namespace Solidity.Yul

/-- Each intrinsically named builtin is present at its exact input/output arities. -/
theorem lookup_builtin_name {a r : Nat} (b : Builtin a r) :
    lookupBuiltin b.name = some ⟨a, r, b⟩ := by
  cases b <;> first
    | (rename_i p; cases p <;> rfl)
    | rfl

/-- The executable catalog never invents a builtin's spelling. -/
theorem lookupBuiltin_sound {name : String} {a r : Nat} {b : Builtin a r}
    (h : lookupBuiltin name = some ⟨a, r, b⟩) : b.name = name := by
  have hn := List.find?_some h
  exact eq_of_beq hn

/-- An independent absence condition over builtin constructors and their names. -/
def NoBuiltin (name : String) : Prop :=
  ∀ (a r : Nat) (b : Builtin a r), b.name ≠ name

theorem lookup_none_sound {name : String} (h : lookupBuiltin name = none) : NoBuiltin name := by
  intro a r b hn
  have hb := lookup_builtin_name b
  rw [hn, h] at hb
  cases hb

theorem lookup_none_complete {name : String} (h : NoBuiltin name) : lookupBuiltin name = none := by
  cases he : lookupBuiltin name with
  | none => rfl
  | some e =>
      rcases e with ⟨a, r, b⟩
      exact False.elim (h a r b (lookupBuiltin_sound he))

/-- No declarative binding is visible at this name. -/
def NoBinding {α : Type} (env : List (String × α)) (name : String) : Prop :=
  ¬ ∃ value, Resolves env name value

theorem resolve_none_sound {α : Type} {env : List (String × α)} {name : String}
    (h : resolve env name = none) : NoBinding env name := by
  rintro ⟨value, d⟩
  have hd := resolve_complete d
  rw [h] at hd
  cases hd

theorem resolve_none_complete {α : Type} {env : List (String × α)} {name : String}
    (h : NoBinding env name) : resolve env name = none := by
  cases he : resolve env name with
  | none => rfl
  | some value => exact False.elim (h ⟨value, resolve_sound he⟩)

end Solidity.Yul
