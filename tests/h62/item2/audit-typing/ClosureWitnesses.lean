import Solidity.Frontend.Static.Closure

/-! Simultaneous premise witnesses for frozen Closure source theorems.
Bool supplies an inhabited carrier and an actual DecidableEq instance.
Each existential bundle keeps all proposition premises together for one input.
These are feasibility witnesses, not compiler success contracts.
-/
namespace H62.AuditTyping.ClosureWitnesses
open Solidity.Frontend.Static

theorem reach_trans : ∃ (_succ : Bool → List Bool) (a _b c : Bool),
    Reach _succ a _b ∧ Reach _succ _b c :=
  ⟨fun _ => [], false, false, false, .refl false, .refl false⟩

theorem foldl_superset : ∃ (_ys _S : List Bool) (a : Bool), a ∈ _S := by
  exact ⟨[true], [false], false, by decide⟩

theorem foldl_mem : ∃ (_ys _S : List Bool) (a : Bool), a ∈ _ys := by
  exact ⟨[true], [false], true, by decide⟩

theorem foldl_sub : ∃ (_ys _S : List Bool) (a : Bool), a ∈ _ys.foldl insertNew _S := by
  exact ⟨[true], [false], true, by decide⟩

theorem foldl_nodup : ∃ (_ys _S : List Bool), _S.Nodup := by
  exact ⟨[true], [false], by decide⟩

theorem foldl_grows : ∃ (_ys _S : List Bool) (y : Bool), y ∈ _ys ∧ y ∉ _S := by
  exact ⟨[true], [false], true, by decide⟩

theorem foldl_same : ∃ (_ys _S : List Bool), ∀ y, y ∈ _ys → y ∈ _S := by
  exact ⟨[false], [false], by decide⟩

theorem grow_superset : ∃ (_succ : Bool → List Bool) (_S : List Bool) (a : Bool), a ∈ _S :=
  ⟨fun _ => [], [false], false, by decide⟩

theorem grow_closed : ∃ (_succ : Bool → List Bool) (_S : List Bool), Closed _succ _S :=
  ⟨fun _ => [], [false], by unfold Closed; decide⟩

theorem grow_grows : ∃ (_succ : Bool → List Bool) (_S : List Bool), ¬ Closed _succ _S :=
  ⟨fun _ => [true], [false], by unfold Closed; decide⟩

theorem grow_nodup : ∃ (_succ : Bool → List Bool) (_S : List Bool), _S.Nodup :=
  ⟨fun _ => [true], [false], by decide⟩

theorem grow_sub : ∃ (_succ : Bool → List Bool) (_S U : List Bool) (a : Bool),
    (∀ x, x ∈ _S → x ∈ U) ∧
    (∀ x, x ∈ U → ∀ y, y ∈ _succ x → y ∈ U) ∧ a ∈ grow _succ _S :=
  ⟨fun _ => [], [false], [false], false, by decide⟩

theorem iter_closed : ∃ (_succ : Bool → List Bool) (_S : List Bool) (_n : Nat), Closed _succ _S :=
  ⟨fun _ => [], [false], 2, by unfold Closed; decide⟩

theorem iter_superset : ∃ (_succ : Bool → List Bool) (_n : Nat) (_S : List Bool) (a : Bool), a ∈ _S :=
  ⟨fun _ => [], 2, [false], false, by decide⟩

theorem iter_nodup : ∃ (_succ : Bool → List Bool) (_n : Nat) (_S : List Bool), _S.Nodup :=
  ⟨fun _ => [], 2, [false], by decide⟩

theorem iter_sub : ∃ (_succ : Bool → List Bool) (U : List Bool) (_n : Nat) (_S : List Bool) (a : Bool),
    (∀ x, x ∈ U → ∀ y, y ∈ _succ x → y ∈ U) ∧
    (∀ x, x ∈ _S → x ∈ U) ∧ a ∈ iter _succ _n _S :=
  ⟨fun _ => [], [false], 2, [false], false, by decide⟩

theorem nodup_subset : ∃ (L U : List Bool), L.Nodup ∧ (∀ a, a ∈ L → a ∈ U) :=
  ⟨[false], [false], by decide⟩

theorem closed_reach : ∃ (_succ : Bool → List Bool) (T : List Bool) (a _b : Bool),
    Closed _succ T ∧ Reach _succ a _b ∧ a ∈ T :=
  ⟨fun _ => [], [false], false, false, by unfold Closed; decide, .refl false, by decide⟩

theorem iter_sound : ∃ (_succ : Bool → List Bool) (a : Bool) (_n : Nat) (_S : List Bool) (_b : Bool),
    (∀ c, c ∈ _S → Reach _succ a c) ∧ _b ∈ iter _succ _n _S := by
  refine ⟨fun _ => [], false, 2, [false], false, ?_, by decide⟩
  intro c hc
  have h : c = false := List.mem_singleton.mp hc
  subst c
  exact .refl false

theorem iter_complete : ∃ (_succ : Bool → List Bool) (U : List Bool) (a _b : Bool),
    (∀ x, x ∈ U → ∀ y, y ∈ _succ x → y ∈ U) ∧ a ∈ U ∧ Reach _succ a _b :=
  ⟨fun _ => [], [false], false, false, by decide, by decide, .refl false⟩

theorem mem_reachable : ∃ (_succ : Bool → List Bool) (U : List Bool) (a _b : Bool),
    (∀ x, x ∈ U → ∀ y, y ∈ _succ x → y ∈ U) ∧ a ∈ U :=
  ⟨fun _ => [], [false], false, true, by decide, by decide⟩

-- These two frozen theorems have global carrier/equality data, but no
-- proposition premises. Retain all their remaining inputs explicitly.
theorem foldl_length : ∃ (_ys _S : List Bool), True :=
  ⟨[true], [false], True.intro⟩

theorem iter_closed_or_long : ∃ (_succ : Bool → List Bool) (_n : Nat) (_S : List Bool), True :=
  ⟨fun _ => [true], 2, [false], True.intro⟩

end H62.AuditTyping.ClosureWitnesses
