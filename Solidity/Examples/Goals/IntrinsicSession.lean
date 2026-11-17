import Solidity.Goals.IntrinsicSession

/-! Pin and controls for the intrinsic-session plan goal. -/

namespace Solidity.Goals

/--
info: open Solidity.Goals.intrinsicSessionSemantics ← Solidity.Semantics.IntrinsicSession.session_semantics_correct plan is0-intrinsic-session
-/
#guard_msgs in
#roadmap_goal intrinsicSessionSemantics

/-! The intrinsic session laws refuse a candidate that never observes an event:
a resumed session whose first action is a credit must show it. -/
namespace IntrinsicSession

open Solidity.Roadmap

/-- The code of an empty compilation. -/
def noCode : Code where
  contracts := []
  main := 0
  roles := fun k => k.elim0
  ctor := fun k => k.elim0
  entry := fun k => k.elim0

/-- An allowed environment whose every action is a credit. -/
def crediting : SessionEnv where
  deployer := Address.zero
  deployNonce := ⟨0, by decide⟩
  deployValue := ⟨0, by decide⟩
  deployArgs := []
  balance := fun _ => ⟨0, by decide⟩
  hasCode := fun _ _ => false
  requests := fun _ _ => some (.credit Address.zero ⟨1, by decide⟩)
  callee := fun _ => .answer (.success [])

example : crediting.Allowed := ⟨fun _ => rfl, fun _ _ _ => rfl, fun _ _ _ _ _ _ => rfl⟩

/-- A candidate without events is refused, whatever its view. -/
example (F : Fixed) (I : IntrinsicSpec) (V : View I)
    (silent : ∀ p e r, (I.lang.sem p e r).events = []) : ¬ Laws F I V := by
  intro laws
  have allowed : I.lang.Allowed (I.ofSession crediting) := by
    rw [I.allowed_iff, I.session_of]
    exact ⟨fun _ => rfl, fun _ _ _ => rfl, fun _ _ _ _ _ _ => rfl⟩
  let start : TypedWorld :=
    ⟨noCode, ContractWorld.World.empty noCode.catalog (funds crediting.balance) noCode.roles⟩
  obtain ⟨r, _, shown⟩ := (laws.credited (V.resume start) (I.ofSession crediting) [] 0
    noCode start.world Address.zero ⟨1, by decide⟩ allowed (laws.starts start _ allowed)
    (by rw [I.session_of]; rfl)).1
  rw [silent] at shown
  exact absurd (List.prefix_nil.mp shown) (by simp)

/-- A resource-failure classification that admits no bound is refused. -/
example (F : Fixed) (I : IntrinsicSpec) (V : View I) (never : ∀ r, ¬ I.NoFail r) :
    ¬ Laws F I V := by
  intro laws
  have allowed : I.lang.Allowed (I.ofSession crediting) := by
    rw [I.allowed_iff, I.session_of]
    exact ⟨fun _ => rfl, fun _ _ _ => rfl, fun _ _ _ _ _ _ => rfl⟩
  let start : TypedWorld :=
    ⟨noCode, ContractWorld.World.empty noCode.catalog (funds crediting.balance) noCode.roles⟩
  obtain ⟨r, good, _⟩ := laws.boundary_observed _ _ _ _ _ (laws.starts start _ allowed)
  exact never r good.2

end IntrinsicSession

end Solidity.Goals
