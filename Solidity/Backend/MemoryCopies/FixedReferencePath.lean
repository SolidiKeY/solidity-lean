import Solidity.Backend.MemoryCopies.FixedReferencePathInterface

/-! Existing path simulation selects the actual shadowful source; live
normalization then transports its representation without rewriting storage. -/
namespace Solidity.Backend.MemoryCopies
open Evm Evm.Memory

theorem fixed_reference_path_select {C : Contract} {Γ : Ctx} {primitive : PrimTy} {count L b : Nat} {frag : Frag Γ}
    (state : State C Γ) (machine : Machine)
    (path : SPath C Γ (.ref (.fixed (.ref (.array (.prim primitive))) count)))
    (reference : SRef C (.ref (.fixed (.ref (.array (.prim primitive))) count)))
    (value : SVal (.ref (.fixed (.ref (.array (.prim primitive))) count)))
    (represented : Sim C L b frag state machine) (supported : spathIn frag false path = true)
    (resolved : path.resolveT state = .ok reference) (found : state.storage.find reference = some value) :
    FixedReferencePathResult L b machine path value := by
  rcases spath_sim path represented supported with
    ⟨actual,source,selected,resolution,live,_,sourceRepr,pathRun⟩ | ⟨refused,_⟩
  · rw [resolved] at resolution
    cases resolution
    have observed : state.storage.find reference = some selected := Sto.find_of_findLive live
    rw [found] at observed
    cases observed
    exact ⟨source,pathRun,sourceRepr,
      fixed_reference_live_representation value machine.store L source sourceRepr⟩
  · rw [resolved] at refused
    cases refused

def fixedReferencePath : FixedReferencePathCertificate := ⟨fixed_reference_path_select⟩

/--
info: 'Solidity.Backend.MemoryCopies.fixed_reference_path_select' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms fixed_reference_path_select
/--
info: 'Solidity.Backend.MemoryCopies.fixedReferencePath' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms fixedReferencePath
end Solidity.Backend.MemoryCopies
