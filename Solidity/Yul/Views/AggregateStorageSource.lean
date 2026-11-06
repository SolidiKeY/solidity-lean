import Solidity.Yul.Views.AggregateStorageSnapshot

namespace Solidity.Yul.Views

/-- Actual effectful source application of the computed canonical snapshot.
Successful preparation is distinct from Source's static/error result. This
component does not claim live-only ownership closes retained storage aliases. -/
def aggregateApplySnapshot? {E τ b Γ} (F : Source.Fr) (d : AggregateStorageDeclaration E τ b)
    (fixed : Roadmap.Evm.Fixed) (p : Source.SPath) (cursor : Nat) (m : SlotView)
    (s : Source.EMState E Γ) : Option (Except Source.Halt Unit × Source.EMState E Γ) :=
  if E.transientRoot p then none else do
   let computed ← d.collect fixed p F.this (aggregateRawLengths m) cursor
   if packedSeparationCheck computed.1 then
     (finiteAccountWrite? (T := E.lay) F.this computed.1 m).map (fun op => (Source.applyOp F op).run s)
   else none

theorem aggregateApply_static {E τ b Γ} (F : Source.Fr) (d : AggregateStorageDeclaration E τ b)
    (fixed p cursor m) (s : Source.EMState E Γ) (result)
    (step : aggregateApplySnapshot? F d fixed p cursor m s = some result) (static : F.static=true) :
    result = (.error (.revert []),s) := by
  unfold aggregateApplySnapshot? at step
  split at step
  · cases step
  ·
    cases computed : d.collect fixed p F.this (aggregateRawLengths m) cursor with
    | none => simp only [computed,Bind.bind,Option.bind] at step; cases step
    | some pair =>
      simp only [computed,Bind.bind,Option.bind] at step
      split at step
      · obtain ⟨op,_,same⟩ := Option.map_eq_some_iff.mp step
        rw [actualApplyOp_run,static] at same
        exact same.symm
      · cases step

theorem aggregateApply_MemOK {E τ b Γ} (F : Source.Fr) (d : AggregateStorageDeclaration E τ b)
    (fixed p cursor m) (s : Source.EMState E Γ) (result)
    (step : aggregateApplySnapshot? F d fixed p cursor m s = some result)
    (H : Source.HeapTy) (ok : Source.MemOK E H s) : Source.MemOK E H result.2 := by
  unfold aggregateApplySnapshot? at step
  split at step
  · cases step
  ·
    cases computed : d.collect fixed p F.this (aggregateRawLengths m) cursor with
    | none => simp only [computed,Bind.bind,Option.bind] at step; cases step
    | some pair =>
      simp only [computed,Bind.bind,Option.bind] at step
      split at step
      · obtain ⟨op,_,same⟩ := Option.map_eq_some_iff.mp step
        rw [actualApplyOp_run] at same
        cases static : F.static
        · rw [static] at same
          cases same
          exact ⟨⟨⟨ok.1.1.heap,ok.1.1.le⟩,ok.1.2⟩,ok.2.1,ok.2.2⟩
        · rw [static] at same
          cases same
          exact ok
      · cases step

theorem aggregateApply_view {E τ b Γ} (F : Source.Fr) (d : AggregateStorageDeclaration E τ b)
    (fixed p cursor m) (s out : Source.EMState E Γ) (cs stop)
    (computed : d.collect fixed p F.this (aggregateRawLengths m) cursor = some (cs,stop))
    (step : aggregateApplySnapshot? F d fixed p cursor m s = some (.ok (),out))
    (static : F.static=false) : finiteView cs (out.2.ex.world.accounts F.this).storage m := by
  unfold aggregateApplySnapshot? at step
  split at step
  · cases step
  ·
    rw [computed] at step
    dsimp only [Bind.bind,Option.bind] at step
    split at step
    · rename_i checked
      obtain ⟨op,prepared,same⟩ := Option.map_eq_some_iff.mp step
      rw [actualApplyOp_run,static] at same
      have state := congrArg Prod.snd same
      cases state
      exact finiteAccountWrite_view F.this _ m s.2.ex op ((packedSeparationCheck_iff _).mp checked) prepared
    · cases step

end Solidity.Yul.Views
