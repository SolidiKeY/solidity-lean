import Solidity.Yul.Views.Generic.Plan

namespace Solidity.Yul.Views.GenericFlow.Banks

variable {E : Source.Env} {Γ : Source.RCtx} {F : Source.Fr}
variable {interface : Generic.OwnershipInterface E Γ F} {layout : interface.Layout}
variable {fixed : Roadmap.Evm.Fixed} {written value : Roadmap.Word}
variable {s : Source.EMState E Γ} {r : ResidualJournal complementCarrierOwnership}
variable {check : List (ScalarPath E.layout (E.lay F.this)) → Bool}

/-- The actual source/journal projections, convertible to each legacy Frame.after. -/
abbrev after (p : Generic.OwnershipPlan F interface layout fixed written value s r check) :
    ResidualCompanion E.layout E.lay E.lay complementCarrierOwnership :=
  ⟨p.step.1.2.2.ex,p.step.2⟩

theorem endTx_reencode
    (p : Generic.OwnershipPlan F interface layout fixed written value s r check)
    (checked : packedSeparationCheck p.next = true) (static : F.static = false) :
    finiteEncode p.next ((companionEndTx (after p)).source.world.accounts F.this).storage
      (fun q => (companionEndTx (after p)).residual.cells (complementKey false F.this q)) = some p.nextRaw := by
  simpa only [companionEndTx, residualEndTx] using p.reencode checked static

theorem transient_unchanged
    (p : Generic.OwnershipPlan F interface layout fixed written value s r check) :
    (after p).source.transient = s.2.ex.transient := by
  unfold after
  cases static : F.static
  · obtain ⟨update,_,same⟩ := Option.map_eq_some_iff.mp p.prepared
    rw [p.nonstatic static,← same]
    rfl
  · rw [p.static static]

/-- Actual writeback equations determine whole-store identity. The inputs are
computed writeback results, not a desired store-preservation law field. -/
theorem same_word_store
    (p : Generic.OwnershipPlan F interface layout fixed written value s r check)
    (sameWord : p.raw written = value)
    (writeback : SlotView → Option (Source.Storage E.layout (E.lay F.this) × SlotView))
    (complement : SlotView)
    (unchanged : writeback p.raw = some ((s.2.ex.world.accounts F.this).storage,complement))
    (actual : writeback p.nextRaw = some (((after p).source.world.accounts F.this).storage,
      fun q => (after p).residual.cells (complementKey false F.this q))) :
    ((after p).source.world.accounts F.this).storage = (s.2.ex.world.accounts F.this).storage := by
  have rawSame : p.nextRaw = p.raw := by
    funext q
    by_cases same : q = written
    · subst q
      exact (find_saveSlot p.raw written value).trans sameWord.symm
    · exact find_saveSlot_other p.raw written q value same
  rw [rawSame] at actual
  exact congrArg Prod.fst (Option.some.inj (actual.symm.trans unchanged))

end Solidity.Yul.Views.GenericFlow.Banks
