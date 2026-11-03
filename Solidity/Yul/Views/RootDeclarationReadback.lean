import Solidity.Yul.Views.RootDeclarationIdentityControls

namespace Solidity.Yul.Views

/-- Real data/view premise for the helper; concrete source-state instances
below derive it from actual snapshot execution, not assumed read adequacy. -/
theorem CheckedRootDeclarations.readCell_view {E ds d scope tr a origin Γ}
    (r : @CheckedRootDeclarations E ds d scope tr a origin) (F : Source.Fr) (s : Source.EMState E Γ)
    (m : SlotView)
    (view : finiteView r.registrations
      (if tr then s.2.ex.transient.cells F.this else (s.2.ex.world.accounts F.this).storage) m)
    (c : ScalarPath E.layout (E.lay a)) (member : c ∈ r.registrations) :
    ∃ v, (Source.readCell (E := E) F c.path).run s = (.ok v,s) ∧ c.codec.encode v = c.field.findWord (m c.slot) := by
  obtain ⟨v,read,encoded⟩ := Option.map_eq_some_iff.mp (view c member)
  refine ⟨v,?_,encoded⟩
  have stateRead : (Source.EM.st (E := E) (Γ := Γ)).run s = (.ok s.2,s) := by rfl
  unfold Source.readCell
  rw [Source.Hoare.run_bind,stateRead]
  dsimp only
  rw [r.bank_agreement c member]
  cases tr with
  | false =>
    change (s.2.ex.world.accounts F.this).storage.read c.path = some v at read
    simp only [Bool.false_eq_true,if_false,read]
    rfl
  | true =>
    change (s.2.ex.transient.cells F.this).read c.path = some v at read
    simp only [if_true,read]
    rfl

end Solidity.Yul.Views

namespace Solidity.Yul.Views.Controls

theorem root_all_actual_source_readback (c : ScalarPath rootEnv.layout (rootEnv.lay account))
    (member : c ∈ rootChecked.registrations) :
    ∃ v, (Source.readCell (E := rootEnv) packedStepFrame c.path).run rootFrame6.1.2 = (.ok v,rootFrame6.1.2) ∧
      c.codec.encode v = c.field.findWord (rootSnapshot c.slot) := by
  apply rootChecked.readCell_view packedStepFrame rootFrame6.1.2 rootSnapshot _ c member
  exact finiteEncode_view rootChecked.registrations _ rootStore.2 rootSnapshot rootChecked.separated root_actual_full_reencode

theorem root_actual_transient_view : finiteView rootTempChecked.registrations
    (rootTempFrame.1.2.2.ex.transient.cells account) (fun _ => rootTempRaw) := by
  exact (finiteViewBool_iff _ _ _).mp (by decide)

theorem root_all_actual_transient_readback (c : ScalarPath rootEnv.layout (rootEnv.lay account))
    (member : c ∈ rootTempChecked.registrations) :
    ∃ v, (Source.readCell (E := rootEnv) packedStepFrame c.path).run rootTempFrame.1.2 = (.ok v,rootTempFrame.1.2) ∧
      c.codec.encode v = c.field.findWord rootTempRaw :=
  rootTempChecked.readCell_view packedStepFrame rootTempFrame.1.2 (fun _ => rootTempRaw) root_actual_transient_view c member

end Solidity.Yul.Views.Controls
