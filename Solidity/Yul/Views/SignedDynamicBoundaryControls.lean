import Solidity.Yul.Views.SignedDynamicMixedControls

namespace Solidity.Yul.Views.Controls

theorem sd_read_live (i : Nat) (bound : i<18) :
    (Source.readLoc (E := sdEnv) packedStepFrame (Source.Loc.stor (τ := .int sdI16) ⟨sdName "xs",[.index i]⟩)).run sdAliases =
      (.ok ((sdX.element_type i) ▸ sdX.elementValue sdFixed account i (sdRaw18 (sdX.element sdFixed account i).slot)),sdAliases) := by
  have member : sdX.element sdFixed account i ∈ sdRegrow.next := by
    change _ ∈ sdLayout.integerSnapshot sdFixed sdRegrow.nextRaw
    rw [sd_regrow_next]
    exact sdLayout.integer_element_member sdFixed sdRaw18 sdXEntry i bound
  have view := sdRegrow.view rfl (sdX.element sdFixed account i) member
  have bank := sdLayout.integer_bank_agreement sdFixed sdRegrow.nextRaw _ member
  have read := sdX.read_element packedStepFrame sdAliases sdFixed i sdRegrow.nextRaw bank view
  rw [sd_regrow_next] at read
  exact read

theorem sd_source_min16 :
    (Source.readLoc (E := sdEnv) packedStepFrame (Source.Loc.stor (τ := .int sdI16) ⟨sdName "xs",[.index 0]⟩)).run sdAliases =
      (.ok (.int (-32768) (by decide)),sdAliases) := sd_read_live 0 (by decide)

theorem sd_source_max16 :
    (Source.readLoc (E := sdEnv) packedStepFrame (Source.Loc.stor (τ := .int sdI16) ⟨sdName "xs",[.index 1]⟩)).run sdAliases =
      (.ok (.int 32767 (by decide)),sdAliases) := sd_read_live 1 (by decide)

theorem sd_source_minus_one16 :
    (Source.readLoc (E := sdEnv) packedStepFrame (Source.Loc.stor (τ := .int sdI16) ⟨sdName "xs",[.index 2]⟩)).run sdAliases =
      (.ok (.int (-1) (by decide)),sdAliases) := sd_read_live 2 (by decide)

theorem sd_source_zero16 :
    (Source.readLoc (E := sdEnv) packedStepFrame (Source.Loc.stor (τ := .int sdI16) ⟨sdName "xs",[.index 3]⟩)).run sdAliases =
      (.ok (.int 0 (by decide)),sdAliases) := sd_read_live 3 (by decide)

theorem sd_payload_sign_boundary : readIntPayload sdI16 32767 = 32767 ∧ readIntPayload sdI16 32768 = -32768 ∧
    readIntPayload sdI16 65535 = -1 ∧ intPayload sdI16 (-32768) = 32768 ∧ intPayload sdI16 (-1) = 65535 := by decide

/-- Old profiles remain intentionally unsigned; signed constructors are not
silently selected by them. The NEW integer trace contains both actual roots. -/
theorem sd_old_unsigned_trace_unchanged : sdLayout.unsignedTrace = [] := rfl

theorem sd_actual_signed_trace : sdLayout.integerTrace = [(sdName "xs",sdI16,0),(sdName "ys",sdI24,64)] := rfl

theorem sd_read_live24 (i : Nat) (bound : i<11) :
    (Source.readLoc (E := sdEnv) packedStepFrame (Source.Loc.stor (τ := .int sdI24) ⟨sdName "ys",[.index i]⟩)).run sdYFill.step.1.2 =
      (.ok ((sdY.element_type i) ▸ sdY.elementValue sdFixed account i (sdMixedRaw (sdY.element sdFixed account i).slot)),sdYFill.step.1.2) := by
  have member : sdY.element sdFixed account i ∈ sdYFill.next := by
    change _ ∈ sdLayout.integerSnapshot sdFixed sdYFill.nextRaw
    rw [sd_mixed_next]
    exact sdLayout.integer_element_member sdFixed sdMixedRaw sdYEntry i bound
  have view := sdYFill.view rfl (sdY.element sdFixed account i) member
  have bank := sdLayout.integer_bank_agreement sdFixed sdYFill.nextRaw _ member
  have read := sdY.read_element packedStepFrame sdYFill.step.1.2 sdFixed i sdYFill.nextRaw bank view
  rw [sd_mixed_next] at read
  exact read

theorem sd_source_max24 :
    (Source.readLoc (E := sdEnv) packedStepFrame (Source.Loc.stor (τ := .int sdI24) ⟨sdName "ys",[.index 1]⟩)).run sdYFill.step.1.2 =
      (.ok (.int 8388607 (by decide)),sdYFill.step.1.2) := sd_read_live24 1 (by decide)

theorem sd_source_minus_one24 :
    (Source.readLoc (E := sdEnv) packedStepFrame (Source.Loc.stor (τ := .int sdI24) ⟨sdName "ys",[.index 2]⟩)).run sdYFill.step.1.2 =
      (.ok (.int (-1) (by decide)),sdYFill.step.1.2) := sd_read_live24 2 (by decide)

theorem sd_source_zero24 :
    (Source.readLoc (E := sdEnv) packedStepFrame (Source.Loc.stor (τ := .int sdI24) ⟨sdName "ys",[.index 3]⟩)).run sdYFill.step.1.2 =
      (.ok (.int 0 (by decide)),sdYFill.step.1.2) := sd_read_live24 3 (by decide)

theorem sd_source_tail24 :
    (Source.readLoc (E := sdEnv) packedStepFrame (Source.Loc.stor (τ := .int sdI24) ⟨sdName "ys",[.index 10]⟩)).run sdYFill.step.1.2 =
      (.ok (.int (-1) (by decide)),sdYFill.step.1.2) := sd_read_live24 10 (by decide)

end Solidity.Yul.Views.Controls
