import Solidity.Backend.PrimitivePackets.UnsignedDiv.Numeric
import Solidity.Backend.PrimitivePackets.UnsignedDiv.Selection

/-! Public selection and actual execution from the operand locals. The only
machine correspondence premise is the existing initial StateRepr; no compiled
value, chosen result, or desired run is supplied. -/
namespace Solidity.Backend.PrimitivePackets.UnsignedDiv

variable {C : Contract} {Γ : Solidity.Ctx} {b L frame : Nat}
  {F : Evm.Frag (modelContext Γ)} {σ : State C (modelContext Γ)}
  {base : Nat → Fin Evm.W} {m : Evm.Machine}

theorem div_eval : (modelDiv C Γ).evalT σ =
    TRes.ofOpt (BinOp.div.evalT rfl σ.env.1 σ.env.2.1) := by
  rfl

theorem mod_eval : (modelMod C Γ).evalT σ =
    TRes.ofOpt (BinOp.mod.evalT rfl σ.env.1 σ.env.2.1) := by
  rfl

private theorem successful_word {v : Uint} {out : Evm.Out}
    (h : Evm.ValOutT .uint (.ok v) out m) :
    ∃ w, Evm.ReprV .uint v w ∧ out = .ok (m.push w) 0 := by
  rcases h with ⟨v', w, hv, hw, ho⟩ | ⟨he, _⟩
  · cases hv
    exact ⟨w, hw, ho⟩
  · cases he

private theorem refused_word {out : Evm.Out}
    (h : Evm.ValOutT .uint (.error .revert) out m) : out = .revert := by
  rcases h with ⟨_, _, he, _⟩ | ⟨_, ho⟩
  · cases he
  · exact ho

theorem selected_div_execution (input : Evm.Memory.StateRepr L b frame F σ base m)
    (hd : σ.env.2.1.val ≠ 0) :
    Evm.Memory.compileVal b F (modelDiv C Γ) = some (selectedDiv b F) ∧
    ∃ v : Uint, ∃ w, v.val = σ.env.1.val.tdiv σ.env.2.1.val ∧
      Evm.ReprV .uint v w ∧
      Evm.run (selectedDiv (C := C) b F).code m = .ok (m.push w) 0 := by
  obtain ⟨v, hv, hn⟩ := div_result σ.env.1 σ.env.2.1 hd
  have hc : Evm.ValOutT .uint ((modelDiv C Γ).evalT σ)
      (Evm.run (selectedDiv (C := C) b F).code m) m :=
    (selectedDiv (C := C) b F).cert.correct input
  rw [div_eval, hv] at hc
  obtain ⟨w, hw, ho⟩ := successful_word hc
  exact ⟨select_div b F, v, w, hn, hw, ho⟩

theorem selected_mod_execution (input : Evm.Memory.StateRepr L b frame F σ base m)
    (hd : σ.env.2.1.val ≠ 0) :
    Evm.Memory.compileVal b F (modelMod C Γ) = some (selectedMod b F) ∧
    ∃ v : Uint, ∃ w, v.val = σ.env.1.val.tmod σ.env.2.1.val ∧
      Evm.ReprV .uint v w ∧
      Evm.run (selectedMod (C := C) b F).code m = .ok (m.push w) 0 := by
  obtain ⟨v, hv, hn⟩ := mod_result σ.env.1 σ.env.2.1 hd
  have hc : Evm.ValOutT .uint ((modelMod C Γ).evalT σ)
      (Evm.run (selectedMod (C := C) b F).code m) m :=
    (selectedMod (C := C) b F).cert.correct input
  rw [mod_eval, hv] at hc
  obtain ⟨w, hw, ho⟩ := successful_word hc
  exact ⟨select_mod b F, v, w, hn, hw, ho⟩

theorem selected_div_zero (input : Evm.Memory.StateRepr L b frame F σ base m)
    (hd : σ.env.2.1.val = 0) :
    Evm.Memory.compileVal b F (modelDiv C Γ) = some (selectedDiv b F) ∧
    Evm.run (selectedDiv (C := C) b F).code m = .revert := by
  have hc : Evm.ValOutT .uint ((modelDiv C Γ).evalT σ)
      (Evm.run (selectedDiv (C := C) b F).code m) m :=
    (selectedDiv (C := C) b F).cert.correct input
  rw [div_eval] at hc
  simp only [BinOp.evalT, BinOp.evalNum, BinOp.arithInt, hd, if_true,
    TRes.ofOpt] at hc
  exact ⟨select_div b F, refused_word hc⟩

theorem selected_mod_zero (input : Evm.Memory.StateRepr L b frame F σ base m)
    (hd : σ.env.2.1.val = 0) :
    Evm.Memory.compileVal b F (modelMod C Γ) = some (selectedMod b F) ∧
    Evm.run (selectedMod (C := C) b F).code m = .revert := by
  have hc : Evm.ValOutT .uint ((modelMod C Γ).evalT σ)
      (Evm.run (selectedMod (C := C) b F).code m) m :=
    (selectedMod (C := C) b F).cert.correct input
  rw [mod_eval] at hc
  simp only [BinOp.evalT, BinOp.evalNum, BinOp.arithInt, hd, if_true,
    TRes.ofOpt] at hc
  exact ⟨select_mod b F, refused_word hc⟩

end Solidity.Backend.PrimitivePackets.UnsignedDiv
