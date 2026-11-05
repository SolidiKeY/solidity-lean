import Solidity.Backend.PrimitivePackets.UnsignedDiv.SourceOrigin
import Solidity.Backend.PrimitivePackets.UnsignedDiv.Execution

/-! Local operand correspondence with independently executed Source and actual
public-compiler execution. This is not whole Source/model state agreement,
source admission, gas/fetched-bytecode correspondence, or ABI realization. -/
namespace Solidity.Backend.PrimitivePackets.UnsignedDiv

variable {C : Contract} {Γ : Solidity.Ctx} {E : Source.Env} {Δ : Source.RCtx}
  {b L frame : Nat} {F : Evm.Frag (modelContext Γ)}
  {σ : State C (modelContext Γ)} {base : Nat → Fin Evm.W} {m : Evm.Machine}

theorem division_packet (input : Evm.Memory.StateRepr L b frame F σ base m)
    (G : Source.Glob E) (fr : Source.Fr) (n : Nat)
    (tail : Source.Locals E.layout Δ) (s : Source.St E)
    (hd : σ.env.2.1.val ≠ 0) :
    Evm.Memory.compileVal b F (modelDiv C Γ) = some (selectedDiv b F) ∧
    ∃ v : Uint, ∃ w, v.val = σ.env.1.val.tdiv σ.env.2.1.val ∧
      (Source.evalE G fr (n + 3) (sourceDiv E Δ)).run
          (sourceLocals σ.env.1 σ.env.2.1 tail, s) =
        (.ok (.val (sourceUInt E.layout v)), (sourceLocals σ.env.1 σ.env.2.1 tail, s)) ∧
      Evm.ReprV .uint v w ∧
      Evm.run (selectedDiv (C := C) b F).code m = .ok (m.push w) 0 := by
  obtain ⟨hc, v, w, hv, hw, ho⟩ := selected_div_execution input hd
  refine ⟨hc, v, w, hv, ?_, hw, ho⟩
  rw [source_div_origin, source_div_result E.layout fr.checked _ _ v hd hv]
  rfl

theorem remainder_packet (input : Evm.Memory.StateRepr L b frame F σ base m)
    (G : Source.Glob E) (fr : Source.Fr) (n : Nat)
    (tail : Source.Locals E.layout Δ) (s : Source.St E)
    (hd : σ.env.2.1.val ≠ 0) :
    Evm.Memory.compileVal b F (modelMod C Γ) = some (selectedMod b F) ∧
    ∃ v : Uint, ∃ w, v.val = σ.env.1.val.tmod σ.env.2.1.val ∧
      (Source.evalE G fr (n + 3) (sourceMod E Δ)).run
          (sourceLocals σ.env.1 σ.env.2.1 tail, s) =
        (.ok (.val (sourceUInt E.layout v)), (sourceLocals σ.env.1 σ.env.2.1 tail, s)) ∧
      Evm.ReprV .uint v w ∧
      Evm.run (selectedMod (C := C) b F).code m = .ok (m.push w) 0 := by
  obtain ⟨hc, v, w, hv, hw, ho⟩ := selected_mod_execution input hd
  refine ⟨hc, v, w, hv, ?_, hw, ho⟩
  rw [source_mod_origin, source_mod_result E.layout fr.checked _ _ v hd hv]
  rfl

/-- Source retains the exact panic payload and original complete state. The
symbolic target exposes only its existing coarse revert constructor. -/
theorem division_zero_packet (input : Evm.Memory.StateRepr L b frame F σ base m)
    (G : Source.Glob E) (fr : Source.Fr) (n : Nat)
    (tail : Source.Locals E.layout Δ) (s : Source.St E)
    (hd : σ.env.2.1.val = 0) :
    (Source.evalE G fr (n + 3) (sourceDiv E Δ)).run
        (sourceLocals σ.env.1 σ.env.2.1 tail, s) =
      (.error (.revert (Source.panicData .divZero)),
        (sourceLocals σ.env.1 σ.env.2.1 tail, s)) ∧
    Evm.Memory.compileVal b F (modelDiv C Γ) = some (selectedDiv b F) ∧
    Evm.run (selectedDiv (C := C) b F).code m = .revert := by
  refine ⟨?_, selected_div_zero input hd⟩
  rw [source_div_origin]
  simp only [Source.intBin, hd, if_true, Source.panic, Except.map]

theorem remainder_zero_packet (input : Evm.Memory.StateRepr L b frame F σ base m)
    (G : Source.Glob E) (fr : Source.Fr) (n : Nat)
    (tail : Source.Locals E.layout Δ) (s : Source.St E)
    (hd : σ.env.2.1.val = 0) :
    (Source.evalE G fr (n + 3) (sourceMod E Δ)).run
        (sourceLocals σ.env.1 σ.env.2.1 tail, s) =
      (.error (.revert (Source.panicData .divZero)),
        (sourceLocals σ.env.1 σ.env.2.1 tail, s)) ∧
    Evm.Memory.compileVal b F (modelMod C Γ) = some (selectedMod b F) ∧
    Evm.run (selectedMod (C := C) b F).code m = .revert := by
  refine ⟨?_, selected_mod_zero input hd⟩
  rw [source_mod_origin]
  simp only [Source.intBin, hd, if_true, Source.panic, Except.map]

end Solidity.Backend.PrimitivePackets.UnsignedDiv
