import SolidityBridge.RoadmapV15.P10.Modular
import SolidityBridge.ExternalEvm.Power

/-! EXP consumes the published reference modular-power theorem. Actual dynamic
C' and complete fetched State/X behavior are retained; no source origin assumed. -/
namespace SolidityBridge.RoadmapV15.P10
open Solidity Solidity.Backend EvmYul Solidity.Evm.External

open scoped Fin.CommRing in
theorem power_word (a b : Scalar.Word) :
    UInt256.exp ⟨a.toFin⟩ ⟨b.toFin⟩ = ⟨(BitVec.ofNat 256 (a.toNat ^ b.toNat)).toFin⟩ := by
  change UInt256.mk (UInt256.exp ⟨a.toFin⟩ ⟨b.toFin⟩).val = _
  apply congrArg UInt256.mk
  rw [reference_pow]
  have ha : (a.toNat : Fin UInt256.size) = a.toFin := Fin.ofNat_val_eq_self a.toFin
  rw [←ha,←Nat.cast_pow]
  rfl

private theorem site_byte (site : Site .EXP) :
    site.state.executionEnv.code.get? (Backend.encode site.before).length = some Backend.Op.EXP.code := by
  change (Backend.encode (site.before ++ .op .EXP :: site.after)).toArray[(Backend.encode site.before).length]? = _
  rw [List.getElem?_toArray]
  simp only [Backend.encode_append,Backend.encode_cons,Instr.encode,List.singleton_append]
  rw [List.getElem?_append_right (Nat.le_refl _)]
  simp only [Nat.sub_self,List.getElem?_cons_zero]

theorem decode_exp (site : Site .EXP) :
    EVM.decode site.state.executionEnv.code site.state.pc = some (.EXP,none) := by
  have byte := site_byte site
  simp only [EVM.decode,Site.pc_nat,byte]
  rfl

/-- The pinned exponent-byte gas formula, not an approved source resource model. -/
theorem power_cost (site : Site .EXP) (a b : Scalar.Word) (tail : Scalar.Stack) :
    EVM.C' (modularSite site (a::b::tail)).state .EXP =
      if UInt256.eq0 ⟨b.toFin⟩ then 10 else 10+50*(1+Nat.log 256 b.toNat) := by rfl

/-- Every intrinsic256-bit exponent has at most32 charged bytes in this pin. -/
theorem power_cost_bound (site : Site .EXP) (a b : Scalar.Word) (tail : Scalar.Stack) :
    EVM.C' (modularSite site (a::b::tail)).state .EXP ≤ 1610 := by
  have logBound : Nat.log 256 b.toNat ≤ 31 := by
    by_cases zero : b.toNat = 0
    · rw [zero,Nat.log_zero_right]
      decide
    · have bound : b.toNat < 256^32 := by
        change b.toNat < 2^256
        exact b.isLt
      have short : Nat.log 256 b.toNat < 32 :=
        (Nat.log_lt_iff_lt_pow (by decide : 1 < 256) zero).2 bound
      omega
  rw [power_cost]
  split <;> omega

private theorem power_gate (s : EVM.State)
    (gas : EVM.C' s .EXP ≤ s.gasAvailable.toNat)
    (arity : 2 ≤ s.stack.length) (capacity : s.stack.length-2+1 ≤ 1024) :
    Assembly.driverGate #[] s .EXP = .ok (s,EVM.C' s .EXP) := by
  have expansion : EVM.memoryExpansionCost s .EXP = 0 := by
    simp only [EVM.memoryExpansionCost,EVM.memoryExpansionCost.μᵢ',Nat.sub_self]
  have charge : s.gasAvailable-UInt256.ofNat 0 = s.gasAvailable := by
    change UInt256.mk (s.gasAvailable.val-0) = s.gasAvailable
    rw [sub_zero]
  have low : ¬s.gasAvailable.toNat < 0 := Nat.not_lt_zero _
  simp only [Assembly.driverGate]
  rw [expansion,charge]
  simp only [EVM.δ,EVM.α,Option.getD_some]
  simp only [if_neg low,if_neg (Nat.not_lt_of_ge gas),if_neg (Nat.not_lt_of_ge arity),if_neg (Nat.not_lt_of_ge capacity)]
  cases perm : s.executionEnv.perm <;> rfl

/-- Actual scalar/fetched/X agreement. The resource premise is the real C'
cost on this exact input stack, not a gate or desired-run certificate. -/
theorem power_agreement (site : Site .EXP) (a b : Scalar.Word) (tail : Scalar.Stack)
    (room : tail.length+2 ≤ 1024)
    (gas : EVM.C' (modularSite site (a::b::tail)).state .EXP ≤ site.seed.gasAvailable.toNat)
    (fuel : Nat) :
    let input := (modularSite site (a::b::tail)).state
    let cost := EVM.C' input .EXP
    let next := (Assembly.chargedPrepare input cost).replaceStackAndIncrPC
      ((BitVec.ofNat 256 (a.toNat ^ b.toNat)::tail).map (fun w => UInt256.mk w.toFin))
    Scalar.step (.op .EXP) (a::b::tail) = some (BitVec.ofNat 256 (a.toNat ^ b.toNat)::tail) ∧
      Assembly.driverSteps 1 (fuel+2) #[] input = .ok next ∧
      EVM.X (fuel+2) #[] input = EVM.X (fuel+1) #[] next := by
  dsimp only
  refine ⟨rfl,?_⟩
  let input := (modularSite site (a::b::tail)).state
  let cost := EVM.C' input .EXP
  have gate : Assembly.driverGate #[] input .EXP = .ok (input,cost) := by
    apply power_gate
    · exact gas
    · change 2 ≤ ((a::b::tail).map (fun w => UInt256.mk w.toFin)).length
      simp only [List.length_map,List.length_cons]; omega
    · change ((a::b::tail).map (fun w => UInt256.mk w.toFin)).length-2+1 ≤ 1024
      simp only [List.length_map,List.length_cons]; omega
  have step : EVM.step (fuel+1) cost (some (.EXP,none)) input =
      .ok ((Assembly.chargedPrepare input cost).replaceStackAndIncrPC
        ((BitVec.ofNat 256 (a.toNat ^ b.toNat)::tail).map (fun w => UInt256.mk w.toFin))) := by
    have word := power_word a b
    simp only [input,modularSite,Site.state,List.map_cons]
    rw [←word]
    rfl
  constructor
  · simp only [Assembly.driverSteps]
    rw [decode_exp (modularSite site (a::b::tail))]
    dsimp only [Option.option,bind,Except.bind]
    rw [gate]
    dsimp only
    rw [step]
  · exact Assembly.X_continue fuel #[] input input _ (.EXP,none) cost
      (decode_exp _) gate step (by unfold Assembly.NonhaltingOpcode; decide)

/-- Uniform adequate primitive budget, discharged from the intrinsic word bound.
This is not a source compiler or whole-program resource certificate. -/
theorem power_uniform_agreement (site : Site .EXP) (a b : Scalar.Word) (tail : Scalar.Stack)
    (room : tail.length+2 ≤ 1024) (gas : 1610 ≤ site.seed.gasAvailable.toNat) (fuel : Nat) :
    let input := (modularSite site (a::b::tail)).state
    let cost := EVM.C' input .EXP
    let next := (Assembly.chargedPrepare input cost).replaceStackAndIncrPC
      ((BitVec.ofNat 256 (a.toNat ^ b.toNat)::tail).map (fun w => UInt256.mk w.toFin))
    Scalar.step (.op .EXP) (a::b::tail) = some (BitVec.ofNat 256 (a.toNat ^ b.toNat)::tail) ∧
      Assembly.driverSteps 1 (fuel+2) #[] input = .ok next ∧
      EVM.X (fuel+2) #[] input = EVM.X (fuel+1) #[] next :=
  power_agreement site a b tail room (Nat.le_trans (power_cost_bound site a b tail) gas) fuel

/-- Exact counted fetched-prefix composition; errors and all State fields flow
through the existing driver. This does not make terminal opcodes nonhalting. -/
theorem fetched_steps_cons (n fuel : Nat) (valid : Array UInt256) (s : EVM.State) :
    Assembly.driverSteps (n+1) (fuel+2) valid s =
      (Assembly.driverSteps 1 (fuel+2) valid s).bind
        (fun next => Assembly.driverSteps n (fuel+1) valid next) := by
  simp only [Assembly.driverSteps]
  cases decoded : EVM.decode s.executionEnv.code s.pc with
  | none => rfl
  | some packet =>
    dsimp only [Option.option,bind,Except.bind]
    cases gate : Assembly.driverGate valid s packet.1 with
    | error error => rfl
    | ok pair =>
      dsimp only [bind,Except.bind]
      cases step : EVM.step (fuel+1) pair.2 (some packet) pair.1 <;> rfl

#print axioms power_word
#print axioms decode_exp
#print axioms power_cost
#print axioms power_cost_bound
#print axioms power_agreement
#print axioms power_uniform_agreement
#print axioms fetched_steps_cons
end SolidityBridge.RoadmapV15.P10
