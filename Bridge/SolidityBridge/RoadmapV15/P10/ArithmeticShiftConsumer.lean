import SolidityBridge.RoadmapV15.P10.SignedDivisionConsumer
import Solidity.Backend.Scalar.SignedShift

/-! SAR consumes actual pinned complement/shift and intrinsic BitVec laws.
Saturation avoids constructing an enormous power for an unbounded word count. -/
namespace SolidityBridge.RoadmapV15.P10
open Solidity Solidity.Backend EvmYul Solidity.Evm.External

open scoped Fin.CommRing in
private theorem complement_word (b : Scalar.Word) :
    UInt256.complement ⟨b.toFin⟩ = ⟨(~~~b).toFin⟩ := by
  change UInt256.mk (UInt256.complement ⟨b.toFin⟩).val = _
  apply congrArg UInt256.mk
  change (0-(b.toFin+1) : Fin (2^256)) = (~~~b).toFin
  rw [BitVec.not_eq_neg_add,BitVec.toFin_sub,BitVec.toFin_neg]
  change 0-(b.toFin+1) = -b.toFin-1
  rw [zero_sub,neg_add,sub_eq_add_neg]

private theorem logical_shift_word (a b : Scalar.Word) :
    UInt256.shiftRight ⟨b.toFin⟩ ⟨a.toFin⟩ = ⟨(b >>> a.toNat).toFin⟩ := by
  unfold UInt256.shiftRight
  by_cases count : a.toNat < 256
  · rw [if_neg (by change ¬a.toNat ≥ 256;omega)]
    apply congrArg UInt256.mk
    apply Fin.ext
    change (b.toNat >>> a.toNat) % 2^256 = (b >>> a.toNat).toNat
    rw [BitVec.toNat_ushiftRight,Nat.shiftRight_eq_div_pow]
    exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) b.isLt)
  · rw [if_pos (by change a.toNat ≥ 256;omega),BitVec.ushiftRight_eq_zero (by omega)]
    rfl

private theorem negative_word (b : Scalar.Word) :
    UInt256.sltBool ⟨b.toFin⟩ ⟨0⟩ = b.msb := by
  have reference := signed_lt_bool b.toFin (⟨0,Solidity.Evm.W_pos⟩ : Fin Solidity.Evm.W)
  change decide (Solidity.Evm.sgn b.toNat < 0) = UInt256.sltBool ⟨b.toFin⟩ ⟨0⟩ at reference
  rw [Scalar.sgn_word] at reference
  rw [←reference]
  cases msb : b.msb
  · have bound : 0 ≤ b.toInt := BitVec.toInt_nonneg_of_msb_false msb
    exact decide_eq_false (not_lt_of_ge bound)
  · have bound : b.toInt < 0 := BitVec.toInt_neg_of_msb_true msb
    exact decide_eq_true bound

/-- Exact reference word observation at every count, including saturation. -/
theorem sar_bitvec (a b : Scalar.Word) :
    UInt256.sar ⟨a.toFin⟩ ⟨b.toFin⟩ = ⟨(b.sshiftRight a.toNat).toFin⟩ := by
  change (if UInt256.sltBool ⟨b.toFin⟩ ⟨0⟩ then
    UInt256.complement (UInt256.shiftRight (UInt256.complement ⟨b.toFin⟩) ⟨a.toFin⟩)
    else UInt256.shiftRight ⟨b.toFin⟩ ⟨a.toFin⟩) = _
  rw [negative_word]
  cases msb : b.msb
  · simp only [Bool.false_eq_true,if_false]
    rw [logical_shift_word,BitVec.sshiftRight_eq_of_msb_false msb]
  · simp only [if_true]
    rw [complement_word,logical_shift_word,complement_word,BitVec.sshiftRight_eq_of_msb_true msb]

theorem sar_word (a b : Scalar.Word) :
    UInt256.sar ⟨a.toFin⟩ ⟨b.toFin⟩ =
      ⟨(if a.toNat < 256 then BitVec.ofInt 256 (b.toInt / (2^a.toNat : Int))
        else if b.toInt < 0 then BitVec.ofInt 256 (-1) else 0).toFin⟩ := by
  rw [sar_bitvec]
  by_cases count : a.toNat < 256
  · rw [if_pos count,BitVec.sshiftRight_eq,Int.shiftRight_eq_div_pow,Int.natCast_pow]
    rfl
  · rw [if_neg count]
    cases msb : b.msb
    · have bound : 0 ≤ b.toInt := BitVec.toInt_nonneg_of_msb_false msb
      rw [if_neg (by omega),BitVec.sshiftRight_eq_of_msb_false msb,
        BitVec.ushiftRight_eq_zero (by omega)]
      rfl
    · have bound : b.toInt < 0 := BitVec.toInt_neg_of_msb_true msb
      rw [if_pos bound,BitVec.sshiftRight_eq_of_msb_true msb,
        BitVec.ushiftRight_eq_zero (by omega)]
      rfl

private theorem shift_byte (site : Site .SAR) :
    site.state.executionEnv.code.get? (Backend.encode site.before).length = some Backend.Op.SAR.code := by
  change (Backend.encode (site.before ++ .op .SAR :: site.after)).toArray[(Backend.encode site.before).length]? = _
  rw [List.getElem?_toArray]
  simp only [Backend.encode_append,Backend.encode_cons,Instr.encode,List.singleton_append]
  rw [List.getElem?_append_right (Nat.le_refl _)]
  simp only [Nat.sub_self,List.getElem?_cons_zero]

theorem decode_sar (site : Site .SAR) :
    EVM.decode site.state.executionEnv.code site.state.pc = some (.SAR,none) := by
  have byte := shift_byte site
  simp only [EVM.decode,Site.pc_nat,byte]
  rfl

private theorem shift_gate (s : EVM.State) (gas : 3 ≤ s.gasAvailable.toNat)
    (enough : 2 ≤ s.stack.length) (room : s.stack.length-2+1 ≤ 1024) :
    Assembly.driverGate #[] s .SAR = .ok (s,3) := by
  have expansion : EVM.memoryExpansionCost s .SAR = 0 := by
    simp only [EVM.memoryExpansionCost,EVM.memoryExpansionCost.μᵢ',Nat.sub_self]
  have charge : s.gasAvailable-UInt256.ofNat 0 = s.gasAvailable := by
    change UInt256.mk (s.gasAvailable.val-0) = s.gasAvailable
    rw [sub_zero]
  simp only [Assembly.driverGate]
  rw [expansion,charge]
  have cost : EVM.C' s .SAR = 3 := rfl
  simp only [cost,EVM.δ,EVM.α,Option.getD_some,if_neg (Nat.not_lt_zero _),
    if_neg (Nat.not_lt_of_ge gas),if_neg (Nat.not_lt_of_ge enough),if_neg (Nat.not_lt_of_ge room)]
  cases s.executionEnv.perm <;> rfl

theorem sar_agreement (site : Site .SAR) (a b : Scalar.Word) (tail : Scalar.Stack)
    (room : tail.length+2 ≤ 1024) (gas : 3 ≤ site.seed.gasAvailable.toNat) (fuel : Nat) :
    let result := if a.toNat < 256 then BitVec.ofInt 256 (b.toInt / (2^a.toNat : Int))
      else if b.toInt < 0 then BitVec.ofInt 256 (-1) else 0
    let input := (modularSite site (a::b::tail)).state
    let next := (Assembly.chargedPrepare input 3).replaceStackAndIncrPC
      ((result::tail).map (fun w => UInt256.mk w.toFin))
    Scalar.step (.op .SAR) (a::b::tail) = some (result::tail) ∧
      Assembly.driverSteps 1 (fuel+2) #[] input = .ok next ∧
      EVM.X (fuel+2) #[] input = EVM.X (fuel+1) #[] next := by
  dsimp only
  refine ⟨rfl,?_⟩
  let input := (modularSite site (a::b::tail)).state
  have gate : Assembly.driverGate #[] input .SAR = .ok (input,3) := by
    apply shift_gate input gas
    · change 2 ≤ ((a::b::tail).map (fun w => UInt256.mk w.toFin)).length
      simp only [List.length_map,List.length_cons];omega
    · change ((a::b::tail).map (fun w => UInt256.mk w.toFin)).length-2+1 ≤ 1024
      simp only [List.length_map,List.length_cons];omega
  have step : EVM.step (fuel+1) 3 (some (.SAR,none)) input =
      .ok ((Assembly.chargedPrepare input 3).replaceStackAndIncrPC
        (((if a.toNat < 256 then BitVec.ofInt 256 (b.toInt / (2^a.toNat : Int))
          else if b.toInt < 0 then BitVec.ofInt 256 (-1) else 0)::tail).map (fun w => UInt256.mk w.toFin))) := by
    have word := sar_word a b
    simp only [input,modularSite,Site.state,List.map_cons]
    rw [←word]
    rfl
  constructor
  · simp only [Assembly.driverSteps]
    rw [decode_sar (modularSite site (a::b::tail))]
    dsimp only [Option.option,bind,Except.bind]
    rw [gate]
    dsimp only
    rw [step]
  · exact Assembly.X_continue fuel #[] input input _ (.SAR,none) 3
      (decode_sar _) gate step (by unfold Assembly.NonhaltingOpcode;decide)

#print axioms sar_bitvec
#print axioms sar_word
#print axioms decode_sar
#print axioms sar_agreement
end SolidityBridge.RoadmapV15.P10
