import SolidityBridge.RoadmapV15.P10.ExponentConsumer
import SolidityBridge.ExternalEvm.SignedOps
import Solidity.Backend.Scalar.SignedMul

/-! Signed division/remainder consumers of the published numeric proof.
No source exceptional-case policy is inferred from raw EVM zero/minimum wrap. -/
namespace SolidityBridge.RoadmapV15.P10
open Solidity Solidity.Backend EvmYul Solidity.Evm.External

private def firstValue : Solidity.Evm.Out → Nat
  | .ok m _ => match m.stack with | .val w::_ => w.val | _ => 0
  | _ => 0

private theorem zero_word (b : Scalar.Word) : (b == 0) = decide (b.toNat = 0) := by
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq,decide_eq_true_eq,BitVec.toNat_eq]
  rfl

theorem signed_div_word (a b : Scalar.Word) :
    UInt256.sdiv ⟨a.toFin⟩ ⟨b.toFin⟩ =
      ⟨(if b == 0 then (0 : Scalar.Word) else BitVec.ofInt 256 (a.toInt.tdiv b.toInt)).toFin⟩ := by
  have core := congrArg firstValue (sdiv_step (Solidity.Evm.Machine.init) a.toFin b.toFin [])
  simp only [Solidity.Evm.Instr.step,Solidity.Evm.Machine.next,firstValue,apply_ite] at core
  have coreNat : (if b.toFin.val = 0 then 0 else (Solidity.Evm.sword
      ((Solidity.Evm.sgn a.toFin.val).tdiv (Solidity.Evm.sgn b.toFin.val))).val) =
      (UInt256.sdiv ⟨a.toFin⟩ ⟨b.toFin⟩).toNat := by
    by_cases zero : b.toFin.val = 0 <;> simpa only [zero,if_pos,if_neg] using core
  change (if b.toNat = 0 then 0 else (Solidity.Evm.sword
    ((Solidity.Evm.sgn a.toNat).tdiv (Solidity.Evm.sgn b.toNat))).val) =
      (UInt256.sdiv ⟨a.toFin⟩ ⟨b.toFin⟩).toNat at coreNat
  change UInt256.mk (UInt256.sdiv ⟨a.toFin⟩ ⟨b.toFin⟩).val = _
  apply congrArg UInt256.mk
  apply Fin.ext
  change (UInt256.sdiv ⟨a.toFin⟩ ⟨b.toFin⟩).toNat =
    (if b == 0 then (0 : Scalar.Word) else BitVec.ofInt 256 (a.toInt.tdiv b.toInt)).toNat
  rw [←coreNat,zero_word]
  have range := Solidity.Evm.tdiv_sgn_range a.isLt (Solidity.Evm.sgn b.toNat)
  rw [Scalar.sgn_word,Scalar.sgn_word] at range
  by_cases zero : b.toNat = 0
  · simp only [zero,if_pos,decide_true]
    rfl
  · simp only [zero,decide_false]
    rw [Scalar.sgn_word,Scalar.sgn_word,Solidity.Evm.sword_val range.1 range.2,
      Scalar.toWord_ofInt _ range]
    rfl

theorem signed_mod_word (a b : Scalar.Word) :
    UInt256.smod ⟨a.toFin⟩ ⟨b.toFin⟩ =
      ⟨(if b == 0 then (0 : Scalar.Word) else BitVec.ofInt 256 (a.toInt.tmod b.toInt)).toFin⟩ := by
  have core := congrArg firstValue (smod_step (Solidity.Evm.Machine.init) a.toFin b.toFin [])
  simp only [Solidity.Evm.Instr.step,Solidity.Evm.Machine.next,firstValue,apply_ite] at core
  have coreNat : (if b.toFin.val = 0 then 0 else (Solidity.Evm.sword
      ((Solidity.Evm.sgn a.toFin.val).tmod (Solidity.Evm.sgn b.toFin.val))).val) =
      (UInt256.smod ⟨a.toFin⟩ ⟨b.toFin⟩).toNat := by
    by_cases zero : b.toFin.val = 0 <;> simpa only [zero,if_pos,if_neg] using core
  change (if b.toNat = 0 then 0 else (Solidity.Evm.sword
    ((Solidity.Evm.sgn a.toNat).tmod (Solidity.Evm.sgn b.toNat))).val) =
      (UInt256.smod ⟨a.toFin⟩ ⟨b.toFin⟩).toNat at coreNat
  change UInt256.mk (UInt256.smod ⟨a.toFin⟩ ⟨b.toFin⟩).val = _
  apply congrArg UInt256.mk
  apply Fin.ext
  change (UInt256.smod ⟨a.toFin⟩ ⟨b.toFin⟩).toNat =
    (if b == 0 then (0 : Scalar.Word) else BitVec.ofInt 256 (a.toInt.tmod b.toInt)).toNat
  rw [←coreNat,zero_word]
  by_cases zero : b.toNat = 0
  · simp only [zero,if_pos,decide_true]
    rfl
  · have nonzero : Solidity.Evm.sgn b.toNat ≠ 0 :=
      fun h => zero ((Solidity.Evm.sgn_eq_zero b.isLt).1 h)
    have small := Solidity.Evm.tmod_range (x := Solidity.Evm.sgn a.toNat)
      (Solidity.Evm.sgn_range b.isLt) nonzero
    have width : (Solidity.Evm.H : Int) < Solidity.Evm.W := by decide +kernel
    have range : -(Solidity.Evm.W : Int) ≤ (Solidity.Evm.sgn a.toNat).tmod (Solidity.Evm.sgn b.toNat) ∧
        (Solidity.Evm.sgn a.toNat).tmod (Solidity.Evm.sgn b.toNat) < Solidity.Evm.W := by omega
    rw [Scalar.sgn_word,Scalar.sgn_word] at range
    simp only [zero,decide_false]
    rw [Scalar.sgn_word,Scalar.sgn_word,Solidity.Evm.sword_val range.1 range.2,
      Scalar.toWord_ofInt _ range]
    rfl

private theorem signed_byte {op : Backend.Op} (site : Site op) :
    site.state.executionEnv.code.get? (Backend.encode site.before).length = some op.code := by
  change (Backend.encode (site.before ++ .op op :: site.after)).toArray[(Backend.encode site.before).length]? = _
  rw [List.getElem?_toArray]
  simp only [Backend.encode_append,Backend.encode_cons,Instr.encode,List.singleton_append]
  rw [List.getElem?_append_right (Nat.le_refl _)]
  simp only [Nat.sub_self,List.getElem?_cons_zero]

private theorem signed_gate (s : EVM.State) (op : Operation .EVM)
    (allowed : op = .SDIV ∨ op = .SMOD) (gas : 5 ≤ s.gasAvailable.toNat)
    (enough : 2 ≤ s.stack.length) (room : s.stack.length-2+1 ≤ 1024) :
    Assembly.driverGate #[] s op = .ok (s,5) := by
  have expansion : EVM.memoryExpansionCost s op = 0 := by
    rcases allowed with rfl|rfl <;>
      simp only [EVM.memoryExpansionCost,EVM.memoryExpansionCost.μᵢ',Nat.sub_self]
  have cost : EVM.C' s op = 5 := by rcases allowed with rfl|rfl <;> rfl
  have delta : EVM.δ op = some 2 := by rcases allowed with rfl|rfl <;> rfl
  have alpha : EVM.α op = some 1 := by rcases allowed with rfl|rfl <;> rfl
  have charge : s.gasAvailable-UInt256.ofNat 0 = s.gasAvailable := by
    change UInt256.mk (s.gasAvailable.val-0) = s.gasAvailable
    rw [sub_zero]
  simp only [Assembly.driverGate]
  rw [expansion,charge]
  simp only [cost,delta,alpha,Option.getD_some,if_neg (Nat.not_lt_zero _),
    if_neg (Nat.not_lt_of_ge gas),if_neg (Nat.not_lt_of_ge enough),if_neg (Nat.not_lt_of_ge room)]
  rcases allowed with rfl|rfl <;> cases s.executionEnv.perm <;> rfl

private theorem signed_checked (input next : EVM.State) (op : Operation .EVM) (fuel : Nat)
    (decoded : EVM.decode input.executionEnv.code input.pc = some (op,none))
    (gate : Assembly.driverGate #[] input op = .ok (input,5))
    (step : EVM.step (fuel+1) 5 (some (op,none)) input = .ok next)
    (nonhalting : Assembly.NonhaltingOpcode op) :
    Assembly.driverSteps 1 (fuel+2) #[] input = .ok next ∧
    EVM.X (fuel+2) #[] input = EVM.X (fuel+1) #[] next := by
  constructor
  · simp only [Assembly.driverSteps]
    rw [decoded]
    dsimp only [Option.option,bind,Except.bind]
    rw [gate]
    dsimp only
    rw [step]
  · exact Assembly.X_continue fuel #[] input input next (op,none) 5 decoded gate step nonhalting

theorem decode_sdiv (site : Site .SDIV) :
    EVM.decode site.state.executionEnv.code site.state.pc = some (.SDIV,none) := by
  have byte := signed_byte site
  simp only [EVM.decode,Site.pc_nat,byte]
  rfl

theorem sdiv_agreement (site : Site .SDIV) (a b : Scalar.Word) (tail : Scalar.Stack)
    (room : tail.length+2 ≤ 1024) (gas : 5 ≤ site.seed.gasAvailable.toNat) (fuel : Nat) :
    let input := (modularSite site (a::b::tail)).state
    let next := (Assembly.chargedPrepare input 5).replaceStackAndIncrPC
      (((if b == 0 then (0 : Scalar.Word) else BitVec.ofInt 256 (a.toInt.tdiv b.toInt))::tail).map (fun w => UInt256.mk w.toFin))
    Scalar.step (.op .SDIV) (a::b::tail) = some ((if b == 0 then (0 : Scalar.Word) else BitVec.ofInt 256 (a.toInt.tdiv b.toInt))::tail) ∧
      Assembly.driverSteps 1 (fuel+2) #[] input = .ok next ∧
      EVM.X (fuel+2) #[] input = EVM.X (fuel+1) #[] next := by
  dsimp only
  refine ⟨rfl,?_⟩
  let input := (modularSite site (a::b::tail)).state
  have gate : Assembly.driverGate #[] input .SDIV = .ok (input,5) := by
    apply signed_gate input .SDIV (Or.inl rfl) gas
    · change 2 ≤ ((a::b::tail).map (fun w => UInt256.mk w.toFin)).length
      simp only [List.length_map,List.length_cons];omega
    · change ((a::b::tail).map (fun w => UInt256.mk w.toFin)).length-2+1 ≤ 1024
      simp only [List.length_map,List.length_cons];omega
  have step : EVM.step (fuel+1) 5 (some (.SDIV,none)) input =
      .ok ((Assembly.chargedPrepare input 5).replaceStackAndIncrPC
        (((if b == 0 then (0 : Scalar.Word) else BitVec.ofInt 256 (a.toInt.tdiv b.toInt))::tail).map (fun w => UInt256.mk w.toFin))) := by
    have word := signed_div_word a b
    simp only [input,modularSite,Site.state,List.map_cons]
    rw [←word]
    rfl
  exact signed_checked input _ .SDIV fuel (decode_sdiv _) gate step
    (by unfold Assembly.NonhaltingOpcode;decide)

theorem decode_smod (site : Site .SMOD) :
    EVM.decode site.state.executionEnv.code site.state.pc = some (.SMOD,none) := by
  have byte := signed_byte site
  simp only [EVM.decode,Site.pc_nat,byte]
  rfl

theorem smod_agreement (site : Site .SMOD) (a b : Scalar.Word) (tail : Scalar.Stack)
    (room : tail.length+2 ≤ 1024) (gas : 5 ≤ site.seed.gasAvailable.toNat) (fuel : Nat) :
    let input := (modularSite site (a::b::tail)).state
    let next := (Assembly.chargedPrepare input 5).replaceStackAndIncrPC
      (((if b == 0 then (0 : Scalar.Word) else BitVec.ofInt 256 (a.toInt.tmod b.toInt))::tail).map (fun w => UInt256.mk w.toFin))
    Scalar.step (.op .SMOD) (a::b::tail) = some ((if b == 0 then (0 : Scalar.Word) else BitVec.ofInt 256 (a.toInt.tmod b.toInt))::tail) ∧
      Assembly.driverSteps 1 (fuel+2) #[] input = .ok next ∧
      EVM.X (fuel+2) #[] input = EVM.X (fuel+1) #[] next := by
  dsimp only
  refine ⟨rfl,?_⟩
  let input := (modularSite site (a::b::tail)).state
  have gate : Assembly.driverGate #[] input .SMOD = .ok (input,5) := by
    apply signed_gate input .SMOD (Or.inr rfl) gas
    · change 2 ≤ ((a::b::tail).map (fun w => UInt256.mk w.toFin)).length
      simp only [List.length_map,List.length_cons];omega
    · change ((a::b::tail).map (fun w => UInt256.mk w.toFin)).length-2+1 ≤ 1024
      simp only [List.length_map,List.length_cons];omega
  have step : EVM.step (fuel+1) 5 (some (.SMOD,none)) input =
      .ok ((Assembly.chargedPrepare input 5).replaceStackAndIncrPC
        (((if b == 0 then (0 : Scalar.Word) else BitVec.ofInt 256 (a.toInt.tmod b.toInt))::tail).map (fun w => UInt256.mk w.toFin))) := by
    have word := signed_mod_word a b
    simp only [input,modularSite,Site.state,List.map_cons]
    rw [←word]
    rfl
  exact signed_checked input _ .SMOD fuel (decode_smod _) gate step
    (by unfold Assembly.NonhaltingOpcode;decide)

#print axioms signed_div_word
#print axioms signed_mod_word
#print axioms decode_sdiv
#print axioms decode_smod
#print axioms sdiv_agreement
#print axioms smod_agreement
end SolidityBridge.RoadmapV15.P10
