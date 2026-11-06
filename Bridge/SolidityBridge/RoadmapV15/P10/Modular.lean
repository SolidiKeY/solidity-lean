import SolidityBridge.RoadmapV15.P10.Execution
import Solidity.Backend.Scalar.Slice

/-! G46.01 full-precision modular consumers. Existing scalar/reference definitions
are used unchanged. These laws do not establish compiler origin or Osaka approval. -/
namespace SolidityBridge.RoadmapV15.P10
open Solidity Solidity.Backend EvmYul Solidity.Evm.External

/-- Actual word representation, with no intermediate word truncation. -/
theorem addMod_word (a b k : Scalar.Word) :
    UInt256.addMod ⟨a.toFin⟩ ⟨b.toFin⟩ ⟨k.toFin⟩ =
      ⟨(if k == 0 then 0 else BitVec.ofNat 256 ((a.toNat + b.toNat) % k.toNat)).toFin⟩ := by
  have zero : UInt256.eq0 ⟨k.toFin⟩ = (k == 0) := by
    simp only [UInt256.eq0,EvmYul.instBEqUInt256,EvmYul.instBEqUInt256.beq]
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq,Fin.ext_iff,BitVec.toNat_eq]
    rfl
  rw [UInt256.addMod,zero]
  split <;> rfl

theorem mulMod_word (a b k : Scalar.Word) :
    UInt256.mulMod ⟨a.toFin⟩ ⟨b.toFin⟩ ⟨k.toFin⟩ =
      ⟨(if k == 0 then 0 else BitVec.ofNat 256 ((a.toNat * b.toNat) % k.toNat)).toFin⟩ := by
  have zero : UInt256.eq0 ⟨k.toFin⟩ = (k == 0) := by
    simp only [UInt256.eq0,EvmYul.instBEqUInt256,EvmYul.instBEqUInt256.beq]
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq,Fin.ext_iff,BitVec.toNat_eq]
    rfl
  rw [UInt256.mulMod,zero]
  split <;> rfl

def modularSite {op : Backend.Op} (site : Site op) (words : Scalar.Stack) : Site op :=
  {site with seed := {site.seed with stack := words.map (fun w => UInt256.mk w.toFin)}}

private theorem site_byte {op : Backend.Op} (site : Site op) :
    site.state.executionEnv.code.get? (Backend.encode site.before).length = some op.code := by
  change (Backend.encode (site.before ++ .op op :: site.after)).toArray[(Backend.encode site.before).length]? = _
  rw [List.getElem?_toArray]
  simp only [Backend.encode_append,Backend.encode_cons,Instr.encode,List.singleton_append]
  rw [List.getElem?_append_right (Nat.le_refl _)]
  simp only [Nat.sub_self,List.getElem?_cons_zero]

private theorem modular_gate (s : EVM.State) (op : Operation .EVM)
    (allowed : op = .ADDMOD ∨ op = .MULMOD)
    (gas : EVM.C' s op ≤ s.gasAvailable.toNat)
    (arity : (EVM.δ op).getD 0 ≤ s.stack.length)
    (capacity : s.stack.length-(EVM.δ op).getD 0+(EVM.α op).getD 0 ≤ 1024) :
    Assembly.driverGate #[] s op = .ok (s,EVM.C' s op) := by
  have expansion : EVM.memoryExpansionCost s op = 0 := by
    rcases allowed with rfl|rfl <;>
      simp only [EVM.memoryExpansionCost,EVM.memoryExpansionCost.μᵢ',Nat.sub_self]
  have charge : s.gasAvailable-UInt256.ofNat 0 = s.gasAvailable := by
    change UInt256.mk (s.gasAvailable.val-0) = s.gasAvailable
    rw [sub_zero]
  have low : ¬s.gasAvailable.toNat < 0 := Nat.not_lt_zero _
  simp only [Assembly.driverGate]
  rw [expansion,charge]
  simp only [if_neg low,if_neg (Nat.not_lt_of_ge gas),if_neg (Nat.not_lt_of_ge arity),if_neg (Nat.not_lt_of_ge capacity)]
  rcases allowed with rfl|rfl <;> cases perm : s.executionEnv.perm <;> rfl

private theorem one_checked (input next : EVM.State) (op : Operation .EVM) (fuel : Nat)
    (decode : EVM.decode input.executionEnv.code input.pc = some (op,none))
    (gate : Assembly.driverGate #[] input op = .ok (input,8))
    (step : EVM.step (fuel+1) 8 (some (op,none)) input = .ok next)
    (nonhalting : Assembly.NonhaltingOpcode op) :
    Assembly.driverSteps 1 (fuel+2) #[] input = .ok next ∧
    EVM.X (fuel+2) #[] input = EVM.X (fuel+1) #[] next := by
  constructor
  · simp only [Assembly.driverSteps]
    rw [decode]
    dsimp only [Option.option,bind,Except.bind]
    rw [gate]
    dsimp only
    rw [step]
  · exact Assembly.X_continue fuel #[] input input next (op,none) 8 decode gate step nonhalting

theorem decode_addmod (site : Site .ADDMOD) :
    EVM.decode site.state.executionEnv.code site.state.pc = some (.ADDMOD,none) := by
  have byte := site_byte site
  simp only [EVM.decode,Site.pc_nat,byte]
  rfl

/-- Scalar result, full charged fetched State and actual X continuation.
Gas/stack capacity are explicit; decoder, gate and execution are derived. -/
theorem addmod_agreement (site : Site .ADDMOD) (a b k : Scalar.Word)
    (tail : Scalar.Stack) (room : tail.length+3 ≤ 1024)
    (gas : 8 ≤ site.seed.gasAvailable.toNat) (fuel : Nat) :
    let result := if k == 0 then 0 else BitVec.ofNat 256 ((a.toNat + b.toNat) % k.toNat)
    let input := (modularSite site (a::b::k::tail)).state
    let next := (Assembly.chargedPrepare input 8).replaceStackAndIncrPC
      ((result::tail).map (fun w => UInt256.mk w.toFin))
    Scalar.step (.op .ADDMOD) (a::b::k::tail) = some (result::tail) ∧
      Assembly.driverSteps 1 (fuel+2) #[] input = .ok next ∧
      EVM.X (fuel+2) #[] input = EVM.X (fuel+1) #[] next := by
  dsimp only
  refine ⟨rfl,?_⟩
  let input := (modularSite site (a::b::k::tail)).state
  have gate : Assembly.driverGate #[] input .ADDMOD = .ok (input,8) := by
    apply modular_gate
    · decide
    · exact gas
    · change 3 ≤ ((a::b::k::tail).map (fun w => UInt256.mk w.toFin)).length
      simp only [List.length_map,List.length_cons]; omega
    · change ((a::b::k::tail).map (fun w => UInt256.mk w.toFin)).length-3+1 ≤ 1024
      simp only [List.length_map,List.length_cons]; omega
  have step : EVM.step (fuel+1) 8 (some (.ADDMOD,none)) input =
      .ok ((Assembly.chargedPrepare input 8).replaceStackAndIncrPC
        (((if k == 0 then 0 else BitVec.ofNat 256 ((a.toNat + b.toNat) % k.toNat))::tail).map
          (fun w => UInt256.mk w.toFin))) := by
    have word := addMod_word a b k
    simp only [input,modularSite,Site.state,List.map_cons]
    rw [←word]
    rfl
  exact one_checked input _ .ADDMOD fuel (decode_addmod _) gate step
    (by unfold Assembly.NonhaltingOpcode; decide)

#print axioms addMod_word
#print axioms decode_addmod
#print axioms addmod_agreement

theorem decode_mulmod (site : Site .MULMOD) :
    EVM.decode site.state.executionEnv.code site.state.pc = some (.MULMOD,none) := by
  have byte := site_byte site
  simp only [EVM.decode,Site.pc_nat,byte]
  rfl

/-- Scalar result, full charged fetched State and actual X continuation.
Gas/stack capacity are explicit; decoder, gate and execution are derived. -/
theorem mulmod_agreement (site : Site .MULMOD) (a b k : Scalar.Word)
    (tail : Scalar.Stack) (room : tail.length+3 ≤ 1024)
    (gas : 8 ≤ site.seed.gasAvailable.toNat) (fuel : Nat) :
    let result := if k == 0 then 0 else BitVec.ofNat 256 ((a.toNat * b.toNat) % k.toNat)
    let input := (modularSite site (a::b::k::tail)).state
    let next := (Assembly.chargedPrepare input 8).replaceStackAndIncrPC
      ((result::tail).map (fun w => UInt256.mk w.toFin))
    Scalar.step (.op .MULMOD) (a::b::k::tail) = some (result::tail) ∧
      Assembly.driverSteps 1 (fuel+2) #[] input = .ok next ∧
      EVM.X (fuel+2) #[] input = EVM.X (fuel+1) #[] next := by
  dsimp only
  refine ⟨rfl,?_⟩
  let input := (modularSite site (a::b::k::tail)).state
  have gate : Assembly.driverGate #[] input .MULMOD = .ok (input,8) := by
    apply modular_gate
    · decide
    · exact gas
    · change 3 ≤ ((a::b::k::tail).map (fun w => UInt256.mk w.toFin)).length
      simp only [List.length_map,List.length_cons]; omega
    · change ((a::b::k::tail).map (fun w => UInt256.mk w.toFin)).length-3+1 ≤ 1024
      simp only [List.length_map,List.length_cons]; omega
  have step : EVM.step (fuel+1) 8 (some (.MULMOD,none)) input =
      .ok ((Assembly.chargedPrepare input 8).replaceStackAndIncrPC
        (((if k == 0 then 0 else BitVec.ofNat 256 ((a.toNat * b.toNat) % k.toNat))::tail).map
          (fun w => UInt256.mk w.toFin))) := by
    have word := mulMod_word a b k
    simp only [input,modularSite,Site.state,List.map_cons]
    rw [←word]
    rfl
  exact one_checked input _ .MULMOD fuel (decode_mulmod _) gate step
    (by unfold Assembly.NonhaltingOpcode; decide)

#print axioms mulMod_word
#print axioms decode_mulmod
#print axioms mulmod_agreement

end SolidityBridge.RoadmapV15.P10
