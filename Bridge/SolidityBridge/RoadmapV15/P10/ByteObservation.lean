import SolidityBridge.RoadmapV15.P10.DecoderAgreement
import Solidity.Evm.TryByteImage
import Solidity.Backend.Scalar.Typed

/-! Actual fetched BYTE and big-endian observations over published definitions. -/
namespace SolidityBridge.RoadmapV15.P10
open Solidity Solidity.Backend EvmYul Solidity.Evm.External

private theorem byte_gate (s : EVM.State) (gas : 3 ≤ s.gasAvailable.toNat)
    (enough : 2 ≤ s.stack.length) (room : s.stack.length-2+1 ≤ 1024) :
    Assembly.driverGate #[] s .BYTE = .ok (s,3) := by
  have expansion : EVM.memoryExpansionCost s .BYTE = 0 := by
    simp only [EVM.memoryExpansionCost,EVM.memoryExpansionCost.μᵢ',Nat.sub_self]
  have charge : s.gasAvailable-UInt256.ofNat 0 = s.gasAvailable := by
    change UInt256.mk (s.gasAvailable.val-0) = s.gasAvailable
    rw [sub_zero]
  simp only [Assembly.driverGate]
  rw [expansion,charge]
  have cost : EVM.C' s .BYTE = 3 := rfl
  simp only [cost,EVM.δ,EVM.α,Option.getD_some,if_neg (Nat.not_lt_zero _),
    if_neg (Nat.not_lt_of_ge gas),if_neg (Nat.not_lt_of_ge enough),if_neg (Nat.not_lt_of_ge room)]
  cases s.executionEnv.perm <;> rfl

/-- Every native index/value, preserving the actual complete state outside the
charged binary stack update. No execution/decoder/frame hypothesis is supplied. -/
theorem byte_fetched (site : Site .BYTE) (a b : Scalar.Word) (tail : Scalar.Stack)
    (room : tail.length+2 ≤ 1024) (gas : 3 ≤ site.seed.gasAvailable.toNat) (fuel : Nat) :
    let input := (modularSite site (a::b::tail)).state
    let result := UInt256.byteAt ⟨a.toFin⟩ ⟨b.toFin⟩
    let next := (Assembly.chargedPrepare input 3).replaceStackAndIncrPC
      (result :: tail.map (fun w => UInt256.mk w.toFin))
    Assembly.driverSteps 1 (fuel+2) #[] input = .ok next ∧
      EVM.X (fuel+2) #[] input = EVM.X (fuel+1) #[] next := by
  dsimp only
  let input := (modularSite site (a::b::tail)).state
  have gate : Assembly.driverGate #[] input .BYTE = .ok (input,3) := by
    apply byte_gate input gas
    · change 2 ≤ ((a::b::tail).map (fun w => UInt256.mk w.toFin)).length
      simp only [List.length_map,List.length_cons];omega
    · change ((a::b::tail).map (fun w => UInt256.mk w.toFin)).length-2+1 ≤ 1024
      simp only [List.length_map,List.length_cons];omega
  have step : EVM.step (fuel+1) 3 (some (.BYTE,none)) input =
      .ok ((Assembly.chargedPrepare input 3).replaceStackAndIncrPC
        (UInt256.byteAt ⟨a.toFin⟩ ⟨b.toFin⟩ :: tail.map (fun w => UInt256.mk w.toFin))) := by
    rfl
  have decoded : EVM.decode input.executionEnv.code input.pc = some (.BYTE,none) :=
    DecoderAgreement.decode_all (modularSite site (a::b::tail))
  constructor
  · simp only [Assembly.driverSteps]
    rw [decoded]
    dsimp only [Option.option,bind,Except.bind]
    rw [gate]
    dsimp only
    rw [step]
  · exact Assembly.X_continue fuel #[] input input _ (.BYTE,none) 3
      decoded gate step (by unfold Assembly.NonhaltingOpcode;decide)

/-- Exact big-endian numeric byte observation at every admitted byte index. -/
theorem byte_nat (a b : UInt256) (small : a.toNat < 32) :
    (UInt256.byteAt a b).toNat = b.toNat / 256^(31-a.toNat) % 256 := by
  have index : ¬a > (⟨31⟩ : UInt256) := by change ¬31<a.toNat;omega
  have count : (31-a.toNat)*8 < UInt256.size := by
    have bound : (31-a.toNat)*8 ≤ 248 := by omega
    exact Nat.lt_of_le_of_lt bound (by decide +kernel)
  have shift : ¬(UInt256.ofNat ((31-a.toNat)*8)).val ≥ 256 := by
    change ¬((31-a.toNat)*8)%UInt256.size ≥ 256
    rw [Nat.mod_eq_of_lt count]
    omega
  unfold UInt256.byteAt
  rw [if_neg index]
  change (UInt256.land (UInt256.shiftRight b (UInt256.ofNat ((31-a.toNat)*8))) ⟨255⟩).toNat = _
  unfold UInt256.shiftRight
  rw [if_neg shift]
  change ((b.val >>> (UInt256.ofNat ((31-a.toNat)*8)).val) &&& (255 : Fin UInt256.size)).val = _
  rw [Fin.and_val,Fin.shiftRight_val]
  change (b.toNat >>> (((31-a.toNat)*8)%UInt256.size)) &&& 255 = _
  rw [Nat.mod_eq_of_lt count,Nat.shiftRight_eq_div_pow]
  change (b.toNat / 2^((31-a.toNat)*8)) &&& (2^8-1) = _
  rw [Nat.and_two_pow_sub_one_eq_mod]
  congr 2
  rw [Nat.mul_comm (31-a.toNat) 8,Nat.pow_mul]

/-- Beyond the full word BYTE yields zero, not an index reduced modulo32. -/
theorem byte_large (a b : UInt256) (large : 32 ≤ a.toNat) : UInt256.byteAt a b = UInt256.ofNat 0 := by
  unfold UInt256.byteAt
  rw [if_pos (by change 31<a.toNat;omega)]
  rfl

/-- Connect actual native BYTE to the published intrinsic typed byte image.
The Fin32 index is essential; no padding or physical memory witness is used. -/
theorem byte_image (w : PrimTy.uint.Denote) (j : Fin 32) :
    (UInt256.byteAt (.ofNat j.val) ⟨(Scalar.encodeValue .uint w).toFin⟩).toNat =
      (Solidity.Evm.TryByteImage.wordByte w j.val).toNat := by
  have fits : j.val < UInt256.size := Nat.lt_trans j.isLt (by decide +kernel)
  have index : (UInt256.ofNat j.val).toNat = j.val := Nat.mod_eq_of_lt fits
  have small : (UInt256.ofNat j.val).toNat < 32 := by rw [index];exact j.isLt
  rw [byte_nat _ _ small,index]
  change (Scalar.encodeValue .uint w).toNat / 256^(31-j.val)%256 =
    (UInt8.ofNat (w.val.toNat / 256^(31-j.val)%256)).toNat
  rw [Scalar.encode_uint_toNat,UInt8.toNat_ofNat',Nat.mod_mod]

theorem byte_image_word (w : PrimTy.uint.Denote) (j : Fin 32) :
    UInt256.byteAt (.ofNat j.val) ⟨(Scalar.encodeValue .uint w).toFin⟩ =
      UInt256.ofNat (Solidity.Evm.TryByteImage.wordByte w j.val).toNat := by
  apply congrArg UInt256.mk
  apply Fin.ext
  change (UInt256.byteAt (.ofNat j.val) ⟨(Scalar.encodeValue .uint w).toFin⟩).toNat = _
  rw [byte_image]
  exact (Nat.mod_eq_of_lt (Nat.lt_trans (Solidity.Evm.TryByteImage.wordByte w j.val).toFin.isLt
    (by decide +kernel : 256 < UInt256.size))).symm

/-- Typed intrinsic byte observation through actual fetched execution. Scalar
BYTE admission is not needed or introduced. The original mapped tail is kept. -/
theorem byte_image_agreement (site : Site .BYTE) (w : PrimTy.uint.Denote) (j : Fin 32)
    (tail : Scalar.Stack) (room : tail.length+2 ≤ 1024)
    (gas : 3 ≤ site.seed.gasAvailable.toNat) (fuel : Nat) :
    let input := (modularSite site (BitVec.ofNat 256 j.val::Scalar.encodeValue .uint w::tail)).state
    let next := (Assembly.chargedPrepare input 3).replaceStackAndIncrPC
      (UInt256.ofNat (Solidity.Evm.TryByteImage.wordByte w j.val).toNat ::
        tail.map (fun v => UInt256.mk v.toFin))
    Assembly.driverSteps 1 (fuel+2) #[] input = .ok next ∧
      EVM.X (fuel+2) #[] input = EVM.X (fuel+1) #[] next := by
  have h := byte_fetched site (BitVec.ofNat 256 j.val) (Scalar.encodeValue .uint w) tail room gas fuel
  dsimp only at h ⊢
  have index : UInt256.mk (BitVec.ofNat 256 j.val).toFin = .ofNat j.val := by
    apply congrArg UInt256.mk
    apply Fin.ext
    rfl
  rw [index,byte_image_word] at h
  exact h

/-- Actual Scalar admission stays unchanged: BYTE is not in its local slice. -/
theorem byte_scalar_refusal (a b : Scalar.Word) (tail : Scalar.Stack) :
    Scalar.step (.op .BYTE) (a::b::tail) = none := rfl

#print axioms byte_fetched
#print axioms byte_nat
#print axioms byte_large
#print axioms byte_image
#print axioms byte_image_word
#print axioms byte_image_agreement
#print axioms byte_scalar_refusal
end SolidityBridge.RoadmapV15.P10
