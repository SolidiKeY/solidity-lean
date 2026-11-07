import SolidityBridge.PrecompileAgreement.Controls
import Lean

/-! Guarded regressions: short nonzero headers must retain the padding factor;
the four-byte common domain and zero-header exception must stay distinct;
validation size/flag/affordability must hold jointly for the same input;
malformed-length membership must be witnessed, not assumed. Reuses the general
frozen padding and validation laws, without comparing compression output.
Private helper instances use their actual imported constants and ordinary
kernel term checking. No native crypto or compiler-success claim is made. -/
open Lean Elab Term in
elab "audit_header_private%" id:ident : term => do
  let env ← getEnv
  let suffix := "." ++ id.getId.toString
  let found := env.constants.toList.filter fun (n, _) =>
    n.toString.startsWith "_private.SolidityBridge.PrecompileAgreement." && n.toString.endsWith suffix
  unless found.length = 1 do throwError "expected one frozen private constant"
  let (name, info) := found.head!
  unless info.levelParams.isEmpty do throwError "unexpected universe parameters"
  return mkConst name

namespace H62.AuditPrecompiles.Successor.Header
open Solidity Solidity.Precompiles Solidity.Roadmap.Evm EvmYul
open SolidityBridge.PrecompileAgreement.Controls (input filled)

def shortHeader : ByteArray := ⟨#[1]⟩
def smallHeader : ByteArray := ⟨#[0,0,0,1,2]⟩
def zeroHeader : ByteArray := ⟨#[0]⟩
def validZero : ByteArray := ⟨Array.replicate 213 0⟩
def validOne : ByteArray := ⟨(Array.replicate 212 (0 : UInt8)).push 1⟩
def invalidFlag : ByteArray := ⟨(Array.replicate 212 (0 : UInt8)).push 2⟩

private theorem header_decode (d : ByteArray) :
    fromByteArrayBigEndian (d.extract 0 4) = ofBE ((d.toList.take 4).map UInt8.toNat) := by
  simp only [fromByteArrayBigEndian, SolidityBridge.PrecompileAgreement.big_reader,
    SolidityBridge.PrecompileAgreement.first_four]

-- Frozen source: SolidityBridge.PrecompileAgreement.Controls.blake_malformed_lengths
theorem blake_malformed_lengths_joint : ∃ (σ : AccountMap .EVM) (g : UInt256) (A : Substate) (n : Nat), n ∈ [0,1,2,3,4,212,214] ∧ (Ξ_BLAKE2_F σ g A (input (filled n)) = (false, ∅, ⟨0⟩, A, .empty)) := by
  have member : 1 ∈ [0,1,2,3,4,212,214] := by decide +kernel
  exact ⟨default, (UInt256.ofNat 50001), default, 1, member, SolidityBridge.PrecompileAgreement.Controls.blake_malformed_lengths default (UInt256.ofNat 50001) default 1 member⟩

-- Frozen source: SolidityBridge.PrecompileAgreement.be_append_byte
theorem be_append_byte_data : ∃ (bs : List UInt8) (b : UInt8), (ofBE ((bs ++ [b]).map UInt8.toNat) = 256 * ofBE (bs.map UInt8.toNat) + b.toNat) := by
  exact ⟨[1,2], 3, (audit_header_private% SolidityBridge.PrecompileAgreement.be_append_byte) [1,2] 3⟩

-- Frozen source: SolidityBridge.PrecompileAgreement.little_reader
theorem little_reader_data : ∃ (bs : List UInt8), (fromBytes' bs = ofBE (bs.reverse.map UInt8.toNat)) := by
  exact ⟨[1,2], (audit_header_private% SolidityBridge.PrecompileAgreement.little_reader) [1,2]⟩

-- Frozen source: SolidityBridge.PrecompileAgreement.big_reader
theorem big_reader_data : ∃ (bs : List UInt8), (fromBytesBigEndian bs = ofBE (bs.map UInt8.toNat)) := by
  exact ⟨[1,2], SolidityBridge.PrecompileAgreement.big_reader [1,2]⟩

-- Frozen source: SolidityBridge.PrecompileAgreement.first_four
theorem first_four_data : ∃ (d : ByteArray), ((d.extract 0 4).toList = d.toList.take 4) := by
  exact ⟨smallHeader, SolidityBridge.PrecompileAgreement.first_four smallHeader⟩

-- Frozen source: SolidityBridge.PrecompileAgreement.append_zero
theorem append_zero_data : ∃ (bs : List Nat), (ofBE (bs ++ [0]) = 256 * ofBE bs) := by
  exact ⟨[1,2], (audit_header_private% SolidityBridge.PrecompileAgreement.append_zero) [1,2]⟩

-- Frozen source: SolidityBridge.PrecompileAgreement.zero_padding
theorem zero_padding_data : ∃ (bs : List Nat) (n : Nat), (ofBE (bs ++ List.replicate n 0) = ofBE bs * 256 ^ n) := by
  exact ⟨[1,2], 1, SolidityBridge.PrecompileAgreement.zero_padding [1,2] 1⟩

-- Frozen source: SolidityBridge.PrecompileAgreement.blake_padding
theorem blake_padding_data : ∃ (d : ByteArray), (Osaka.gas .blake2f d.toList =
      fromByteArrayBigEndian (d.extract 0 4) * 256 ^ (4 - min 4 d.size)) := by
  exact ⟨shortHeader, SolidityBridge.PrecompileAgreement.blake_padding shortHeader⟩

-- Frozen source: SolidityBridge.PrecompileAgreement.blake_zero_header
theorem blake_zero_header_joint : ∃ (d : ByteArray), fromByteArrayBigEndian (d.extract 0 4) = 0 ∧ (Osaka.gas .blake2f d.toList = 0) := by
  have zero : fromByteArrayBigEndian (zeroHeader.extract 0 4) = 0 := by rw [header_decode, SolidityBridge.PrecompileAgreement.byte_list]; decide +kernel
  exact ⟨zeroHeader, zero, SolidityBridge.PrecompileAgreement.blake_zero_header zeroHeader zero⟩

-- Frozen source: SolidityBridge.PrecompileAgreement.blake_price
theorem blake_price_joint : ∃ (d : ByteArray), 4 ≤ d.size ∧ (Osaka.gas .blake2f d.toList = fromByteArrayBigEndian (d.extract 0 4)) := by
  have header : 4 ≤ smallHeader.size := by decide +kernel
  exact ⟨smallHeader, header, SolidityBridge.PrecompileAgreement.blake_price smallHeader header⟩

-- Frozen source: SolidityBridge.PrecompileAgreement.blake_gas
theorem blake_gas_joint : ∃ (σ : AccountMap .EVM) (g : UInt256) (A : Substate) (I : ExecutionEnv .EVM), 4 ≤ I.calldata.size ∧ ((Ξ_BLAKE2_F σ g A I).2.2.1.toNat =
      if (Ξ_BLAKE2_F σ g A I).1 then g.toNat - Osaka.gas .blake2f I.calldata.toList else 0) := by
  have header : 4 ≤ (input smallHeader).calldata.size := by decide +kernel
  exact ⟨default, (UInt256.ofNat 50001), default, (input smallHeader), header, SolidityBridge.PrecompileAgreement.blake_gas default (UInt256.ofNat 50001) default (input smallHeader) header⟩

-- Frozen source: SolidityBridge.PrecompileAgreement.blake_valid
theorem blake_valid_joint : ∃ (σ : AccountMap .EVM) (g : UInt256) (A : Substate) (I : ExecutionEnv .EVM), fromByteArrayBigEndian (I.calldata.extract 0 4) ≤ g.toNat ∧ I.calldata.size = 213 ∧ I.calldata[212]! = 0 ∧ (Ξ_BLAKE2_F σ g A I =
      (true, σ, g - .ofNat (fromByteArrayBigEndian (I.calldata.extract 0 4)), A,
        ffi.BLAKE2Compress I.calldata)) := by
  have enough : fromByteArrayBigEndian ((input validZero).calldata.extract 0 4) ≤ (UInt256.ofNat 50001).toNat := by rw [header_decode, SolidityBridge.PrecompileAgreement.byte_list, SolidityBridge.PrecompileAgreement.ofNat_nat 50001 (by decide)]; decide +kernel
  have size : (input validZero).calldata.size = 213 := by decide +kernel
  have flag : (input validZero).calldata[212]! = 0 := by decide +kernel
  exact ⟨default, (UInt256.ofNat 50001), default, (input validZero), enough, size, flag, SolidityBridge.PrecompileAgreement.blake_valid default (UInt256.ofNat 50001) default (input validZero) enough size flag⟩

-- Frozen source: SolidityBridge.PrecompileAgreement.blake_insufficient
theorem blake_insufficient_joint : ∃ (σ : AccountMap .EVM) (g : UInt256) (A : Substate) (I : ExecutionEnv .EVM), g.toNat < fromByteArrayBigEndian (I.calldata.extract 0 4) ∧ (Ξ_BLAKE2_F σ g A I = (false, ∅, ⟨0⟩, A, .empty)) := by
  have short : (UInt256.ofNat 0).toNat < fromByteArrayBigEndian ((input smallHeader).calldata.extract 0 4) := by rw [header_decode, SolidityBridge.PrecompileAgreement.byte_list, SolidityBridge.PrecompileAgreement.ofNat_nat 0 (by decide)]; decide +kernel
  exact ⟨default, (UInt256.ofNat 0), default, (input smallHeader), short, SolidityBridge.PrecompileAgreement.blake_insufficient default (UInt256.ofNat 0) default (input smallHeader) short⟩

-- Frozen source: SolidityBridge.PrecompileAgreement.blake_invalid_flag
theorem blake_invalid_flag_joint : ∃ (σ : AccountMap .EVM) (g : UInt256) (A : Substate) (I : ExecutionEnv .EVM), I.calldata.size = 213 ∧ I.calldata[212]! = 2 ∧ (Ξ_BLAKE2_F σ g A I = (false, ∅, ⟨0⟩, A, .empty)) := by
  have size : (input invalidFlag).calldata.size = 213 := by decide +kernel
  have flag : (input invalidFlag).calldata[212]! = 2 := by decide +kernel
  exact ⟨default, (UInt256.ofNat 50001), default, (input invalidFlag), size, flag, SolidityBridge.PrecompileAgreement.blake_invalid_flag default (UInt256.ofNat 50001) default (input invalidFlag) size flag⟩

-- Frozen source: SolidityBridge.PrecompileAgreement.blake_valid_one
theorem blake_valid_one_joint : ∃ (σ : AccountMap .EVM) (g : UInt256) (A : Substate) (I : ExecutionEnv .EVM), fromByteArrayBigEndian (I.calldata.extract 0 4) ≤ g.toNat ∧ I.calldata.size = 213 ∧ I.calldata[212]! = 1 ∧ (Ξ_BLAKE2_F σ g A I =
      (true, σ, g - .ofNat (fromByteArrayBigEndian (I.calldata.extract 0 4)), A,
        ffi.BLAKE2Compress I.calldata)) := by
  have enough : fromByteArrayBigEndian ((input validOne).calldata.extract 0 4) ≤ (UInt256.ofNat 50001).toNat := by rw [header_decode, SolidityBridge.PrecompileAgreement.byte_list, SolidityBridge.PrecompileAgreement.ofNat_nat 50001 (by decide)]; decide +kernel
  have size : (input validOne).calldata.size = 213 := by decide +kernel
  have flag : (input validOne).calldata[212]! = 1 := by decide +kernel
  exact ⟨default, (UInt256.ofNat 50001), default, (input validOne), enough, size, flag, SolidityBridge.PrecompileAgreement.blake_valid_one default (UInt256.ofNat 50001) default (input validOne) enough size flag⟩

-- Frozen source: SolidityBridge.PrecompileAgreement.blake_invalid_size
theorem blake_invalid_size_joint : ∃ (σ : AccountMap .EVM) (g : UInt256) (A : Substate) (I : ExecutionEnv .EVM), I.calldata.size ≠ 213 ∧ (Ξ_BLAKE2_F σ g A I = (false, ∅, ⟨0⟩, A, .empty)) := by
  have size : (input smallHeader).calldata.size ≠ 213 := by decide +kernel
  exact ⟨default, (UInt256.ofNat 50001), default, (input smallHeader), size, SolidityBridge.PrecompileAgreement.blake_invalid_size default (UInt256.ofNat 50001) default (input smallHeader) size⟩

-- Frozen source: SolidityBridge.PrecompileAgreement.blake_zero_gas
theorem blake_zero_gas_joint : ∃ (σ : AccountMap .EVM) (g : UInt256) (A : Substate) (I : ExecutionEnv .EVM), fromByteArrayBigEndian (I.calldata.extract 0 4) = 0 ∧ ((Ξ_BLAKE2_F σ g A I).2.2.1.toNat =
      if (Ξ_BLAKE2_F σ g A I).1 then g.toNat - Osaka.gas .blake2f I.calldata.toList else 0) := by
  have zero : fromByteArrayBigEndian ((input zeroHeader).calldata.extract 0 4) = 0 := by rw [header_decode, SolidityBridge.PrecompileAgreement.byte_list]; decide +kernel
  exact ⟨default, (UInt256.ofNat 50001), default, (input zeroHeader), zero, SolidityBridge.PrecompileAgreement.blake_zero_gas default (UInt256.ofNat 50001) default (input zeroHeader) zero⟩

/-- info: 'H62.AuditPrecompiles.Successor.Header.blake_malformed_lengths_joint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms blake_malformed_lengths_joint
/-- info: 'H62.AuditPrecompiles.Successor.Header.be_append_byte_data' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms be_append_byte_data
/-- info: 'H62.AuditPrecompiles.Successor.Header.little_reader_data' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms little_reader_data
/-- info: 'H62.AuditPrecompiles.Successor.Header.big_reader_data' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms big_reader_data
/-- info: 'H62.AuditPrecompiles.Successor.Header.first_four_data' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms first_four_data
/-- info: 'H62.AuditPrecompiles.Successor.Header.append_zero_data' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms append_zero_data
/-- info: 'H62.AuditPrecompiles.Successor.Header.zero_padding_data' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms zero_padding_data
/-- info: 'H62.AuditPrecompiles.Successor.Header.blake_padding_data' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms blake_padding_data
/-- info: 'H62.AuditPrecompiles.Successor.Header.blake_zero_header_joint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms blake_zero_header_joint
/-- info: 'H62.AuditPrecompiles.Successor.Header.blake_price_joint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms blake_price_joint
/-- info: 'H62.AuditPrecompiles.Successor.Header.blake_gas_joint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms blake_gas_joint
/-- info: 'H62.AuditPrecompiles.Successor.Header.blake_valid_joint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms blake_valid_joint
/-- info: 'H62.AuditPrecompiles.Successor.Header.blake_insufficient_joint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms blake_insufficient_joint
/-- info: 'H62.AuditPrecompiles.Successor.Header.blake_invalid_flag_joint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms blake_invalid_flag_joint
/-- info: 'H62.AuditPrecompiles.Successor.Header.blake_valid_one_joint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms blake_valid_one_joint
/-- info: 'H62.AuditPrecompiles.Successor.Header.blake_invalid_size_joint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms blake_invalid_size_joint
/-- info: 'H62.AuditPrecompiles.Successor.Header.blake_zero_gas_joint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms blake_zero_gas_joint
run_cmd Lean.logInfo "HEADER_APPLICABILITY_PASS joint=10 data=7"
end H62.AuditPrecompiles.Successor.Header
