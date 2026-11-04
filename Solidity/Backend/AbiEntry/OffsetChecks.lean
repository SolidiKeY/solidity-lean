import Solidity.Backend.AbiEntry.OffsetChecksInterface
import Solidity.Backend.Scalar.SignedBits
import Solidity.Backend.Selection.InterfaceV2

/-! Actual existing numeric opcodes for the indexed decoder's signed modular
checks. Backend SWAP indices are zero-based (SWAP0 is physical SWAP1).
No unsigned natural-span criterion replaces the original predicates. -/
namespace Solidity.Backend.AbiEntry.OffsetChecks
open Scalar

def tailCode : Program :=
  [pushByte 1,.op (.SWAP 0),.op .SUB,.op (.SWAP 1),.op (.SWAP 0),
    .op .SUB,.op .SUB,.op (.SWAP 0),.op .SLT]

def regionCode : Program :=
  [.op .MUL,.op (.SWAP 0),.op .SUB,.op (.SWAP 0),pushByte 32,
    .op .ADD,.op (.SWAP 0),.op .SLT,.op .ISZERO]

private theorem signed (value : Scalar.Word) :
    Solidity.AbiEntry.toInt value.toNat=value.toInt := signedOf_word value

private theorem sub_nat (a b : Scalar.Word) :
    (a-b).toNat=Solidity.AbiEntry.sub a.toNat b.toNat := by
  simp only [BitVec.toNat_sub,Solidity.AbiEntry.sub,Solidity.AbiEntry.W_eq,
    Nat.mod_eq_of_lt b.isLt,Nat.add_comm]

private theorem mul_nat (a b : Scalar.Word) :
    (a*b).toNat=Solidity.AbiEntry.wrap (a.toNat*b.toNat) := BitVec.toNat_mul a b

private theorem plus_nat (a : Scalar.Word) :
    (a+32).toNat=Solidity.AbiEntry.wrap (a.toNat+32) := by
  rw [BitVec.toNat_add]
  rfl

private theorem flag_zero (value : Bool) : flag (flag value == 0)=flag (!value) := by
  cases value <;> rfl

theorem tail_raw (size base relative extent : Scalar.Word) (suffix : Stack) :
    run tailCode (extent::size::base::relative::suffix)=
      some (flag (relative.toInt<((size-base)-(extent-1)).toInt)::suffix) := by
  rw [tailCode,run,step_pushByte]
  simp only [run,step,numericStep,unary,binary,applyBinary,
    swap,exchange,Option.map_some,Option.bind_some]
  rfl

theorem region_raw (size address length stride : Scalar.Word) (suffix : Stack) :
    run regionCode (length::stride::size::address::suffix)=
      some (flag (!decide ((size-length*stride).toInt<(32+address).toInt))::suffix) := by
  have prefixRun : run [.op .MUL,.op (.SWAP 0),.op .SUB,.op (.SWAP 0)]
      (length::stride::size::address::suffix)=some (address::(size-length*stride)::suffix) := by
    simp only [run,step,numericStep,unary,binary,applyBinary,swap,exchange,
      Option.map_some,Option.bind_some]
  change run ([.op .MUL,.op (.SWAP 0),.op .SUB,.op (.SWAP 0)]++
    [pushByte 32,.op .ADD,.op (.SWAP 0),.op .SLT,.op .ISZERO])
      (length::stride::size::address::suffix)=_
  rw [run_append,prefixRun]
  simp only [Option.bind_some]
  rw [run,step_pushByte]
  simp only [Option.bind_some,run,step,numericStep,unary,binary,applyUnary,applyBinary,
    swap,exchange,Option.map_some,flag_zero]
  rfl

theorem tail_correct (size base relative extent : Scalar.Word) (suffix : Stack) :
    run tailCode (extent::size::base::relative::suffix)=
      some (flag (Solidity.AbiEntry.tailFits size.toNat base.toNat relative.toNat extent.toNat)::suffix) := by
  rw [tail_raw]
  unfold Solidity.AbiEntry.tailFits Solidity.AbiEntry.slt
  rw [←signed relative,←signed ((size-base)-(extent-1)),sub_nat,sub_nat,sub_nat]
  rfl

theorem region_correct (size address length stride : Scalar.Word) (suffix : Stack) :
    run regionCode (length::stride::size::address::suffix)=
      some (flag (Solidity.AbiEntry.regionFits size.toNat address.toNat length.toNat stride.toNat)::suffix) := by
  rw [region_raw]
  unfold Solidity.AbiEntry.regionFits Solidity.AbiEntry.slt
  rw [BitVec.add_comm (32 : Scalar.Word) address,←signed (size-length*stride),
    ←signed (address+32),sub_nat,mul_nat,plus_nat]

theorem tail_capacity (suffix : Stack) (room : suffix.length+5≤1024) :
    stackBound tailCode ((suffix.length+4 : Nat) : Int)=true := by
  simp only [tailCode,stackBound,heightTrace,stackDelta,pushByte,numericDelta,
    unary,binary,Option.isSome_some,Option.isSome_none,ite_true,ite_false,Bool.false_eq_true,
    List.all_cons,List.all_nil,Bool.and_true,safeHeight,Bool.and_eq_true,decide_eq_true_eq]
  omega

theorem region_capacity (suffix : Stack) (room : suffix.length+5≤1024) :
    stackBound regionCode ((suffix.length+4 : Nat) : Int)=true := by
  simp only [regionCode,stackBound,heightTrace,stackDelta,pushByte,numericDelta,
    unary,binary,Option.isSome_some,Option.isSome_none,ite_true,ite_false,Bool.false_eq_true,
    List.all_cons,List.all_nil,Bool.and_true,safeHeight,Bool.and_eq_true,decide_eq_true_eq]
  omega

def tailFrame (size base relative extent : Scalar.Word) :
    Selection.V2.FrameCertificate [extent,size,base,relative]
      [flag (Solidity.AbiEntry.tailFits size.toNat base.toNat relative.toNat extent.toNat)] where
  code := tailCode
  peak := 1
  inputRoom := by change (4 : Nat)+1≤1024;decide
  frame := tail_correct size base relative extent
  capacity := by
    intro suffix room
    simp only [List.cons_append,List.nil_append,List.length_cons] at room ⊢
    exact tail_capacity suffix room

def regionFrame (size address length stride : Scalar.Word) :
    Selection.V2.FrameCertificate [length,stride,size,address]
      [flag (Solidity.AbiEntry.regionFits size.toNat address.toNat length.toNat stride.toNat)] where
  code := regionCode
  peak := 1
  inputRoom := by change (4 : Nat)+1≤1024;decide
  frame := region_correct size address length stride
  capacity := by
    intro suffix room
    simp only [List.cons_append,List.nil_append,List.length_cons] at room ⊢
    exact region_capacity suffix room

def certificate : Interface.OffsetChecksCertificate tailCode regionCode where
  tail_correct := tail_correct
  region_correct := region_correct
  tail_capacity := tail_capacity
  region_capacity := region_capacity

/-- info: 'Solidity.Backend.AbiEntry.OffsetChecks.tail_raw' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms tail_raw
/-- info: 'Solidity.Backend.AbiEntry.OffsetChecks.region_raw' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms region_raw
/-- info: 'Solidity.Backend.AbiEntry.OffsetChecks.tail_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms tail_correct
/-- info: 'Solidity.Backend.AbiEntry.OffsetChecks.region_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms region_correct
/-- info: 'Solidity.Backend.AbiEntry.OffsetChecks.tail_capacity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms tail_capacity
/-- info: 'Solidity.Backend.AbiEntry.OffsetChecks.region_capacity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms region_capacity
/-- info: 'Solidity.Backend.AbiEntry.OffsetChecks.tailFrame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms tailFrame
/-- info: 'Solidity.Backend.AbiEntry.OffsetChecks.regionFrame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms regionFrame
/-- info: 'Solidity.Backend.AbiEntry.OffsetChecks.certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms certificate
end Solidity.Backend.AbiEntry.OffsetChecks
