import Solidity.Backend.Scalar.Axioms
import Solidity.Backend.Scalar.FixedBytes
import Solidity.Backend.Scalar.WidthGuards
import Solidity.Backend.Scalar.Select
import Solidity.Backend.Scalar.Combinations
import Solidity.Backend.Scalar.Composition
import Solidity.Backend.Scalar.SignedPower

/-! Task-specific encoded-byte reference fixtures. Expected stacks are kernel
controls of the independent slice. External EVM agreement is separate evidence. -/
namespace Solidity.Backend.Scalar

structure ScalarVector where
  name : String
  code : Program
  input : Stack
  expected : Stack
  accepts : Bool := true

def smallVectors : List ScalarVector := [
  ⟨"mixed-width-source-certificate", mixedWidthCode, [99], [1,99], true⟩,
  ⟨"uint8-wrap-sub", unsigned_subAt ⟨0, by decide⟩, [0,1,99], [255,99], true⟩,
  ⟨"int8-wrap-add", signed_addAt ⟨0, by decide⟩, [127,1,99], [BitVec.ofInt 256 (-128),99], true⟩,
  ⟨"int8-wrap-mul", signed_mulAt ⟨0, by decide⟩, [BitVec.ofInt 256 (-128),2,99], [0,99], true⟩,
  ⟨"uint8-div-body", unsigned_divAt ⟨0, by decide⟩, [255,2,99], [127,99], true⟩,
  ⟨"uint8-mod-body", unsigned_modAt ⟨0, by decide⟩, [255,7,99], [3,99], true⟩,
  ⟨"int8-div-wrapped-body", signed_divAt ⟨0, by decide⟩, [BitVec.ofInt 256 (-128),BitVec.ofInt 256 (-1),99], [BitVec.ofInt 256 (-128),99], true⟩,
  ⟨"int8-mod-body", signed_modAt ⟨0, by decide⟩, [BitVec.ofInt 256 (-127),3,99], [BitVec.ofInt 256 (-1),99], true⟩,
  ⟨"uint8-shl-cleanup", uintShl.code ++ unsignedCode ⟨0, by decide⟩, [128,1,99], [0,99], true⟩,
  ⟨"int8-sar-cleanup", intShr.code ++ signedCode ⟨0, by decide⟩, [BitVec.ofInt 256 (-7),300,99], [BitVec.ofInt 256 (-1),99], true⟩,
  ⟨"uint8-power-cleanup", wrappingPow.code ++ unsignedCode ⟨0, by decide⟩, [2,8,99], [0,99], true⟩,
  ⟨"signed-power-prepare-negative", powerPrepare, [BitVec.ofInt 256 (-2),3,99], [2,3,1,99], true⟩,
  ⟨"signed-power-prepare-minimum", powerPrepare, [encodeValue .int minimumInt,1,99], [BitVec.ofNat 256 (2^255),1,1,99], true⟩,
  ⟨"signed-power-post-negative-bound", powerPostTest, [BitVec.ofNat 256 (2^255),1,99], [0,BitVec.ofNat 256 (2^255),1,99], true⟩,
  ⟨"signed-power-post-positive-bound", powerPostTest, [BitVec.ofNat 256 (2^255),0,99], [1,BitVec.ofNat 256 (2^255),0,99], true⟩,
  ⟨"signed-power-apply-negative", powerSignBody, [8,1,99], [BitVec.ofInt 256 (-8),99], true⟩,
  ⟨"signed-power-apply-positive", powerSignBody, [8,0,99], [8,99], true⟩,
  ⟨"literal-normalize", [pushWord (BitVec.ofInt 256 (-1))], [99], [BitVec.ofInt 256 (-1),99], true⟩,
  ⟨"bool-not", booleanNot.code, [1,99], [0,99], true⟩,
  ⟨"bool-and", booleanAnd.code, [1,0,99], [0,99], true⟩,
  ⟨"uint-lt", uintLt.code, [3,7,99], [1,99], true⟩,
  ⟨"int-lt", intLt.code, [BitVec.ofInt 256 (-3),2,99], [1,99], true⟩,
  ⟨"uint-and", uintAnd.code, [0xab,0x0f,99], [0x0b,99], true⟩,
  ⟨"int-xor", intXor.code, [BitVec.ofInt 256 (-1),7,99], [BitVec.ofInt 256 (-8),99], true⟩,
  ⟨"uint-complement", uintNot.code, [0,99], [BitVec.ofInt 256 (-1),99], true⟩,
  ⟨"wrap-add", wrappingAdd.code, [BitVec.ofInt 256 (-1),1,99], [0,99], true⟩,
  ⟨"wrap-sub", wrappingSub.code, [0,1,99], [BitVec.ofInt 256 (-1),99], true⟩,
  ⟨"wrap-mul", wrappingMul.code, [BitVec.ofNat 256 (2^255),2,99], [0,99], true⟩,
  ⟨"wrap-power", wrappingPow.code, [2,256,99], [0,99], true⟩,
  ⟨"div", [.op .DIV], [7,2,99], [3,99], true⟩,
  ⟨"div-order-negative", [.op .DIV], [7,2,99], [0,99], false⟩,
  ⟨"mod", [.op .MOD], [7,2,99], [1,99], true⟩,
  ⟨"sdiv", [.op .SDIV], [BitVec.ofInt 256 (-7),2,99], [BitVec.ofInt 256 (-3),99], true⟩,
  ⟨"smod", [.op .SMOD], [BitVec.ofInt 256 (-7),2,99], [BitVec.ofInt 256 (-1),99], true⟩,
  ⟨"shl", uintShl.code, [3,2,99], [12,99], true⟩,
  ⟨"shr-saturation", uintShr.code, [7,256,99], [0,99], true⟩,
  ⟨"sar-negative-count", intShr.code, [8,BitVec.ofInt 256 (-1),99], [8,99], true⟩,
  ⟨"sar-negative-saturation", intShr.code, [BitVec.ofInt 256 (-7),256,99], [BitVec.ofInt 256 (-1),99], true⟩,
  ⟨"uint8-clean", unsignedCode ⟨0, by decide⟩, [257,99], [1,99], true⟩,
  ⟨"int8-clean", signedCode ⟨0, by decide⟩, [255,99], [BitVec.ofInt 256 (-1),99], true⟩,
  ⟨"int8-expansion", signedExpansionCode ⟨0, by decide⟩, [255,99], [BitVec.ofInt 256 (-1),99], true⟩,
  ⟨"bytes-widen", bytesResizeCode ⟨0, by decide⟩ ⟨1, by decide⟩, [0xab,99], [0xab00,99], true⟩,
  ⟨"bytes-narrow", bytesResizeCode ⟨1, by decide⟩ ⟨0, by decide⟩, [0xabcd,99], [0xab,99], true⟩,
  ⟨"checked-uint-add-test", unsignedAddTest, [BitVec.ofInt 256 (-1),1,99], [1,BitVec.ofInt 256 (-1),1,99], true⟩,
  ⟨"checked-uint-sub-test", unsignedSubTest, [0,1,99], [1,0,1,99], true⟩,
  ⟨"checked-uint-mul-test", unsignedMulTest, [BitVec.ofNat 256 (2^255),2,99], [1,BitVec.ofNat 256 (2^255),2,99], true⟩,
  ⟨"checked-int-add-test", signedAddTest, [BitVec.ofInt 256 ((2^255-1:Nat):Int),1,99], [1,BitVec.ofInt 256 ((2^255-1:Nat):Int),1,99], true⟩,
  ⟨"checked-int-mul-special", signedMulTest, [BitVec.ofInt 256 (-1),encodeValue .int minimumInt,99], [1,BitVec.ofInt 256 (-1),encodeValue .int minimumInt,99], true⟩,
  ⟨"checked-neg-test", negationTest, [encodeValue .int minimumInt,99], [1,encodeValue .int minimumInt,99], true⟩,
  ⟨"signed-div-overflow-test", signedDivOverflowTest, [encodeValue .int minimumInt,BitVec.ofInt 256 (-1),99], [1,encodeValue .int minimumInt,BitVec.ofInt 256 (-1),99], true⟩,
  ⟨"zero-divisor-test", zeroTest ⟨1, by decide⟩, [7,0,99], [1,7,0,99], true⟩,
  ⟨"uint8-width-test", unsignedWidthTest ⟨0, by decide⟩, [256,99], [1,256,99], true⟩,
  ⟨"int8-width-test", signedWidthTest ⟨0, by decide⟩, [BitVec.ofInt 256 (-129),99], [1,BitVec.ofInt 256 (-129),99], true⟩,
  ⟨"addmod-wide", modularBody .addmod, [BitVec.ofInt 256 (-1),1,7,99], [2,99], true⟩,
  ⟨"mulmod-wide", modularBody .mulmod, [BitVec.ofNat 256 (2^255),2,7,99], [2,99], true⟩
]

theorem smallVectors_kernel : ∀ v ∈ smallVectors,
    decide (run v.code v.input = some v.expected) = v.accepts := by decide +kernel

def powerVectors : List ScalarVector := [
  ⟨"power-uint256-fit", powerTest ⟨31, by decide⟩, [2,255,99], [0,2,255,99], true⟩,
  ⟨"power-uint256-overflow", powerTest ⟨31, by decide⟩, [2,256,99], [1,2,256,99], true⟩,
  ⟨"power-uint8-fit", powerTest ⟨0, by decide⟩, [2,7,99], [0,2,7,99], true⟩,
  ⟨"power-uint8-overflow", powerTest ⟨0, by decide⟩, [2,8,99], [1,2,8,99], true⟩,
  ⟨"power-unit-large-count", powerTest ⟨31, by decide⟩, [1,256,99], [0,1,256,99], true⟩,
  ⟨"power-zero-exponent", powerTest ⟨31, by decide⟩, [999,0,99], [0,999,0,99], true⟩
]

theorem powerVectors_kernel : ∀ v ∈ powerVectors, run v.code v.input = some v.expected := by
  intro v hv
  simp only [powerVectors, List.mem_cons, List.not_mem_nil, or_false] at hv
  rcases hv with h | h | h | h | h | h
  all_goals subst v; rw [powerTest_correct]; rfl

/-- info: 'Solidity.Backend.Scalar.smallVectors_kernel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms smallVectors_kernel
/-- info: 'Solidity.Backend.Scalar.powerVectors_kernel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms powerVectors_kernel

private def jsonBytes (xs : List UInt8) : String :=
  "[" ++ String.intercalate "," (xs.map (fun b => toString b.toNat)) ++ "]"
private def jsonStack (xs : Stack) : String :=
  "[" ++ String.intercalate "," (xs.map (fun w => "\"" ++ toString w.toNat ++ "\"")) ++ "]"
def ScalarVector.json (v : ScalarVector) : String :=
  "{\"name\":\"" ++ v.name ++ "\",\"body\":" ++ jsonBytes (Backend.encode v.code) ++
  ",\"code\":" ++ jsonBytes (Backend.encode (v.input.reverse.map pushWord ++ v.code)) ++
  ",\"input\":" ++ jsonStack v.input ++ ",\"expected\":" ++ jsonStack v.expected ++
  ",\"accepts\":" ++ (if v.accepts then "true" else "false") ++ "}"
end Solidity.Backend.Scalar

def main : IO Unit := do
  for v in Solidity.Backend.Scalar.smallVectors ++ Solidity.Backend.Scalar.powerVectors do
    IO.println v.json

-- Evaluation exports data only; smallVectors_kernel remains a kernel proof.
#eval main
