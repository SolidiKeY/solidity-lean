import tests.«v13-abi-world».RecursiveFixtures
namespace Solidity.Backend.AbiWorld.RecursiveControls
open AbiEntry RecursiveLayout

def onePs : List Param := [{shape := Row,loc := .memory}]
def oneVals : Vals (onePs.map Param.shape) := .cons (row []) .nil
def one : Input := RecursiveEntry.input onePs oneVals sel (List.replicate 32 0) 128
def altered (I : Input) (p n : Nat) : Input :=
  {I with data := I.data.take p ++ AbiEntry.wordBytes n ++ I.data.drop (p+32)}
def wrong : Input := altered one 4 64
def badOffset : Input := altered one 4 (lim+1)
def short : Input := ⟨sel ++ AbiEntry.wordBytes 32 ++ AbiEntry.wordBytes 300 ++
  AbiEntry.wordBytes 7 ++ AbiEntry.wordBytes 11 ++ AbiEntry.wordBytes 128 ++ List.replicate 16 0,128⟩
def exact : Input := {one with free := lim-192}
def over : Input := {exact with free := exact.free+1}
def truncatedPanic : Input := {short with free := lim-100}
def cursor (I : Input) (f : Nat) := NestedByteControls.cursor I f onePs
def err (I : Input) (f : Nat) := DynamicListControls.err (entry I f onePs)

theorem baseline : cursor one 10 = some 192 ∧ cursor exact 10 = some 192 ∧
    err over 10 = 2 ∧ err one 0 = 3 := by decide +kernel

theorem malformed : err badOffset 10 = 1 ∧ err short 10 = 1 ∧ err truncatedPanic 10 = 2 := by
  constructor
  · decide +kernel
  constructor <;> decide +kernel

def shortPayload : Input := ⟨sel ++ AbiEntry.wordBytes 32 ++ AbiEntry.wordBytes 300 ++
  AbiEntry.wordBytes 7 ++ AbiEntry.wordBytes 11 ++ AbiEntry.wordBytes 128 ++ AbiEntry.wordBytes 2 ++ [0],128⟩
def payloadPanic : Input := {shortPayload with free := lim-223}
theorem payload_priority : err shortPayload 10 = 1 ∧ err payloadPanic 10 = 2 := by
  constructor <;> decide +kernel

def zeroVal : AbiEntry.Val (.fixed U 0) := .fixed .nil
def zeroPs : List Param := [{shape := .fixed U 0,loc := .memory}]
def zeroInput : Input := ⟨sel,128⟩
def paddedZero : Input := ⟨sel ++ List.replicate 32 0,128⟩
theorem fixed_zero : DynamicListControls.err (entry zeroInput 2 zeroPs) = 1 ∧
    NestedByteControls.cursor paddedZero 2 zeroPs = some 0 := by decide +kernel

/-- info: 'Solidity.Backend.AbiWorld.RecursiveControls.baseline' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms baseline
/-- info: 'Solidity.Backend.AbiWorld.RecursiveControls.malformed' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms malformed
/-- info: 'Solidity.Backend.AbiWorld.RecursiveControls.fixed_zero' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms fixed_zero
/-- info: 'Solidity.Backend.AbiWorld.RecursiveControls.payload_priority' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms payload_priority
end Solidity.Backend.AbiWorld.RecursiveControls
