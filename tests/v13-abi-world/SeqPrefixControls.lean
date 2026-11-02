import Solidity.Backend.AbiWorld.SeqPrefix
namespace Solidity.Backend.AbiWorld.SeqPrefixControls
open AbiEntry RecursiveLayout

def xs : Seq .bytes 1 := .cons (.bytes [0,255]) .nil
def ys : Seq .bytes 1 := .cons (.bytes []) .nil
def zs : Seq .bytes 1 := .cons (.bytes (List.replicate 33 17)) .nil
def sel : List UInt8 := [9,0,0,1]
def post : List UInt8 := List.replicate 32 0
def sample (tail : Seq .bytes 1) : Input :=
  ⟨sel ++ encodeArgs (.cons (.array (SeqPrefix.append xs tail)) .nil) ++ post,128⟩
def hp : List UInt8 := sel ++ AbiEntry.wordBytes 32 ++ AbiEntry.wordBytes 2

theorem data (tail : Seq .bytes 1) : (sample tail).data = hp ++
    (AbiEntry.assemble.go (Seq.parts (SeqPrefix.append xs tail)) 64).1 ++ [] ++
    (AbiEntry.assemble.go (Seq.parts (SeqPrefix.append xs tail)) 64).2 ++ post := by
  simpa only [sample,hp,List.append_nil,List.nil_append] using SeqPrefix.array_data xs tail sel post 128

theorem sizes : (sample ys).size = 260 ∧ (sample zs).size = 324 := by decide +kernel

theorem decoded_prefix (tail : Seq .bytes 1) (size : (sample tail).size ≤ lim) :
    mseq (sample tail) 4 .bytes 68 0 1 96 = .ok (xs,160) := by
  apply SeqPrefix.window xs tail (sample tail) hp [] post 68 0 64 96 4
  · decide +kernel
  · decide +kernel
  · exact data tail
  · decide +kernel
  · exact size
  · change 128 + (96 + sequenceAllocation xs) ≤ lim; decide +kernel
  · decide +kernel

theorem both_prefix : mseq (sample ys) 4 .bytes 68 0 1 96 = .ok (xs,160) ∧
    mseq (sample zs) 4 .bytes 68 0 1 96 = .ok (xs,160) := by
  constructor
  · apply decoded_prefix; rw [sizes.1]; decide +kernel
  · apply decoded_prefix; rw [sizes.2]; decide +kernel

/-- Actual outer allocation, with a nonzero incoming element cursor. -/
theorem outer : alloc (sample ys) 0 96 = .ok 96 ∧ alloc (sample zs) 0 96 = .ok 96 := by
  simp only [alloc,sample,if_pos (show 128 + (0 + roundUp 96) ≤ lim from by decide +kernel)]
  exact ⟨rfl,rfl⟩
/-- Original recursive decrement: the second element is read with f=3,
index ONE and the cursor returned by the first element. -/
theorem suffix_empty : mseq (sample ys) 3 .bytes 68 1 1 160 = .ok (ys,192) := by
  apply SeqPrefix.window ys (.nil : Seq .bytes 0) (sample ys)
    (hp ++ AbiEntry.wordBytes 64) (Val.enc (.bytes [0,255])) post 68 1 128 160 3
  all_goals decide +kernel

theorem suffix_33 : mseq (sample zs) 3 .bytes 68 1 1 160 = .ok (zs,256) := by
  apply SeqPrefix.window zs (.nil : Seq .bytes 0) (sample zs)
    (hp ++ AbiEntry.wordBytes 64) (Val.enc (.bytes [0,255])) post 68 1 128 160 3
  all_goals decide +kernel

theorem actual_wrong_cursor : mseq (sample zs) 3 .bytes 68 1 1 160 ≠ .ok (zs,192) := by
  simp only [Nat.zero_add,suffix_33]
  intro bad
  have cur : (256 : Nat) = 192 := congrArg Prod.snd (Except.ok.inj bad)
  cases (by decide +kernel : (256 : Nat) ≠ 192) cur

theorem fuel_zero : mseq (sample ys) 0 .bytes 68 1 1 160 = .error .fuel := rfl

theorem wrong_cursor : (160 : Nat) ≠ 192 ∧ (192 : Nat) ≠ 256 := by decide +kernel
/-- Both selected fragments compose into ACTUAL two-element mseq on
one input, with the original decrement and reached allocation cursor. -/
theorem full_empty : mseq (sample ys) 4 .bytes 68 0 2 96 = .ok (SeqPrefix.append xs ys,192) := by
  have h := SeqPrefix.singleton_element (sample ys) 3 .bytes 68 0 96 160 (.bytes [0,255]) both_prefix.1
  rw [mseq,h]
  simp only [Nat.zero_add,suffix_empty]
  rfl

theorem full_33 : mseq (sample zs) 4 .bytes 68 0 2 96 = .ok (SeqPrefix.append xs zs,256) := by
  have h := SeqPrefix.singleton_element (sample zs) 3 .bytes 68 0 96 160 (.bytes [0,255]) both_prefix.2
  rw [mseq,h]
  simp only [Nat.zero_add,suffix_33]
  rfl

/-- info: 'Solidity.Backend.AbiWorld.SeqPrefix.parts_cast' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.AbiWorld.SeqPrefix.parts_cast
/-- info: 'Solidity.Backend.AbiWorld.SeqPrefix.parts_append' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.AbiWorld.SeqPrefix.parts_append
/-- info: 'Solidity.Backend.AbiWorld.SeqPrefix.allocation_cast' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.AbiWorld.SeqPrefix.allocation_cast
/-- info: 'Solidity.Backend.AbiWorld.SeqPrefix.allocation_append' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.AbiWorld.SeqPrefix.allocation_append
/-- info: 'Solidity.Backend.AbiWorld.SeqPrefix.array_data' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.AbiWorld.SeqPrefix.array_data
/-- info: 'Solidity.Backend.AbiWorld.SeqPrefix.window' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.AbiWorld.SeqPrefix.window
/-- info: 'Solidity.Backend.AbiWorld.SeqPrefix.noninterference' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.AbiWorld.SeqPrefix.noninterference
/-- info: 'Solidity.Backend.AbiWorld.SeqPrefixControls.data' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.AbiWorld.SeqPrefixControls.data
/-- info: 'Solidity.Backend.AbiWorld.SeqPrefixControls.sizes' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.AbiWorld.SeqPrefixControls.sizes
/-- info: 'Solidity.Backend.AbiWorld.SeqPrefixControls.decoded_prefix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.AbiWorld.SeqPrefixControls.decoded_prefix
/-- info: 'Solidity.Backend.AbiWorld.SeqPrefixControls.both_prefix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.AbiWorld.SeqPrefixControls.both_prefix
/-- info: 'Solidity.Backend.AbiWorld.SeqPrefixControls.outer' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.AbiWorld.SeqPrefixControls.outer
/-- info: 'Solidity.Backend.AbiWorld.SeqPrefixControls.suffix_empty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.AbiWorld.SeqPrefixControls.suffix_empty
/-- info: 'Solidity.Backend.AbiWorld.SeqPrefixControls.suffix_33' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.AbiWorld.SeqPrefixControls.suffix_33
/-- info: 'Solidity.Backend.AbiWorld.SeqPrefixControls.fuel_zero' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.AbiWorld.SeqPrefixControls.fuel_zero
/-- info: 'Solidity.Backend.AbiWorld.SeqPrefixControls.wrong_cursor' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.AbiWorld.SeqPrefixControls.wrong_cursor
/-- info: 'Solidity.Backend.AbiWorld.SeqPrefixControls.actual_wrong_cursor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.AbiWorld.SeqPrefixControls.actual_wrong_cursor
/-- info: 'Solidity.Backend.AbiWorld.SeqPrefix.singleton_element' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.AbiWorld.SeqPrefix.singleton_element
/-- info: 'Solidity.Backend.AbiWorld.SeqPrefixControls.full_empty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.AbiWorld.SeqPrefixControls.full_empty
/-- info: 'Solidity.Backend.AbiWorld.SeqPrefixControls.full_33' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.AbiWorld.SeqPrefixControls.full_33
end Solidity.Backend.AbiWorld.SeqPrefixControls
