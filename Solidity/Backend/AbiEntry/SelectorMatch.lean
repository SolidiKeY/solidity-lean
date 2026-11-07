import Solidity.Backend.AbiEntry.SelectorMatchInterface
import Solidity.Backend.AbiEntry.CalldataWord
import Solidity.Backend.Selection.InterfaceV2

/-! Actual SHR/EQ selector predicate. The raw theorem retains the full-prefix
condition; padded partial prefixes are not source selector matches. -/
namespace Solidity.Backend.AbiEntry.SelectorMatch
open Scalar
private def extract : Program := [pushByte 224,.op .SHR]
def code (selector : Vector UInt8 4) : Program :=
  extract++[pushWord (BitVec.ofNat 256 (Source.beValue selector.toList)),.op .EQ]

private theorem selector_bound (selector : Vector UInt8 4) : Source.beValue selector.toList<2^256 := by
  have bounded : Source.beValue selector.toList<256^4 := by
    simpa only [Vector.length_toList] using Yul.Views.scalar_beValue_bound selector.toList
  exact Nat.lt_trans bounded (by decide)

private theorem extract_run (word : Scalar.Word) (suffix : Stack) :
    run extract (word::suffix)=some ((word>>>224)::suffix) := by
  rw [extract,run,step_pushByte]
  rfl

theorem numeric (selector : Vector UInt8 4) (word : Scalar.Word) (suffix : Stack) :
    run (code selector) (word::suffix)=
      some (flag (decide (word.toNat/2^224=Source.beValue selector.toList))::suffix) := by
  rw [code,run_append,extract_run]
  simp only [Option.bind_some]
  rw [run,step_pushWord]
  simp only [Option.bind_some,run,step,numericStep,unary,binary,applyBinary]
  have comparison : (BitVec.ofNat 256 (Source.beValue selector.toList)==word>>>224)=
      decide (word.toNat/2^224=Source.beValue selector.toList) := by
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq,decide_eq_true_eq,BitVec.toNat_eq,BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (selector_bound selector),BitVec.toNat_ushiftRight,Nat.shiftRight_eq_div_pow]
    exact eq_comm
  rw [comparison]

private theorem append_value (headBytes rest : List UInt8) :
    Source.beValue (headBytes++rest)=Source.beValue headBytes*256^rest.length+Source.beValue rest := by
  have aux (xs : List UInt8) : Source.beValue (headBytes++xs.reverse)=
      Source.beValue headBytes*256^xs.reverse.length+Source.beValue xs.reverse := by
    induction xs with
    | nil => simp only [List.reverse_nil,List.append_nil,List.length_nil,Nat.pow_zero,Nat.mul_one];rfl
    | cons byte xs ih =>
      rw [List.reverse_cons,←List.append_assoc,Source.beValue_append,ih,Source.beValue_append,
        List.length_append,List.length_singleton,Nat.pow_succ]
      simp only [Nat.add_mul,Nat.mul_assoc,Nat.add_assoc]
  simpa only [List.reverse_reverse] using aux rest.reverse

private theorem high_prefix (bytes : List UInt8) (length : bytes.length=32) :
    Source.beValue bytes/2^224=Source.beValue (bytes.take 4) := by
  have split := append_value (bytes.take 4) (bytes.drop 4)
  rw [List.take_append_drop] at split
  have rest : (bytes.drop 4).length=28 := by rw [List.length_drop,length]
  rw [rest] at split
  have bounded := Yul.Views.scalar_beValue_bound (bytes.drop 4)
  rw [rest] at bounded
  rw [show (2 : Nat)^224=256^28 from by decide,split,Nat.add_comm,
    Nat.add_mul_div_right _ _ (by decide : 0<(256 : Nat)^28),Nat.div_eq_of_lt bounded,Nat.zero_add]

private theorem padded_prefix (bytes : List UInt8) (full : 4≤bytes.length) :
    (Source.fitBytes 32 bytes).take 4=bytes.take 4 := by
  apply List.ext_getElem?
  intro i
  by_cases inside : i<4
  · rw [List.getElem?_take_of_lt inside,Yul.Views.abi_fitBytes_byte _ 32 i (by omega),
      List.getElem?_take_of_lt inside,List.getElem?_eq_getElem (by omega : i<bytes.length)]
    rfl
  · have left : ((Source.fitBytes 32 bytes).take 4).length≤i := by rw [List.length_take];omega
    have right : (bytes.take 4).length≤i := by rw [List.length_take];omega
    rw [List.getElem?_eq_none left,List.getElem?_eq_none right]

private theorem bytes_injective (left right : List UInt8) (length : left.length=right.length) :
    Source.beValue left=Source.beValue right ↔ left=right := by
  constructor
  · intro same
    calc left=Source.beBytes left.length (Source.beValue left) := (Yul.Views.scalar_beBytes_value left).symm
         _=Source.beBytes right.length (Source.beValue right) := by rw [length,same]
         _=right := Yul.Views.scalar_beBytes_value right
  · exact congrArg Source.beValue

theorem raw (selector : Vector UInt8 4) (frame : Source.Fr) (full : 4≤frame.cd.length) (suffix : Stack) :
    run (code selector) (BitVec.ofNat 256 (Solidity.AbiEntry.load frame.cd 0)::suffix)=
      some (flag (frame.cd.take 4==selector.toList)::suffix) := by
  rw [numeric,BitVec.toNat_ofNat]
  have bounded : Solidity.AbiEntry.load frame.cd 0<2^256 := Solidity.AbiEntry.load_lt _ _
  rw [Nat.mod_eq_of_lt bounded,CalldataWord.load]
  change some (flag (decide (Source.beValue (Source.fitBytes 32 frame.cd)/2^224=
    Source.beValue selector.toList))::suffix)=_
  rw [high_prefix _ (Source.fitBytes_length _ _),padded_prefix _ full]
  have length : (frame.cd.take 4).length=selector.toList.length := by
    simp only [List.length_take,Vector.length_toList]
    omega
  have same : decide (Source.beValue (frame.cd.take 4)=Source.beValue selector.toList)=
      (frame.cd.take 4==selector.toList) := by
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq,beq_iff_eq,bytes_injective _ _ length]
  rw [same]

theorem capacity (selector : Vector UInt8 4) (suffix : Stack) (room : suffix.length+2≤1024) :
    stackBound (code selector) ((suffix.length+1 : Nat) : Int)=true := by
  simp only [code,extract,List.cons_append,List.nil_append,stackBound,heightTrace,stackDelta,
    pushWord,pushByte,numericDelta,unary,binary,Option.isSome_some,Option.isSome_none,ite_true,
    ite_false,Bool.false_eq_true,List.all_cons,List.all_nil,Bool.and_true,safeHeight,
    Bool.and_eq_true,decide_eq_true_eq]
  omega

/-- Preserve the actual Source fixed-hash selector, with its intrinsic width. -/
def sourceSelector {E : Source.Env} (global : Source.Glob E) (signature : List Char) : Vector UInt8 4 :=
  ⟨(global.selector signature).toArray,by
    simp only [List.size_toArray,Source.Glob.selector,List.length_take,Source.wordBytes_length]
    decide⟩

theorem source_bytes {E : Source.Env} (global : Source.Glob E) (signature : List Char) :
    (sourceSelector global signature).toList=global.selector signature := List.toList_toArray

/-- Numeric value of the actual fixed-hash prefix, using the proved byte split. -/
theorem source_value {E : Source.Env} (global : Source.Glob E) (signature : List Char) :
    Source.beValue (sourceSelector global signature).toList=
      (global.fixed.hash (Source.asciiBytes signature)).val/2^224 := by
  rw [source_bytes]
  have exactPrefix := high_prefix (Source.wordBytes (global.fixed.hash (Source.asciiBytes signature)))
    (Source.wordBytes_length _)
  rw [Source.wordBytes_value] at exactPrefix
  exact exactPrefix.symm

theorem source_raw {E : Source.Env} (global : Source.Glob E) (signature : List Char)
    (frame : Source.Fr) (full : 4≤frame.cd.length) (suffix : Stack) :
    run (code (sourceSelector global signature))
      (BitVec.ofNat 256 (Solidity.AbiEntry.load frame.cd 0)::suffix)=
      some (flag (global.selector signature==frame.cd.take 4)::suffix) := by
  rw [raw _ frame full suffix,source_bytes]
  have symmetric : (frame.cd.take 4==global.selector signature)=
      (global.selector signature==frame.cd.take 4) := by
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq]
    exact eq_comm
  rw [symmetric]

theorem short_no_match (selector : Vector UInt8 4) (bytes : List UInt8) (short : bytes.length<4) :
    (bytes.take 4==selector.toList)=false := by
  have unequal : bytes.take 4≠selector.toList := by
    intro same
    have length := congrArg List.length same
    simp only [List.length_take,Vector.length_toList] at length
    omega
  cases matched : bytes.take 4==selector.toList with
  | false => rfl
  | true => exact False.elim (unequal (eq_of_beq matched))

def frameCertificate (selector : Vector UInt8 4) (word : Scalar.Word) :
    Selection.V2.FrameCertificate [word]
      [flag (decide (word.toNat/2^224=Source.beValue selector.toList))] where
  code := code selector
  peak := 1
  inputRoom := by change (1 : Nat)+1≤1024;decide
  frame := numeric selector word
  capacity := by
    intro suffix room
    simp only [List.cons_append,List.nil_append,List.length_cons] at room ⊢
    exact capacity selector suffix room

def certificate : Interface.SelectorMatchCertificate code where
  numeric := numeric
  raw := raw
  capacity := capacity

/-- info: 'Solidity.Backend.AbiEntry.SelectorMatch.numeric' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms numeric
/-- info: 'Solidity.Backend.AbiEntry.SelectorMatch.raw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms raw
/-- info: 'Solidity.Backend.AbiEntry.SelectorMatch.capacity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms capacity
/-- info: 'Solidity.Backend.AbiEntry.SelectorMatch.source_bytes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms source_bytes
/-- info: 'Solidity.Backend.AbiEntry.SelectorMatch.source_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms source_value
/-- info: 'Solidity.Backend.AbiEntry.SelectorMatch.source_raw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms source_raw
/-- info: 'Solidity.Backend.AbiEntry.SelectorMatch.short_no_match' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms short_no_match
/-- info: 'Solidity.Backend.AbiEntry.SelectorMatch.frameCertificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms frameCertificate
/-- info: 'Solidity.Backend.AbiEntry.SelectorMatch.certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms certificate
end Solidity.Backend.AbiEntry.SelectorMatch
