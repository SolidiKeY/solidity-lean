import Solidity.Yul.Compilation.NestedWrites
import Solidity.Backend.Selection.FrameCapacityV2
/-! Concrete Yul target slices inhabit the published nonvacuous V2 frame
contract. Capacity covers actual Scalar prefixes, not native expanded control,
charged EVM execution, source G24 or a V12 function calling convention. -/
namespace SolidityBridge.Yul.FrameCertificatesV2
open Solidity Backend Scalar
open Solidity.Yul.Compilation

/-- Existing finite update data need one spare word exactly when nonempty. -/
def updatePeak {n k : Nat} : NestedWrites n k → Nat
  | [] => 0
  | _::_ => 1

/-- Actual DUP under a fixed live prefix, with one real spare word. -/
def readFrame {n k : Nat} (locals : Vector Word n) (newer : Vector Word k)
    (i : Fin n) (accessible : k + i.val < 16) (room : k + n + 1 ≤ 1024) :
    Selection.V2.FrameCertificate (newer.toList ++ locals.toList)
      (locals[i.val] :: (newer.toList ++ locals.toList)) where
  code := [readSlot ⟨k + i.val,accessible⟩]
  peak := 1
  inputRoom := by simpa only [List.length_append,Vector.length_toList] using room
  frame := by
    intro tail
    have actual : run [readSlot ⟨k + i.val,accessible⟩]
        (newer.toList ++ (locals.toList ++ tail)) =
        some (locals[i.val] :: (newer.toList ++ (locals.toList ++ tail))) := by
      simp only [run,read_under_prefix locals newer i accessible tail,Option.bind_some]
    simpa only [List.cons_append,List.append_assoc] using actual
  capacity := by
    intro tail admitted
    have spare : k + n + tail.length + 1 ≤ 1024 := by
      simpa only [List.length_append,Vector.length_toList] using admitted
    simpa only [List.length_append,Vector.length_toList] using
      (read_local_bound_iff (k+n) ⟨k+i.val,accessible⟩ tail).mpr spare

/-- Supplied-value SWAP/POP uses zero EXTRA words: the value is already part
of the input. This is distinct from a sequence which emits a PUSH first. -/
def writeFrame {n k : Nat} (locals : Vector Word n) (newer : Vector Word k)
    (i : Fin n) (accessible : k + i.val < 16) (value : Word)
    (room : k + n + 1 ≤ 1024) :
    Selection.V2.FrameCertificate (value :: (newer.toList ++ locals.toList))
      (newer.toList ++ (locals.set i.val value i.isLt).toList) where
  code := writeSlot ⟨k + i.val,accessible⟩
  peak := 0
  inputRoom := by
    simpa only [List.length_cons,List.length_append,Vector.length_toList,Nat.add_zero] using room
  frame := by
    intro tail
    simpa only [List.cons_append,List.append_assoc] using
      write_under_prefix locals newer i accessible value tail
  capacity := by
    intro tail admitted
    have height : ((value :: (newer.toList ++ locals.toList)) ++ tail).length =
        k + n + tail.length + 1 := by
      simp only [List.length_cons,List.length_append,Vector.length_toList]
      omega
    have spare : k + n + tail.length + 1 ≤ 1024 := by
      rw [height] at admitted
      simpa only [Nat.add_zero] using admitted
    rw [height]
    exact (write_local_bound_iff (k+n) ⟨k+i.val,accessible⟩ tail).mpr spare

/-- Actual finite old-local updates. V2 inputRoom admits the empty caller;
capacity is derived for every admitted caller, never assumed as a field. -/
def updatesFrame {n k : Nat} (writes : NestedWrites n k)
    (locals : Vector Word n) (newer : Vector Word k)
    (room : k + n + updatePeak writes ≤ 1024) :
    Selection.V2.FrameCertificate (newer.toList ++ locals.toList)
      (newer.toList ++ (updatedLocals locals (oldWrites writes)).toList) := by
  cases writes with
  | nil =>
    exact Selection.V2.identityFrame (newer.toList ++ locals.toList) (by
      simpa only [List.length_append,Vector.length_toList,updatePeak,Nat.add_zero] using room)
  | cons first rest =>
    refine ⟨writeSequence (shiftedWrites (first::rest)),1,?_,?_,?_⟩
    · simpa only [List.length_append,Vector.length_toList,updatePeak] using room
    · intro tail
      simpa only [List.append_assoc] using nested_writes_run (first::rest) locals newer tail
    · intro tail admitted
      have spare : k + n + tail.length + 1 ≤ 1024 := by
        simpa only [List.length_append,Vector.length_toList] using admitted
      simpa only [List.length_append,Vector.length_toList] using
        nested_writes_bound (first::rest) tail spare

/-- These target-package checks are not source admission or a new calling
convention. Live accessibility and physical room are tested independently. -/
def read? {n k : Nat} (locals : Vector Word n) (newer : Vector Word k) (i : Fin n) :
    Option (Selection.V2.FrameCertificate (newer.toList ++ locals.toList)
      (locals[i.val] :: (newer.toList ++ locals.toList))) :=
  if accessible : k + i.val < 16 then
    if room : k + n + 1 ≤ 1024 then some (readFrame locals newer i accessible room) else none
  else none

def write? {n k : Nat} (locals : Vector Word n) (newer : Vector Word k)
    (i : Fin n) (value : Word) :
    Option (Selection.V2.FrameCertificate (value :: (newer.toList ++ locals.toList))
      (newer.toList ++ (locals.set i.val value i.isLt).toList)) :=
  if accessible : k + i.val < 16 then
    if room : k + n + 1 ≤ 1024 then some (writeFrame locals newer i accessible value room) else none
  else none

def updates? {n k : Nat} (writes : NestedWrites n k)
    (locals : Vector Word n) (newer : Vector Word k) :
    Option (Selection.V2.FrameCertificate (newer.toList ++ locals.toList)
      (newer.toList ++ (updatedLocals locals (oldWrites writes)).toList)) :=
  if room : k + n + updatePeak writes ≤ 1024 then some (updatesFrame writes locals newer room) else none

end SolidityBridge.Yul.FrameCertificatesV2
