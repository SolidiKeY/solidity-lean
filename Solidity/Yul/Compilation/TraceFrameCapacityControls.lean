import Solidity.Yul.Compilation.TraceFrameCapacity
import Solidity.Yul.Compilation.ArithmeticMachine
/-! Actual compiled ADD at DUP16, tight caller/transient capacity, balanced
programs and nonvacuous V2 refusal controls. Capacity is not native gas or G24. -/
namespace Solidity.Yul.Compilation.TraceFrameCapacity.Controls
open Backend Scalar

abbrev compiled := ArithmeticMachine.addCompiled
def program := (compiled.lowered.code 14).get (by rfl)
def dirty : Scalar.Word := BitVec.ofNat 256 (2^200+257)

def addFrame (a b : Scalar.Word) (newer : Vector Scalar.Word 14) :
 Selection.V2.FrameCertificate (newer.toList++[a,b]) ((a+b)::(newer.toList++[a,b])) :=
 expression compiled 14 program (Option.some_get (by rfl)).symm #v[a,b] newer (by
   simp only [List.length_append,Vector.length_toList]; decide)

theorem actual_program : program = [.op (.DUP 15),.op (.DUP 15),.op .ADD] := rfl
theorem actual_peak : peak program = 2 := by decide

theorem frame_run (a b : Scalar.Word) (newer : Vector Scalar.Word 14) (tail : Stack) :
 Scalar.run (addFrame a b newer).code ((newer.toList++[a,b])++tail) =
 some (((a+b)::(newer.toList++[a,b]))++tail) := (addFrame a b newer).frame tail

theorem empty_capacity (a b : Scalar.Word) (newer : Vector Scalar.Word 14) :
 stackBound (addFrame a b newer).code ((newer.toList++[a,b]).length : Int) = true :=
 (addFrame a b newer).capacity_empty

theorem caller_iff (tail : Stack) : stackBound program ((16+tail.length : Nat) : Int) = true ↔ tail.length ≤ 1006 := by
 have actual := capacity_iff program 16 tail.length (by decide)
 rw [actual_peak] at actual
 constructor
 · intro h
   have bound := actual.mp h
   omega
 · intro h
   apply actual.mpr
   omega

def concrete := addFrame 5 7 (Vector.replicate 14 dirty)
def input : Stack := (Vector.replicate 14 dirty).toList++[5,7]

theorem transient_boundary (tail : Vector Scalar.Word 1006) :
 (5::7::(input++tail.toList)).length ≤ 1024 := by
 apply concrete.prefixes tail.toList (by
   simp only [List.length_append,Vector.length_toList,List.length_cons,List.length_nil]
   decide) (program.take 2) (program.drop 2) _ (by rfl)
 rfl

theorem final_fits_but_peak_fails (tail : Vector Scalar.Word 1007) :
 Scalar.run program (input++tail.toList) = some (12::(input++tail.toList)) ∧
 (12::(input++tail.toList)).length = 1024 ∧ stackBound program ((input++tail.toList).length : Int) = false := by
 constructor
 · exact concrete.frame tail.toList
 · constructor
   · simp only [input,List.length_cons,List.length_append,Vector.length_toList,List.length_nil]
   · simp only [input,List.length_append,Vector.length_toList,List.length_cons,List.length_nil]
     decide

def balanced : Program := (List.replicate 16 [.op (.DUP 0),.op .POP]).flatten

theorem balanced_peak : peak balanced = 1 := by
 have upper := (capacity_iff balanced 1 1022 (by decide)).mp (by decide)
 have first : (1 : Int) ∈ heightTrace balanced 0 := by
   change (1 : Int) ∈ 0::1::_
   exact List.mem_cons_of_mem 0 List.mem_cons_self
 have lower := (peak_spec balanced).2 1 first
 omega
theorem balanced_length : balanced.length = 32 := by decide

def balancedFrame : Selection.V2.FrameCertificate [dirty] [dirty] :=
 frame balanced [dirty] [dirty] (by rfl) (by decide)

theorem balanced_caller (tail : Vector Scalar.Word 1022) :
 stackBound balanced (([dirty]++tail.toList).length : Int) = true := by
 have room : 1+1022+peak balanced ≤ 1024 := by rw [balanced_peak]; decide
 have actual := (capacity_iff balanced 1 1022 (by decide)).mpr room
 simpa only [List.length_append,List.length_cons,List.length_nil,Vector.length_toList] using actual

def pushRun (input : Vector Scalar.Word 1024) : Scalar.run [pushWord 0] input.toList = some (0::input.toList) := by
 simp only [Scalar.run,step_pushWord,Option.bind_some]

theorem overfull_refused (input : Vector Scalar.Word 1024) :
 (frame? [pushWord 0] input.toList (0::input.toList) (pushRun input)).isNone = true := by
 simp only [frame?,Vector.length_toList]
 rfl

theorem no_fake_overfull (input : Vector Scalar.Word 1024) :
 ¬ Nonempty (Selection.V2.FrameCertificate input.toList (0::input.toList)) :=
 Selection.V2.no_overfull_output _ _ (by simp only [List.length_cons,Vector.length_toList]; decide)

theorem operand_refusal (output : Stack) :
 ¬ ∃ c : Selection.V2.FrameCertificate [] output, c.code = [.op (.DUP 15)] := by
 rintro ⟨c,code⟩
 have actual := c.frame []
 rw [code] at actual
 cases actual

#guard Scalar.stackBound [.op (.DUP 15)] 0
#guard Scalar.run [.op (.DUP 15)] [] = none
#guard !(Scalar.stackBound program 1023)
#guard Scalar.stackBound program 1022
#guard (compiled.lowered.code 15).isNone
#guard peak [pushWord dirty,.op .POP] = 1
#guard peak [.op .POP] = 0
#guard peak [] = 0
/-- info: 'Solidity.Yul.Compilation.TraceFrameCapacity.Controls.actual_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms actual_program
/-- info: 'Solidity.Yul.Compilation.TraceFrameCapacity.Controls.actual_peak' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms actual_peak
/-- info: 'Solidity.Yul.Compilation.TraceFrameCapacity.Controls.frame_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms frame_run
/-- info: 'Solidity.Yul.Compilation.TraceFrameCapacity.Controls.empty_capacity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms empty_capacity
/-- info: 'Solidity.Yul.Compilation.TraceFrameCapacity.Controls.caller_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms caller_iff
/-- info: 'Solidity.Yul.Compilation.TraceFrameCapacity.Controls.transient_boundary' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms transient_boundary
/-- info: 'Solidity.Yul.Compilation.TraceFrameCapacity.Controls.final_fits_but_peak_fails' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms final_fits_but_peak_fails
/-- info: 'Solidity.Yul.Compilation.TraceFrameCapacity.Controls.balanced_peak' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms balanced_peak
/-- info: 'Solidity.Yul.Compilation.TraceFrameCapacity.Controls.balanced_length' depends on axioms: [propext] -/
#guard_msgs in
#print axioms balanced_length
/-- info: 'Solidity.Yul.Compilation.TraceFrameCapacity.Controls.balanced_caller' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms balanced_caller
/-- info: 'Solidity.Yul.Compilation.TraceFrameCapacity.Controls.overfull_refused' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms overfull_refused
/-- info: 'Solidity.Yul.Compilation.TraceFrameCapacity.Controls.no_fake_overfull' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms no_fake_overfull
/-- info: 'Solidity.Yul.Compilation.TraceFrameCapacity.Controls.operand_refusal' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms operand_refusal
/-- info: 'Solidity.Yul.Compilation.TraceFrameCapacity.Controls.addFrame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms addFrame
/-- info: 'Solidity.Yul.Compilation.TraceFrameCapacity.Controls.balancedFrame' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms balancedFrame
/-- info: 'Solidity.Yul.Compilation.TraceFrameCapacity.Controls.pushRun' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms pushRun
end Solidity.Yul.Compilation.TraceFrameCapacity.Controls
