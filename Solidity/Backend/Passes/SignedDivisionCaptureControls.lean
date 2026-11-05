import Solidity.Backend.Passes.SignedDivisionCapture
import Solidity.Backend.PrimitivePackets.SignedDiv.Controls

/-! Actual public signed-division capture, both modes/pipelines, complete frame
and heap observations. Primitive Source panic payloads remain producer facts. -/
namespace Solidity.Backend.Passes.SignedDivisionCaptureControls
open Evm Evm.Memory Evm.Compiler Backend.PrimitivePackets
open SignedDivisionCapture
open SignedDiv.Controls (P Γ F target machine negSeven two minus)
open Source.SemanticsExamples (G0 F0)

abbrev i : Idx Γ (.val .int) := .here
abbrev j : Idx Γ (.val .int) := .there .here
def name : Var := .user "quotient"
def quotient : PrimTy.int.Denote := SignedDiv.quotient negSeven two (by decide) (by decide)

theorem initial7 (a d : PrimTy.int.Denote) :
    StateRepr 1 0 7 F (target a d) CompileExamples.base (machine a d) := by
  apply memory_frame (SignedDiv.Controls.initial a d) (by decide)
  · intro p r
    unfold CompileExamples.base
    split <;> decide
  · intro s r
    unfold CompileExamples.base
    split <;> decide

def updateCode : CompiledVal 0 (F.push (.val .int) .ok) (update (C := P) (Γ := Γ)) :=
  (Memory.compileVal 0 (F.push (.val .int) .ok) update).get (by rfl)

theorem evaluated (checked : Bool) :
    (SignedDiv.expression checked i j).evalT (target negSeven two) = .ok quotient :=
  ordinary_value checked i j (target negSeven two) negSeven two rfl rfl (by decide) (by decide)

def after (v : PrimTy.int.Denote) (tail : List Word) : Machine :=
  writeMachine (writeMachine {(machine negSeven two) with stack := tail} 6 (.val (sword v.val))) 4 w[0]

theorem joined (checked : Bool) (tail : List Word) :
    run ((code (C := P) 0 F checked i j name).code ++ (reader (C := P) 0 F checked i j name).code)
      {(machine negSeven two) with stack := tail} =
      .ok ((after quotient tail).push (.val (sword quotient.val))) 0 := by
  obtain ⟨cw,uw,cr,ur,runs⟩ := CapturedValueStability.execution name
    (SignedDiv.expression checked i j) (SignedDiv.selected 0 F checked i j) j update updateCode
    (initial7 negSeven two) (by decide) quotient zero (evaluated checked) rfl
  have cword := SignedDiv.Controls.word_unique quotient cw cr
  have uword := SignedDiv.Controls.word_unique zero uw ur
  subst cw
  subst uw
  have actual := runs tail
  have codeEq : (code (C := P) 0 F checked i j name).code =
      (CapturedValueStability.compiled name (SignedDiv.expression checked i j)
        (SignedDiv.selected 0 F checked i j) j update updateCode).code := by
    cases checked <;> rfl
  have readEq : (reader (C := P) 0 F checked i j name).code = [.mload 6] := rfl
  rw [codeEq,readEq,run_append_ok actual.2.2.2.2.1]
  exact actual.2.2.2.2.2

def cells : List Nat := [6,5,4,3,2,1,0,16,17,18,20,21]
theorem observations (tail : List Word) :
    (cells.map ((after quotient tail).push (.val (sword quotient.val))).mem,
      ((after quotient tail).push (.val (sword quotient.val))).stack) =
      ([.val (sword (-3)),.val (sword (-7)),w[0],w[0],w[16],w[16],w[20],
        w[2],w[7],w[9],w[1],w[4]],.val (sword (-3)) :: tail) := rfl

theorem origin (p : Roadmap.Pipeline) (checked : Bool) (fuel : Nat) : type_of%
    (ordinary (G0 p) F0 fuel (SignedDiv.Controls.source negSeven two) (target negSeven two)
      .here (.there .here) i j checked name negSeven two rfl rfl rfl rfl
      (by decide) (by decide) (initial7 negSeven two) (by decide)) :=
  ordinary (G0 p) F0 fuel (SignedDiv.Controls.source negSeven two) (target negSeven two)
    .here (.there .here) i j checked name negSeven two rfl rfl rfl rfl
    (by decide) (by decide) (initial7 negSeven two) (by decide)

theorem zero_rejected (checked : Bool) (tail : List Word) :
    run ((code (C := P) 0 F checked i j name).code ++ (reader (C := P) 0 F checked i j name).code)
      {(machine negSeven SignedDiv.Controls.zero) with stack := tail} = .revert :=
  (rejected checked i j name (initial7 negSeven SignedDiv.Controls.zero) (by decide)
    (SignedDiv.intrinsic_zero _ checked i j negSeven SignedDiv.Controls.zero rfl rfl rfl) tail).2

theorem checked_overflow (tail : List Word) :
    run ((code (C := P) 0 F true i j name).code ++ (reader (C := P) 0 F true i j name).code)
      {(machine Backend.Scalar.minimumInt minus) with stack := tail} = .revert :=
  (rejected true i j name (initial7 Backend.Scalar.minimumInt minus) (by decide)
    (SignedDiv.intrinsic_overflow _ i j Backend.Scalar.minimumInt minus rfl rfl rfl rfl).1 tail).2

theorem unchecked_overflow : type_of%
    (shared false i j name (initial7 Backend.Scalar.minimumInt minus) (by decide) Backend.Scalar.minimumInt
      (SignedDiv.intrinsic_overflow _ i j Backend.Scalar.minimumInt minus rfl rfl rfl rfl).2) :=
  shared false i j name (initial7 Backend.Scalar.minimumInt minus) (by decide) Backend.Scalar.minimumInt
    (SignedDiv.intrinsic_overflow _ i j Backend.Scalar.minimumInt minus rfl rfl rfl rfl).2

/-- Full independent Source panic distinctions from the published producer. -/
theorem zero_source (p : Roadmap.Pipeline) (checked : Bool) (fuel : Nat) (tail : List Word) :
    type_of% (SignedDiv.Controls.zero_both p checked fuel tail) :=
  SignedDiv.Controls.zero_both p checked fuel tail

theorem overflow_source (p : Roadmap.Pipeline) (fuel : Nat) (tail : List Word) :
    type_of% (SignedDiv.Controls.overflow_both p fuel tail) :=
  SignedDiv.Controls.overflow_both p fuel tail

def observe : Evm.Out → Option (List Word × List Word)
  | .ok m _ => some (cells.map m.mem,m.stack)
  | _ => none

def wrong : PrimTy.int.Denote := ⟨-4,by decide⟩
theorem wrong_floor (checked : Bool) :
    observe (run ((code (C := P) 0 F checked i j name).code ++ (reader (C := P) 0 F checked i j name).code)
      (machine negSeven two)) ≠ observe (.ok ((after wrong []).push (.val (sword (-4)))) 0) := by
  cases checked <;> decide +kernel

def recapture (checked : Bool) : CompiledVal 0 (code (C := P) 0 F checked i j name).frag
    (SignedDiv.expression (C := P) checked (.there i) (.there j)) :=
  (Memory.compileVal 0 (code (C := P) 0 F checked i j name).frag
    (SignedDiv.expression (C := P) checked (.there i) (.there j))).get (SignedDiv.selectable 0 _ checked (.there i) (.there j))

theorem recapture_public (checked : Bool) :
    Memory.compileVal 0 (code (C := P) 0 F checked i j name).frag
      (SignedDiv.expression (C := P) checked (.there i) (.there j)) = some (recapture checked) :=
  (Option.some_get _).symm

theorem wrong_recapture (checked : Bool) :
    observe (run ((code (C := P) 0 F checked i j name).code ++ (recapture checked).code)
      (machine negSeven two)) ≠
    observe (run ((code (C := P) 0 F checked i j name).code ++ (reader (C := P) 0 F checked i j name).code)
      (machine negSeven two)) := by
  cases checked <;> decide +kernel

theorem corrupt_tail (checked : Bool) :
    observe (run ((code (C := P) 0 F checked i j name).code ++ (reader (C := P) 0 F checked i j name).code)
      {(machine negSeven two) with stack := [w[77],w[88]]}) ≠
    observe (.ok ((after quotient [w[88],w[77]]).push (.val (sword (-3)))) 0) := by
  cases checked <;> decide +kernel

theorem insufficient_frame (checked : Bool) :
    ¬ (Compilation.memory (code (C := P) 0 F checked i j name)).Input 1 6 CompileExamples.base
      (target negSeven two) (machine negSeven two) := by
  intro h
  have bound := h.2.1
  change 0+7 ≤ 6 at bound
  omega

def overflowAfter (tail : List Word) : Machine :=
  writeMachine (writeMachine {(machine Backend.Scalar.minimumInt minus) with stack := tail}
    6 (.val (sword Backend.Scalar.minimumInt.val))) 4 w[0]

theorem overflow_joined (tail : List Word) :
    run ((code (C := P) 0 F false i j name).code ++ (reader (C := P) 0 F false i j name).code)
      {(machine Backend.Scalar.minimumInt minus) with stack := tail} =
      .ok ((overflowAfter tail).push (.val (sword Backend.Scalar.minimumInt.val))) 0 := by
  have value := (SignedDiv.intrinsic_overflow (target Backend.Scalar.minimumInt minus) i j
    Backend.Scalar.minimumInt minus rfl rfl rfl rfl).2
  obtain ⟨cw,uw,cr,ur,runs⟩ := CapturedValueStability.execution name
    (SignedDiv.expression false i j) (SignedDiv.selected 0 F false i j) j update updateCode
    (initial7 Backend.Scalar.minimumInt minus) (by decide) Backend.Scalar.minimumInt zero value rfl
  have cword := SignedDiv.Controls.word_unique Backend.Scalar.minimumInt cw cr
  have uword := SignedDiv.Controls.word_unique zero uw ur
  subst cw
  subst uw
  have actual := runs tail
  have codeEq : (code (C := P) 0 F false i j name).code =
      (CapturedValueStability.compiled name (SignedDiv.expression false i j)
        (SignedDiv.selected 0 F false i j) j update updateCode).code := rfl
  have readEq : (reader (C := P) 0 F false i j name).code = [.mload 6] := rfl
  rw [codeEq,readEq,run_append_ok actual.2.2.2.2.1]
  exact actual.2.2.2.2.2

theorem overflow_observations (tail : List Word) :
    (cells.map ((overflowAfter tail).push (.val (sword Backend.Scalar.minimumInt.val))).mem,
      ((overflowAfter tail).push (.val (sword Backend.Scalar.minimumInt.val))).stack) =
      ([.val (sword Backend.Scalar.minimumInt.val),.val (sword Backend.Scalar.minimumInt.val),
        w[0],w[0],w[16],w[16],w[20],w[2],w[7],w[9],w[1],w[4]],
        .val (sword Backend.Scalar.minimumInt.val) :: tail) := rfl

theorem checked_not_wrap (tail : List Word) :
    run ((code (C := P) 0 F true i j name).code ++ (reader (C := P) 0 F true i j name).code)
      {(machine Backend.Scalar.minimumInt minus) with stack := tail} ≠
      .ok ((overflowAfter tail).push (.val (sword Backend.Scalar.minimumInt.val))) 0 := by
  rw [checked_overflow tail]
  intro h
  cases h

end Solidity.Backend.Passes.SignedDivisionCaptureControls

/-- info: 'Solidity.Backend.Passes.SignedDivisionCaptureControls.initial7' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.Passes.SignedDivisionCaptureControls.initial7

/-- info: 'Solidity.Backend.Passes.SignedDivisionCaptureControls.evaluated' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.Passes.SignedDivisionCaptureControls.evaluated

/-- info: 'Solidity.Backend.Passes.SignedDivisionCaptureControls.joined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.Passes.SignedDivisionCaptureControls.joined

/-- info: 'Solidity.Backend.Passes.SignedDivisionCaptureControls.observations' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.Passes.SignedDivisionCaptureControls.observations

/-- info: 'Solidity.Backend.Passes.SignedDivisionCaptureControls.origin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.Passes.SignedDivisionCaptureControls.origin

/-- info: 'Solidity.Backend.Passes.SignedDivisionCaptureControls.zero_rejected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.Passes.SignedDivisionCaptureControls.zero_rejected

/-- info: 'Solidity.Backend.Passes.SignedDivisionCaptureControls.checked_overflow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.Passes.SignedDivisionCaptureControls.checked_overflow

/-- info: 'Solidity.Backend.Passes.SignedDivisionCaptureControls.unchecked_overflow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.Passes.SignedDivisionCaptureControls.unchecked_overflow

/-- info: 'Solidity.Backend.Passes.SignedDivisionCaptureControls.zero_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.Passes.SignedDivisionCaptureControls.zero_source

/-- info: 'Solidity.Backend.Passes.SignedDivisionCaptureControls.overflow_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.Passes.SignedDivisionCaptureControls.overflow_source

/-- info: 'Solidity.Backend.Passes.SignedDivisionCaptureControls.wrong_floor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.Passes.SignedDivisionCaptureControls.wrong_floor

/-- info: 'Solidity.Backend.Passes.SignedDivisionCaptureControls.recapture_public' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.Passes.SignedDivisionCaptureControls.recapture_public

/-- info: 'Solidity.Backend.Passes.SignedDivisionCaptureControls.wrong_recapture' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.Passes.SignedDivisionCaptureControls.wrong_recapture

/-- info: 'Solidity.Backend.Passes.SignedDivisionCaptureControls.corrupt_tail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.Passes.SignedDivisionCaptureControls.corrupt_tail

/-- info: 'Solidity.Backend.Passes.SignedDivisionCaptureControls.insufficient_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.Passes.SignedDivisionCaptureControls.insufficient_frame

/-- info: 'Solidity.Backend.Passes.SignedDivisionCaptureControls.overflow_joined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.Passes.SignedDivisionCaptureControls.overflow_joined

/-- info: 'Solidity.Backend.Passes.SignedDivisionCaptureControls.overflow_observations' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.Passes.SignedDivisionCaptureControls.overflow_observations

/-- info: 'Solidity.Backend.Passes.SignedDivisionCaptureControls.checked_not_wrap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.Passes.SignedDivisionCaptureControls.checked_not_wrap
