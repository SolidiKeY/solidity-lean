import Solidity.Backend.Passes.SignedSubtractionCapture
import Solidity.Backend.Passes.SignedDivisionCaptureControls
import Solidity.Backend.PrimitivePackets.SignedSub.Controls

/-! Wrapping subtraction captured before old-local mutation, with the existing
nonempty aliased-array heap retained in every complete observation vector. -/
namespace Solidity.Backend.Passes.SignedSubtractionCaptureControls
open Evm Evm.Memory Evm.Compiler Backend.PrimitivePackets Solidity.Lowering.V07
open SignedSubtractionCapture
open SignedDiv.Controls (P Γ F target machine)
open SignedSub.Controls (minimum maximum)
open Source.SemanticsExamples (G0 F0)
abbrev i : Idx Γ (.val .int) := .here
abbrev j : Idx Γ (.val .int) := .there .here
def name : Var := .user "difference"
def ti : Bool → Idx Γ (.val .int) | false => i | true => j

def native (x y : Int) (hx : SignedSub.ty.lo ≤ x ∧ x ≤ SignedSub.ty.hi)
    (hy : SignedSub.ty.lo ≤ y ∧ y ≤ SignedSub.ty.hi) : State P Γ :=
  target (integerValue SignedSub.ty x hx) (integerValue SignedSub.ty y hy)
def targetMachine (x y : Int) : Machine :=
  writeMachine (writeMachine CompileExamples.machine 4 (.val (sword y))) 5 (.val (sword x))

theorem represented (x y : Int) (hx : SignedSub.ty.lo ≤ x ∧ x ≤ SignedSub.ty.hi)
    (hy : SignedSub.ty.lo ≤ y ∧ y ≤ SignedSub.ty.hi) :
    StateRepr 1 0 7 F (native x y hx hy) CompileExamples.base (targetMachine x y) :=
  SignedDivisionCaptureControls.initial7 (integerValue SignedSub.ty x hx) (integerValue SignedSub.ty y hy)

theorem family (x y : Int) (hx : SignedSub.ty.lo ≤ x ∧ x ≤ SignedSub.ty.hi)
    (hy : SignedSub.ty.lo ≤ y ∧ y ≤ SignedSub.ty.hi) :
    IntegerLocalFamily SignedSub.ty SignedSub.Controls.si ti
      (SignedSub.Controls.source x y hx hy).1 (native x y hx hy).env := by
  constructor
  · intro k
    cases k <;> exact integer_related _ _ _
  · intro k l
    cases k <;> cases l <;> decide

def wrapped (x y : Int) : PrimTy.int.Denote :=
  integerValue SignedSub.ty (SignedSub.ty.wrap (x-y)) (SignedSub.ty.wrap_mem (x-y))

theorem evaluated (x y : Int) (hx : SignedSub.ty.lo ≤ x ∧ x ≤ SignedSub.ty.hi)
    (hy : SignedSub.ty.lo ≤ y ∧ y ≤ SignedSub.ty.hi) :
    (SignedSub.value i j).evalT (native x y hx hy) = .ok (wrapped x y) :=
  SignedWordSubtraction.sub_value_run (native x y hx hy) (.simple (.local i)) (.simple (.local j)) x y hx hy rfl rfl

def updateCode : CompiledVal 0 (F.push (.val .int) .ok) (update (C := P) (Γ := Γ)) :=
  (Memory.compileVal 0 (F.push (.val .int) .ok) update).get (by rfl)
def after (x y : Int) (tail : List Word) : Machine :=
  writeMachine (writeMachine {(targetMachine x y) with stack := tail}
    6 (.val (sword (SignedSub.ty.wrap (x-y))))) 4 w[0]

theorem joined (x y : Int) (hx : SignedSub.ty.lo ≤ x ∧ x ≤ SignedSub.ty.hi)
    (hy : SignedSub.ty.lo ≤ y ∧ y ≤ SignedSub.ty.hi) (tail : List Word) :
    run ((code (C := P) 0 F i j name).code ++ (reader (C := P) 0 F i j name).code)
      {(targetMachine x y) with stack := tail} =
      .ok ((after x y tail).push (.val (sword (SignedSub.ty.wrap (x-y))))) 0 := by
  obtain ⟨cw,uw,cr,ur,runs⟩ := CapturedValueStability.execution name
    (SignedSub.value i j) (SignedSub.selected 0 F i j) j update updateCode
    (represented x y hx hy) (by decide) (wrapped x y) zero (evaluated x y hx hy) rfl
  have cword := SignedDiv.Controls.word_unique (wrapped x y) cw cr
  have uword := SignedDiv.Controls.word_unique zero uw ur
  subst cw
  subst uw
  have actual := runs tail
  have codeEq : (code (C := P) 0 F i j name).code =
      (CapturedValueStability.compiled name (SignedSub.value i j)
        (SignedSub.selected 0 F i j) j update updateCode).code := rfl
  have readEq : (reader (C := P) 0 F i j name).code = [.mload 6] := rfl
  rw [codeEq,readEq,run_append_ok actual.2.2.2.2.1]
  exact actual.2.2.2.2.2

def cells : List Nat := [6,5,4,3,2,1,0,16,17,18,20,21]
theorem observations (x y : Int) (tail : List Word) :
    (cells.map ((after x y tail).push (.val (sword (SignedSub.ty.wrap (x-y))))).mem,
      ((after x y tail).push (.val (sword (SignedSub.ty.wrap (x-y))))).stack) =
      ([.val (sword (SignedSub.ty.wrap (x-y))),.val (sword x),w[0],w[0],w[16],w[16],w[20],
        w[2],w[7],w[9],w[1],w[4]],.val (sword (SignedSub.ty.wrap (x-y))) :: tail) := rfl

theorem origin (p : Roadmap.Pipeline) (fuel : Nat) (x y : Int)
    (hx : SignedSub.ty.lo ≤ x ∧ x ≤ SignedSub.ty.hi)
    (hy : SignedSub.ty.lo ≤ y ∧ y ≤ SignedSub.ty.hi) : type_of%
    (application (G0 p) F0 fuel (SignedSub.Controls.source x y hx hy) (native x y hx hy)
      SignedSub.Controls.si ti (family x y hx hy) false true x y hx hy rfl rfl name
      (represented x y hx hy) (by decide)) :=
  application (G0 p) F0 fuel (SignedSub.Controls.source x y hx hy) (native x y hx hy)
    SignedSub.Controls.si ti (family x y hx hy) false true x y hx hy rfl rfl name
    (represented x y hx hy) (by decide)

def observe : Evm.Out → Option (List Word × List Word)
  | .ok m _ => some (cells.map m.mem,m.stack)
  | _ => none

theorem both_wrap_vectors :
    observe (run ((code (C := P) 0 F i j name).code ++ (reader (C := P) 0 F i j name).code)
      (targetMachine minimum 1)) = some
      ([.val (sword maximum),.val (sword minimum),w[0],w[0],w[16],w[16],w[20],w[2],w[7],w[9],w[1],w[4]],
        [.val (sword maximum)]) ∧
    observe (run ((code (C := P) 0 F i j name).code ++ (reader (C := P) 0 F i j name).code)
      (targetMachine maximum (-1))) = some
      ([.val (sword minimum),.val (sword maximum),w[0],w[0],w[16],w[16],w[20],w[2],w[7],w[9],w[1],w[4]],
        [.val (sword minimum)]) := by
  constructor <;> decide +kernel

def recapture : CompiledVal 0 (code (C := P) 0 F i j name).frag
    (SignedSub.value (C := P) (.there i) (.there j)) :=
  (Memory.compileVal 0 (code (C := P) 0 F i j name).frag
    (SignedSub.value (C := P) (.there i) (.there j))).get (by rfl)

theorem recapture_public : Memory.compileVal 0 (code (C := P) 0 F i j name).frag
    (SignedSub.value (C := P) (.there i) (.there j)) = some recapture := (Option.some_get _).symm

theorem wrong_recapture :
    observe (run ((code (C := P) 0 F i j name).code ++ recapture.code) (targetMachine minimum 1)) ≠
      observe (run ((code (C := P) 0 F i j name).code ++ (reader (C := P) 0 F i j name).code)
        (targetMachine minimum 1)) := by decide +kernel

theorem corrupt_tail :
    observe (run ((code (C := P) 0 F i j name).code ++ (reader (C := P) 0 F i j name).code)
      {(targetMachine minimum 1) with stack := [w[77],w[88]]}) ≠
      observe (.ok ((after minimum 1 [w[88],w[77]]).push (.val (sword maximum))) 0) := by decide +kernel

theorem insufficient_frame : ¬ (Compilation.memory (code (C := P) 0 F i j name)).Input 1 6 CompileExamples.base
    (native minimum 1 (by decide +kernel) (by decide +kernel)) (targetMachine minimum 1) := by
  intro h
  have bound := h.2.1
  change 0+7 ≤ 6 at bound
  omega

/-- These Source boundaries are not promoted into a checked-ABI compiler claim. -/
theorem source_checked_boundary (p : Roadmap.Pipeline) : type_of%
    (SignedSub.Controls.checked_overflow_boundary p) := SignedSub.Controls.checked_overflow_boundary p

theorem no_horizon_promotion (p : Roadmap.Pipeline) : type_of%
    (SignedSub.Controls.no_horizon_promotion p) := SignedSub.Controls.no_horizon_promotion p

end Solidity.Backend.Passes.SignedSubtractionCaptureControls

/-- info: 'Solidity.Backend.Passes.SignedSubtractionCaptureControls.represented' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.Passes.SignedSubtractionCaptureControls.represented

/-- info: 'Solidity.Backend.Passes.SignedSubtractionCaptureControls.family' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.Passes.SignedSubtractionCaptureControls.family

/-- info: 'Solidity.Backend.Passes.SignedSubtractionCaptureControls.evaluated' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.Passes.SignedSubtractionCaptureControls.evaluated

/-- info: 'Solidity.Backend.Passes.SignedSubtractionCaptureControls.joined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.Passes.SignedSubtractionCaptureControls.joined

/-- info: 'Solidity.Backend.Passes.SignedSubtractionCaptureControls.observations' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.Passes.SignedSubtractionCaptureControls.observations

/-- info: 'Solidity.Backend.Passes.SignedSubtractionCaptureControls.origin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.Passes.SignedSubtractionCaptureControls.origin

/-- info: 'Solidity.Backend.Passes.SignedSubtractionCaptureControls.both_wrap_vectors' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.Passes.SignedSubtractionCaptureControls.both_wrap_vectors

/-- info: 'Solidity.Backend.Passes.SignedSubtractionCaptureControls.recapture_public' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.Passes.SignedSubtractionCaptureControls.recapture_public

/-- info: 'Solidity.Backend.Passes.SignedSubtractionCaptureControls.wrong_recapture' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.Passes.SignedSubtractionCaptureControls.wrong_recapture

/-- info: 'Solidity.Backend.Passes.SignedSubtractionCaptureControls.corrupt_tail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.Passes.SignedSubtractionCaptureControls.corrupt_tail

/-- info: 'Solidity.Backend.Passes.SignedSubtractionCaptureControls.insufficient_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.Passes.SignedSubtractionCaptureControls.insufficient_frame

/-- info: 'Solidity.Backend.Passes.SignedSubtractionCaptureControls.source_checked_boundary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.Passes.SignedSubtractionCaptureControls.source_checked_boundary

/-- info: 'Solidity.Backend.Passes.SignedSubtractionCaptureControls.no_horizon_promotion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.Passes.SignedSubtractionCaptureControls.no_horizon_promotion
