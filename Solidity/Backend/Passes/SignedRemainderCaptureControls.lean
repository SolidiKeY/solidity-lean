import Solidity.Backend.Passes.SignedRemainderCapture
import Solidity.Backend.PrimitivePackets.SignedMod.Controls

/-! Capture real signed remainders over the published populated aliasing heap.
Numeric guard capacities stay explicit and are separately inhabited. -/
namespace Solidity.Backend.Passes.SignedRemainderCaptureControls
open Evm Evm.Memory Evm.Compiler Backend.PrimitivePackets
open SignedRemainderCapture
open SignedMod.Controls (C Γ fragment target machine globals frame source initial)
abbrev i : Idx Γ (.val .int) := .here
abbrev j : Idx Γ (.val .int) := .there .here
def name : Var := .user "remainder"
def saved : List (Fin W) := [wmod 77,wmod 88]

theorem capacities :
    Backend.Scalar.stackBound (Backend.Scalar.zeroTest ⟨1,by decide⟩) ((saved.length+2:Nat):Int) = true ∧
    Backend.Scalar.stackBound [.op .SMOD] ((saved.length+2:Nat):Int) = true := by decide +kernel

def after (x y : Int) (hx : SignedMod.Range x) (hy : SignedMod.Range y) (tail : List Word) : Machine :=
  writeMachine (writeMachine {(machine x y hx hy) with stack := tail} 6 (.val (sword (x.tmod y)))) 4 w[0]

theorem joined (x y : Int) (hx : SignedMod.Range x) (hy : SignedMod.Range y)
    (nonzero : y ≠ 0) (tail : List Word) :
    run ((whole (C := C) 0 fragment i j name).code ++ (reader (C := C) 0 fragment i j name).code)
      {(machine x y hx hy) with stack := tail} =
      .ok ((after x y hx hy tail).push (.val (sword (x.tmod y)))) 0 := by
  let v := SignedMod.lower (x.tmod y) (SignedMod.remainder_range x y hy nonzero)
  obtain ⟨cw,uw,cr,ur,runs⟩ := physical i j name (initial x y hx hy) (by decide) v
    (value_nonzero _ i j x y hx hy nonzero rfl rfl)
  have cword : cw = .val (sword (x.tmod y)) := SignedMod.int_repr_unique cr (ReprV.int_word v)
  have uword : uw = w[0] := SignedMod.int_repr_unique ur (ReprV.int_word zero)
  subst cw
  subst uw
  exact (runs tail).2.2.2.2

def cells : List Nat := [6,5,4,3,2,1,0,7,16,17,18,20,21]
theorem observations (x y : Int) (hx : SignedMod.Range x) (hy : SignedMod.Range y) (tail : List Word) :
    let m := (after x y hx hy tail).push (.val (sword (x.tmod y)))
    (cells.map m.mem,m.stack) =
      ([.val (sword (x.tmod y)),.val (sword x),w[0],w[0],w[16],w[16],w[20],w[0],
        w[2],w[7],w[9],w[1],w[4]],.val (sword (x.tmod y)) :: tail) := rfl

theorem origin_and_component (p : Roadmap.Pipeline) (checked : Bool) (fuel : Nat)
    (x y : Int) (hx : SignedMod.Range x) (hy : SignedMod.Range y) (nonzero : y ≠ 0) : type_of%
    (application (globals p) (frame checked) fuel (source x y hx hy) (target x y hx hy)
      .here (.there .here) i j name x y hx hy nonzero rfl rfl rfl rfl
      (initial x y hx hy) (by decide) saved capacities.1 capacities.2) :=
  application (globals p) (frame checked) fuel (source x y hx hy) (target x y hx hy)
    .here (.there .here) i j name x y hx hy nonzero rfl rfl rfl rfl
    (initial x y hx hy) (by decide) saved capacities.1 capacities.2

theorem zero_rejected (x : Int) (hx : SignedMod.Range x) (tail : List Word) :
    run ((whole (C := C) 0 fragment i j name).code ++ (reader (C := C) 0 fragment i j name).code)
      {(machine x 0 hx (by decide)) with stack := tail} = .revert :=
  (rejected i j name (initial x 0 hx (by decide)) (by decide)
    (value_zero _ i j x hx (by decide) rfl rfl) tail).2

theorem zero_source (p : Roadmap.Pipeline) (checked : Bool) (fuel : Nat) (x : Int) (hx : SignedMod.Range x) :
    type_of% (SignedMod.Controls.source_failure p checked fuel x hx) :=
  SignedMod.Controls.source_failure p checked fuel x hx

theorem guard_required : type_of% SignedMod.Controls.raw_zero_differs := SignedMod.Controls.raw_zero_differs

def observe : Evm.Out → Option (List Word × List Word)
  | .ok m _ => some (cells.map m.mem,m.stack)
  | _ => none

theorem negative_vector :
    observe (run ((whole (C := C) 0 fragment i j name).code ++ (reader (C := C) 0 fragment i j name).code)
      (machine (-7) 3 (by decide) (by decide))) = some
      ([.val (sword (-1)),.val (sword (-7)),w[0],w[0],w[16],w[16],w[20],w[0],
        w[2],w[7],w[9],w[1],w[4]],[.val (sword (-1))]) := by decide +kernel

theorem minimum_success (tail : List Word) :
    run ((whole (C := C) 0 fragment i j name).code ++ (reader (C := C) 0 fragment i j name).code)
      {(machine (-(Evm.H:Int)) (-1) (by decide) (by decide)) with stack := tail} =
      .ok ((after (-(Evm.H:Int)) (-1) (by decide) (by decide) tail).push w[0]) 0 := by
  simpa only [SignedMod.minimum_remainder_neg_one] using
    joined (-(Evm.H:Int)) (-1) (by decide) (by decide) (by decide) tail

theorem minimum_vector :
    observe (run ((whole (C := C) 0 fragment i j name).code ++ (reader (C := C) 0 fragment i j name).code)
      (machine (-(Evm.H:Int)) (-1) (by decide) (by decide))) = some
      ([w[0],.val (sword (-(Evm.H:Int))),w[0],w[0],w[16],w[16],w[20],w[0],
        w[2],w[7],w[9],w[1],w[4]],[w[0]]) := by decide +kernel

theorem wrong_euclidean :
    observe (run ((whole (C := C) 0 fragment i j name).code ++ (reader (C := C) 0 fragment i j name).code)
      (machine (-7) 3 (by decide) (by decide))) ≠ some
      ([w[2],.val (sword (-7)),w[0],w[0],w[16],w[16],w[20],w[0],
        w[2],w[7],w[9],w[1],w[4]],[w[2]]) := by decide +kernel

def recapture : CompiledVal 0 (code (C := C) 0 fragment i j name).frag
    (SignedMod.expression (C := C) (.there i) (.there j)) :=
  SignedMod.selected 0 (code (C := C) 0 fragment i j name).frag (.there i) (.there j)

theorem recapture_public : Memory.compileVal 0 (code (C := C) 0 fragment i j name).frag
    (SignedMod.expression (C := C) (.there i) (.there j)) = some recapture := rfl

theorem wrong_recapture :
    observe (run ((whole (C := C) 0 fragment i j name).code ++ recapture.code)
      (machine (-7) 3 (by decide) (by decide))) ≠
    observe (run ((whole (C := C) 0 fragment i j name).code ++ (reader (C := C) 0 fragment i j name).code)
      (machine (-7) 3 (by decide) (by decide))) := by decide +kernel

theorem corrupt_tail :
    observe (run ((whole (C := C) 0 fragment i j name).code ++ (reader (C := C) 0 fragment i j name).code)
      {(machine (-7) 3 (by decide) (by decide)) with stack := [w[77],w[88]]}) ≠
    observe (.ok ((after (-7) 3 (by decide) (by decide) [w[88],w[77]]).push (.val (sword (-1)))) 0) := by decide +kernel

theorem insufficient_frame : ¬ (whole (C := C) 0 fragment i j name).Input 1 6 SignedMod.Controls.HeapFixture.base
    (target (-7) 3 (by decide) (by decide)) (machine (-7) 3 (by decide) (by decide)) := by
  intro h
  have bound := h.2.1
  change 0+7 ≤ 6 at bound
  omega

theorem no_horizon_promotion (p : Roadmap.Pipeline) (checked : Bool) :
    type_of% (SignedMod.Controls.too_short_horizon p checked) := SignedMod.Controls.too_short_horizon p checked

end Solidity.Backend.Passes.SignedRemainderCaptureControls

/-- info: 'Solidity.Backend.Passes.SignedRemainderCaptureControls.capacities' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.Passes.SignedRemainderCaptureControls.capacities

/-- info: 'Solidity.Backend.Passes.SignedRemainderCaptureControls.joined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.Passes.SignedRemainderCaptureControls.joined

/-- info: 'Solidity.Backend.Passes.SignedRemainderCaptureControls.observations' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.Passes.SignedRemainderCaptureControls.observations

/-- info: 'Solidity.Backend.Passes.SignedRemainderCaptureControls.origin_and_component' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.Passes.SignedRemainderCaptureControls.origin_and_component

/-- info: 'Solidity.Backend.Passes.SignedRemainderCaptureControls.zero_rejected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.Passes.SignedRemainderCaptureControls.zero_rejected

/-- info: 'Solidity.Backend.Passes.SignedRemainderCaptureControls.zero_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.Passes.SignedRemainderCaptureControls.zero_source

/-- info: 'Solidity.Backend.Passes.SignedRemainderCaptureControls.guard_required' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.Passes.SignedRemainderCaptureControls.guard_required

/-- info: 'Solidity.Backend.Passes.SignedRemainderCaptureControls.negative_vector' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.Passes.SignedRemainderCaptureControls.negative_vector

/-- info: 'Solidity.Backend.Passes.SignedRemainderCaptureControls.minimum_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.Passes.SignedRemainderCaptureControls.minimum_success

/-- info: 'Solidity.Backend.Passes.SignedRemainderCaptureControls.minimum_vector' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.Passes.SignedRemainderCaptureControls.minimum_vector

/-- info: 'Solidity.Backend.Passes.SignedRemainderCaptureControls.wrong_euclidean' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.Passes.SignedRemainderCaptureControls.wrong_euclidean

/-- info: 'Solidity.Backend.Passes.SignedRemainderCaptureControls.recapture_public' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.Passes.SignedRemainderCaptureControls.recapture_public

/-- info: 'Solidity.Backend.Passes.SignedRemainderCaptureControls.wrong_recapture' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.Passes.SignedRemainderCaptureControls.wrong_recapture

/-- info: 'Solidity.Backend.Passes.SignedRemainderCaptureControls.corrupt_tail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.Passes.SignedRemainderCaptureControls.corrupt_tail

/-- info: 'Solidity.Backend.Passes.SignedRemainderCaptureControls.insufficient_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.Passes.SignedRemainderCaptureControls.insufficient_frame

/-- info: 'Solidity.Backend.Passes.SignedRemainderCaptureControls.no_horizon_promotion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.Passes.SignedRemainderCaptureControls.no_horizon_promotion
