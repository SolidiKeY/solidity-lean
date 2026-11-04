import Solidity.Backend.PrimitivePackets.SignedSub.Execution
import Solidity.Backend.MemoryOps.StructDefaults.WordControls
import Solidity.Source.SemanticsExamples

namespace Solidity.Backend.PrimitivePackets.SignedSub.Controls
open Evm Evm.Memory Solidity.Lowering.V07
open Source.SemanticsExamples
namespace Seed
abbrev C := Solidity.Backend.MemoryOps.StructDefaults.WordControls.C
abbrev initial := Solidity.Backend.MemoryOps.StructDefaults.WordControls.initial
abbrev machine := Solidity.Backend.MemoryOps.StructDefaults.WordControls.machine
abbrev bases := Solidity.Backend.MemoryOps.StructDefaults.WordControls.bases
abbrev represented := Solidity.Backend.MemoryOps.StructDefaults.WordControls.initial_repr
end Seed
abbrev C := Seed.C
abbrev Γ : Ctx := [.val .int, .val .int]
def frag : Frag Γ := Frag.init Γ
abbrev first : Idx Γ (.val .int) := .here
abbrev second : Idx Γ (.val .int) := .there .here

def target (x y : Int) (hx : ty.lo ≤ x ∧ x ≤ ty.hi) (hy : ty.lo ≤ y ∧ y ≤ ty.hi) : State C Γ :=
  (Seed.initial.push (t := .val .int) (integerValue ty y hy)).push
    (t := .val .int) (integerValue ty x hx)

def machine (x y : Int) : Machine :=
  writeMachine (writeMachine Seed.machine 1 (.val (sword y))) 2 (.val (sword x))

theorem represented (x y : Int) (hx : ty.lo ≤ x ∧ x ≤ ty.hi) (hy : ty.lo ≤ y ∧ y ≤ ty.hi) :
    StateRepr 1 1 64 frag (target x y hx hy) Seed.bases (machine x y) :=
  ((Seed.represented.1.consVal (integerValue ty y hy) (.val (sword y))
    (ReprV.int_word _) (by decide +kernel)).consVal (integerValue ty x hx) (.val (sword x))
      (ReprV.int_word _) (by decide +kernel))

def source (x y : Int) (hx : ty.lo ≤ x ∧ x ≤ ty.hi) (hy : ty.lo ≤ y ∧ y ≤ ty.hi) :
    Source.EMState E0 [.int ty, .int ty] :=
  (.cons (.int x hx) (.cons (.int y hy) .nil), s0)

def si : Bool → Source.Idx [.int ty, .int ty] (.int ty)
  | false => .here
  | true => .there .here

def ti : Bool → Idx Γ (.val .int)
  | false => first
  | true => second

theorem family (x y : Int) (hx : ty.lo ≤ x ∧ x ≤ ty.hi) (hy : ty.lo ≤ y ∧ y ≤ ty.hi) :
    IntegerLocalFamily ty si ti (source x y hx hy).1 (target x y hx hy).env := by
  constructor
  · intro k
    cases k <;> exact integer_related _ _ _
  · intro k l
    cases k <;> cases l <;> decide

def application (p : Roadmap.Pipeline) (fuel : Nat) (x y : Int)
    (hx : ty.lo ≤ x ∧ x ≤ ty.hi) (hy : ty.lo ≤ y ∧ y ≤ ty.hi) :=
  execution (G0 p) F0 fuel (source x y hx hy) (target x y hx hy) si ti
    (family x y hx hy) false true x y hx hy rfl rfl 1 1 64 frag Seed.bases
      (machine x y) (represented x y hx hy)

def code : List Instr := (selected (C := C) 1 frag first second).code

theorem public_selection : Memory.compileVal (C := C) 1 frag (value first second) =
    some (selected 1 frag first second) := selection 1 frag first second

theorem actual_code : code = [.mload 2, .mload 1, .swap 1, .sub] := by rfl

theorem retained_run (p : Roadmap.Pipeline) (fuel : Nat) (x y : Int)
    (hx : ty.lo ≤ x ∧ x ≤ ty.hi) (hy : ty.lo ≤ y ∧ y ≤ ty.hi) (tail : List Word) :
    run code {(machine x y) with stack := w[77] :: w[88] :: tail} =
      .ok (({(machine x y) with stack := w[77] :: w[88] :: tail} : Machine).push
        (.val (sword (ty.wrap (x-y))))) 0 :=
  ((application p fuel x y hx hy).2 (w[77] :: w[88] :: tail)).1

theorem source_run (p : Roadmap.Pipeline) (fuel : Nat) (x y : Int)
    (hx : ty.lo ≤ x ∧ x ≤ ty.hi) (hy : ty.lo ≤ y ∧ y ≤ ty.hi) :
    (Source.evalE (G0 p) {F0 with checked := false} (fuel+3)
      (.binary .sub (.local (.here : Source.Idx [.int ty, .int ty] (.int ty)))
        (.local (.there .here)))).run (source x y hx hy) =
      (.ok (.val (Source.intWrap ty (x-y))), source x y hx hy) :=
  (application p fuel x y hx hy).1

def signedResult : Evm.Out → Option Int
  | .ok m 0 => match m.stack with | .val n :: _ => some (sgn n.val) | _ => none
  | _ => none

theorem negative_left : signedResult (run code (machine (-5) 3)) = some (-8) := by decide +kernel

theorem negative_right : signedResult (run code (machine 5 (-3))) = some 8 := by decide +kernel

def minimum : Int := -(2^255 : Int)
def maximum : Int := (2^255 : Int)-1

theorem min_wrap : signedResult (run code (machine minimum 1)) = some maximum := by decide +kernel

theorem max_wrap : signedResult (run code (machine maximum (-1))) = some minimum := by decide +kernel

theorem equal_operands : signedResult (run code (machine minimum minimum)) = some 0 := by decide +kernel

theorem wrong_sign_refused : signedResult (run code (machine (-5) 3)) ≠ some 8 := by decide +kernel

theorem unwrapped_result_refused : signedResult (run code (machine minimum 1)) ≠ some (minimum-1) := by decide +kernel

theorem both_source_pipelines (p : Roadmap.Pipeline) :
    intOf ((Source.evalE (G0 p) {F0 with checked := false} 3
      (.binary .sub (.local (.here : Source.Idx [.int ty, .int ty] (.int ty)))
        (.local (.there .here)))).run (source minimum 1 (by decide +kernel) (by decide +kernel))) =
      some maximum := by
  rw [source_run p 0 minimum 1 (by decide +kernel) (by decide +kernel)]
  decide +kernel

theorem source_negative_left (p : Roadmap.Pipeline) :
    intOf ((Source.evalE (G0 p) {F0 with checked := false} 3
      (.binary .sub (.local (.here : Source.Idx [.int ty, .int ty] (.int ty)))
        (.local (.there .here)))).run (source (-5) 3 (by decide +kernel) (by decide +kernel))) =
      some (-8) := by
  rw [source_run p 0 (-5) 3 (by decide +kernel) (by decide +kernel)]
  decide +kernel

theorem source_negative_right (p : Roadmap.Pipeline) :
    intOf ((Source.evalE (G0 p) {F0 with checked := false} 3
      (.binary .sub (.local (.here : Source.Idx [.int ty, .int ty] (.int ty)))
        (.local (.there .here)))).run (source 5 (-3) (by decide +kernel) (by decide +kernel))) =
      some 8 := by
  rw [source_run p 0 5 (-3) (by decide +kernel) (by decide +kernel)]
  decide +kernel

theorem both_source_max_wrap (p : Roadmap.Pipeline) :
    intOf ((Source.evalE (G0 p) {F0 with checked := false} 3
      (.binary .sub (.local (.here : Source.Idx [.int ty, .int ty] (.int ty)))
        (.local (.there .here)))).run (source maximum (-1) (by decide +kernel) (by decide +kernel))) =
      some minimum := by
  rw [source_run p 0 maximum (-1) (by decide +kernel) (by decide +kernel)]
  decide +kernel

theorem nonempty_frame : ((machine (-5) 3).stack, (machine (-5) 3).mem 0,
    (machine (-5) 3).mem 63) = ([w[77]], w[128], w[99]) := by decide +kernel

theorem no_horizon_promotion (p : Roadmap.Pipeline) :
    (Source.evalE (G0 p) {F0 with checked := false} 0
      (.binary .sub (.local (.here : Source.Idx [.int ty, .int ty] (.int ty)))
        (.local (.there .here)))).run (source minimum 1 (by decide +kernel) (by decide +kernel)) =
      (.error .timeout, source minimum 1 (by decide +kernel) (by decide +kernel)) := by rfl

theorem checked_overflow_boundary (p : Roadmap.Pipeline) :
    revertOf ((Source.evalE (G0 p) {F0 with checked := true} 3
      (.binary .sub (.local (.here : Source.Idx [.int ty, .int ty] (.int ty)))
        (.local (.there .here)))).run (source minimum 1 (by decide +kernel) (by decide +kernel))) =
      some (Source.panicData .arithmetic) := by
  cases p <;> decide +kernel

/-- info: 'Solidity.Backend.PrimitivePackets.SignedSub.Controls.represented' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms represented
/-- info: 'Solidity.Backend.PrimitivePackets.SignedSub.Controls.retained_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms retained_run
/-- info: 'Solidity.Backend.PrimitivePackets.SignedSub.Controls.source_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms source_run
/-- info: 'Solidity.Backend.PrimitivePackets.SignedSub.Controls.negative_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms negative_left
/-- info: 'Solidity.Backend.PrimitivePackets.SignedSub.Controls.negative_right' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms negative_right
/-- info: 'Solidity.Backend.PrimitivePackets.SignedSub.Controls.min_wrap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms min_wrap
/-- info: 'Solidity.Backend.PrimitivePackets.SignedSub.Controls.max_wrap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms max_wrap
/-- info: 'Solidity.Backend.PrimitivePackets.SignedSub.Controls.equal_operands' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms equal_operands
/-- info: 'Solidity.Backend.PrimitivePackets.SignedSub.Controls.wrong_sign_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms wrong_sign_refused
/-- info: 'Solidity.Backend.PrimitivePackets.SignedSub.Controls.unwrapped_result_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms unwrapped_result_refused
/-- info: 'Solidity.Backend.PrimitivePackets.SignedSub.Controls.both_source_pipelines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms both_source_pipelines
/-- info: 'Solidity.Backend.PrimitivePackets.SignedSub.Controls.nonempty_frame' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms nonempty_frame
/-- info: 'Solidity.Backend.PrimitivePackets.SignedSub.Controls.no_horizon_promotion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms no_horizon_promotion
/-- info: 'Solidity.Backend.PrimitivePackets.SignedSub.Controls.family' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms family
/-- info: 'Solidity.Backend.PrimitivePackets.SignedSub.Controls.public_selection' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms public_selection
/-- info: 'Solidity.Backend.PrimitivePackets.SignedSub.Controls.actual_code' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms actual_code
/-- info: 'Solidity.Backend.PrimitivePackets.SignedSub.Controls.checked_overflow_boundary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms checked_overflow_boundary
/-- info: 'Solidity.Backend.PrimitivePackets.SignedSub.Controls.source_negative_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms source_negative_left
/-- info: 'Solidity.Backend.PrimitivePackets.SignedSub.Controls.source_negative_right' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms source_negative_right
/-- info: 'Solidity.Backend.PrimitivePackets.SignedSub.Controls.both_source_max_wrap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms both_source_max_wrap
end Solidity.Backend.PrimitivePackets.SignedSub.Controls
