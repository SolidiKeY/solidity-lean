import Solidity.Backend.Passes.ShiftCapture
import Solidity.Backend.MemoryOps.StructDefaults.WordControls

/-! Capture observes the original runtime count, then clears it. Saturated
counts are successful zero results, not compiler refusals or Source panics. -/
namespace Solidity.Backend.Passes.ShiftCaptureControls
open Evm Evm.Memory Evm.Compiler Backend.PrimitivePackets.Shifts
open Backend.MemoryOps.StructDefaults.WordControls (C initial bases machine initial_repr)
open ShiftCapture
abbrev Γ : Ctx := [.val .uint,.val .uint]
abbrev i : Idx Γ (.val .uint) := .here
abbrev j : Idx Γ (.val .uint) := .there .here
def name : Var := .user "shift"
def state (x k : Fin W) : State C Γ :=
  (initial.push (t := .val .uint) (indexValue k)).push (t := .val .uint) (indexValue x)
def input (x k : Fin W) : Machine := writeMachine (writeMachine machine 1 (.val k)) 2 (.val x)
theorem represented (x k : Fin W) :
    StateRepr 1 1 64 (Frag.init Γ) (state x k) bases (input x k) :=
  (initial_repr.1.consVal (indexValue k) (.val k) ⟨k,rfl,rfl⟩ (by decide)).consVal
    (indexValue x) (.val x) ⟨x,rfl,rfl⟩ (by decide)

theorem inhabited (left : Bool) (x k : Fin W) : type_of%
    (application left i j name x k (represented x k) (by decide) (by rfl) (by rfl)) :=
  application left i j name x k (represented x k) (by decide) (by rfl) (by rfl)

def after (left : Bool) (x k : Fin W) (tail : List Word) : Machine :=
  writeMachine (writeMachine {(input x k) with stack := tail} 3 (.val (resultWord left x k))) 1 w[0]

theorem joined (left : Bool) (x k : Fin W) (tail : List Word) :
    run ((whole (C := C) 1 left i j name).code ++ [.mload 3])
      {(input x k) with stack := tail} =
      .ok ((after left x k tail).push (.val (resultWord left x k))) 0 := by
  have successfulRun := General.runtime_execution (C := C) 1 left i j x k
    {(input x k) with stack := tail} (by rfl) (by rfl)
  have emitted : (whole (C := C) 1 left i j name).code =
      (General.selected (C := C) 1 left i j).code ++ [.mstore 3,.push w[0],.mstore 1] := by
    cases left <;> rfl
  rw [emitted,List.append_assoc,run_append_ok successfulRun]
  rfl

def cells : List Nat := [3,2,1,0,63,128]
def observe : Evm.Out → Option (List Word × List Word)
  | .ok m _ => some (cells.map m.mem,m.stack)
  | _ => none

theorem ordered (left : Bool) (x k : Fin W) (tail : List Word) :
    observe (run ((whole (C := C) 1 left i j name).code ++ [.mload 3])
      {(input x k) with stack := tail}) =
      some ([.val (resultWord left x k),.val x,w[0],w[128],w[99],w[0]],
        .val (resultWord left x k)::tail) := by
  rw [joined]
  rfl

theorem source_expression {E : Source.Env} (G : Source.Glob E) (F : Source.Fr)
    (fuel : Nat) (left : Bool) (x k : Fin W) (s : Source.St E) :
    let ls := Source.Locals.cons (Source.Val.int (x.val : Int) (word_range x))
      (.cons (.int (k.val : Int) (word_range k)) .nil)
    type_of% (General.source_execution G F fuel left
      (Source.Idx.here : Source.Idx [.int Source.IntTy.u256,.int Source.IntTy.u256] _)
      (.there .here) ls s x k rfl rfl) :=
  General.source_execution G F fuel left .here (.there .here) _ s x k rfl rfl

theorem left_vector : observe (run ((whole (C := C) 1 true i j name).code ++ [.mload 3])
    (input (wmod 5) (wmod 3))) =
    some ([w[40],w[5],w[0],w[128],w[99],w[0]],[w[40],w[77]]) := by decide +kernel

theorem right_vector : observe (run ((whole (C := C) 1 false i j name).code ++ [.mload 3])
    (input (wmod 40) (wmod 3))) =
    some ([w[5],w[40],w[0],w[128],w[99],w[0]],[w[5],w[77]]) := by decide +kernel

theorem saturated (left : Bool) (tail : List Word) :
    observe (run ((whole (C := C) 1 left i j name).code ++ [.mload 3])
      {(input (wmod 5) (wmod 256)) with stack := tail}) =
      some ([w[0],w[5],w[0],w[128],w[99],w[0]],w[0]::tail) := by
  simpa only [result_saturated left (wmod 5) (wmod 256) (by decide)] using
    ordered left (wmod 5) (wmod 256) tail

theorem wrong_recapture : observe (run ((whole (C := C) 1 true i j name).code ++ [.mload 3])
    (input (wmod 5) (wmod 3))) ≠
    some ([w[5],w[5],w[0],w[128],w[99],w[0]],[w[5],w[77]]) := by decide +kernel

theorem wrong_saturated_modulo : observe (run ((whole (C := C) 1 true i j name).code ++ [.mload 3])
    (input (wmod 5) (wmod 256))) ≠
    some ([w[5],w[5],w[0],w[128],w[99],w[0]],[w[5],w[77]]) := by decide +kernel

theorem corrupted_tail : observe (run ((whole (C := C) 1 true i j name).code ++ [.mload 3])
    (input (wmod 5) (wmod 3))) ≠
    some ([w[40],w[5],w[0],w[128],w[99],w[0]],[w[40],w[88]]) := by decide +kernel

def wrongProgram : Prog C Γ (.val .uint :: Γ) :=
  .cons (.assignLocal j (.simple (.lit 0 (by decide))))
    (.cons (.declLocal .uint name (some (General.target true i j))) .nil)
def wrongCode : CompiledProg 1 (Frag.init Γ) wrongProgram :=
  (compileProg 1 (Frag.init Γ) wrongProgram).get (by rfl)
theorem wrong_public : compileProg 1 (Frag.init Γ) wrongProgram = some wrongCode := rfl

theorem wrong_order_vector : observe (run (wrongCode.code ++ [.mload 3])
    (input (wmod 5) (wmod 3))) =
    some ([w[5],w[5],w[0],w[128],w[99],w[0]],[w[5],w[77]]) := by decide +kernel

theorem wrong_order_source : wrongProgram.run (state (wmod 5) (wmod 3)) ≠
    (program true i j name).run (state (wmod 5) (wmod 3)) := by
  intro same
  let project := fun (out : TRes (Solidity.Out C [] (.val .uint :: Γ))) =>
    match out with
    | .ok result => some [(TEnv.get .here result.st.env).val,
        (TEnv.get (.there .here) result.st.env).val,
        (TEnv.get (.there (.there .here)) result.st.env).val]
    | .error _ => none
  have projected : (some [5,5,0] : Option (List Int)) = some [40,5,0] := congrArg project same
  have different : (some [5,5,0] : Option (List Int)) ≠ some [40,5,0] := by decide
  exact different projected

theorem insufficient_frame : ¬ (1+(Γ.length+1) ≤ 3) := by decide

theorem input_refused (left : Bool) (x k : Fin W) :
    ¬ (whole (C := C) 1 left i j name).Input 1 3 bases (state x k) (input x k) := by
  intro admitted
  have bound := admitted.2.1
  cases left <;> change 4 ≤ 3 at bound <;> omega

/-- info: 'Solidity.Backend.Passes.ShiftCaptureControls.input_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms input_refused
/-- info: 'Solidity.Backend.Passes.ShiftCaptureControls.wrong_public' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms wrong_public
/-- info: 'Solidity.Backend.Passes.ShiftCaptureControls.wrong_order_vector' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms wrong_order_vector
/-- info: 'Solidity.Backend.Passes.ShiftCaptureControls.wrong_order_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms wrong_order_source
/-- info: 'Solidity.Backend.Passes.ShiftCaptureControls.represented' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms represented
/-- info: 'Solidity.Backend.Passes.ShiftCaptureControls.inhabited' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms inhabited
/-- info: 'Solidity.Backend.Passes.ShiftCaptureControls.joined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms joined
/-- info: 'Solidity.Backend.Passes.ShiftCaptureControls.ordered' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ordered
/-- info: 'Solidity.Backend.Passes.ShiftCaptureControls.source_expression' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms source_expression
/-- info: 'Solidity.Backend.Passes.ShiftCaptureControls.left_vector' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms left_vector
/-- info: 'Solidity.Backend.Passes.ShiftCaptureControls.right_vector' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms right_vector
/-- info: 'Solidity.Backend.Passes.ShiftCaptureControls.saturated' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms saturated
/-- info: 'Solidity.Backend.Passes.ShiftCaptureControls.wrong_recapture' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms wrong_recapture
/-- info: 'Solidity.Backend.Passes.ShiftCaptureControls.wrong_saturated_modulo' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms wrong_saturated_modulo
/-- info: 'Solidity.Backend.Passes.ShiftCaptureControls.corrupted_tail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms corrupted_tail
/-- info: 'Solidity.Backend.Passes.ShiftCaptureControls.insufficient_frame' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms insufficient_frame
end Solidity.Backend.Passes.ShiftCaptureControls
