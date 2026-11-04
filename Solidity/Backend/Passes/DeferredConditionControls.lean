import Solidity.Backend.Passes.DeferredCondition
import Solidity.Backend.Passes.QueueCompletionControls

/-! One publicly selected operand for both runtime Booleans. Capture precedes
mutation and private-context removal. These are intrinsic symbolic controls. -/
namespace Solidity.Backend.Passes.DeferredCondition.Controls
open Evm Evm.Memory Evm.Compiler
open Passes.Controls.Fixture
open ReferenceControls (Γb fb state target input_repr)
open QueueCompletionControls (good gc update uc after cells)

def operand : DeferredSource.Operand C Γb (.prim .bool) :=
  ⟨.val .bool :: Γb,CapturedValueStability.program (.user "saved") good .here update,
    .val (.simple (.local .here))⟩
def code : CompiledProg 0 fb operand.code :=
  (Memory.compileProg 0 fb operand.code).get (by decide +kernel)
def reader : CompiledVal 0 code.frag (expression operand) :=
  (Memory.compileVal 0 code.frag (expression operand)).get (by decide +kernel)

theorem code_public : Memory.compileProg 0 fb operand.code = some code :=
  (Option.some_get _).symm
theorem reader_public : Memory.compileVal 0 code.frag (expression operand) = some reader :=
  (Option.some_get _).symm

def result (a : Bool) : Solidity.Out C (state a).H Γb :=
  ⟨(state a).setLocal .here false,List.prefix_refl _⟩
theorem source (a : Bool) : operand.run (state a) = .ok (result a,.prim a) := by
  cases a <;> with_unfolding_all rfl

theorem input (a : Bool) : (Compilation.memory code).Input 1 6 base (state a) (target a) := by
  exact ⟨input_repr a,by decide +kernel,.inl rfl⟩

theorem correlated (a : Bool) : type_of%
  (shared operand code reader (input a) (by rfl) (result a) a (source a)) :=
  shared operand code reader (input a) (by rfl) (result a) a (source a)

theorem joined (a : Bool) (tail : List Word) :
    run (code.code ++ reader.code) {(target a) with stack := tail} =
      .ok ((after a tail).push (.val (bword a))) 0 := by
  exact QueueCompletionControls.joined a tail

/-- All original locals, aliases, array elements and allocator cursor. -/
theorem observations (a : Bool) (tail : List Word) :
    (cells.map ((after a tail).push (.val (bword a))).mem,
      ((after a tail).push (.val (bword a))).stack) =
      ([.val (bword a),w[0],w[0],w[16],w[16],w[20],w[2],w[7],w[9],w[1],w[4]],
        .val (bword a) :: tail) := rfl

def observe : Evm.Out → Option (List Word × List Word)
  | .ok m _ => some (cells.map m.mem,m.stack)
  | _ => none

theorem wrong_recapture :
    observe (run (code.code ++ [.mload 4]) (target true)) ≠
      observe (run (code.code ++ reader.code) (target true)) := by decide +kernel

theorem skipped_capture : observe (run reader.code (target true)) ≠
    observe (run (code.code ++ reader.code) (target true)) := by decide +kernel

theorem corrupt_tail :
    observe (run (code.code ++ reader.code) {(target true) with stack := [w[77],w[88]]}) ≠
      observe (.ok ((after true [w[88],w[77]]).push w[1]) 0) := by decide +kernel

theorem insufficient_frame : ¬ (Compilation.memory code).Input 1 5 base (state true) (target true) := by
  intro h
  have bound := h.2.1
  change 0 + 6 ≤ 5 at bound
  omega

end Solidity.Backend.Passes.DeferredCondition.Controls

/-- info: 'Solidity.Backend.Passes.DeferredCondition.Controls.code_public' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.Passes.DeferredCondition.Controls.code_public

/-- info: 'Solidity.Backend.Passes.DeferredCondition.Controls.reader_public' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.Passes.DeferredCondition.Controls.reader_public

/-- info: 'Solidity.Backend.Passes.DeferredCondition.Controls.source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.Passes.DeferredCondition.Controls.source

/-- info: 'Solidity.Backend.Passes.DeferredCondition.Controls.input' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.Passes.DeferredCondition.Controls.input

/-- info: 'Solidity.Backend.Passes.DeferredCondition.Controls.correlated' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.Passes.DeferredCondition.Controls.correlated

/-- info: 'Solidity.Backend.Passes.DeferredCondition.Controls.joined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.Passes.DeferredCondition.Controls.joined

/-- info: 'Solidity.Backend.Passes.DeferredCondition.Controls.observations' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.Passes.DeferredCondition.Controls.observations

/-- info: 'Solidity.Backend.Passes.DeferredCondition.Controls.wrong_recapture' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.Passes.DeferredCondition.Controls.wrong_recapture

/-- info: 'Solidity.Backend.Passes.DeferredCondition.Controls.skipped_capture' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.Passes.DeferredCondition.Controls.skipped_capture

/-- info: 'Solidity.Backend.Passes.DeferredCondition.Controls.corrupt_tail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.Passes.DeferredCondition.Controls.corrupt_tail

/-- info: 'Solidity.Backend.Passes.DeferredCondition.Controls.insufficient_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.Passes.DeferredCondition.Controls.insufficient_frame
