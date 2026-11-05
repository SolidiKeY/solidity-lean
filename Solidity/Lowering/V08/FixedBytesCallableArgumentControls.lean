import Solidity.Lowering.V08.FixedBytesCallableArgument
import Solidity.Lowering.V07.FixedBytesAssignmentControls

/-! Kernel-checked clients of actual converted argument execution. The complete
published initial relation and populated machines are reused; no callee,
ABI encoding or runtime-frame correspondence is assumed. -/
namespace Solidity.Lowering.V08.FixedBytesCallableArgument.Controls
open Solidity Source
open Solidity.Lowering.V07
open FixedBytesAssignmentControls
open Source.SemanticsExamples
open MixedAssignmentControls (globals)

def actual_client (n : Nat) (w : 1 ≤ n ∧ n ≤ 32) (p : Roadmap.Pipeline)
    (checked static : Bool) (extra : Nat) (old rhs : List UInt8) :=
  transport_argument (globals p) {F0 with checked := checked,static := static} extra
    (source n w old rhs) (target n w old rhs) n w (mapping n w) BindingRel
    (initial n w old rhs) (reflect n w) .here (.there .here) .here (.there .here)
    rfl rfl (FixedBytesAssignmentControls.payload n rhs) (Source.fitBytes_length n rhs) rfl

def binary_client (p : Roadmap.Pipeline) (checked static : Bool) :=
  actual_client 2 (by decide +kernel) p checked static 0 [255,128] [0,1]
def maximum_client (p : Roadmap.Pipeline) :=
  actual_client 32 (by decide +kernel) p false false 0 [] (List.replicate 32 255)

theorem zero_timeout (p : Roadmap.Pipeline) :
    (Source.evalConvArgs (globals p) F0 0
      (arguments 2 (by decide +kernel) (.here : Source.Idx (SrcCtx 2 (by decide +kernel)) _)
        (.there .here))).run (source 2 (by decide +kernel) [255,128] [0,1]) =
      (.error .timeout,source 2 (by decide +kernel) [255,128] [0,1]) := by rfl

theorem argument_timeout (p : Roadmap.Pipeline) :
    (Source.evalConvArgs (globals p) F0 1
      (arguments 2 (by decide +kernel) (.here : Source.Idx (SrcCtx 2 (by decide +kernel)) _)
        (.there .here))).run (source 2 (by decide +kernel) [255,128] [0,1]) =
      (.error .timeout,source 2 (by decide +kernel) [255,128] [0,1]) := by rfl


abbrev binaryState := source 2 (by decide +kernel) [255,128] [0,1]
abbrev binaryArguments := arguments (E := MixedAssignmentControls.E) 2 (by decide +kernel)
  (.here : Source.Idx (SrcCtx 2 (by decide +kernel)) _) (.there .here)

theorem binary_actual (p : Roadmap.Pipeline) :
    (Source.evalConvArgs (globals p) F0 4 binaryArguments).run binaryState =
      (.ok (.cons (.fixedBytes [0,1] (by decide +kernel)) .nil),
       (binaryState.1.set .here (.fixedBytes [0,1] (by decide +kernel)),binaryState.2)) := by
  first | exact argument_actual (globals p) F0 0 binaryState 2 (by decide +kernel) .here (.there .here) [0,1] (by decide +kernel) rfl | decide | omega | rfl

theorem wrong_byte_order (p : Roadmap.Pipeline) :
    (Source.evalConvArgs (globals p) F0 4 binaryArguments).run binaryState ≠
      (.ok (.cons (.fixedBytes [1,0] (by decide +kernel)) .nil),
       (binaryState.1.set .here (.fixedBytes [0,1] (by decide +kernel)),binaryState.2)) := by
  rw [binary_actual]
  intro bad
  cases bad

theorem stale_caller (p : Roadmap.Pipeline) :
    (Source.evalConvArgs (globals p) F0 4 binaryArguments).run binaryState ≠
      (.ok (.cons (.fixedBytes [0,1] (by decide +kernel)) .nil),binaryState) := by
  rw [binary_actual]
  intro bad
  have slot := congrArg (fun result => result.2.1.get
    (.here : Source.Idx (SrcCtx 2 (by decide +kernel)) _)) bad
  cases slot

end Solidity.Lowering.V08.FixedBytesCallableArgument.Controls

/-- info: 'Solidity.Lowering.V08.FixedBytesCallableArgument.Controls.actual_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Lowering.V08.FixedBytesCallableArgument.Controls.actual_client
/-- info: 'Solidity.Lowering.V08.FixedBytesCallableArgument.Controls.binary_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Lowering.V08.FixedBytesCallableArgument.Controls.binary_client
/-- info: 'Solidity.Lowering.V08.FixedBytesCallableArgument.Controls.maximum_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Lowering.V08.FixedBytesCallableArgument.Controls.maximum_client
/-- info: 'Solidity.Lowering.V08.FixedBytesCallableArgument.Controls.zero_timeout' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Lowering.V08.FixedBytesCallableArgument.Controls.zero_timeout
/-- info: 'Solidity.Lowering.V08.FixedBytesCallableArgument.Controls.argument_timeout' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Lowering.V08.FixedBytesCallableArgument.Controls.argument_timeout

/-- info: 'Solidity.Lowering.V08.FixedBytesCallableArgument.Controls.binary_actual' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Lowering.V08.FixedBytesCallableArgument.Controls.binary_actual
/-- info: 'Solidity.Lowering.V08.FixedBytesCallableArgument.Controls.wrong_byte_order' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Lowering.V08.FixedBytesCallableArgument.Controls.wrong_byte_order
/-- info: 'Solidity.Lowering.V08.FixedBytesCallableArgument.Controls.stale_caller' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Lowering.V08.FixedBytesCallableArgument.Controls.stale_caller
