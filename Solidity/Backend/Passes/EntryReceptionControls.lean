import Solidity.Backend.Passes.EntryReception
import Solidity.Backend.Passes.FreshBooleanControls

/-! Complete actual admitted-value/body observations, separate from emitted
ABI decoder adequacy. Prefix negatives do not invent a post-revert machine. -/
namespace Solidity.Backend.Passes.EntryReceptionControls
open Evm Evm.Memory
open Controls.Fixture FixedBooleanSequence FreshBooleanFailure EntryReception

private def words (out : Evm.Out) : Option (List Nat) :=
  match out with
  | .ok m _ => (m.stack ++ addresses.map m.mem).mapM fun w =>
      match w with | .val v => some v.val | .slot _ => none
  | _ => none

theorem admitted_complete_vectors :
    AbiEntry.verdict (input 1) 4 params = .run (.cons (.word one) .nil) ∧
    words (run (prefixCode (decoded one)) {initialMachine with stack := [w[77],w[88]]}) =
      some [77,88,261,99,259,256,259,4,1,4,0,2,7,9,1,5] ∧
    AbiEntry.verdict (input 0) 4 params = .run (.cons (.word zero) .nil) ∧
    words (run (FreshBooleanCompilation.wholeStage (decoded zero)).code
      {initialMachine with stack := [w[77],w[88]]}) =
      some [77,88,261,99,259,256,256,7,0,7,9,2,8,9,1,4] := by
  exact ⟨one_admitted,by decide +kernel,zero_admitted,by decide +kernel⟩

theorem wrong_order_after_admission :
    words (run (population.code ++ ((initializer (decoded one)).code ++
      (wrongReceiver.code ++ FreshBooleanControls.wrongCapture.code)))
      {initialMachine with stack := [w[77],w[88]]}) =
      some [77,88,261,99,259,256,259,7,1,4,0,2,7,9,1,5] ∧
    words (run (population.code ++ ((initializer (decoded one)).code ++
      (wrongReceiver.code ++ FreshBooleanControls.wrongCapture.code)))
      {initialMachine with stack := [w[77],w[88]]}) ≠
      some [77,88,261,99,259,256,259,4,1,4,0,2,7,9,1,5] := by
  exact ⟨by decide +kernel,by decide +kernel⟩

theorem wrong_projection : ¬ ReprV .bool false (.val (wmod one.val)) := by
  intro h
  change Evm.Word.val (wmod one.val) = Evm.Word.val (bword false) at h
  have eq := Evm.Word.val.inj h
  exact (by decide : wmod one.val ≠ bword false) eq

theorem corrupted_saved_tail :
    words (run (prefixCode (decoded one)) {initialMachine with stack := [w[88],w[77]]}) ≠
      some [77,88,261,99,259,256,259,4,1,4,0,2,7,9,1,5] := by decide +kernel

theorem short_calldata_entry_failure :
    AbiEntry.verdict ({data := [],free := 128} : AbiEntry.Input) 4 params = .revert := by
  with_unfolding_all rfl

end Solidity.Backend.Passes.EntryReceptionControls
