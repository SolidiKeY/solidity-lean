import Solidity.Backend.Passes.CompilerCallScopeRecognition
import Solidity.Backend.Passes.MemoryCallScopeObservations

namespace Solidity.Backend.Passes.CompilerCallScopeRecognition.Controls
open Evm Evm.Memory MemoryCallControls
open CompilerCallScopeRecognition

private def words (out : Evm.Out) (addresses : List Nat) : Option (List Nat) := do
  match out with
  | .ok m _ => (m.stack ++ addresses.map m.mem).mapM fun w => match w with
    | .val v => some v.val
    | .slot _ => none
  | _ => none
abbrev addresses := MemoryCallObservations.addresses
def prefixCode : List Instr := allocation.code ++ actual.code
def code : List Instr := allocation.code ++ (actual.code ++ CompilerCallScopeRecognition.consumer.code)

theorem prefix_vector : words (run prefixCode {machine with stack := [w[77],w[88]]}) addresses =
    some [77,88,264,99,256,42,256,259,259,259,1,7,0,2,33,34,1,44] := by
  with_unfolding_all decide +kernel

theorem final_vector : words (run code {machine with stack := [w[77],w[88]]}) addresses =
    some [77,88,264,99,256,42,256,259,259,259,1,8,0,2,33,34,1,44] := by
  with_unfolding_all decide +kernel

theorem skipped_consumer_refused : words (run prefixCode {machine with stack := [w[77],w[88]]}) addresses ≠
    words (run code {machine with stack := [w[77],w[88]]}) addresses := by
  rw [prefix_vector,final_vector]
  decide

theorem corrupted_tail_refused : words (run code {machine with stack := [w[77],w[88]]}) addresses ≠
    some [78,88,264,99,256,42,256,259,259,259,1,8,0,2,33,34,1,44] := by
  rw [final_vector]
  decide

end Solidity.Backend.Passes.CompilerCallScopeRecognition.Controls
