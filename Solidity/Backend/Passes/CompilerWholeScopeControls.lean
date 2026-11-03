import Solidity.Backend.Passes.CompilerWholeScope

namespace Solidity.Backend.Passes.CompilerWholeScope.Controls
open Evm Evm.Memory MemoryCallControls

private def words (out : Evm.Out) (addresses : List Nat) : Option (List Nat) := do
  match out with
  | .ok m _ => (m.stack ++ addresses.map m.mem).mapM fun w => match w with
    | .val v => some v.val
    | .slot _ => none
  | _ => none
abbrev addresses := MemoryCallObservations.addresses

theorem complete_vector : words (run actual.code {machine with stack := [w[77],w[88]]}) addresses =
    some [77,88,264,99,256,42,256,259,259,259,1,8,0,2,33,34,1,44] := by
  with_unfolding_all decide +kernel

/-- A different, well-typed source program retains the extra return locals
and consumes them. It is not an alternative association of the scoped program. -/
def unscopedProgram : Prog C [] After := (allocate.join call).join consume
theorem unscoped_some : (Compiler.compile 1 (Frag.init []) unscopedProgram).isSome = true := by decide +kernel
@[irreducible] def unscoped : Compiler.Compilation 1 (Frag.init []) unscopedProgram :=
  (Compiler.compile 1 (Frag.init []) unscopedProgram).get unscoped_some

theorem unscoped_vector : words (run unscoped.code {machine with stack := [w[77],w[88]]}) addresses =
    some [77,88,264,99,256,42,256,259,259,259,1,8,0,2,42,34,1,44] := by
  with_unfolding_all decide +kernel

theorem omitted_scope_differs : words (run actual.code {machine with stack := [w[77],w[88]]}) addresses ≠
    words (run unscoped.code {machine with stack := [w[77],w[88]]}) addresses := by
  rw [complete_vector,unscoped_vector]
  decide

theorem corrupted_tail_refused : words (run actual.code {machine with stack := [w[77],w[88]]}) addresses ≠
    some [78,88,264,99,256,42,256,259,259,259,1,8,0,2,33,34,1,44] := by
  rw [complete_vector]
  decide

end Solidity.Backend.Passes.CompilerWholeScope.Controls
