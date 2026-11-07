import Solidity.Backend.Passes.ValueReflection
import Solidity.Backend.PrimitivePackets.Bitwise.Selected

/-! A typed receiving context for the published clean-width bitwise selector.
The target run is derived from runtime local cells, then reflected through the
selected certificate. No Source admission or physical bytecode claim is made. -/
namespace Solidity.Backend.Passes.BitwiseValueContext
open Evm Evm.Memory

/-- One selected certificate and one actual intrinsic value work for every
saved tail. Selection and execution are conclusions, not supplied premises. -/
theorem application {C : Contract} {b L frame : Nat}
    {state : State C Backend.PrimitivePackets.Bitwise.context} {base : Nat → Fin W} {machine : Machine}
    (op : Source.BinOp) (supported : Backend.PrimitivePackets.Bitwise.Supported op) (width : Fin 32)
    (x y : Nat) (hx : x < 2 ^ (Backend.PrimitivePackets.Bitwise.unsigned width).bits)
    (hy : y < 2 ^ (Backend.PrimitivePackets.Bitwise.unsigned width).bits)
    (represented : StateRepr L b frame (Frag.init Backend.PrimitivePackets.Bitwise.context) state base machine)
    (left : machine.mem (b+1) = .val (wmod x))
    (right : machine.mem b = .val (wmod y)) :
    ∃ (compiled : CompiledVal b (Frag.init Backend.PrimitivePackets.Bitwise.context) (Backend.PrimitivePackets.Bitwise.expression C op))
      (value : PrimTy.uint.Denote),
      compileVal b (Frag.init Backend.PrimitivePackets.Bitwise.context) (Backend.PrimitivePackets.Bitwise.expression C op) = some compiled ∧
      compiled.code = Backend.PrimitivePackets.Bitwise.code b op ∧
      (Backend.PrimitivePackets.Bitwise.expression C op).evalT state = .ok value ∧
      ReprV .uint value (.val (wmod (Backend.PrimitivePackets.Bitwise.value op x y))) ∧
      ∀ tail : List Word, run compiled.code {machine with stack := tail} =
        .ok ({machine with stack := tail}.push (.val (wmod (Backend.PrimitivePackets.Bitwise.value op x y)))) 0 := by
  have selection := Backend.PrimitivePackets.Bitwise.selected C b op supported
  cases chosen : compileVal b (Frag.init Backend.PrimitivePackets.Bitwise.context) (Backend.PrimitivePackets.Bitwise.expression C op) with
  | none => rw [chosen] at selection; cases selection
  | some compiled =>
    have code : compiled.code = Backend.PrimitivePackets.Bitwise.code b op := by
      rw [chosen] at selection
      exact Option.some.inj selection
    have execution : run compiled.code machine =
        .ok (machine.push (.val (wmod (Backend.PrimitivePackets.Bitwise.value op x y)))) 0 := by
      rw [code]
      exact Backend.PrimitivePackets.Bitwise.execute b op supported width x y hx hy machine left right
    obtain ⟨value, source, relation⟩ :=
      ValueReflection.success compiled _ represented execution
    refine ⟨compiled, value, rfl, code, source, relation, ?_⟩
    intro tail
    rw [code]
    exact Backend.PrimitivePackets.Bitwise.execute b op supported width x y hx hy {machine with stack := tail} left right

/-- info: 'Solidity.Backend.Passes.BitwiseValueContext.application' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms application
end Solidity.Backend.Passes.BitwiseValueContext
