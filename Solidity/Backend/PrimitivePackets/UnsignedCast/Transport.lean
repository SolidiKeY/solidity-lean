import Solidity.Backend.PrimitivePackets.UnsignedCast.Compiler

/-! Independent Source cast to publicly selected symbolic code, over initial
local-value alignment and an existing physical state representation only. -/
namespace Solidity.Backend.PrimitivePackets.UnsignedCast
open Solidity.Lowering.V07
open Evm Evm.Memory

/-- Both pipelines evaluate the actual cast at every sufficient Source horizon.
The caller's checked mode and complete Source state are retained. -/
theorem source_both_pipelines {E : Source.Env} {Γ : Source.RCtx}
    (G : Source.Glob E) (F : Source.Fr) (fuel : Nat) (source : Source.EMState E Γ)
    (bits : Nat) (legal : Legal bits) (i : Source.Idx Γ (.int Source.IntTy.u256))
    (n : Int) (range : Source.IntTy.u256.lo ≤ n ∧ n ≤ Source.IntTy.u256.hi)
    (read : source.1.get i = .int n range) :
    ∀ pipeline : Roadmap.Pipeline,
    (Source.evalE {G with pipeline := pipeline} F (fuel+2) (expression bits legal i)).run source =
      (.ok (.val (Source.intWrap (targetTy bits legal) n)),source) := by
  intro pipeline
  exact source_run _ F fuel source bits legal i n range read

/-- No completing-horizon fact is silently assumed at horizon zero or one. -/
theorem source_timeout {E : Source.Env} {Γ : Source.RCtx}
    (G : Source.Glob E) (F : Source.Fr) (source : Source.EMState E Γ)
    (bits : Nat) (legal : Legal bits) (i : Source.Idx Γ (.int Source.IntTy.u256)) :
    (Source.evalE G F 0 (expression bits legal i)).run source = (.error .timeout,source) ∧
    (Source.evalE G F 1 (expression bits legal i)).run source = (.error .timeout,source) := by
  constructor <;> rfl

/-- General packet: all legal smaller uint widths, arbitrary local values,
public compiler selection, exact result word and a nonempty saved tail.
The exact output machine preserves memory, store, balances and all other
non-stack fields; the physical representation is preserved as well. -/
theorem transport {E : Source.Env} {srcΓ : Source.RCtx} {C : Contract} {Γ : Ctx}
    (G : Source.Glob E) (F : Source.Fr) (fuel : Nat)
    (source : Source.EMState E srcΓ) (target : State C Γ)
    (bits : Nat) (legal : Legal bits)
    (i : Source.Idx srcΓ (.int Source.IntTy.u256)) (j : Idx Γ (.val .uint))
    (n : Int) (range : Source.IntTy.u256.lo ≤ n ∧ n ≤ Source.IntTy.u256.hi)
    (sourceRead : source.1.get i = .int n range)
    (targetRead : TEnv.get j target.env = integerValue Source.IntTy.u256 n range)
    (offset L frame : Nat) (frag : Frag Γ) (base : Nat → Fin W) (machine : Machine)
    (represented : StateRepr L offset frame frag target base machine)
    (head : Word) (tail : List Word) :
    let result := integerValue (targetTy bits legal) ((targetTy bits legal).wrap n)
      ((targetTy bits legal).wrap_mem n)
    (Source.evalE G F (fuel+2) (expression bits legal i)).run source =
      (.ok (.val (Source.intWrap (targetTy bits legal) n)),source) ∧
    (value bits legal j).evalT target = .ok result ∧
    IntValueRel (targetTy bits legal)
      (Source.intWrap (targetTy bits legal) n : Source.Val E.layout (.int (targetTy bits legal))) result ∧
    Memory.compileVal offset frag (value (C := C) bits legal j) = some (selected offset frag bits legal j) ∧
    run (instructions offset bits j) {machine with stack := head :: tail} =
      .ok ({machine with stack := head :: tail}.push (.val result.word)) 0 ∧
    StateRepr L offset frame frag target base
      ({machine with stack := head :: tail}.push (.val result.word)) := by
  exact ⟨source_run G F fuel source bits legal i n range sourceRead,
    value_run target bits legal j n range targetRead,
    integer_related _ _ _,compile_selection offset frag bits legal j,
    machine_run target offset L frame frag base machine represented bits legal j n range targetRead _,
    (represented.stack _).push _⟩

end Solidity.Backend.PrimitivePackets.UnsignedCast
