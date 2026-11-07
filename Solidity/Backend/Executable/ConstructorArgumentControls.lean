import Solidity.Source.Hoare
import Solidity.Backend.Executable.ConstructorArgumentObservations
import Solidity.Backend.Aggregates.ByteParameterControls

/-! Inhabited argument-preparation controls, not constructor/runtime closure. -/
namespace Solidity.Backend.Executable.ConstructorArgumentObservations.Checks
open Solidity Lowering.V07 Solidity.Backend.Executable.ConstructorLocalArguments
open Solidity.Backend.Executable.ConstructorArgumentObservations

-- Source state and two old aliases/objects are reused from the published control.
abbrev E := Solidity.Backend.Aggregates.ByteParameterControls.E
abbrev C := Solidity.Backend.Aggregates.ByteParameterControls.C

def signed16 : Source.IntTy := ⟨true,16,by decide⟩
def x := integerValue Source.IntTy.u8 255 (by decide)
def y := integerValue signed16 (-7) (by decide)
def caller := (Solidity.Backend.Aggregates.ByteParameterControls.aliasTarget.push
  (t := .val (integerPrim Source.IntTy.u8)) x).push
  (t := .val (integerPrim signed16)) y

def fixed : Roadmap.Fixed where
  evm := { keccak := fun _ => 0, keccak_lt := fun _ => by decide,
           precompile := fun _ _ => none, precompileGas := fun _ _ => 0 }
  ledger := fun bal _ a => bal a
  regionLen := 1
  rootSlots := 1

def global (p : Roadmap.Pipeline) : Source.Glob E where
  prog := { body := fun _ => none, consts := fun _ => none, inits := fun _ => [],
            ctor := fun _ => none, ctorLocals := fun _ => [],
            baseArgs := fun _ => [], contracts := [] }
  pipeline := p
  fixed := fixed
  balance0 := fun _ => ⟨0,by decide⟩
  hasCode := fun _ _ => false
  callee := fun _ => .answer (.success [])
  timestamp := ⟨0,by decide⟩

def before : Source.EMState E [.int Source.IntTy.u8,.int signed16,.bytes .memory,.bytes .memory] :=
  (.cons (.int 255 (by decide)) (.cons (.int (-7) (by decide))
    Solidity.Backend.Aggregates.ByteParameterControls.sourceLocals),
    Solidity.Backend.Aggregates.ByteParameterControls.sourceState)
def selectedSource : Source.RConvArgs E
    [.int Source.IntTy.u8,.int signed16,.bytes .memory,.bytes .memory]
    [.int Source.IntTy.u8,.int signed16] := sourceArgs _ _ (by decide) (by decide)
def selectedTarget := targetArgs (C := C) Source.IntTy.u8 signed16
  (.there .here : Idx _ (.val (integerPrim Source.IntTy.u8)))
  (.here : Idx [.val (integerPrim signed16),.val (integerPrim Source.IntTy.u8),
    .mem Solidity.bytesR,
    .mem Solidity.bytesR] (.val (integerPrim signed16)))
/-- Inhabited mixed-width, ordered, populated-caller and budget controls.
The fixture hash is unused by these local argument operations. -/
theorem inhabited :
∀ p : Roadmap.Pipeline,
 (Source.evalConvArgs
  (global p)
  Solidity.Backend.Aggregates.ByteParameterControls.frame 3
  selectedSource).run
  before =
 (.ok (.cons (.int 255 (by decide)) (.cons (.int (-7) (by decide)) .nil)),
  before) ∧
 (Source.evalConvArgs
  (global p)
  Solidity.Backend.Aggregates.ByteParameterControls.frame 0
  selectedSource).run
  before =
 (.error .timeout,before) ∧
 selectedTarget.evalT
  caller =
 .ok (y,
  (x,())) ∧
 ((selectedTarget.evalT
  caller).toOption.map
  targetKeys) = some [some 255,some (-7)] ∧
 ((selectedTarget.evalT
  caller).toOption.map
  targetKeys) ≠ some [some (-7),some 255] ∧
 before.2.heap.get 0 =
 some ⟨.bytes .memory,.bytes [170,187]⟩ ∧
 TEnv.get (.there (.there .here))
  caller.env =
 TEnv.get (.there (.there (.there .here)))
  caller.env := by
  intro p
  exact ⟨rfl,rfl,rfl,rfl,by decide,rfl,rfl⟩

end Solidity.Backend.Executable.ConstructorArgumentObservations.Checks
