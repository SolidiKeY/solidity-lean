import Solidity.Backend.Passes.CompilerV2
import Solidity.Backend.Passes.CompilerScalarBridge

/-!
# The v3 checked entry: v2, then selected scalar recursive calls

`CompilerV3.compile` is additive beside v2 and the frozen v1 (H314): it
returns the v2 result whenever v2 accepts. Where v2 refuses a push-free
singleton program whose statement keeps its context, it runs the scalar
selector `ScalarSourceCompiler.compile` at the fixed parameters `c = 5`,
`arena = 16`, `pointer = 9`, `bottom = 8` and, when `Shape` holds for the
program's `b` and context, returns the bridged `Compilation.memoryCalls`
(`CompilerScalarBridge.selectedProgram`). The parameters are a limit of this
entry, not of the bridge: a context that does not fit below cell 9 is refused.

Acceptance is not agreement on every world: the bridged cost excludes the
states whose typed run is exhausted, panics or diverges, so those states are
never an `Input` of the accepted result.
-/
namespace Solidity.Backend.Passes.CompilerV3

open Evm Evm.Memory Evm.Compiler
open Backend.InternalFlow.RuntimeFrame

variable {C : Contract}

/-- A statement that keeps its context, selected as a scalar recursive call
and bridged, when the fixed parameters fit `b` and the context. -/
def scalarStatement (b : Nat) {Γ : Ctx} (F : Frag Γ) (s : Stmt C Γ Γ) :
    Option (Calls.Program b F (.cons s .nil)) :=
  if shape : CompilerScalarBridge.Shape b 5 16 9 8 Γ then
    (ScalarSourceCompiler.compile b 5 16 9 8 F s).map
      fun selected => CompilerScalarBridge.selectedProgram selected shape
  else none

/-- A singleton program whose statement keeps its context. -/
def scalarProgram (b : Nat) {Γ Δ : Ctx} (F : Frag Γ) (P : Prog C Γ Δ) :
    Option (Calls.Program b F P) :=
  if same : Δ = Γ then by
    subst same
    exact match P with
      | .cons s .nil => scalarStatement b F s
      | _ => none
  else none

/-- **The v3 checked entry.** v2 first; where v2 refuses a push-free program,
the bridged scalar selection through the existing `memoryCalls` branch. -/
def compile (b : Nat) {Γ Δ : Ctx} (F : Frag Γ) (P : Prog C Γ Δ) :
    Option (Compilation b F P) :=
  match CompilerV2.compile b F P with
  | some result => some result
  | none =>
    if pushFree : Evm.Prog.pushes P = 0 then
      (scalarProgram b F P).map fun selected => .memoryCalls selected pushFree
    else none

/-- v3 keeps every v2 result. -/
theorem compile_of_v2 {b : Nat} {Γ Δ : Ctx} {F : Frag Γ} {P : Prog C Γ Δ}
    {result : Compilation b F P} (accepted : CompilerV2.compile b F P = some result) :
    compile b F P = some result := by
  simp only [compile, accepted]

/-- v3 keeps every v1 result. -/
theorem compile_of_v1 {b : Nat} {Γ Δ : Ctx} {F : Frag Γ} {P : Prog C Γ Δ}
    {result : Compilation b F P} (accepted : Compiler.compile b F P = some result) :
    compile b F P = some result :=
  compile_of_v2 (CompilerV2.compile_of_v1 accepted)

/-- Where v2 refuses, a selected scalar call under `Shape` is accepted with
its bridged program. -/
theorem compile_of_selected {b : Nat} {Γ : Ctx} {F : Frag Γ} {s : Stmt C Γ Γ}
    {selected : ScalarSourceCompiler.Selected b 5 16 9 8 F s}
    (v2 : CompilerV2.compile b F (.cons s .nil) = none)
    (pushFree : Evm.Prog.pushes (Prog.cons s .nil) = 0)
    (shape : CompilerScalarBridge.Shape b 5 16 9 8 Γ)
    (chosen : ScalarSourceCompiler.compile b 5 16 9 8 F s = some selected) :
    compile b F (.cons s .nil) =
      some (.memoryCalls (CompilerScalarBridge.selectedProgram selected shape) pushFree) := by
  have step : scalarProgram b F (.cons s .nil) =
      some (CompilerScalarBridge.selectedProgram selected shape) := by
    unfold scalarProgram
    rw [dif_pos rfl]
    change scalarStatement b F s = _
    unfold scalarStatement
    rw [dif_pos shape, chosen]
    rfl
  simp only [compile, v2, pushFree, step, dite_true, Option.map_some]

end Solidity.Backend.Passes.CompilerV3

#print axioms Solidity.Backend.Passes.CompilerV3.compile_of_v1
#print axioms Solidity.Backend.Passes.CompilerV3.compile_of_selected
