import Solidity.Backend.Passes.CaptureControls
import Solidity.Evm.MemoryStructExamples

/-! Separate nontrivial local and field instances of the generic capture
adapters. The field instance reuses a published populated representation. -/
namespace Solidity.Backend.Passes.CaptureCases
open Solidity.Evm Solidity.Evm.Memory
open Solidity.Backend.Passes.Controls.Fixture

namespace Local
private abbrev F : Frag Γ := Frag.init Γ
def stmt : Stmt C Γ Γ := .assignIncDec .here .postInc rfl (.local .here) rfl
def val : CompiledVal (C := C) 0 F
    (bumpResultValue .postInc rfl (.simple (.local .here))) :=
  (compileVal 0 F _).get (by decide +kernel)
def bump : CompiledStmt (C := C) 0 F (.incDec .postInc rfl (.local .here)) :=
  (compileStmt 0 F _).get (by decide +kernel)
def code : List Instr := val.code ++ bump.code ++ [.mstore 3]
def actual := (compileStmt 0 F stmt).get (by decide +kernel)
theorem actual_code : code = actual.code := rfl
theorem self_source : stmt.run σ = .ok ⟨σ, List.prefix_refl _⟩ := by with_unfolding_all rfl

theorem generic_instance (tail : List Word) :
    GrowingResult 1 0 6 0 F σ base {machine with stack := tail}
      (stmt.run σ) (run code {machine with stack := tail}) :=
  capture_local_frame .here .here .postInc rfl rfl val.code bump.code val.cert bump.cert
    fixture_repr (by decide) LinkedControls.frame_six.heap.above
    LinkedControls.frame_six.structs.above tail

private def cellValue (result : Evm.Out) : Option Nat :=
  match result with
  | .ok m _ => match m.mem 3 with | .val w => some w.val | _ => none
  | _ => none

/-- Postfix self-capture restores0; omitting the deferred capture store leaves1. -/
theorem deferred_store_matters :
    cellValue (run code machine) = some 0 ∧
      cellValue (run bump.code machine) = some 1 := by
  constructor <;> decide +kernel
end Local

namespace Field
private abbrev Ξ : Ctx := [.val .uint, .mem (.array (.prim .uint)),
  .mem (.struct "Toggle"), .mem (.struct "Toggle"), .mem (.struct "Toggle")]
private abbrev F : Frag Ξ := Frag.init Ξ
private abbrev old : Idx Ξ (.mem (.struct "Toggle")) := .there (.there (.there .here))
private abbrev other : Idx Ξ (.mem (.struct "Toggle")) := .there (.there .here)
def loc : OpLoc C Ξ .uint := .mfield (.var old rfl) "n" rfl
def stmt : Stmt C Ξ Ξ := .assignIncDec .here .postInc rfl loc rfl
def val : CompiledVal (C := C) 1 F
    (bumpResultValue .postInc rfl (.readMem (.field (.var old rfl) "n" rfl))) :=
  (compileVal 1 F _).get (by decide +kernel)
def bump : CompiledStmt 1 F (.incDec .postInc rfl loc) :=
  (compileStmt 1 F _).get (by decide +kernel)
def code : List Instr := val.code ++ bump.code ++ [.mstore 5]
def actual := (compileStmt 1 F stmt).get (by decide +kernel)
theorem actual_code : code = actual.code := rfl

private def cells (n : Nat) : Evm.Out → Option Nat
  | .ok m _ => match m.mem n with | .val w => some w.val | _ => none
  | _ => none
private def sourceValues {H : HTy} (result : TRes (Solidity.Out C H Ξ)) : Option (List Int) := do
  let o ← result.toOption
  let a ← (Val.readMem (MLoc.field (.var old rfl) "n" rfl)).evalT o.st |>.toOption
  let b ← (Val.readMem (MLoc.field (.var other rfl) "n" rfl)).evalT o.st |>.toOption
  pure [(TEnv.get (.here : Idx Ξ (.val .uint)) o.st.env).1, a.1, b.1]

/-- A real populated source heap with two aliases and an independent struct
inhabits the field adapter: saved7, mutated8, independent9, pointer identity.
The published fixture is represented; fresh reachability is supplied separately
by the mixed/allocating capture controls, not claimed for this struct fixture. -/
theorem inhabited :
    ∃ (σ : State C Ξ) (base : Nat → Fin W) (m : Machine),
      StateRepr 1 1 8 F σ base m ∧
      (∀ tail, GrowingResult 1 1 8 0 F σ base {m with stack := tail}
        (stmt.run σ) (run code {m with stack := tail})) ∧
      sourceValues (stmt.run σ) = some [7, 8, 9] ∧
      [5, 33, 41, 1, 2, 3, 4].mapM (fun n => cells n (run code m)) =
        some [7, 8, 9, 32, 32, 40, 48] := by
  refine ⟨_, _, _, StructExamples.Public.fixture, ?_, ?_, ?_⟩
  · intro tail
    exact capture_field_frame .here .postInc rfl (.var old rfl) "n" rfl rfl
      val.code bump.code val.cert bump.cert StructExamples.Public.fixture (by decide)
      StructExamples.Public.fixture.heap.above StructExamples.Public.fixture.structs.above tail
  · decide +kernel
  · decide +kernel
end Field

end Solidity.Backend.Passes.CaptureCases
