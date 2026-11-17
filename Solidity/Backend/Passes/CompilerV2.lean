import Solidity.Evm.Compiler
import Solidity.Backend.InternalFlow.RuntimeFrameV3CallProducerRefTupleCall

/-!
# The v2 checked entry: v1, then automatic tuple-return calls

`CompilerV2.compile` is an additive entry beside the frozen v1 entry
`Evm.Compiler.compile` (H314). It returns the v1 result whenever v1 accepts.
Where v1 refuses a push-free program, it selects the program statement by
statement: the structural selector `Composition.compileStatement`, or, for a
call with tuple return binders, the published checked emitter `Tuple.emit`
over the selected frame expansion. The result is the existing
`Compilation.memoryCalls` constructor, so `Compilation.correct_exact` applies
to it unchanged; no certificate is supplied by hand.

v1 is untouched: `compile_of_v1` and `v1_none_of_none` state that v2 only
adds acceptance.
-/
namespace Solidity.Backend.Passes.CompilerV2

open Evm Evm.Memory Evm.Compiler
open Backend.InternalFlow.RuntimeFrame
open Backend.InternalFlow.RuntimeFrame.V3CallProducerRef

variable {C : Contract}

/-- A call with tuple return binders, selected automatically: the frame
expansion is selected structurally and `Tuple.emit` adds the result copies.
Every other statement is refused here. -/
def tupleStatement (b : Nat) {Γ Δ : Ctx} (F : Frag Γ) :
    (s : Stmt C Γ Δ) → Option (Composition.Statement b F s)
  | .call f args (.rets bs) body =>
    (Composition.compileProgram b F (Tuple.expand args bs body)).map (Tuple.emit f args bs body)
  | _ => none

/-- One statement: the structural selector first, then a tuple-return call. -/
def statement (b : Nat) {Γ Δ : Ctx} (F : Frag Γ) (s : Stmt C Γ Δ) :
    Option (Composition.Statement b F s) :=
  match Composition.compileStatement b F s with
  | some selected => some selected
  | none => tupleStatement b F s

/-- A program of structurally selected statements and tuple-return calls. -/
def program (b : Nat) {Γ Δ : Ctx} (F : Frag Γ) :
    (P : Prog C Γ Δ) → Option (Composition.Program b F P)
  | .nil => some (Composition.nil b F)
  | .cons head tail => do
    let first ← statement b F head
    let rest ← program b first.checked.frag tail
    pure (Composition.cons first rest)

/-- **The v2 checked entry.** v1 first; where v1 refuses a push-free program,
the tuple-return selection through the existing `memoryCalls` branch. -/
def compile (b : Nat) {Γ Δ : Ctx} (F : Frag Γ) (P : Prog C Γ Δ) :
    Option (Compilation b F P) :=
  match Compiler.compile b F P with
  | some result => some result
  | none =>
    if pushFree : Evm.Prog.pushes P = 0 then
      (program b F P).map fun selected => .memoryCalls selected.checked pushFree
    else none

/-- v2 keeps every v1 result. -/
theorem compile_of_v1 {b : Nat} {Γ Δ : Ctx} {F : Frag Γ} {P : Prog C Γ Δ}
    {result : Compilation b F P} (accepted : Compiler.compile b F P = some result) :
    compile b F P = some result := by
  simp only [compile, accepted]

/-- A v2 refusal is a v1 refusal. -/
theorem v1_none_of_none {b : Nat} {Γ Δ : Ctx} {F : Frag Γ} {P : Prog C Γ Δ}
    (refused : compile b F P = none) : Compiler.compile b F P = none := by
  cases v1 : Compiler.compile b F P with
  | none => rfl
  | some result => rw [compile_of_v1 v1] at refused; cases refused

/-- Where v1 refuses, v2 is exactly the tuple-return selection. -/
theorem compile_of_selected {b : Nat} {Γ Δ : Ctx} {F : Frag Γ} {P : Prog C Γ Δ}
    {selected : Composition.Program b F P} (v1 : Compiler.compile b F P = none)
    (pushFree : Evm.Prog.pushes P = 0) (chosen : program b F P = some selected) :
    compile b F P = some (.memoryCalls selected.checked pushFree) := by
  simp only [compile, v1, pushFree, chosen, dite_true, Option.map_some]

end Solidity.Backend.Passes.CompilerV2

#print axioms Solidity.Backend.Passes.CompilerV2.compile_of_v1
#print axioms Solidity.Backend.Passes.CompilerV2.v1_none_of_none
#print axioms Solidity.Backend.Passes.CompilerV2.compile_of_selected
