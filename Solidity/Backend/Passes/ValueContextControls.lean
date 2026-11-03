import Solidity.Backend.Passes.ValueContext
import Solidity.Backend.Passes.ValueSequenceControls

/-! Real fresh declarations, old primitive/reference observations, wrong
unshifted-index negatives and unchanged core refusals. -/
namespace Solidity.Backend.Passes.ValueContextControls
open Solidity.Evm Solidity.Evm.Compiler Solidity.Evm.Memory
open Solidity.Backend.Passes.Controls.Fixture
open Solidity.Backend.Passes.ValueSequenceControls
private abbrev A : RefTy := .array (.prim .uint)
private abbrev F : Frag Γ := Frag.init Γ

def eleven : PrimTy.uint.Denote := ⟨11, rfl⟩
def zero : PrimTy.uint.Denote := ⟨0, rfl⟩
def localExpr : Val C Γ .uint := .simple (.local .here)
def localValue : CompiledVal 0 F localExpr :=
  (compileVal 0 F localExpr).get (by decide +kernel)
def scalarProg : Prog C Γ (.val .uint :: Γ) :=
  .cons (.declLocal .uint (.user "fresh") (some (.simple (.lit 11 rfl)))) .nil
def scalarStage : CompiledProg 0 F scalarProg :=
  (compileProg 0 F scalarProg).get (by decide +kernel)
def refProg : Prog C Γ (.mem A :: Γ) :=
  .cons (.declMem A (.user "freshRef")
    (some (.alias (.var (.there (.there (.there .here))) rfl))) rfl rfl) .nil
def refStage : CompiledProg 0 F refProg := (compileProg 0 F refProg).get (by decide +kernel)

theorem scalar_source : scalarProg.run σ = .ok ⟨σ.push eleven, List.prefix_refl _⟩ := by
  with_unfolding_all rfl

theorem reference_source : refProg.run σ =
    .ok ⟨σ.push (t := .mem A) (some CompileExamples.r1), List.prefix_refl _⟩ := by
  with_unfolding_all rfl

theorem scalar_run (tail : List Word) :
    run scalarStage.code {machine with stack := tail} =
      .ok (writeMachine {machine with stack := tail} 4 w[11]) 0 := by rfl

theorem reference_run (tail : List Word) :
    run refStage.code {machine with stack := tail} =
      .ok (writeMachine {machine with stack := tail} 4 w[20]) 0 := by rfl

/-- Original emitted code works at its newly weakened source context;
this genuinely extends the separated frame4 to frame6. -/
def scalar_transport (tail : List Word) :=
  value_after_fresh_scalar localValue fixture_repr eleven w[11]
    (ReprV.uint_of rfl) (frame' := 6) (by decide)
    LinkedControls.frame_six.heap.above LinkedControls.frame_six.structs.above
    (v := zero) rfl tail

def reference_transport (tail : List Word) :=
  value_after_fresh_reference a fixture_repr CompileExamples.r1
    (frame' := 6) (by decide) LinkedControls.frame_six.heap.above
    LinkedControls.frame_six.structs.above first_source tail

theorem scalar_decl_prefix (tail : List Word) :
    ∃ word, ReprV .uint zero word ∧
      run (scalarStage.code ++ localValue.code) {machine with stack := tail} =
        .ok ((writeMachine {machine with stack := tail} 4 w[11]).push word) 0 := by
  obtain ⟨word, hw, ht⟩ := scalar_transport tail
  exact ⟨word, hw, by rw [run_append_ok (scalar_run tail)]; exact ht⟩

theorem reference_decl_prefix (tail : List Word) :
    ∃ word, ReprV .uint seven word ∧
      run (refStage.code ++ a.code) {machine with stack := tail} =
        .ok ((writeMachine {machine with stack := tail} 4 w[20]).push word) 0 := by
  obtain ⟨word, hw, ht⟩ := reference_transport tail
  exact ⟨word, hw, by rw [run_append_ok (reference_run tail)]; exact ht⟩

/-- A selected old invalid read still reverts after a fresh scalar/ref;
the failure does not disappear under context transport. -/
theorem preserved_failures (tail : List Word) :
    run ExpressionControls.checkedBad.code (writeMachine {machine with stack := tail} 4 w[11]) = .revert ∧
    run ExpressionControls.checkedBad.code (writeMachine {machine with stack := tail} 4 w[20]) = .revert := by
  constructor
  · exact (value_fresh_scalar_revert_iff ExpressionControls.checkedBad fixture_repr eleven w[11]
      (ReprV.uint_of rfl) (frame' := 6) (by decide) LinkedControls.frame_six.heap.above
      LinkedControls.frame_six.structs.above tail).mpr (by with_unfolding_all rfl)
  · exact (value_fresh_reference_revert_iff ExpressionControls.checkedBad fixture_repr CompileExamples.r1
      (frame' := 6) (by decide) LinkedControls.frame_six.heap.above
      LinkedControls.frame_six.structs.above tail).mpr (by with_unfolding_all rfl)

def wrongScalar : Val C (.val .uint :: Γ) .uint := .simple (.local .here)
def wrongRef : Val C (.mem A :: Γ) .uint :=
  .readMem (.index .dyn (.var .here rfl) (.simple (.lit 0 rfl)))
def wrongScalarCode : CompiledVal 0 (F.push (.val .uint) .ok) wrongScalar :=
  (compileVal 0 _ wrongScalar).get (by decide +kernel)
def wrongRefCode : CompiledVal 0 (F.push (.mem A) .ok) wrongRef :=
  (compileVal 0 _ wrongRef).get (by decide +kernel)

theorem source_wrong_index :
    (localExpr.wk (Thin.drop (t := .val .uint) .refl)).evalT (σ.push eleven) = .ok zero ∧
    wrongScalar.evalT (σ.push eleven) = .ok eleven ∧
    (first.wk (Thin.drop (t := .mem A) .refl)).evalT
      (σ.push (t := .mem A) (some CompileExamples.r1)) = .ok seven ∧
    wrongRef.evalT (σ.push (t := .mem A) (some CompileExamples.r1)) = .ok four := by
  refine ⟨?_, rfl, ?_, ?_⟩
  · exact (value_fresh_eval (fresh := .val .uint) σ eleven localExpr).trans rfl
  · exact (value_fresh_eval (fresh := .mem A) σ (some CompileExamples.r1) first).trans first_source
  · with_unfolding_all rfl

private def stackValues : Evm.Out → Option (List Nat)
  | .ok m _ => m.stack.mapM (fun w => match w with | .val n => some n.val | _ => none)
  | _ => none

theorem target_wrong_index :
    stackValues (run (scalarStage.code ++ localValue.code) machine) = some [0] ∧
    stackValues (run (scalarStage.code ++ wrongScalarCode.code) machine) = some [11] ∧
    stackValues (run (refStage.code ++ a.code) machine) = some [7] ∧
    stackValues (run (refStage.code ++ wrongRefCode.code) machine) = some [4] := by
  decide +kernel

/-- Empty core fallback equality never manufactures core acceptance. The
actual memory certificate is nonempty and remains the transported certificate. -/
theorem core_refusal_preserved : valIn F first = false ∧
    valIn (F.push (.val .uint) .ok) (first.wk (Thin.drop (t := .val .uint) .refl)) = false ∧
    Evm.compileVal 0 first = [] ∧ (value_fresh (.val .uint) a).code ≠ [] := by
  refine ⟨rfl, ?_, rfl, ?_⟩
  · rw [core_val_fresh_in]
    rfl
  · have hl : (value_fresh (.val .uint) a).code.length ≠ 0 := by decide +kernel
    exact fun he => hl (congrArg List.length he)


private def cell (n : Nat) : Evm.Out → Option Nat
  | .ok m _ => match m.mem n with | .val w => some w.val | _ => none
  | _ => none

/-- Fresh cell plus ALL prior fixture locals, aliases, headers and elements. -/
theorem ordered_scalar_memory : [4,3,2,1,0,16,17,18,20,21].mapM
    (fun n => cell n (run (scalarStage.code ++ localValue.code) machine)) =
      some [11,0,16,16,20,2,7,9,1,4] := by
  obtain ⟨word, _, ht⟩ := scalar_decl_prefix []
  change run (scalarStage.code ++ localValue.code) machine = _ at ht
  rw [ht]
  dsimp only [cell, Machine.push, writeMachine]
  decide +kernel

theorem ordered_reference_memory : [4,3,2,1,0,16,17,18,20,21].mapM
    (fun n => cell n (run (refStage.code ++ a.code) machine)) =
      some [20,0,16,16,20,2,7,9,1,4] := by
  obtain ⟨word, _, ht⟩ := reference_decl_prefix []
  change run (refStage.code ++ a.code) machine = _ at ht
  rw [ht]
  dsimp only [cell, Machine.push, writeMachine]
  decide +kernel


/-- Actual successful emitted declaration precedes the reached revert. -/
theorem declaration_failures (tail : List Word) :
    run (scalarStage.code ++ ExpressionControls.checkedBad.code) {machine with stack := tail} = .revert ∧
    run (refStage.code ++ ExpressionControls.checkedBad.code) {machine with stack := tail} = .revert := by
  constructor
  · rw [run_append_ok (scalar_run tail)]
    exact (preserved_failures tail).1
  · rw [run_append_ok (reference_run tail)]
    exact (preserved_failures tail).2

theorem source_failures :
    (ExpressionControls.badTest.wk (Thin.drop (t := .val .uint) .refl)).evalT
      (σ.push eleven) = .error .revert ∧
    (ExpressionControls.badTest.wk (Thin.drop (t := .mem A) .refl)).evalT
      (σ.push (t := .mem A) (some CompileExamples.r1)) = .error .revert := by
  constructor
  · exact (value_fresh_eval (fresh := .val .uint) σ eleven ExpressionControls.badTest).trans
      (by with_unfolding_all rfl)
  · exact (value_fresh_eval (fresh := .mem A) σ (some CompileExamples.r1) ExpressionControls.badTest).trans
      (by with_unfolding_all rfl)


def recognizedScalar : CompiledVal 0 (F.push (.val .uint) .ok)
    (localExpr.wk (Thin.drop (t := .val .uint) .refl)) :=
  (compileVal 0 _ _).get (by decide +kernel)
def recognizedReference : CompiledVal 0 (F.push (.mem A) .ok)
    (first.wk (Thin.drop (t := .mem A) .refl)) :=
  (compileVal 0 _ _).get (by decide +kernel)

theorem recognizers_same_code : recognizedScalar.code = localValue.code ∧
    recognizedReference.code = a.code := ⟨rfl, rfl⟩

end Solidity.Backend.Passes.ValueContextControls
