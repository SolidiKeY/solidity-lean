import Solidity.Backend.StructuredFlow.SourceDispatch
import Solidity.Backend.StructuredFlow.AssignmentBlocksCompiler
import Solidity.Backend.StructuredFlow.ConditionalSourceCompiler
import Solidity.Backend.StructuredFlow.ConditionalSequenceCompiler
import Solidity.Backend.StructuredFlow.ConditionalReturnCompiler
import Solidity.Backend.StructuredFlow.ConditionalContinuationCompiler
import Solidity.Backend.StructuredFlow.ReturnTailCompiler
import Solidity.Backend.StructuredFlow.ReturnPairCompiler
import Solidity.Backend.StructuredFlow.WhileBreakCompiler
import Solidity.Backend.StructuredFlow.WhileContinueCompiler
import Solidity.Backend.StructuredFlow.WhileReturnCompiler
import Solidity.Backend.StructuredFlow.ForBreakCompiler
import Solidity.Backend.StructuredFlow.ForContinueCompiler
import Solidity.Backend.StructuredFlow.ForReturnCompiler
import Solidity.Backend.StructuredFlow.DoWhileBreakCompiler
import Solidity.Backend.StructuredFlow.DoWhileContinueCompiler
import Solidity.Backend.StructuredFlow.DoWhileReturnCompiler

/-!
# Operational correctness for the Source dispatcher

Guards upgrading syntax extraction into a Source-adequacy claim without an
operational proof. Signature reuse retains each existing compiler theorem's
entire conclusion, including exact Source fuel/outcome, reached map, globals,
return capture and native execution facts. No Source evaluator is introduced.
-/
namespace Solidity.Backend.StructuredFlow.SourceDispatch
open Solidity.Lowering.V07 Solidity.Lowering.G19

theorem contextMap_boolSlot {srcΓ : Source.RCtx} {Γ : Ctx} (m : ContextMap srcΓ Γ)
    (i : Source.Idx srcΓ .bool) (typed : (m.slot i).1 = .val .bool) :
    m.slot i = ⟨.val .bool,AssignmentReturnFlag.boolSlot m i typed⟩ := by
  have castSlot (slot : (u : LTy) × Idx Γ u) (h : slot.1 = .val .bool) :
      slot = ⟨.val .bool,Eq.mp (congrArg (fun u => Idx Γ u) h) slot.2⟩ := by
    cases slot with
    | mk u index =>
      cases h
      rfl
  exact castSlot (m.slot i) typed

/-- A proved proposition, used to reuse an existing theorem's exact signature.
The proof is constructed here, never supplied as a dispatch admission premise. -/
structure OperationalFact where
  statement : Prop
  proof : statement

private def factOf {P : Prop} (proof : P) : OperationalFact := ⟨P,proof⟩

private def bindEmission (actual expected : List Evm.Instr) (same : actual = expected)
    (fact : OperationalFact) : OperationalFact :=
  ⟨actual = expected ∧ fact.statement,⟨same,fact.proof⟩⟩

private def allFacts {α : Sort u} (facts : α → OperationalFact) : OperationalFact :=
  ⟨∀ x, (facts x).statement, fun x => (facts x).proof⟩

/-- Native configuration and input state are fixed before selecting an old
signature. Only that signature's original remaining premises are quantified. -/
def operationalFact {E : Source.Env} {M : Bool} {R : List Source.STy}
    {k : Source.SCtx} {srcΓ srcΔ : Source.RCtx} {s : Source.RStmt E R M k srcΓ srcΔ}
    {C : Contract} {Γ : Ctx}
    (G : Source.Glob E) (F : Source.Fr) (fuel nps : Nat) (ph : Option (Source.Ph E))
    (source : Source.EMState E srcΓ) (target : State C Γ) (m : ContextMap srcΓ Γ)
    (Rel : (τ : Source.STy) → (u : LTy) → Source.Val E.layout τ → u.TDenote C target.H → Prop)
    (aligned : m.Related Rel source.1 target.env)
    (base L : Nat) (frame : Evm.Frag Γ) (machine : Evm.Machine)
    (entry : Evm.Sim C L base frame target machine)
    (plan : Plan E M s) (mapped : Mapping m plan)
    (outFrame : Evm.Frag (program (C := C) m plan mapped).1)
    (checked : Evm.inFragP frame (program (C := C) m plan mapped).2 = some outFrame) :
    OperationalFact := by
  let returns := R
  let scope := k
  let nativeCode := program (C := C) m plan mapped
  cases plan <;> dsimp [Mapping,program] at mapped outFrame checked
  case blocks steps =>
    exact bindEmission (Evm.compileProg base nativeCode.2)
      (AssignmentBlocksCompiler.emit (C := C) base mapped.index steps) rfl (allFacts (fun (capacity : L + Evm.Prog.pushes nativeCode.2 ≤ Evm.Lmax) =>
        factOf (AssignmentBlocksCompiler.correct (returns := returns) (M := M) (k := scope) (L := L) (base := base) G F fuel nps ph steps source target m Rel mapped.index mapped.exact aligned entry checked capacity)))
  case conditional ci ca i a j b =>
    exact bindEmission (Evm.compileProg base nativeCode.2)
      (ConditionalSourceCompiler.emit (C := C) base mapped.condition.dest.index mapped.condition.donor.index mapped.left.dest.index mapped.left.donor.index mapped.rightDest.index mapped.rightDonor.index) rfl (allFacts (fun (boolReflect : ∀ (v : Source.Val E.layout .bool) (b : Bool),
      Rel .bool (.val .bool) v b → v = .bool b) =>
      allFacts (fun (capacity : L + Evm.Prog.pushes nativeCode.2 ≤ Evm.Lmax) =>
        factOf (ConditionalSourceCompiler.correct (returns := returns) (M := M) (k := scope) (L := L) (base := base) G F fuel nps ph source target m Rel aligned boolReflect ci ca i a j b mapped.condition.dest.index mapped.condition.donor.index mapped.left.dest.index mapped.left.donor.index mapped.rightDest.index mapped.rightDonor.index mapped.condition.dest.exact mapped.condition.donor.exact mapped.left.dest.exact mapped.left.donor.exact mapped.rightDest.exact mapped.rightDonor.exact entry checked capacity))))
  case returning ci ca i a j b =>
    exact bindEmission (Evm.compileProg base nativeCode.2)
      (ConditionalReturnCompiler.emit (C := C) base mapped.condition.dest.index mapped.condition.donor.index mapped.left.dest.index mapped.left.donor.index mapped.rightDest.index mapped.rightDonor.index) rfl (allFacts (fun (boolReflect : ∀ (v : Source.Val E.layout .bool) (b : Bool),
      Rel .bool (.val .bool) v b → v = .bool b) =>
      allFacts (fun (capacity : L + Evm.Prog.pushes nativeCode.2 ≤ Evm.Lmax) =>
        factOf (ConditionalReturnCompiler.correct (M := M) (k := scope) (L := L) (base := base) G F fuel nps ph source target m Rel aligned boolReflect ci ca i a j b mapped.condition.dest.index mapped.condition.donor.index mapped.left.dest.index mapped.left.donor.index mapped.rightDest.index mapped.rightDonor.index mapped.condition.dest.exact mapped.condition.donor.exact mapped.left.dest.exact mapped.left.donor.exact mapped.rightDest.exact mapped.rightDonor.exact entry checked capacity))))
  case continuation ci ca i a j b tail =>
    exact bindEmission (Evm.compileProg base nativeCode.2)
      (ConditionalContinuationCompiler.emit (C := C) base mapped.condition.dest.index mapped.condition.donor.index mapped.left.dest.index mapped.left.donor.index mapped.rightDest.index mapped.rightDonor.index .nil) rfl (allFacts (fun (boolReflect : ∀ (v : Source.Val E.layout .bool) (b : Bool),
      Rel .bool (.val .bool) v b → v = .bool b) =>
      allFacts (fun (capacity : L + Evm.Prog.pushes nativeCode.2 ≤ Evm.Lmax) =>
        factOf (ConditionalContinuationCompiler.correct (M := M) (k := scope) (L := L) (base := base) G F fuel nps ph source target m Rel aligned boolReflect ci ca i a j b mapped.condition.dest.index mapped.condition.donor.index mapped.left.dest.index mapped.left.donor.index mapped.rightDest.index mapped.rightDonor.index mapped.condition.dest.exact mapped.condition.donor.exact mapped.left.dest.exact mapped.left.donor.exact mapped.rightDest.exact mapped.rightDonor.exact tail .nil entry checked capacity))))
  case sequence ci ca i a j b dest donor =>
    exact bindEmission (Evm.compileProg base nativeCode.2)
      (ConditionalSequenceCompiler.emit (C := C) base mapped.1.condition.dest.index mapped.1.condition.donor.index mapped.1.left.dest.index mapped.1.left.donor.index mapped.1.rightDest.index mapped.1.rightDonor.index mapped.2.dest.index mapped.2.donor.index) rfl (allFacts (fun (boolReflect : ∀ (v : Source.Val E.layout .bool) (b : Bool),
      Rel .bool (.val .bool) v b → v = .bool b) =>
      allFacts (fun (capacity : L + Evm.Prog.pushes nativeCode.2 ≤ Evm.Lmax) =>
        factOf (ConditionalSequenceCompiler.correct (returns := returns) (M := M) (k := scope) (L := L) (base := base) G F fuel nps ph source target m Rel aligned boolReflect ci ca i a j b dest donor mapped.1.condition.dest.index mapped.1.condition.donor.index mapped.1.left.dest.index mapped.1.left.donor.index mapped.1.rightDest.index mapped.1.rightDonor.index mapped.2.dest.index mapped.2.donor.index mapped.1.condition.dest.exact mapped.1.condition.donor.exact mapped.1.left.dest.exact mapped.1.left.donor.exact mapped.1.rightDest.exact mapped.1.rightDonor.exact mapped.2.dest.exact mapped.2.donor.exact entry checked capacity))))
  case returnTail ci ca dest donor =>
    exact bindEmission (Evm.compileProg base nativeCode.2)
      (ReturnTailCompiler.emit (C := C) base mapped.1.dest.index mapped.1.donor.index mapped.2.dest.index mapped.2.donor.index) rfl (allFacts (fun (boolReflect : ∀ (v : Source.Val E.layout .bool) (b : Bool),
      Rel .bool (.val .bool) v b → v = .bool b) =>
      allFacts (fun (capacity : L + Evm.Prog.pushes nativeCode.2 ≤ Evm.Lmax) =>
        factOf (ReturnTailCompiler.correct (M := M) (k := scope) (L := L) (base := base) G F fuel nps ph source target m Rel aligned boolReflect ci ca dest donor mapped.1.dest.index mapped.1.donor.index mapped.2.dest.index mapped.2.donor.index mapped.1.dest.exact mapped.1.donor.exact mapped.2.dest.exact mapped.2.donor.exact entry checked capacity))))
  case returnPair ci ca i a dest donor =>
    exact bindEmission (Evm.compileProg base nativeCode.2)
      (ReturnPairCompiler.emit (C := C) base mapped.1.dest.index mapped.1.donor.index mapped.2.1.dest.index mapped.2.1.donor.index mapped.2.2.dest.index mapped.2.2.donor.index) rfl (allFacts (fun (boolReflect : ∀ (v : Source.Val E.layout .bool) (b : Bool),
      Rel .bool (.val .bool) v b → v = .bool b) =>
      allFacts (fun (capacity : L + Evm.Prog.pushes nativeCode.2 ≤ Evm.Lmax) =>
        factOf (ReturnPairCompiler.correct (M := M) (k := scope) (L := L) (base := base) G F fuel nps ph source target m Rel aligned boolReflect ci ca i a dest donor mapped.1.dest.index mapped.1.donor.index mapped.2.1.dest.index mapped.2.1.donor.index mapped.2.2.dest.index mapped.2.2.donor.index mapped.1.dest.exact mapped.1.donor.exact mapped.2.1.dest.exact mapped.2.1.donor.exact mapped.2.2.dest.exact mapped.2.2.donor.exact entry checked capacity))))
  case whileBreak i a =>
    exact bindEmission (Evm.compileProg base nativeCode.2)
      (ForBreakCompiler.emit (C := C) base m i a mapped.dest.type_eq mapped.donor.type_eq) rfl (allFacts (fun (boolReflect : ∀ (v : Source.Val E.layout .bool) (b : Bool),
      Rel .bool (.val .bool) v b → v = .bool b) =>
      factOf (WhileBreakCompiler.correct (returns := returns) (M := M) (l := scope.loop) (u := scope.unchecked) (L := L) (base := base) G F fuel nps ph source target m Rel aligned boolReflect i a mapped.dest.type_eq mapped.donor.type_eq (contextMap_boolSlot m i mapped.dest.type_eq) (contextMap_boolSlot m a mapped.donor.type_eq) entry)))
  case whileContinue i a tail =>
    exact bindEmission (Evm.compileProg base nativeCode.2)
      (WhileContinueCompiler.emit (C := C) base m i a mapped.dest.type_eq mapped.donor.type_eq) rfl (allFacts (fun (boolReflect : ∀ (v : Source.Val E.layout .bool) (b : Bool),
      Rel .bool (.val .bool) v b → v = .bool b) =>
      allFacts (fun (falseValue : Rel .bool (.val .bool) (.bool false) false) =>
        allFacts (fun (capacity : L + Evm.Prog.pushes nativeCode.2 ≤ Evm.Lmax) =>
        factOf (WhileContinueCompiler.correct (returns := returns) (M := M) (l := scope.loop) (u := scope.unchecked) (L := L) (base := base) G F fuel nps ph source target m Rel aligned boolReflect falseValue i a mapped.dest.type_eq mapped.donor.type_eq (contextMap_boolSlot m i mapped.dest.type_eq) (contextMap_boolSlot m a mapped.donor.type_eq) tail entry checked capacity)))))
  case whileReturn i a =>
    exact bindEmission (Evm.compileProg base nativeCode.2)
      (MappedCondition.emit base m i a mapped.dest.type_eq mapped.donor.type_eq) rfl (allFacts (fun (boolReflect : ∀ (v : Source.Val E.layout .bool) (b : Bool),
      Rel .bool (.val .bool) v b → v = .bool b) =>
      factOf (WhileReturnCompiler.correct (M := M) (l := scope.loop) (u := scope.unchecked) (L := L) (base := base) G F fuel nps ph source target m Rel aligned boolReflect i a mapped.dest.type_eq mapped.donor.type_eq (contextMap_boolSlot m i mapped.dest.type_eq) (contextMap_boolSlot m a mapped.donor.type_eq) entry)))
  case forBreak i a post =>
    exact bindEmission (Evm.compileProg base nativeCode.2)
      (ForBreakCompiler.emit (C := C) base m i a mapped.dest.type_eq mapped.donor.type_eq) rfl (allFacts (fun (boolReflect : ∀ (v : Source.Val E.layout .bool) (b : Bool),
      Rel .bool (.val .bool) v b → v = .bool b) =>
      factOf (ForBreakCompiler.correct (returns := returns) (M := M) (l := scope.loop) (u := scope.unchecked) (L := L) (base := base) G F fuel nps ph source target m Rel aligned boolReflect i a mapped.dest.type_eq mapped.donor.type_eq (contextMap_boolSlot m i mapped.dest.type_eq) (contextMap_boolSlot m a mapped.donor.type_eq) post entry)))
  case forContinue i a tail =>
    exact bindEmission (Evm.compileProg base nativeCode.2)
      (ForContinueCompiler.emit (C := C) base m i a mapped.dest.type_eq mapped.donor.type_eq) rfl (allFacts (fun (boolReflect : ∀ (v : Source.Val E.layout .bool) (b : Bool),
      Rel .bool (.val .bool) v b → v = .bool b) =>
      allFacts (fun (falseValue : Rel .bool (.val .bool) (.bool false) false) =>
        allFacts (fun (capacity : L + Evm.Prog.pushes nativeCode.2 ≤ Evm.Lmax) =>
        factOf (ForContinueCompiler.correct (returns := returns) (M := M) (l := scope.loop) (u := scope.unchecked) (L := L) (base := base) G F fuel nps ph source target m Rel aligned boolReflect falseValue i a mapped.dest.type_eq mapped.donor.type_eq (contextMap_boolSlot m i mapped.dest.type_eq) (contextMap_boolSlot m a mapped.donor.type_eq) tail entry checked capacity)))))
  case forReturn i a post =>
    exact bindEmission (Evm.compileProg base nativeCode.2)
      (ForReturnCompiler.emit (C := C) base m i a mapped.dest.type_eq mapped.donor.type_eq) rfl (allFacts (fun (boolReflect : ∀ (v : Source.Val E.layout .bool) (b : Bool),
      Rel .bool (.val .bool) v b → v = .bool b) =>
      factOf (ForReturnCompiler.correct (M := M) (l := scope.loop) (u := scope.unchecked) (L := L) (base := base) G F fuel nps ph source target m Rel aligned boolReflect i a mapped.dest.type_eq mapped.donor.type_eq (contextMap_boolSlot m i mapped.dest.type_eq) (contextMap_boolSlot m a mapped.donor.type_eq) post entry)))
  case doBreak i a condition =>
    exact bindEmission (Evm.compileProg base nativeCode.2)
      (ForBreakCompiler.emit (C := C) base m i a mapped.dest.type_eq mapped.donor.type_eq) rfl (allFacts (fun (boolReflect : ∀ (v : Source.Val E.layout .bool) (b : Bool),
      Rel .bool (.val .bool) v b → v = .bool b) =>
      factOf (DoWhileBreakCompiler.correct (returns := returns) (M := M) (l := scope.loop) (u := scope.unchecked) (L := L) (base := base) G F fuel nps ph source target m Rel aligned boolReflect i a mapped.dest.type_eq mapped.donor.type_eq (contextMap_boolSlot m i mapped.dest.type_eq) (contextMap_boolSlot m a mapped.donor.type_eq) condition entry)))
  case doContinue i a tail =>
    exact bindEmission (Evm.compileProg base nativeCode.2)
      (ForBreakCompiler.emit (C := C) base m i a mapped.dest.type_eq mapped.donor.type_eq) rfl (allFacts (fun (boolReflect : ∀ (v : Source.Val E.layout .bool) (b : Bool),
      Rel .bool (.val .bool) v b → v = .bool b) =>
      factOf (DoWhileContinueCompiler.correct (returns := returns) (M := M) (l := scope.loop) (u := scope.unchecked) (L := L) (base := base) G F fuel nps ph source target m Rel aligned boolReflect i a mapped.dest.type_eq mapped.donor.type_eq (contextMap_boolSlot m i mapped.dest.type_eq) (contextMap_boolSlot m a mapped.donor.type_eq) tail entry)))
  case doReturn i a condition =>
    exact bindEmission (Evm.compileProg base nativeCode.2)
      (DoWhileReturnCompiler.emit (C := C) base m i a mapped.dest.type_eq mapped.donor.type_eq) rfl (allFacts (fun (boolReflect : ∀ (v : Source.Val E.layout .bool) (b : Bool),
      Rel .bool (.val .bool) v b → v = .bool b) =>
      allFacts (fun (capacity : L + Evm.Prog.pushes nativeCode.2 ≤ Evm.Lmax) =>
        factOf (DoWhileReturnCompiler.correct (M := M) (l := scope.loop) (u := scope.unchecked) (L := L) (base := base) G F fuel nps ph source target m Rel aligned boolReflect i a mapped.dest.type_eq mapped.donor.type_eq (contextMap_boolSlot m i mapped.dest.type_eq) (contextMap_boolSlot m a mapped.donor.type_eq) condition entry checked capacity))))

/-- The actual accepted code and the complete original operational law at
that same source, target, map, base, input frame and machine configuration. -/
theorem Compiled.correct {E : Source.Env} {M : Bool} {R : List Source.STy}
    {k : Source.SCtx} {srcΓ srcΔ : Source.RCtx} {s : Source.RStmt E R M k srcΓ srcΔ}
    {C : Contract} {Γ : Ctx} {m : ContextMap srcΓ Γ} {base : Nat} {frame : Evm.Frag Γ}
    (compiled : Compiled (C := C) s m base frame)
    (G : Source.Glob E) (F : Source.Fr) (fuel nps : Nat) (ph : Option (Source.Ph E))
    (source : Source.EMState E srcΓ) (target : State C Γ)
    (Rel : (τ : Source.STy) → (u : LTy) → Source.Val E.layout τ → u.TDenote C target.H → Prop)
    (aligned : m.Related Rel source.1 target.env)
    (L : Nat) (machine : Evm.Machine) (entry : Evm.Sim C L base frame target machine) :
    compiled.result.code = Evm.compileProg base (program (C := C) m compiled.plan compiled.mapping).2 ∧
    (operationalFact G F fuel nps ph source target m Rel aligned base L frame machine entry
      compiled.plan compiled.mapping compiled.outFrame compiled.admitted).statement :=
  ⟨compiled.code_exact,(operationalFact G F fuel nps ph source target m Rel aligned base L frame machine entry
      compiled.plan compiled.mapping compiled.outFrame compiled.admitted).proof⟩

end Solidity.Backend.StructuredFlow.SourceDispatch
