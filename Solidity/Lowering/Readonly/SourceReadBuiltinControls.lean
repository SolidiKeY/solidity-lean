import Solidity.Lowering.Readonly.SourceExpressionEffects
import Solidity.Source.SemanticsExamples

/-! Actual read/construction/builtin helper controls. The array environment and
post-seeding checkpoint are explicit; this is not full getter admission, crypto
correctness or native/compiler correspondence. -/
namespace Solidity.Lowering.Readonly.SourceReadBuiltinControls
open Solidity.Source Solidity.Source.SemanticsExamples
open SourceHistory
namespace C
def unit : Syn .unit := .unit (.cons (.contract false "C" .none .nil
  (.cons (.stateVar (.array Solidity.Source.Examples.u256 .none) none none none false "items" .none) .nil)) .nil)
def E : Env := unit.env
def path : SPath := ⟨⟨some "C", "items"⟩, []⟩
def ty : STy := .array .storage uint none
def seed : EM E [] Unit := do
  writeLen FC path 2
  writeAt FC (path.go (.index 0)) (Solidity.Source.Val.int (t := IntTy.u256) 7 (by decide))
  writeAt FC (path.go (.index 1)) (Solidity.Source.Val.int (t := IntTy.u256) 9 (by decide))
def checkpoint := (seed.run (L0 E, St.init E)).2.2
end C
def selected (fuel : Nat) (index : Solidity.Roadmap.Word) :=
  (getterPath {FC with static := true} fuel (wordBytes index) C.ty C.path 0 : EM C.E [] _).run (L0 C.E, C.checkpoint)
def readSelected := (readAt {FC with static := true} (C.path.go (.index 1)) uint : EM C.E [] _).run (L0 C.E, (selected 4 (word 1)).2.2)
def digest := (ret32 (.fixedBytes 2 (by decide)) [7] : EM C.E [] _).run (L0 C.E, C.checkpoint)
def digestBad := (ret32 .bool [7] : EM C.E [] _).run (L0 C.E, C.checkpoint)
def fieldValues : Vals C.E.layout [.bool, uint] :=
  .cons (.bool true) (.cons (.int 7 (by decide)) .nil)
def constructed := (fieldsOf fieldValues [.bool, uint] : EM C.E [] _).run (L0 C.E, C.checkpoint)
def fieldMismatch := (fieldsOf fieldValues [uint, uint] : EM C.E [] _).run (L0 C.E, C.checkpoint)
def fieldCount := (fieldsOf fieldValues [.bool] : EM C.E [] _).run (L0 C.E, C.checkpoint)
def yes : RArgs EB [] [.bool] := .cons (.bool true) .nil
def no : RArgs EB [] [.bool] := .cons (.bool false) .nil
def reason : RArgs EB [] [.bool, .stringLit [7,9]] := .cons (.bool false) (.cons (.str [7,9]) .nil)
def numbers : RArgs EB [] [uint,uint,uint] := .cons (lit 7) (.cons (lit 5) (.cons (lit 3) .nil))
def builtin {σs : List STy} (pipeline : Solidity.Roadmap.Pipeline) (b : Builtin) (args : RArgs EB [] σs) (τ : STy) :=
  (evalBuiltin {(GB (fun _ => .answer (.success []))) with pipeline := pipeline}
    {FC with static := true} 8 b args τ).run (L0 EB, sB)

theorem observations : Solidity.Lowering.Readonly.SourceReadBuiltinControls.C.E.pathTy Solidity.Lowering.Readonly.SourceReadBuiltinControls.C.path = some Solidity.Lowering.Readonly.SourceReadBuiltinControls.C.ty ∧
 Solidity.Lowering.Readonly.SourceReadBuiltinControls.C.E.pathTy (Solidity.Lowering.Readonly.SourceReadBuiltinControls.C.path.go (.index 1)) = some Solidity.Source.SemanticsExamples.uint ∧
 (Solidity.Lowering.Readonly.SourceReadBuiltinControls.C.seed.run (Solidity.Source.L0 Solidity.Lowering.Readonly.SourceReadBuiltinControls.C.E, Solidity.Source.St.init Solidity.Lowering.Readonly.SourceReadBuiltinControls.C.E)).1 = .ok () ∧
 Solidity.Lowering.Readonly.SourceReadBuiltinControls.C.checkpoint.ex.journal.length = 3 ∧
 (Solidity.Lowering.Readonly.SourceReadBuiltinControls.selected 4 (Solidity.Source.SemanticsExamples.word 1)).1 = .ok (Solidity.Lowering.Readonly.SourceReadBuiltinControls.C.path.go (.index 1), Solidity.Source.SemanticsExamples.uint) ∧
 (Solidity.Lowering.Readonly.SourceReadBuiltinControls.selected 4 (Solidity.Source.SemanticsExamples.word 1)).2.2.ex = Solidity.Lowering.Readonly.SourceReadBuiltinControls.C.checkpoint.ex ∧
 Solidity.Lowering.Readonly.SourceReadBuiltinControls.readSelected.1 = .ok (.int 9 (by decide)) ∧
 (Solidity.Lowering.Readonly.SourceReadBuiltinControls.selected 4 (Solidity.Source.SemanticsExamples.word 2)).1 = .error (.revert (Solidity.Source.panicData .index)) ∧
 (Solidity.Lowering.Readonly.SourceReadBuiltinControls.selected 0 (Solidity.Source.SemanticsExamples.word 1)).1 = .ok (Solidity.Lowering.Readonly.SourceReadBuiltinControls.C.path.go (.index 1), Solidity.Source.SemanticsExamples.uint) ∧
 Solidity.Lowering.Readonly.SourceReadBuiltinControls.digest.1 = .ok (.val (.fixedBytes [7,0] (by rfl))) ∧
 Solidity.Lowering.Readonly.SourceReadBuiltinControls.digestBad.1 = .error (.stuck "digest type") ∧
 Solidity.Lowering.Readonly.SourceReadBuiltinControls.constructed.1 = .ok (.cons (.val (.bool true)) (.cons (.val (.int 7 (by decide))) .nil)) ∧
 Solidity.Lowering.Readonly.SourceReadBuiltinControls.fieldMismatch.1 = .error (.stuck "member type") ∧
 Solidity.Lowering.Readonly.SourceReadBuiltinControls.fieldCount.1 = .error (.stuck "member count") ∧
 Solidity.Lowering.Readonly.SourceReadBuiltinControls.constructed.2.2.ex = Solidity.Lowering.Readonly.SourceReadBuiltinControls.C.checkpoint.ex ∧
 (Solidity.Lowering.Readonly.SourceReadBuiltinControls.builtin .legacy .assert Solidity.Lowering.Readonly.SourceReadBuiltinControls.yes (.tuple [])).1 = .ok (.tuple .nil) ∧
 (Solidity.Lowering.Readonly.SourceReadBuiltinControls.builtin .viaIR .assert Solidity.Lowering.Readonly.SourceReadBuiltinControls.yes (.tuple [])).1 = .ok (.tuple .nil) ∧
 (Solidity.Lowering.Readonly.SourceReadBuiltinControls.builtin .legacy .assert Solidity.Lowering.Readonly.SourceReadBuiltinControls.no (.tuple [])).1 = .error (.revert (Solidity.Source.panicData .assert)) ∧
 (Solidity.Lowering.Readonly.SourceReadBuiltinControls.builtin .viaIR .require Solidity.Lowering.Readonly.SourceReadBuiltinControls.reason (.tuple [])).1 = .error (.revert (Solidity.Source.errorData [7,9])) ∧
 (Solidity.Lowering.Readonly.SourceReadBuiltinControls.builtin .legacy .gasleft (.nil : Solidity.Source.RArgs Solidity.Source.SemanticsExamples.EB [] []) Solidity.Source.SemanticsExamples.uint).1 = .error (.stuck "builtin") ∧
 (Solidity.Lowering.Readonly.SourceReadBuiltinControls.builtin .legacy .assert Solidity.Lowering.Readonly.SourceReadBuiltinControls.yes .bool).1 = .error (.stuck "builtin result") ∧
 (Solidity.Lowering.Readonly.SourceReadBuiltinControls.builtin .legacy .assert (.nil : Solidity.Source.RArgs Solidity.Source.SemanticsExamples.EB [] []) (.tuple [])).1 = .error (.stuck "builtin") ∧
 (Solidity.Lowering.Readonly.SourceReadBuiltinControls.builtin .legacy .addmod Solidity.Lowering.Readonly.SourceReadBuiltinControls.numbers Solidity.Source.SemanticsExamples.uint).1 = .ok (.val (.int 0 (by decide))) ∧
 (Solidity.Lowering.Readonly.SourceReadBuiltinControls.builtin .viaIR .addmod Solidity.Lowering.Readonly.SourceReadBuiltinControls.numbers Solidity.Source.SemanticsExamples.uint).1 = .ok (.val (.int 0 (by decide))) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rfl

theorem expression_client : ∀ {E : Solidity.Source.Env} (G : Solidity.Source.Glob E) (F : Solidity.Source.Fr) {Γ : Solidity.Source.RCtx}, Solidity.Lowering.Readonly.SourceHistory.Effect F.static (Solidity.Source.evalE G F 1 (Solidity.Source.RExpr.bool true : Solidity.Source.RExpr E Γ .bool)) := by
  intro E G F Γ
  exact Solidity.Lowering.Readonly.SourceHistory.evalE_succ G F 0
    (Solidity.Lowering.Readonly.SourceHistory.at_zero G) (.bool true)

theorem gas_refused : (Solidity.Lowering.Readonly.SourceReadBuiltinControls.builtin .legacy .gasleft
 (Solidity.Source.RArgs.nil : Solidity.Source.RArgs Solidity.Source.SemanticsExamples.EB [] [])
 Solidity.Source.SemanticsExamples.uint).1 ≠ .ok (.val (.int 0 (by decide))) := by
  rw [Solidity.Lowering.Readonly.SourceReadBuiltinControls.observations.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1]
  intro impossible
  cases impossible

end Solidity.Lowering.Readonly.SourceReadBuiltinControls
