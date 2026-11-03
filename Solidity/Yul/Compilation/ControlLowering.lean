import Solidity.Yul.Compilation.PureLowering
import Solidity.Backend.Control

/-! Emit existing structured Backend.Block control. Local slices are proved
against Scalar.run; assembler placement is existing Backend.Control. Actual
fetched JUMP/JUMPI execution and source loop horizons remain joint obligations. -/
namespace Solidity.Yul.Compilation
open Backend Scalar

def lowerBranch {n : Nat} {condition : Vector Word n → Word}
    {yes no : Vector Word n → Vector Word n}
    (c : LoweredExpr n condition) (a : LoweredStmt n yes) (b : LoweredStmt n no)
    (depth : Nat) : Option Backend.Block :=
  (c.code depth).bind (fun cc => (a.code depth).bind (fun aa =>
    (b.code depth).map (fun bb => .ite cc (.code aa) (.code bb))))

theorem lowerBranch_parts {n : Nat} {condition : Vector Word n → Word}
    {yes no : Vector Word n → Vector Word n}
    (c : LoweredExpr n condition) (a : LoweredStmt n yes) (b : LoweredStmt n no)
    (depth : Nat) (target : Backend.Block) (selected : lowerBranch c a b depth = some target) :
    ∃ cc aa bb, c.code depth = some cc ∧ a.code depth = some aa ∧ b.code depth = some bb ∧
      target = .ite cc (.code aa) (.code bb) := by
  unfold lowerBranch at selected
  cases hc : c.code depth with
  | none => simp only [hc, Option.bind_none] at selected; cases selected
  | some cc =>
    cases ha : a.code depth with
    | none => simp only [hc, ha, Option.bind_some, Option.bind_none] at selected; cases selected
    | some aa =>
      cases hb : b.code depth with
      | none => simp only [hc, ha, hb, Option.bind_some, Option.map_none] at selected; cases selected
      | some bb =>
        simp only [hc, ha, hb, Option.bind_some, Option.map_some] at selected
        cases selected
        exact ⟨cc, aa, bb, rfl, rfl, rfl, rfl⟩

/-- Concrete accepted condition/arm executions; no conditional-driver law is
assumed or claimed. The value word must be consumed by the target driver. -/
theorem lowerBranch_slices {n : Nat} {condition : Vector Word n → Word}
    {yes no : Vector Word n → Vector Word n}
    (c : LoweredExpr n condition) (a : LoweredStmt n yes) (b : LoweredStmt n no)
    (depth : Nat) (target : Backend.Block) (selected : lowerBranch c a b depth = some target)
    (locals : Vector Word n) (newer : Vector Word depth) (tail : Stack) :
    ∃ cc aa bb, target = .ite cc (.code aa) (.code bb) ∧
      run cc (newer.toList ++ (locals.toList ++ tail)) =
        some (condition locals :: (newer.toList ++ (locals.toList ++ tail))) ∧
      run (if condition locals = 0 then bb else aa) (newer.toList ++ (locals.toList ++ tail)) =
        some (newer.toList ++ ((if condition locals = 0 then no locals else yes locals).toList ++ tail)) := by
  obtain ⟨cc, aa, bb, hc, ha, hb, ht⟩ := lowerBranch_parts c a b depth target selected
  refine ⟨cc, aa, bb, ht, c.correct depth cc hc locals newer tail, ?_⟩
  by_cases h : condition locals = 0
  · simp only [h, ite_true]; exact b.correct depth bb hb locals newer tail
  · simp only [h, ite_false]; exact a.correct depth aa ha locals newer tail

def lowerWhile {n : Nat} {condition : Vector Word n → Word}
    {update : Vector Word n → Vector Word n}
    (c : LoweredExpr n condition) (body : LoweredStmt n update) (depth : Nat) :
    Option Backend.Block :=
  (c.code depth).bind (fun cc => (body.code depth).map (fun bb => .loop cc (.code bb)))

/-- Label/layout safety for accepted structured emission reuses the actual
assembler theorem. This is not the missing execution/refinement theorem. -/
theorem emittedControl_assembles (target : Backend.Block) (labelBase byteBase : Nat)
    (fits : ∀ l ∈ refs (target.expand labelBase).1,
      byteBase + tagOffset (fun _ => (32 : Fin 33)) (target.expand labelBase).1 l < 256 ^ 32) :
    (assemble byteBase (fun x : Empty => nomatch x) (target.expand labelBase).1).isSome :=
  target.expand_assemble_isSome labelBase byteBase _ fits

#print axioms lowerBranch_parts
#print axioms lowerBranch_slices
#print axioms emittedControl_assembles
end Solidity.Yul.Compilation
