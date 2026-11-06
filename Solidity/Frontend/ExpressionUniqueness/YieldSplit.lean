import Solidity.Frontend.ExpressionUniqueness.YieldShape

/-!
# Invert actual printer executions into successful child executions

These are state-printer inversion facts. They recover existing children and
independently consumed layout states from the parent's actual success, without
assuming a token root cut, parser completeness or uniqueness.
-/

namespace Solidity.Frontend.ExpressionUniqueness

open Solidity.Source Solidity.Frontend.Checked

theorem bind_success_split {α β : Type} (p : Pr α) (k : α → Pr β)
    (initial rest : List Choice) (result : β) (h : (p >>= k) initial = some (result, rest)) :
    ∃ value middle, p initial = some (value, middle) ∧ k value middle = some (result, rest) := by
  change (p initial).bind (fun r => k r.1 r.2) = some (result, rest) at h
  cases hp : p initial with
  | none => rw [hp] at h; cases h
  | some pair =>
    rcases pair with ⟨value, middle⟩
    refine ⟨value, middle, rfl, ?_⟩
    simpa only [hp, Option.bind_some] using h

theorem pure_success_split {α : Type} (value result : α) (initial rest : List Choice)
    (h : (pure value : Pr α) initial = some (result, rest)) : result = value ∧ rest = initial := by
  change some (value, initial) = some (result, rest) at h
  exact ⟨(Prod.mk.inj (Option.some.inj h)).1.symm, (Prod.mk.inj (Option.some.inj h)).2.symm⟩

theorem pair_pure_success_split {α β γ : Type} (p : Pr α) (q : Pr β) (render : α → β → γ)
    (initial rest : List Choice) (result : γ)
    (h : (do let x ← p; let y ← q; pure (render x y)) initial = some (result, rest)) :
    ∃ x y middle, p initial = some (x, middle) ∧ q middle = some (y, rest) ∧ result = render x y := by
  obtain ⟨x, middle, hp, remainder⟩ := bind_success_split p
    (fun x => do let y ← q; pure (render x y)) initial rest result h
  obtain ⟨y, final, hq, hpure⟩ := bind_success_split q
    (fun y => pure (render x y)) middle rest result remainder
  obtain ⟨value, states⟩ := pure_success_split (render x y) result final rest hpure
  subst final
  exact ⟨x, y, middle, hp, hq, value⟩

theorem one_pure_success_split {α β : Type} (p : Pr α) (render : α → β)
    (initial rest : List Choice) (result : β)
    (h : (do let x ← p; pure (render x)) initial = some (result, rest)) :
    ∃ x, p initial = some (x, rest) ∧ result = render x := by
  obtain ⟨x, middle, hp, hpure⟩ := bind_success_split p (fun x => pure (render x))
    initial rest result h
  obtain ⟨value, states⟩ := pure_success_split (render x) result middle rest hpure
  subst middle
  exact ⟨x, hp, value⟩

theorem exp_yield_parts (a b : Syn .expr) (initial rest : List Choice)
    (items : List (List Tok)) (h : (Syn.exp a b).yield initial = some (items, rest)) :
    ∃ xs ys middle, a.yield initial = some (xs, middle) ∧ b.yield middle = some (ys, rest) ∧
      items = [xs.flatten ++ pu .exp ++ ys.flatten] :=
  pair_pure_success_split a.yield b.yield (fun xs ys => [xs.flatten ++ pu .exp ++ ys.flatten])
    initial rest items h

theorem mul_yield_parts (op : MulOp) (a b : Syn .expr) (initial rest : List Choice)
    (items : List (List Tok)) (h : (Syn.mulDivMod op a b).yield initial = some (items, rest)) :
    ∃ xs ys middle, a.yield initial = some (xs, middle) ∧ b.yield middle = some (ys, rest) ∧
      items = [xs.flatten ++ pu op.punct ++ ys.flatten] :=
  pair_pure_success_split a.yield b.yield (fun xs ys => [xs.flatten ++ pu op.punct ++ ys.flatten])
    initial rest items h

theorem add_yield_parts (op : AddOp) (a b : Syn .expr) (initial rest : List Choice)
    (items : List (List Tok)) (h : (Syn.addSub op a b).yield initial = some (items, rest)) :
    ∃ xs ys middle, a.yield initial = some (xs, middle) ∧ b.yield middle = some (ys, rest) ∧
      items = [xs.flatten ++ pu op.punct ++ ys.flatten] :=
  pair_pure_success_split a.yield b.yield (fun xs ys => [xs.flatten ++ pu op.punct ++ ys.flatten])
    initial rest items h

theorem shift_yield_parts (op : ShiftOp) (a b : Syn .expr) (initial rest : List Choice)
    (items : List (List Tok)) (h : (Syn.shift op a b).yield initial = some (items, rest)) :
    ∃ xs ys middle, a.yield initial = some (xs, middle) ∧ b.yield middle = some (ys, rest) ∧
      items = [xs.flatten ++ pu op.punct ++ ys.flatten] :=
  pair_pure_success_split a.yield b.yield (fun xs ys => [xs.flatten ++ pu op.punct ++ ys.flatten])
    initial rest items h

theorem order_yield_parts (op : OrderOp) (a b : Syn .expr) (initial rest : List Choice)
    (items : List (List Tok)) (h : (Syn.order op a b).yield initial = some (items, rest)) :
    ∃ xs ys middle, a.yield initial = some (xs, middle) ∧ b.yield middle = some (ys, rest) ∧
      items = [xs.flatten ++ pu op.punct ++ ys.flatten] :=
  pair_pure_success_split a.yield b.yield (fun xs ys => [xs.flatten ++ pu op.punct ++ ys.flatten])
    initial rest items h

theorem equality_yield_parts (op : EqOp) (a b : Syn .expr) (initial rest : List Choice)
    (items : List (List Tok)) (h : (Syn.equality op a b).yield initial = some (items, rest)) :
    ∃ xs ys middle, a.yield initial = some (xs, middle) ∧ b.yield middle = some (ys, rest) ∧
      items = [xs.flatten ++ pu op.punct ++ ys.flatten] :=
  pair_pure_success_split a.yield b.yield (fun xs ys => [xs.flatten ++ pu op.punct ++ ys.flatten])
    initial rest items h

theorem bitAnd_yield_parts (a b : Syn .expr) (initial rest : List Choice)
    (items : List (List Tok)) (h : (Syn.bitAnd a b).yield initial = some (items, rest)) :
    ∃ xs ys middle, a.yield initial = some (xs, middle) ∧ b.yield middle = some (ys, rest) ∧
      items = [xs.flatten ++ pu .bitAnd ++ ys.flatten] :=
  pair_pure_success_split a.yield b.yield (fun xs ys => [xs.flatten ++ pu .bitAnd ++ ys.flatten])
    initial rest items h

theorem bitXor_yield_parts (a b : Syn .expr) (initial rest : List Choice)
    (items : List (List Tok)) (h : (Syn.bitXor a b).yield initial = some (items, rest)) :
    ∃ xs ys middle, a.yield initial = some (xs, middle) ∧ b.yield middle = some (ys, rest) ∧
      items = [xs.flatten ++ pu .bitXor ++ ys.flatten] :=
  pair_pure_success_split a.yield b.yield (fun xs ys => [xs.flatten ++ pu .bitXor ++ ys.flatten])
    initial rest items h

theorem bitOr_yield_parts (a b : Syn .expr) (initial rest : List Choice)
    (items : List (List Tok)) (h : (Syn.bitOr a b).yield initial = some (items, rest)) :
    ∃ xs ys middle, a.yield initial = some (xs, middle) ∧ b.yield middle = some (ys, rest) ∧
      items = [xs.flatten ++ pu .bitOr ++ ys.flatten] :=
  pair_pure_success_split a.yield b.yield (fun xs ys => [xs.flatten ++ pu .bitOr ++ ys.flatten])
    initial rest items h

theorem and_yield_parts (a b : Syn .expr) (initial rest : List Choice)
    (items : List (List Tok)) (h : (Syn.and a b).yield initial = some (items, rest)) :
    ∃ xs ys middle, a.yield initial = some (xs, middle) ∧ b.yield middle = some (ys, rest) ∧
      items = [xs.flatten ++ pu .and ++ ys.flatten] :=
  pair_pure_success_split a.yield b.yield (fun xs ys => [xs.flatten ++ pu .and ++ ys.flatten])
    initial rest items h

theorem or_yield_parts (a b : Syn .expr) (initial rest : List Choice)
    (items : List (List Tok)) (h : (Syn.or a b).yield initial = some (items, rest)) :
    ∃ xs ys middle, a.yield initial = some (xs, middle) ∧ b.yield middle = some (ys, rest) ∧
      items = [xs.flatten ++ pu .or ++ ys.flatten] :=
  pair_pure_success_split a.yield b.yield (fun xs ys => [xs.flatten ++ pu .or ++ ys.flatten])
    initial rest items h

theorem assignment_yield_parts (op : AssignOp) (a b : Syn .expr) (initial rest : List Choice)
    (items : List (List Tok)) (h : (Syn.assign op a b).yield initial = some (items, rest)) :
    ∃ xs ys middle, a.yield initial = some (xs, middle) ∧ b.yield middle = some (ys, rest) ∧
      items = [xs.flatten ++ pu op.punct ++ ys.flatten] :=
  pair_pure_success_split a.yield b.yield (fun xs ys => [xs.flatten ++ pu op.punct ++ ys.flatten])
    initial rest items h

theorem conditional_yield_parts (c a b : Syn .expr) (initial rest : List Choice)
    (items : List (List Tok)) (h : (Syn.cond c a b).yield initial = some (items, rest)) :
    ∃ xs ys zs middle next, c.yield initial = some (xs, middle) ∧
      a.yield middle = some (ys, next) ∧ b.yield next = some (zs, rest) ∧
      items = [xs.flatten ++ pu .question ++ ys.flatten ++ pu .colon ++ zs.flatten] := by
  obtain ⟨xs, middle, hc, remainder⟩ := bind_success_split c.yield
    (fun xs => do let ys ← a.yield; let zs ← b.yield
                  pure [xs.flatten ++ pu .question ++ ys.flatten ++ pu .colon ++ zs.flatten])
    initial rest items h
  obtain ⟨ys, zs, next, ha, hb, value⟩ := pair_pure_success_split a.yield b.yield
    (fun ys zs => [xs.flatten ++ pu .question ++ ys.flatten ++ pu .colon ++ zs.flatten])
    middle rest items remainder
  exact ⟨xs, ys, zs, middle, next, hc, ha, hb, value⟩

theorem prefix_yield_parts (op : PrefixOp) (e : Syn .expr) (initial rest : List Choice)
    (items : List (List Tok)) (h : (Syn.unaryPrefix op e).yield initial = some (items, rest)) :
    ∃ xs, e.yield initial = some (xs, rest) ∧ items = [op.punct ++ xs.flatten] :=
  one_pure_success_split e.yield (fun xs => [op.punct ++ xs.flatten]) initial rest items h

theorem suffix_yield_parts (op : SuffixOp) (e : Syn .expr) (initial rest : List Choice)
    (items : List (List Tok)) (h : (Syn.unarySuffix op e).yield initial = some (items, rest)) :
    ∃ xs, e.yield initial = some (xs, rest) ∧ items = [xs.flatten ++ pu op.punct] :=
  one_pure_success_split e.yield (fun xs => [xs.flatten ++ pu op.punct]) initial rest items h

end Solidity.Frontend.ExpressionUniqueness
