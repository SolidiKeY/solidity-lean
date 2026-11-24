import Solidity.Correctness.Lowering.Total.CallSpellExt

/-!
Executable realization of the landed additive ExprX contract. Tables, Spells
and CallSpellExt remain unchanged. This module proves spelling soundness and
completeness, not the registry's shared semantic Meaning or statement decoding.
-/
namespace Solidity.Correctness.Lowering.Total.Decode.Calls

open Source (Syn)
open CallSpellExt

variable (T : Tables) (R : Registry)

mutual
/-- Decode expressions under the additive registered-call contract. Claimed
calls read their raw arguments; ordinary calls recursively decode arguments. -/
def expr : RawExpr → Option (Syn .expr)
  | .num n => some (num n)
  | .name x => some (.ident x)
  | .bool b => some (.lit (.bool b))
  | .field e f => (expr e).map (.member · f)
  | .index e k => do pure (.index (← expr e) (.some (← expr k)))
  | .binop op a b => do pure ((← binop op) (← expr a) (← expr b))
  | .unop .neg a => (expr a).map (.unaryPrefix .neg)
  | .unop .not a => (expr a).map (.unaryPrefix .not)
  | .unop .bnot a => (expr a).map (.unaryPrefix .bitNot)
  | .unop .toInt a => (expr a).map fun a =>
      .call (.elemType intElem (by decide)) (.positional (.cons a .nil))
  | .unop .toUint a => (expr a).map fun a =>
      .call (.elemType uintElem (by decide)) (.positional (.cons a .nil))
  | .ternary c a b => do pure (.cond (← expr c) (← expr a) (← expr b))
  | .incDec .preInc e => (expr e).map (.unaryPrefix .inc)
  | .incDec .preDec e => (expr e).map (.unaryPrefix .dec)
  | .incDec .postInc e => (expr e).map (.unarySuffix .inc)
  | .incDec .postDec e => (expr e).map (.unarySuffix .dec)
  | .call f args =>
      match R.lookup f with
      | some c => c.spell args
      | none => (exprs args).map fun args => .call (.ident f) (.positional args)
  | .modular op a b k => do
      pure (.call (.ident op.toStr)
        (.positional (.cons (← expr a) (.cons (← expr b) (.cons (← expr k) .nil)))))
  | .env k => T.env k
  | .tuple (a :: b :: rest) => do
      pure (.tuple (.some (← expr a)) (.cons (.some (← expr b)) (← components rest)))
  | .assign l r => do pure (.assign .assign (← expr l) (← expr r))
  | .opAssign op l r => do pure (.assign (← assignOp op) (← expr l) (← expr r))
  | _ => none
/-- Argument lists of the version. -/
def exprs : List RawExpr → Option (Syn (.list .expr))
  | [] => some .nil
  | e :: es => do pure (.cons (← expr e) (← exprs es))
/-- Tuple components of the version. -/
def components : List RawExpr → Option (Syn (.list (.opt .expr)))
  | [] => some .nil
  | e :: es => do pure (.cons (.some (← expr e)) (← components es))
end


/-- Split the binds of a decoder equation. -/
local macro "bind_simp" " at " h:ident : tactic =>
  `(tactic| simp only [Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff,
      Option.map_eq_some_iff, Option.some.injEq, reduceCtorEq, exists_const, false_and,
      exists_false] at $h:ident)

/-- Unfold one decoder equation and split its binds. -/
local macro "spell_simp " f:ident " at " h:ident : tactic =>
  `(tactic| simp only [$f:ident, Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff,
      Option.map_eq_some_iff, Option.some.injEq, reduceCtorEq, exists_const, false_and,
      exists_false] at $h:ident)


variable {T : Tables} {R : Registry}

mutual
theorem of_spelling : ∀ {e t}, ExprX T R e t → expr T R e = some t
  | _, _, .num _ | _, _, .name _ | _, _, .bool _ => by simp [expr]
  | _, _, .field _ h => by simp [expr, (of_spelling h)]
  | _, _, .index h k => by simp [expr, (of_spelling h), (of_spelling k)]
  | _, _, .binop o h k e => by simp [expr, o, (of_spelling h), (of_spelling k), e]
  | _, _, .neg h | _, _, .not h | _, _, .bnot h | _, _, .toInt h | _, _, .toUint h
  | _, _, .preInc h | _, _, .preDec h | _, _, .postInc h | _, _, .postDec h => by
      simp [expr, (of_spelling h)]
  | _, _, .ternary c a b => by simp [expr, (of_spelling c), (of_spelling a), (of_spelling b)]
  | _, _, .call f unclaimed h => by
      have absent : R.lookup f = none := by
        cases found : R.lookup f with
        | none => rfl
        | some c => simp [Registry.claims, found] at unclaimed
      simp [expr, absent, of_spellings h]
  | _, _, .claimed found spelled => by simp [expr, found, spelled]
  | _, _, .modular _ a b k => by simp [expr, (of_spelling a), (of_spelling b), (of_spelling k)]
  | _, _, .env h => by simp [expr, h]
  | _, _, .tuple a b r => by simp [expr, (of_spelling a), (of_spelling b), (of_components r)]
  | _, _, .assign l r => by simp [expr, (of_spelling l), (of_spelling r)]
  | _, _, .opAssign o l r => by simp [expr, o, (of_spelling l), (of_spelling r)]
theorem of_spellings : ∀ {es t}, ExprsX T R es t → exprs T R es = some t
  | _, _, .nil => by simp [exprs]
  | _, _, .cons h k => by simp [exprs, of_spelling h, of_spellings k]
theorem of_components : ∀ {es t}, ComponentsX T R es t → components T R es = some t
  | _, _, .nil => by simp [components]
  | _, _, .cons h k => by simp [components, of_spelling h, of_components k]
end

mutual
theorem expr_spellsX : (e : RawExpr) → (t : Syn .expr) → expr T R e = some t → ExprX T R e t
  | .num n, t, h => by spell_simp expr at h; subst h; exact .num n
  | .name x, t, h => by spell_simp expr at h; subst h; exact .name x
  | .bool b, t, h => by spell_simp expr at h; subst h; exact .bool b
  | .field e f, t, h => by
      spell_simp expr at h; obtain ⟨a, ha, rfl⟩ := h; exact .field f (expr_spellsX _ _ ha)
  | .index e k, t, h => by
      spell_simp expr at h; obtain ⟨a, ha, b, hb, rfl⟩ := h
      exact .index (expr_spellsX _ _ ha) (expr_spellsX _ _ hb)
  | .binop op a b, t, h => by
      spell_simp expr at h; obtain ⟨f, hf, a', ha, b', hb, rfl⟩ := h
      exact .binop hf (expr_spellsX _ _ ha) (expr_spellsX _ _ hb) rfl
  | .unop .neg a, t, h => by
      spell_simp expr at h; obtain ⟨a', ha, rfl⟩ := h; exact .neg (expr_spellsX _ _ ha)
  | .unop .not a, t, h => by
      spell_simp expr at h; obtain ⟨a', ha, rfl⟩ := h; exact .not (expr_spellsX _ _ ha)
  | .unop .bnot a, t, h => by
      spell_simp expr at h; obtain ⟨a', ha, rfl⟩ := h; exact .bnot (expr_spellsX _ _ ha)
  | .unop .toInt a, t, h => by
      spell_simp expr at h; obtain ⟨a', ha, rfl⟩ := h; exact .toInt (expr_spellsX _ _ ha)
  | .unop .toUint a, t, h => by
      spell_simp expr at h; obtain ⟨a', ha, rfl⟩ := h; exact .toUint (expr_spellsX _ _ ha)
  | .ternary c a b, t, h => by
      spell_simp expr at h; obtain ⟨c', hc, a', ha, b', hb, rfl⟩ := h
      exact .ternary (expr_spellsX _ _ hc) (expr_spellsX _ _ ha) (expr_spellsX _ _ hb)
  | .incDec .preInc e, t, h => by
      spell_simp expr at h; obtain ⟨a', ha, rfl⟩ := h; exact .preInc (expr_spellsX _ _ ha)
  | .incDec .preDec e, t, h => by
      spell_simp expr at h; obtain ⟨a', ha, rfl⟩ := h; exact .preDec (expr_spellsX _ _ ha)
  | .incDec .postInc e, t, h => by
      spell_simp expr at h; obtain ⟨a', ha, rfl⟩ := h; exact .postInc (expr_spellsX _ _ ha)
  | .incDec .postDec e, t, h => by
      spell_simp expr at h; obtain ⟨a', ha, rfl⟩ := h; exact .postDec (expr_spellsX _ _ ha)
  | .call f args, t, h => by
      cases found : R.lookup f with
      | some c =>
          exact .claimed found (by simpa only [expr, found] using h)
      | none =>
          simp only [expr, found] at h
          bind_simp at h
          obtain ⟨a', ha, rfl⟩ := h
          exact .call f (by simp only [Registry.claims, found, Option.isSome_none])
            (exprs_spellsX _ _ ha)
  | .modular op a b k, t, h => by
      spell_simp expr at h; obtain ⟨a', ha, b', hb, k', hk, rfl⟩ := h
      exact .modular op (expr_spellsX _ _ ha) (expr_spellsX _ _ hb) (expr_spellsX _ _ hk)
  | .env k, t, h => by spell_simp expr at h; exact .env h
  | .tuple (a :: b :: rest), t, h => by
      spell_simp expr at h; obtain ⟨a', ha, b', hb, r', hr, rfl⟩ := h
      exact .tuple (expr_spellsX _ _ ha) (expr_spellsX _ _ hb) (components_spellsX _ _ hr)
  | .assign l r, t, h => by
      spell_simp expr at h; obtain ⟨l', hl, r', hr, rfl⟩ := h
      exact .assign (expr_spellsX _ _ hl) (expr_spellsX _ _ hr)
  | .opAssign op l r, t, h => by
      spell_simp expr at h; obtain ⟨o, ho, l', hl, r', hr, rfl⟩ := h
      exact .opAssign ho (expr_spellsX _ _ hl) (expr_spellsX _ _ hr)
  | .newArr .., _, h | .named .., _, h | .tuple [], _, h | .tuple [_], _, h => by
      spell_simp expr at h
theorem exprs_spellsX : (es : List RawExpr) → (t : Syn (.list .expr)) →
    exprs T R es = some t → ExprsX T R es t
  | [], t, h => by spell_simp exprs at h; subst h; exact .nil
  | e :: es, t, h => by
      spell_simp exprs at h; obtain ⟨a, ha, b, hb, rfl⟩ := h
      exact .cons (expr_spellsX _ _ ha) (exprs_spellsX _ _ hb)
theorem components_spellsX : (es : List RawExpr) → (t : Syn (.list (.opt .expr))) →
    components T R es = some t → ComponentsX T R es t
  | [], t, h => by spell_simp components at h; subst h; exact .nil
  | e :: es, t, h => by
      spell_simp components at h; obtain ⟨a, ha, b, hb, rfl⟩ := h
      exact .cons (expr_spellsX _ _ ha) (components_spellsX _ _ hb)
end


/-- The decoder returns exactly the additive spelling relation, including
claimed calls at arbitrary expression depth. -/
theorem conformsX : ConformsX T R (expr T R) :=
  fun e t => ⟨expr_spellsX e t, of_spelling⟩

/-- The additive relation has one spelling per raw expression. -/
theorem unique {e a b} (ha : ExprX T R e a) (hb : ExprX T R e b) : a = b :=
  Option.some.inj ((of_spelling ha).symm.trans (of_spelling hb))

mutual
/-- A registry does not change expressions containing no claimed call. The
premise is the contract's compatibility domain, not an admission restriction. -/
theorem conservative : (e : RawExpr) → R.Unclaimed e → expr T R e = T.expr e
  | .num _, _ | .name _, _ | .bool _, _ | .env _, _ | .newArr .., _
  | .named .., _ | .tuple [], _ | .tuple [_], _ => rfl
  | .field e f, h => by
      simp only [Registry.Unclaimed, RawExpr.any, Bool.false_or] at h
      simp [expr, Tables.expr, conservative e h]
  | .index a b, h | .binop _ a b, h | .assign a b, h | .opAssign _ a b, h => by
      simp only [Registry.Unclaimed, RawExpr.any, Bool.false_or, Bool.or_eq_false_iff] at h
      simp [expr, Tables.expr, conservative a h.1, conservative b h.2]
  | .unop op a, h => by
      simp only [Registry.Unclaimed, RawExpr.any, Bool.false_or] at h
      cases op <;> simp [expr, Tables.expr, conservative a h]
  | .incDec op a, h => by
      simp only [Registry.Unclaimed, RawExpr.any, Bool.false_or] at h
      cases op <;> simp [expr, Tables.expr, conservative a h]
  | .ternary a b c, h | .modular _ a b c, h => by
      simp only [Registry.Unclaimed, RawExpr.any, Bool.false_or, Bool.or_eq_false_iff] at h
      simp [expr, Tables.expr, conservative a h.1.1, conservative b h.1.2,
        conservative c h.2]
  | .call f args, h => by
      simp only [Registry.Unclaimed, RawExpr.any, Bool.or_eq_false_iff] at h
      have absent : R.lookup f = none := by
        cases found : R.lookup f with
        | none => rfl
        | some c => simp [Registry.claims, found] at h
      have children : ∀ e ∈ args, R.Unclaimed e := by
        intro e he
        simpa only [Registry.Unclaimed, Bool.not_eq_true] using
          (List.any_eq_false.mp h.2) ⟨e, he⟩ (List.mem_attach _ _)
      simp [expr, Tables.expr, absent, conservative_args args children]
  | .tuple (a :: b :: rest), h => by
      simp only [Registry.Unclaimed, RawExpr.any, Bool.false_or] at h
      have children : ∀ e ∈ a :: b :: rest, R.Unclaimed e := by
        intro e he
        simpa only [Registry.Unclaimed, Bool.not_eq_true] using
          (List.any_eq_false.mp h) ⟨e, he⟩ (List.mem_attach _ _)
      simp [expr, Tables.expr, conservative a (children a (by simp)),
        conservative b (children b (by simp)),
        conservative_components rest (fun e he => children e (by simp [he]))]
theorem conservative_args : (es : List RawExpr) → (∀ e ∈ es, R.Unclaimed e) →
    exprs T R es = T.exprs es
  | [], _ => rfl
  | e :: es, h => by
      simp [exprs, Tables.exprs, conservative e (h e (by simp)),
        conservative_args es (fun a ha => h a (by simp [ha]))]
theorem conservative_components : (es : List RawExpr) → (∀ e ∈ es, R.Unclaimed e) →
    components T R es = T.components es
  | [], _ => rfl
  | e :: es, h => by
      simp [components, Tables.components, conservative e (h e (by simp)),
        conservative_components es (fun a ha => h a (by simp [ha]))]
end

/-- Both the nested and node-level contracts hold for this implementation. -/
theorem conforms : Conforms T R (expr T R) :=
  ⟨fun _ _ _ h => by simp only [expr, h], conservative⟩

/-- Any implementation of the full relation contract has the same node-level
behavior, independently of how that implementation recurses. -/
theorem conformsX_conforms : conformsX_conforms_statement := by
  intro T R f hf
  have same : f = expr T R := by
    funext e
    apply Option.ext
    intro t
    exact (hf e t).trans (conformsX e t).symm
  subst f
  exact conforms

/-- The published v2/v1 relation compatibility statement follows from the two
executable decoder characterizations; no second relation is defined here. -/
theorem unclaimed_spelling : exprX_unclaimed_statement := by
  intro T R e t h
  rw [← conformsX e t, conservative e h]
  exact ⟨Spells.expr_spellsT e t, Spells.ExprT.decode⟩

private theorem unclaimed_nil : (e : RawExpr) → Registry.Unclaimed [] e
  | .num _ | .name _ | .bool _ | .env _ => by
      simp only [Registry.Unclaimed, RawExpr.any, Bool.false_or]
  | .field a _ | .unop _ a | .incDec _ a | .newArr _ a => by
      simpa only [Registry.Unclaimed, RawExpr.any, Bool.false_or] using unclaimed_nil a
  | .index a b | .binop _ a b | .assign a b | .opAssign _ a b => by
      simp only [Registry.Unclaimed, RawExpr.any, Bool.false_or, Bool.or_eq_false_iff]
      exact ⟨unclaimed_nil a, unclaimed_nil b⟩
  | .ternary a b c | .modular _ a b c => by
      simp only [Registry.Unclaimed, RawExpr.any, Bool.false_or, Bool.or_eq_false_iff]
      exact ⟨⟨unclaimed_nil a, unclaimed_nil b⟩, unclaimed_nil c⟩
  | .call _ args | .named _ _ args | .tuple args => by
      simp only [Registry.Unclaimed, RawExpr.any, claims_nil, Bool.false_or, List.any_eq_false]
      intro a _
      simpa only [Registry.Unclaimed, Bool.not_eq_true] using unclaimed_nil a.val
termination_by e => sizeOf e
decreasing_by
  all_goals simp_wf
  all_goals first | omega | (have := List.sizeOf_lt_of_mem a.property; omega)

/-- The empty registry recovers v1 exactly, as required by the published
contract; no syntactic or semantic input exclusions are added. -/
theorem empty_spelling : exprX_nil_statement :=
  fun T e t => unclaimed_spelling T [] e t (unclaimed_nil e)

end Solidity.Correctness.Lowering.Total.Decode.Calls
