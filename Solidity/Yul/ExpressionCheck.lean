import Solidity.Yul.CatalogLaws
import Solidity.Source.Syntax

/-!
# Declarative Yul expressions over the existing grammar

This consumes S00/G08–G11's `Syn .yulExpr`; it introduces no lexer or
untyped intermediate tree. Environments contain intrinsic references, and
all returned derivations compute an arity-indexed expression.
The enclosing whole-block/environment construction remains a separate obligation.
-/
namespace Solidity.Yul
open Solidity.Source (Syn YulLit)

/-- Read-only names at an expression occurrence. The block checker constructs
these tables after hoisting functions and checking all visible-name collisions. -/
structure ExprEnv (F : List Sig) (X : List ExternalType) (n : Nat) where
  locals : List (String × Fin n)
  functions : List (String × ((s : Sig) × Member F s))
  externals : List (String × ExternalRef X false)

def externalKey (base : String) (suffix : List String) : String :=
  String.intercalate "." (base :: suffix)

/-- Short Yul strings are left-aligned in their word. String escape/Unicode
validity belongs to the existing checked lexer, not this conversion. -/
def bytesWord (bs : List UInt8) : Word :=
  word (bs.foldl (fun a b => 256 * a + b.toNat) 0 * 256 ^ (32 - bs.length))

/-- Literal meaning is independent of the checker. -/
inductive LiteralD : YulLit → Word → Type where
  | dec {n : Nat} : n < 2 ^ 256 → LiteralD (.dec n) (word n)
  | hex {n : Nat} : n < 2 ^ 256 → LiteralD (.hex n) (word n)
  | bool (b : Bool) : LiteralD (.bool b) (truth b)
  | str {bs : List UInt8} : bs.length ≤ 32 → LiteralD (.str bs) (bytesWord bs)
  | hexStr {bs : List UInt8} : bs.length ≤ 32 → LiteralD (.hexStr bs) (bytesWord bs)

def inferLiteral (l : YulLit) : Option ((w : Word) × LiteralD l w) :=
  match l with
  | .dec n => if h : n < 2 ^ 256 then some ⟨word n, .dec h⟩ else none
  | .hex n => if h : n < 2 ^ 256 then some ⟨word n, .hex h⟩ else none
  | .bool b => some ⟨truth b, .bool b⟩
  | .str bs => if h : bs.length ≤ 32 then some ⟨bytesWord bs, .str h⟩ else none
  | .hexStr bs => if h : bs.length ≤ 32 then some ⟨bytesWord bs, .hexStr h⟩ else none

mutual
/-- Static expression semantics on the original grammar, with lexical lookup
and exact builtin/function arities. Local bindings take priority over external
references only at an unsuffixed identifier. -/
inductive ExprD {F : List Sig} {X : List ExternalType} {n : Nat} (E : ExprEnv F X n) :
    Syn .yulExpr → Nat → Type where
  | literal {l w} : LiteralD l w → ExprD E (.yulLit l) 1
  | «variable» {name i} : Resolves E.locals name i → ExprD E (.yulPath name []) 1
  | external {name suffix ref} :
      (suffix ≠ [] ∨ NoBinding E.locals name) →
      Resolves E.externals (externalKey name suffix) ref →
      ExprD E (.yulPath name suffix) 1
  | builtin {name args a r} (b : Builtin a r) :
      b.name = name → ArgsD E args a → ExprD E (.yulCall name args) r
  | call {name args s} (f : Member F s) :
      NoBuiltin name → Resolves E.functions name ⟨s, f⟩ →
      ArgsD E args s.args → ExprD E (.yulCall name args) s.rets

/-- Each operand is single-valued and the operand count is exact. -/
inductive ArgsD {F : List Sig} {X : List ExternalType} {n : Nat} (E : ExprEnv F X n) :
    Syn (.list .yulExpr) → Nat → Type where
  | nil : ArgsD E .nil 0
  | cons {e es a} : ExprD E e 1 → ArgsD E es a → ArgsD E (.cons e es) (a + 1)
end

/-- The result type is computed from the existing grammar category. This is
not a new syntax tree: only Yul expressions and their operand lists have output. -/
def InferResult {F X n} (E : ExprEnv F X n) (c : Solidity.Source.Cat) : Syn c → Type :=
  match c with
  | .yulExpr => fun e => Option ((r : Nat) × ExprD E e r)
  | .list .yulExpr => fun es => Option ((a : Nat) × ArgsD E es a)
  | _ => fun _ => Unit

/-- The list constructor acts only at the Yul operand category. Its inputs
are already computed under the generalized recursor motive. -/
def inferCons {F X n} (E : ExprEnv F X n) (c : Solidity.Source.Cat)
    (e : Syn c) (es : Syn (.list c)) (de : InferResult E c e)
    (ds : InferResult E (.list c) es) : InferResult E (.list c) (.cons e es) := by
  cases c <;> first
    | exact ()
    | exact do
        let ⟨r, d⟩ ← de
        if h : r = 1 then
          let ⟨a, rest⟩ ← ds
          some ⟨a + 1, .cons (h ▸ d) rest⟩
        else none

/-- Traverse the indexed source grammar with a motive generalizing its category
(Gate G0), avoiding fixed-index case casts. Other categories produce no checking result. -/
def inferNode {F X n} (E : ExprEnv F X n) (c : Solidity.Source.Cat) (t : Syn c) :
    InferResult E c t := by
  apply Syn.casesOn (motive := fun c t => InferResult E c t) t
  case yulLit =>
    intro l
    exact (inferLiteral l).map (fun ⟨_, d⟩ => ⟨1, .literal d⟩)
  case yulPath =>
    intro name suffix
    exact if hs : suffix = [] then
      match hl : resolve E.locals name with
      | some _i => some ⟨1, hs.symm ▸ .«variable» (resolve_sound hl)⟩
      | none => match he : resolve E.externals (externalKey name suffix) with
        | some _ref => some ⟨1, .external (.inr (resolve_none_sound hl)) (resolve_sound he)⟩
        | none => none
    else match he : resolve E.externals (externalKey name suffix) with
      | some _ref => some ⟨1, .external (.inl hs) (resolve_sound he)⟩
      | none => none
  case yulCall =>
    intro name args
    exact do
      let ⟨a, ad⟩ ← inferNode E _ args
      match hb : lookupBuiltin name with
      | some ⟨ba, br, b⟩ =>
          if h : a = ba then some ⟨br, .builtin b (lookupBuiltin_sound hb) (h ▸ ad)⟩ else none
      | none => match hf : resolve E.functions name with
        | some ⟨s, f⟩ =>
            if h : a = s.args then some ⟨s.rets, .call f (lookup_none_sound hb) (resolve_sound hf) (h ▸ ad)⟩ else none
        | none => none
  case nil =>
    intro c
    cases c <;> first | exact () | exact some ⟨0, .nil⟩
  case cons =>
    intro c e es
    exact inferCons E c e es (inferNode E c e) (inferNode E (.list c) es)
  all_goals intros; exact ()
termination_by structural t

/-- Elaborate an expression directly into its independent judgement. -/
def inferExpr {F X n} (E : ExprEnv F X n) (e : Syn .yulExpr) :
    Option ((r : Nat) × ExprD E e r) := inferNode E _ e

def inferArgs {F X n} (E : ExprEnv F X n) (es : Syn (.list .yulExpr)) :
    Option ((a : Nat) × ArgsD E es a) := inferNode E _ es

/-- Constructor equations keep simplification away from the generic recursor. -/
theorem inferExpr_literal {F X n} (E : ExprEnv F X n) (l : YulLit) :
    inferExpr E (.yulLit l) = (inferLiteral l).map (fun ⟨_, d⟩ => ⟨1, .literal d⟩) := rfl

theorem inferExpr_path {F X n} (E : ExprEnv F X n) (name : String) (suffix : List String) :
    inferExpr E (.yulPath name suffix) =
      (if hs : suffix = [] then
        match hl : resolve E.locals name with
        | some _i => some ⟨1, hs.symm ▸ .«variable» (resolve_sound hl)⟩
        | none => match he : resolve E.externals (externalKey name suffix) with
          | some _ref => some ⟨1, .external (.inr (resolve_none_sound hl)) (resolve_sound he)⟩
          | none => none
      else match he : resolve E.externals (externalKey name suffix) with
        | some _ref => some ⟨1, .external (.inl hs) (resolve_sound he)⟩
        | none => none) := rfl

theorem inferExpr_call {F X n} (E : ExprEnv F X n) (name : String) (args : Syn (.list .yulExpr)) :
    inferExpr E (.yulCall name args) = (do
      let ⟨a, ad⟩ ← inferArgs E args
      match hb : lookupBuiltin name with
      | some ⟨ba, br, b⟩ =>
          if h : a = ba then some ⟨br, .builtin b (lookupBuiltin_sound hb) (h ▸ ad)⟩ else none
      | none => match hf : resolve E.functions name with
        | some ⟨s, f⟩ =>
            if h : a = s.args then some ⟨s.rets, .call f (lookup_none_sound hb) (resolve_sound hf) (h ▸ ad)⟩ else none
        | none => none) := rfl

theorem inferArgs_cons {F X n} (E : ExprEnv F X n) (e : Syn .yulExpr) (es : Syn (.list .yulExpr)) :
    inferArgs E (.cons e es) = (do
      let ⟨r, d⟩ ← inferExpr E e
      if h : r = 1 then
        let ⟨a, ds⟩ ← inferArgs E es
        some ⟨a + 1, .cons (h ▸ d) ds⟩
      else none) := rfl

/-- Every declaratively meaningful literal is accepted, with its exact value. -/
theorem LiteralD.complete {l w} (d : LiteralD l w) : inferLiteral l = some ⟨w, d⟩ := by
  cases d with
  | dec h => exact dif_pos h
  | hex h => exact dif_pos h
  | bool b => rfl
  | str h => exact dif_pos h
  | hexStr h => exact dif_pos h

mutual
/-- Soundness is intrinsic in the returned derivation; this computes its term. -/
def ExprD.term {F X n} {E : ExprEnv F X n} {e r} (d : ExprD E e r) : Expr F X n r := by
  cases d with
  | @literal l w _ => exact .literal w
  | @«variable» name i _ => exact .«local» i
  | @external name suffix ref _ _ => exact .external ref
  | builtin b _ args => exact .builtin b args.terms
  | call f _ _ args => exact .call f args.terms
termination_by structural d

def ArgsD.terms {F X n} {E : ExprEnv F X n} {es a} (d : ArgsD E es a) :
    Fin a → Expr F X n 1 := by
  cases d with
  | nil => exact Fin.elim0
  | cons e es => exact Fin.cases e.term es.terms
termination_by structural d
end

mutual
/-- Completeness against the independent declarative expression relation. -/
theorem ExprD.complete {F X n} {E : ExprEnv F X n} {e r} (d : ExprD E e r) :
    inferExpr E e = some ⟨r, d⟩ := by
  cases d with
  | literal ld =>
      simp only [inferExpr_literal, LiteralD.complete ld, Option.map_some]
  | @«variable» name i hl =>
      rw [inferExpr_path, dif_pos rfl]
      split
      · next j hj =>
        have hi : j = i := Option.some.inj (hj.symm.trans (resolve_complete hl))
        subst j
        rfl
      · next hj =>
        have hc := resolve_complete hl
        rw [hj] at hc
        cases hc
  | @external name suffix ref hp he =>
      by_cases hs : suffix = []
      · subst suffix
        have hl : resolve E.locals _ = none := resolve_none_complete (hp.resolve_left (fun h => h rfl))
        rw [inferExpr_path, dif_pos rfl]
        split
        · next j hj => rw [hl] at hj; cases hj
        · split
          · next r hr =>
            have hh : r = ref := Option.some.inj (hr.symm.trans (resolve_complete he))
            subst r
            rfl
          · next hr => have hc := resolve_complete he; rw [hr] at hc; cases hc
      · rw [inferExpr_path, dif_neg hs]
        split
        · next r hr =>
          have hh : r = ref := Option.some.inj (hr.symm.trans (resolve_complete he))
          subst r
          rfl
        · next hr => have hc := resolve_complete he; rw [hr] at hc; cases hc
  | builtin b hb ad =>
      have hl : lookupBuiltin _ = some ⟨_, _, b⟩ := hb ▸ lookup_builtin_name b
      simp only [inferExpr_call, ArgsD.complete ad, bind, Option.bind_some]
      split
      · next ba br bb hh =>
        have he := Option.some.inj (hh.symm.trans hl)
        cases he
        rw [dif_pos rfl]
      · next hh => rw [hh] at hl; cases hl
  | call f hb hf ad =>
      have hl := lookup_none_complete hb
      simp only [inferExpr_call, ArgsD.complete ad, bind, Option.bind_some]
      split
      · next ba br bb hh => rw [hl] at hh; cases hh
      · split
        · next sig fn hh =>
          have he := Option.some.inj (hh.symm.trans (resolve_complete hf))
          cases he
          rw [dif_pos rfl]
        · next hh => have hc := resolve_complete hf; rw [hh] at hc; cases hc
termination_by structural d

/-- Completeness includes every operand's single-result constraint. -/
theorem ArgsD.complete {F X n} {E : ExprEnv F X n} {es a} (d : ArgsD E es a) :
    inferArgs E es = some ⟨a, d⟩ := by
  cases d with
  | nil => rfl
  | cons de ds =>
      simp only [inferArgs_cons, ExprD.complete de, bind, Option.bind_some, dite_true, ArgsD.complete ds]
termination_by structural d
end

/-- The executable expression check is sound against the independent relation. -/
theorem inferExpr_sound {F X n} {E : ExprEnv F X n} {e} (h : (inferExpr E e).isSome = true) :
    ∃ r, Nonempty (ExprD E e r) := by
  cases hc : inferExpr E e with
  | none => rw [hc] at h; cases h
  | some result => exact ⟨result.1, ⟨result.2⟩⟩

/-- Complete static expression checking for the given intrinsic symbol tables.
Tier, compiler-dependent and block-safety admission are separate checks. -/
theorem inferExpr_iff {F X n} (E : ExprEnv F X n) (e : Syn .yulExpr) :
    (inferExpr E e).isSome = true ↔ ∃ r, Nonempty (ExprD E e r) := by
  constructor
  · exact inferExpr_sound
  · rintro ⟨r, ⟨d⟩⟩
    rw [ExprD.complete d]
    rfl

/-- Two derivations for the same grammar tree and intrinsic environment agree
as packed results, including their inferred arity. -/
theorem ExprD.result_unique : ∀ (F : List Solidity.Yul.Sig) (X : List Solidity.Yul.ExternalType) (n : Nat)
 (E : Solidity.Yul.ExprEnv F X n) (tree : Solidity.Source.Syn .yulExpr) (firstCount secondCount : Nat)
 (first : Solidity.Yul.ExprD E tree firstCount)
 (second : Solidity.Yul.ExprD E tree secondCount),
 (⟨firstCount,first⟩ : (count : Nat) × Solidity.Yul.ExprD E tree count) = ⟨secondCount,second⟩ := by
  intro F X n E tree firstCount secondCount first second
  exact Option.some.inj ((ExprD.complete first).symm.trans (ExprD.complete second))

/-- Two derivations for the same grammar tree and intrinsic environment agree
as packed results, including their inferred arity. -/
theorem ArgsD.result_unique : ∀ (F : List Solidity.Yul.Sig) (X : List Solidity.Yul.ExternalType) (n : Nat)
 (E : Solidity.Yul.ExprEnv F X n) (tree : Solidity.Source.Syn (.list .yulExpr)) (firstCount secondCount : Nat)
 (first : Solidity.Yul.ArgsD E tree firstCount)
 (second : Solidity.Yul.ArgsD E tree secondCount),
 (⟨firstCount,first⟩ : (count : Nat) × Solidity.Yul.ArgsD E tree count) = ⟨secondCount,second⟩ := by
  intro F X n E tree firstCount secondCount first second
  exact Option.some.inj ((ArgsD.complete first).symm.trans (ArgsD.complete second))

/-- Packed derivation uniqueness transports to the generated intrinsic expression,
retaining its arity. This is a typed consequence of result_unique. -/
theorem ExprD.term_result_unique : ∀ (F : List Solidity.Yul.Sig) (X : List Solidity.Yul.ExternalType) (n : Nat)
 (E : Solidity.Yul.ExprEnv F X n) (tree : Solidity.Source.Syn .yulExpr) (firstCount secondCount : Nat)
 (first : Solidity.Yul.ExprD E tree firstCount)
 (second : Solidity.Yul.ExprD E tree secondCount),
 (⟨firstCount,Solidity.Yul.ExprD.term first⟩ : (count : Nat) × Solidity.Yul.Expr F X n count) =
 ⟨secondCount,Solidity.Yul.ExprD.term second⟩ := by
  intro F X n E tree firstCount secondCount first second
  exact congrArg
    (fun result : (count : Nat) × ExprD E tree count =>
      (⟨result.1,ExprD.term result.2⟩ : (count : Nat) × Expr F X n count))
    (ExprD.result_unique F X n E tree firstCount secondCount first second)

/-- Packed operand derivations determine the exact arity-indexed operand function. -/
theorem ArgsD.terms_result_unique : ∀ (F : List Solidity.Yul.Sig) (X : List Solidity.Yul.ExternalType) (n : Nat)
 (E : Solidity.Yul.ExprEnv F X n) (tree : Solidity.Source.Syn (.list .yulExpr)) (firstCount secondCount : Nat)
 (first : Solidity.Yul.ArgsD E tree firstCount)
 (second : Solidity.Yul.ArgsD E tree secondCount),
 (⟨firstCount,Solidity.Yul.ArgsD.terms first⟩ : (count : Nat) × (Fin count → Solidity.Yul.Expr F X n 1)) =
 ⟨secondCount,Solidity.Yul.ArgsD.terms second⟩ := by
  intro F X n E tree firstCount secondCount first second
  exact congrArg
    (fun result : (count : Nat) × ArgsD E tree count =>
      (⟨result.1,ArgsD.terms result.2⟩ : (count : Nat) × (Fin count → Expr F X n 1)))
    (ArgsD.result_unique F X n E tree firstCount secondCount first second)

end Solidity.Yul
