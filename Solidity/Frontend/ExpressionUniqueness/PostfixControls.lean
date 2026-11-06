import Solidity.Frontend.ExpressionUniqueness.PostfixSpans
import Solidity.Frontend.ExpressionUniqueness.MemberSpans
import Solidity.Frontend.ExpressionUniqueness.ArgumentSpans
import Solidity.Frontend.ExpressionUniqueness.LayoutBoundary

/-!
# Inhabited arbitrary-depth mixed postfix controls

Each step includes index, slice, member, options and call. The existing intrinsic
syntax is the only tree representation. Original precedence is certified at every
step; exact words and depth reconstruction cover arbitrarily large mixed trees.
-/

namespace Solidity.Frontend.ExpressionUniqueness

open Solidity.Source Solidity.Frontend.Checked

theorem pair_pure_success_join {α β γ : Type} (p : Pr α) (q : Pr β) (render : α → β → γ)
    (initial middle final : List Choice) (x : α) (y : β)
    (hp : p initial = some (x, middle)) (hq : q middle = some (y, final)) :
    (do let a ← p; let b ← q; pure (render a b)) initial = some (render x y, final) := by
  change (p initial).bind (fun r => (q r.2).bind (fun s => some (render r.1 s.1, s.2))) = _
  rw [hp, Option.bind_some, hq]
  rfl

theorem triple_pure_success_join {α β γ δ : Type} (p : Pr α) (q : Pr β) (r : Pr γ)
    (render : α → β → γ → δ) (initial middle next final : List Choice) (x : α) (y : β) (z : γ)
    (hp : p initial = some (x, middle)) (hq : q middle = some (y, next)) (hr : r next = some (z, final)) :
    (do let a ← p; let b ← q; let c ← r; pure (render a b c)) initial = some (render x y z, final) := by
  change (p initial).bind (fun a => (q a.2).bind (fun b =>
    (r b.2).bind (fun c => some (render a.1 b.1 c.1, c.2)))) = _
  rw [hp, Option.bind_some, hq, Option.bind_some, hr]
  rfl

def postfixStep (base : Syn .expr) : Syn .expr :=
  .call (.callOptions (.member (.slice (.index base .none) .none .none) "address")
    (.namedArg "gas" (.ident "g")) .nil) (.positional .nil)

def postfixTail : List Tok :=
  [.punct .lbrack, .punct .rbrack, .punct .lbrack, .punct .colon, .punct .rbrack,
   .punct .period, .elem .address, .punct .lbrace, .ident "gas", .punct .colon,
   .ident "g", .punct .rbrace, .punct .lparen, .punct .rparen]

theorem postfixStep_prec (base : Syn .expr) (hp : base.prec = true)
    (hl : 15 ≤ base.level) (hn : base.isNew = false) : (postfixStep base).prec = true := by
  have hall : base.all Syn.precNode = true := (Bool.and_eq_true_iff.mp hp).2
  have root : (Syn.index base .none).precNode = true := by
    simp only [Syn.precNode, hn, Bool.not_false, Bool.and_true, decide_eq_true_eq]
    exact hl
  have indexAll : (Syn.index base .none).all Syn.precNode = true :=
    Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨root, hall⟩, rfl⟩
  have sliceAll : (Syn.slice (.index base .none) .none .none).all Syn.precNode = true :=
    Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨rfl, indexAll⟩, rfl⟩, rfl⟩
  have memberAll : (Syn.member (.slice (.index base .none) .none .none) "address").all Syn.precNode = true :=
    Bool.and_eq_true_iff.mpr ⟨rfl, sliceAll⟩
  have optionsAll : (Syn.callOptions (.member (.slice (.index base .none) .none .none) "address")
      (.namedArg "gas" (.ident "g")) .nil).all Syn.precNode = true :=
    Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨rfl, memberAll⟩, rfl⟩, rfl⟩
  have callAll : (postfixStep base).all Syn.precNode = true :=
    Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨rfl, optionsAll⟩, rfl⟩
  exact Bool.and_eq_true_iff.mpr ⟨rfl, callAll⟩

theorem postfixStep_yield (base : Syn .expr) (initial final : List Choice) (items : List (List Tok))
    (hy : base.yield initial = some (items, final)) :
    (postfixStep base).yield initial = some ([items.flatten ++ postfixTail], final) := by
  let iw : List Tok := items.flatten ++ pu .lbrack ++ pu .rbrack
  have hi : (Syn.index base .none).yield initial = some ([iw], final) := by
    simpa only [List.flatten_nil, List.append_nil] using
      pair_pure_success_join base.yield (Syn.none : Syn (.opt .expr)).yield
        (fun xs ys => [xs.flatten ++ pu .lbrack ++ ys.flatten ++ pu .rbrack])
        initial final final items [] hy rfl
  let sw : List Tok := iw ++ pu .lbrack ++ pu .colon ++ pu .rbrack
  have hs : (Syn.slice (.index base .none) .none .none).yield initial = some ([sw], final) := by
    simpa only [List.flatten_cons, List.flatten_nil, List.append_nil] using
      triple_pure_success_join (Syn.index base .none).yield (Syn.none : Syn (.opt .expr)).yield
        (Syn.none : Syn (.opt .expr)).yield
        (fun xs ys zs => [xs.flatten ++ pu .lbrack ++ ys.flatten ++ pu .colon ++ zs.flatten ++ pu .rbrack])
        initial final final final [iw] [] [] hi rfl rfl
  let mw : List Tok := sw ++ pu .period ++ [.elem .address]
  have hm : (Syn.member (.slice (.index base .none) .none .none) "address").yield initial = some ([mw], final) := by
    change ((Syn.slice (.index base .none) .none .none).yield initial).bind (fun r =>
      some ([r.1.flatten ++ pu .period ++ [.elem .address]], r.2)) = _
    rw [hs]
    simp only [Option.bind_some, List.flatten_cons, List.flatten_nil, List.append_nil, mw]
  let ow : List Tok := mw ++ braces [.ident "gas", .punct .colon, .ident "g"]
  have ho : (Syn.callOptions (.member (.slice (.index base .none) .none .none) "address")
      (.namedArg "gas" (.ident "g")) .nil).yield initial = some ([ow], final) := by
    simpa only [List.flatten_cons, List.flatten_nil, List.append_nil, commaSep_single] using
      triple_pure_success_join (Syn.member (.slice (.index base .none) .none .none) "address").yield
        (Syn.namedArg "gas" (.ident "g")).yield (Syn.nil : Syn (.list .namedArg)).yield
        (fun xs ys zs => [xs.flatten ++ braces (commaSep (ys.flatten :: zs))])
        initial final final final [mw] [[.ident "gas", .punct .colon, .ident "g"]] [] hm rfl rfl
  have hc : (postfixStep base).yield initial = some ([ow ++ parens []], final) := by
    simpa only [postfixStep, List.flatten_cons, List.flatten_nil, List.append_nil] using
      pair_pure_success_join
        (Syn.callOptions (.member (.slice (.index base .none) .none .none) "address")
          (.namedArg "gas" (.ident "g")) .nil).yield (Syn.positional .nil).yield
        (fun xs ys => [xs.flatten ++ ys.flatten]) initial final final [ow] [parens []] ho rfl
  simpa only [ow, mw, sw, iw, postfixTail, parens, braces, pu, List.append_assoc,
    List.cons_append, List.nil_append] using hc

def postfixTower : Nat → Syn .expr
  | 0 => .ident "a"
  | n + 1 => postfixStep (postfixTower n)

def postfixTowerTokens : Nat → List Tok
  | 0 => [.ident "a"]
  | n + 1 => postfixTowerTokens n ++ postfixTail

theorem postfixTower_prec (n : Nat) : (postfixTower n).prec = true := by
  induction n with
  | zero => rfl
  | succ n ih =>
    apply postfixStep_prec _ ih
    · cases n <;> first | exact (by decide : 15 ≤ 16) | exact (by decide : 15 ≤ 15)
    · cases n <;> rfl

theorem postfixTower_yield (n : Nat) (rest : List Choice) :
    (postfixTower n).yield rest = some ([postfixTowerTokens n], rest) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simpa only [postfixTower, postfixTowerTokens, List.flatten_cons, List.flatten_nil, List.append_nil] using
      postfixStep_yield (postfixTower n) rest rest [postfixTowerTokens n] ih

theorem postfixTower_certified (n : Nat) :
    (postfixTower n).Derives (postfixTowerTokens n) ∧ (postfixTower n).prec = true :=
  ⟨⟨[], (expr_toks_iff _ [] _).mpr (postfixTower_yield n [])⟩, postfixTower_prec n⟩

theorem postfixTowerTokens_length (n : Nat) : (postfixTowerTokens n).length = 14 * n + 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [postfixTowerTokens, List.length_append, ih]
    change 14 * n + 1 + 14 = 14 * (n + 1) + 1
    omega

theorem postfixTower_same_yield_unique (n m : Nat) (ts : List Tok)
    (hn : (postfixTower n).Derives ts) (hm : (postfixTower m).Derives ts) : postfixTower n = postfixTower m := by
  obtain ⟨Ln, hLn⟩ := hn
  obtain ⟨Lm, hLm⟩ := hm
  have an := (expr_toks_iff _ Ln ts).mp hLn
  have am := (expr_toks_iff _ Lm ts).mp hLm
  rw [postfixTower_yield] at an am
  have en : postfixTowerTokens n = ts := (List.cons.inj (Prod.mk.inj (Option.some.inj an)).1).1
  have em : postfixTowerTokens m = ts := (List.cons.inj (Prod.mk.inj (Option.some.inj am)).1).1
  have lengths := congrArg List.length (en.trans em.symm)
  rw [postfixTowerTokens_length, postfixTowerTokens_length] at lengths
  have depth : n = m := by omega
  rw [depth]

def optionalHoles : Nat → Syn (.list (.opt .expr))
  | 0 => .nil
  | n + 1 => .cons .none (optionalHoles n)

theorem optionalHoles_yield (n : Nat) (rest : List Choice) :
    (optionalHoles n).yield rest = some (List.replicate n [], rest) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change ((optionalHoles n).yield rest).bind (fun r => some ([] :: r.1, r.2)) = _
    rw [ih]
    rfl

theorem optionalHoles_nonemptyWords_refuted (n : Nat) : ¬ NonemptyWords (List.replicate (n + 1) []) := by
  intro h
  have member : ([] : List Tok) ∈ List.replicate (n + 1) [] :=
    List.mem_cons.mpr (Or.inl rfl)
  exact h [] member rfl

theorem expressionList_empty_component_impossible (initial final : List Choice) :
    ¬ ∃ args : Syn (.list .expr), args.yield initial = some ([[]], final) := by
  rintro ⟨args, h⟩
  exact expressionList_yield_nonemptyWords args initial [[]] final h []
    (List.mem_singleton.mpr rfl) rfl

end Solidity.Frontend.ExpressionUniqueness
