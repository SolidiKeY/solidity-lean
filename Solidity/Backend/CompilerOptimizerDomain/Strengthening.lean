import Solidity.Backend.AbiWorld.PublicCompilerTotal
import Solidity.Optimizer.UnusedVar

/-! Successful strengthening of accepted inputs preserves the accepted domain. -/
namespace Solidity.Backend.CompilerOptimizerDomain
open Solidity Solidity.Optimizer.ConstFold
open Solidity.Backend.AbiWorld.PublicCompilerTotal
variable {C : Contract}

theorem val_str_ok {Γ Δ : Ctx} (w : Thin Γ Δ) : {p : PrimTy} →
    {v : Val C Δ p} → {v' : Val C Γ p} → ValOk v → Val.str? w v = some v' → ValOk v'
  | _, _, _, .lit n h, e => by
      simp only [Val.str?, Simple.str?, Option.map_some, Option.some.injEq] at e
      cases e; exact .lit n h
  | _, _, _, .bool b, e => by cases e; exact .bool b
  | _, _, _, .local i, e => by
      simp only [Val.str?, Simple.str?, Option.map_eq_some_iff] at e
      obtain ⟨_, ⟨j, _, rfl⟩, rfl⟩ := e
      exact .local j
  | _, _, _, .env k hp hk, e => by
      simp only [Val.str?, Simple.str?, Option.map_some, Option.some.injEq] at e
      cases e; exact .env k hp hk
  | _, _, _, .read _, e => nomatch e
  | _, _, _, .len .., e => nomatch e
  | _, _, _, .binop op h hq ha hb, e => by
      simp only [Val.str?] at e
      split at e <;> try contradiction
      cases e; exact .binop op h hq (val_str_ok w ha ‹_›) (val_str_ok w hb ‹_›)
  | _, _, _, .unop op h hq ha, e => by
      simp only [Val.str?, Option.map_eq_some_iff] at e
      obtain ⟨_, he, rfl⟩ := e
      exact .unop op h hq (val_str_ok w ha he)
  | _, _, _, .ternary hc ha hb, e => by
      simp only [Val.str?] at e
      split at e <;> try contradiction
      cases e; exact .ternary (val_str_ok w hc ‹_›) (val_str_ok w ha ‹_›) (val_str_ok w hb ‹_›)

mutual
/-- Successful accepted statements contain no alias-kind operations. -/
theorem stmt_str_ok : {Δ Δ' : Ctx} → {K K' : Kinds} → {s : Solidity.Stmt C Δ Δ'} →
    StmtOk K s K' → {Γ : Ctx} → (w : Thin Γ Δ) →
    {r : (Γ' : Ctx) × Thin Γ' Δ' × Solidity.Stmt C Γ Γ'} → Stmt.str? w s = some r →
    (L : Kinds) → ∃ L', StmtOk L r.2.2 L'
  | _, _, _, _, _, .assign .., _, _, _, e, _ => nomatch e
  | _, _, _, _, _, .assignLocal i hv, _, w, _, e, L => by
      simp only [Stmt.str?] at e
      split at e <;> try contradiction
      cases e; exact ⟨L, .assignLocal _ (val_str_ok w hv ‹_›)⟩
  | _, _, _, _, _, .declNone p x, _, _, _, e, L => by cases e; exact ⟨false :: L, .declNone p x⟩
  | _, _, _, _, _, .declSome p x hv, _, w, _, e, L => by
      simp only [Stmt.str?, Option.map_eq_some_iff] at e
      obtain ⟨_, he, rfl⟩ := e
      exact ⟨false :: L, .declSome p x (val_str_ok w hv he)⟩
  | _, _, _, _, _, .declStorage .., _, _, _, e, _ => nomatch e
  | _, _, _, _, _, .declIndexed .., _, _, _, e, _ => nomatch e
  | _, _, _, _, _, .rebind .., _, _, _, e, _ => nomatch e
  | _, _, _, _, _, .rebindIndexed .., _, _, _, e, _ => nomatch e
  | _, _, _, _, _, .opAssign .., _, _, _, e, _ => nomatch e
  | _, _, _, _, _, .incDec .., _, _, _, e, _ => nomatch e
  | _, _, _, _, _, .require hc, _, w, _, e, L => by
      simp only [Stmt.str?, Option.map_eq_some_iff] at e
      obtain ⟨_, he, rfl⟩ := e
      exact ⟨L, .require (val_str_ok w hc he)⟩
  | _, _, _, _, _, .assert hc, _, w, _, e, L => by
      simp only [Stmt.str?, Option.map_eq_some_iff] at e
      obtain ⟨_, he, rfl⟩ := e
      exact ⟨L, .assert (val_str_ok w hc he)⟩
  | _, _, _, _, _, .revert, _, _, _, e, L => by cases e; exact ⟨L, .revert⟩
  | _, _, _, _, _, .callNone .., _, _, _, e, _ => nomatch e
  | _, _, _, _, _, .callVal .., _, _, _, e, _ => nomatch e
  | _, _, _, _, _, .ite hc ht he, _, w, _, e, L => by
      simp only [Stmt.str?] at e
      split at e <;> try contradiction
      cases e
      exact ⟨L, .ite (val_str_ok w hc ‹_›) (prog_str_ok ht w ‹_› L) (prog_str_ok he w ‹_› L)⟩
  | _, _, _, _, _, .block hb, _, w, _, e, L => by
      simp only [Stmt.str?] at e
      split at e <;> try contradiction
      cases e; exact ⟨L, .block (prog_str_ok hb w ‹_› L)⟩
  | _, _, _, _, _, .loop .., _, _, _, e, _ => nomatch e

theorem prog_str_ok : {Δ Δ' : Ctx} → {K : Kinds} → {P : Solidity.Prog C Δ Δ'} →
    ProgOk K P → {Γ : Ctx} → (w : Thin Γ Δ) → {r : Str C Γ Δ'} →
    Prog.str? w P = some r → (L : Kinds) → ProgOk L r.2.2
  | _, _, _, _, .nil, _, _, _, e, _ => by cases e; exact .nil
  | _, _, _, _, .cons hs hp, _, w, _, e, L => by
      simp only [Prog.str?] at e
      split at e <;> try contradiction
      split at e <;> try contradiction
      cases e
      obtain ⟨L', hs'⟩ := stmt_str_ok hs w ‹_› L
      exact .cons hs' (prog_str_ok hp _ ‹_› L')
end

end Solidity.Backend.CompilerOptimizerDomain
