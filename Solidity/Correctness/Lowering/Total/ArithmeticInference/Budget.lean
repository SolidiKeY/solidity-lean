import Solidity.Correctness.Lowering.Total.ArithmeticInference.Fragment
import Solidity.Correctness.Lowering.Total.CalleeInference.Args

/-!
# Structural fuel and the argument budgets

`depth e` is at most the node count of the spelling (`depth_le_nodes`, for
every spelled model expression), and argument `i` of a spelled list fits the
list's node count less `i + 2` (`arg_nodes`, `args_budget`). So the family in
order meets the per-argument premises of `CalleeInference.alias_inferN` at the
budgets `n - 1 - i` (`args_inferN`, `args_inferN_nodes`) and those of
`alias_infer` at `args.nodes.length + 2 - i` (`args_infer`); `exprs_get`
relates the model list to `argExprs` position by position.
-/

namespace Solidity.Correctness.Lowering.Total.ArithmeticInference

open Source (STy Syn Typed Q)
open Decode (Tables)
open CalleeInference (argExprs)

variable {Γ : Source.Ctx} {T : Tables}

/-- Every syntax tree has a node. -/
theorem nodes_pos {c : Source.Cat} (s : Syn c) : 0 < s.nodes.length := by
  cases s <;> simp [Syn.nodes]

theorem binop_nodes {op : BinOp} {f : Syn .expr → Syn .expr → Syn .expr}
    (h : Decode.binop op = some f) (a b : Syn .expr) :
    (f a b).nodes.length = a.nodes.length + b.nodes.length + 1 := by
  cases op <;> cases h <;> simp [Syn.nodes] <;> omega

theorem expr_unop_nodes {op : UnOp} {a : RawExpr} {s : Syn .expr}
    (hs : T.expr (.unop op a) = some s) :
    ∃ sa, T.expr a = some sa ∧ sa.nodes.length + 1 ≤ s.nodes.length := by
  cases h : T.expr a with
  | none => cases op <;> simp [Tables.expr, h] at hs
  | some sa =>
    refine ⟨sa, rfl, ?_⟩
    cases op <;> simp [Tables.expr, h] at hs <;> subst hs <;> simp [Syn.nodes] <;> omega

/-- **Structural fuel**: the fuel a spelled expression needs is at most its
node count (for every model expression, in or out of the family). -/
theorem depth_le_nodes {e : RawExpr} : ∀ {s : Syn .expr}, T.expr e = some s →
    depth e ≤ s.nodes.length := by
  induction e using depth.induct with
  | case1 op a b h => intro s _; rw [depth, if_pos h]; exact nodes_pos s
  | case2 op a b h iha ihb =>
    intro s hs
    obtain ⟨f, sa, sb, hf, hsa, hsb, rfl⟩ := expr_binop.mp hs
    have := iha hsa; have := ihb hsb
    rw [depth, if_neg h, binop_nodes hf, Nat.add_le_add_iff_right, Nat.max_le]
    omega
  | case3 op a h => intro s _; rw [depth, if_pos h]; exact nodes_pos s
  | case4 op a h ih =>
    intro s hs
    obtain ⟨sa, hsa, hle⟩ := expr_unop_nodes hs
    have := ih hsa
    rw [depth, if_neg h]; omega
  | case5 t h1 h2 =>
    intro s _
    cases t <;> first | (simp only [depth]; exact nodes_pos s) | exact (h1 _ _ _ rfl).elim
                      | exact (h2 _ _ rfl).elim

/-- A positional argument's nodes, its position and the list's two closing
nodes fit in the list. -/
theorem arg_nodes : ∀ {args : Syn (.list .expr)} {i : Nat} {a : Syn .expr},
    (argExprs args)[i]? = some a → a.nodes.length + i + 2 ≤ args.nodes.length
  | .nil, _, _, h => by simp [argExprs] at h
  | .cons e es, 0, _, h => by
      simp only [argExprs, List.getElem?_cons_zero, Option.some.injEq] at h
      subst h; have := nodes_pos es; simp [Syn.nodes]; omega
  | .cons e es, i + 1, _, h => by
      have := arg_nodes (args := es) (i := i) (by simpa [argExprs] using h)
      have := nodes_pos e; simp [Syn.nodes]; omega

theorem exprs_cons {e : RawExpr} {es : List RawExpr} {args : Syn (.list .expr)} :
    T.exprs (e :: es) = some args ↔
      ∃ a as, T.expr e = some a ∧ T.exprs es = some as ∧ args = .cons a as := by
  cases h1 : T.expr e <;> cases h2 : T.exprs es <;> simp [Tables.exprs, h1, h2, eq_comm]

/-- The spelled argument list is the model list, position by position. -/
theorem exprs_get : ∀ {es : List RawExpr} {args : Syn (.list .expr)}, T.exprs es = some args →
    (argExprs args).length = es.length ∧
      ∀ (i : Nat) a, (argExprs args)[i]? = some a → ∃ e, es[i]? = some e ∧ T.expr e = some a
  | [], args, h => by
      simp only [Tables.exprs, Option.some.injEq] at h; subst h
      exact ⟨by simp [argExprs], fun i a hi => by simp [argExprs] at hi⟩
  | e :: es, args, h => by
      obtain ⟨a, as, ha, has, rfl⟩ := exprs_cons.mp h
      obtain ⟨hl, hg⟩ := exprs_get has
      refine ⟨by simp [argExprs, hl], fun i b hi => ?_⟩
      cases i with
      | zero =>
        simp only [argExprs, List.getElem?_cons_zero, Option.some.injEq] at hi
        subst hi; exact ⟨e, rfl, ha⟩
      | succ i => simpa using hg i b (by simpa [argExprs] using hi)

variable {es : List RawExpr} {σs : List STy} {args : Syn (.list .expr)} {n : Nat}

/-- **The position-dependent budget is structural**: argument `i` needs at
most the list's node count less `i + 2`. -/
theorem args_budget (hs : T.exprs es = some args) {i : Nat} {e : RawExpr}
    (hi : es[i]? = some e) : depth e + i + 2 ≤ args.nodes.length := by
  obtain ⟨hl, hg⟩ := exprs_get hs
  have hlt : i < (argExprs args).length := by
    rw [hl]; exact (List.getElem?_eq_some_iff.mp hi).1
  obtain ⟨e', he', ha⟩ := hg i _ (List.getElem?_eq_getElem hlt)
  cases hi.symm.trans he'
  have := depth_le_nodes ha
  have := arg_nodes (List.getElem?_eq_getElem hlt)
  omega

/-- **Arithmetic arguments at the fuels `TypedArgs.inferN n` passes**: the
length and per-position premises of `CalleeInference.alias_inferN`, from the
family in order and each position's budget `n - 1 - i`. -/
theorem args_inferN (hs : T.exprs es = some args) (hlen : σs.length = es.length)
    (hty : ∀ (i : Nat) e σ, es[i]? = some e → σs[i]? = some σ → Infers Γ e σ)
    (hfuel : ∀ (i : Nat) e, es[i]? = some e → depth e ≤ n - 1 - i) :
    σs.length = (argExprs args).length ∧
      ∀ (i : Nat) a σ, (argExprs args)[i]? = some a → σs[i]? = some σ →
        ∃ d, Typed.inferN (n - 1 - i) Γ a = some ⟨σ, d⟩ := by
  obtain ⟨hl, hg⟩ := exprs_get hs
  refine ⟨hlen.trans hl.symm, fun i a σ hi hσ => ?_⟩
  obtain ⟨e, he, ha⟩ := hg i a hi
  exact (hty i e σ he hσ).inferN_of_le ha (hfuel i e he)

/-- The same with the budgets discharged by the list's node count. -/
theorem args_inferN_nodes (hs : T.exprs es = some args) (hlen : σs.length = es.length)
    (hty : ∀ (i : Nat) e σ, es[i]? = some e → σs[i]? = some σ → Infers Γ e σ)
    (hn : args.nodes.length ≤ n + 1) :
    σs.length = (argExprs args).length ∧
      ∀ (i : Nat) a σ, (argExprs args)[i]? = some a → σs[i]? = some σ →
        ∃ d, Typed.inferN (n - 1 - i) Γ a = some ⟨σ, d⟩ :=
  args_inferN hs hlen hty fun i e he => by have := args_budget hs he; omega

/-- **Arithmetic arguments at `Typed.infer`'s fuel**: the premises of
`CalleeInference.alias_infer`, position `i` at `args.nodes.length + 2 - i`,
with no fuel hypothesis. -/
theorem args_infer (hs : T.exprs es = some args) (hlen : σs.length = es.length)
    (hty : ∀ (i : Nat) e σ, es[i]? = some e → σs[i]? = some σ → Infers Γ e σ) :
    σs.length = (argExprs args).length ∧
      ∀ (i : Nat) a σ, (argExprs args)[i]? = some a → σs[i]? = some σ →
        ∃ d, Typed.inferN (args.nodes.length + 2 - i) Γ a = some ⟨σ, d⟩ := by
  obtain ⟨hl, hg⟩ := exprs_get hs
  refine ⟨hlen.trans hl.symm, fun i a σ hi hσ => ?_⟩
  obtain ⟨e, he, ha⟩ := hg i a hi
  exact (hty i e σ he hσ).inferN_of_le ha (by have := args_budget hs he; omega)

end Solidity.Correctness.Lowering.Total.ArithmeticInference
