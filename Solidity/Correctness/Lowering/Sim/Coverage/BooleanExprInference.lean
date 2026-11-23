import Solidity.Correctness.Lowering.Sim.Coverage.BooleanLocals

/-! Expression inference completeness for the H1361 grammar, as a prerequisite
for `Solidity.Goals.loweringBySimulation`. These proofs use Source's actual
fuel and inference routines, without a replacement decoder. -/
namespace Solidity.Correctness.Lowering.Sim.Coverage.BooleanDomain

/-- The Boolean inference fact, including absence of a numeric constant, at
all fuels above the actual Source node count. -/
def InfersBool (Γ : Source.Ctx) (t : Source.Syn .expr) : Prop :=
  t.const = none ∧ ∀ n, t.nodes.length < n → ∃ d : Source.Typed Γ t .bool,
    Source.Typed.inferN n Γ t = some ⟨.bool, d⟩

private theorem name_infers {names : List String} {Γ : Source.Ctx} {x : String}
    (hΓ : Γ.locals = names.map (fun x => (x, Source.STy.bool))) (hx : x ∈ names) :
    InfersBool Γ (.ident x) := by
  refine ⟨rfl, ?_⟩
  intro n hn
  cases n with
  | zero => omega
  | succ n => exact bound_typed_infer hΓ hx n

private theorem bool_infers (Γ : Source.Ctx) (b : Bool) : InfersBool Γ (.lit (.bool b)) := by
  refine ⟨rfl, ?_⟩
  intro n hn
  cases n with
  | zero => omega
  | succ n => exact ⟨.bool b, rfl⟩

private theorem not_infers {Γ : Source.Ctx} {t : Source.Syn .expr} (h : InfersBool Γ t) :
    InfersBool Γ (.unaryPrefix .not t) := by
  refine ⟨rfl, ?_⟩
  intro n hn
  simp only [Source.Syn.nodes, List.length_cons] at hn
  cases n with
  | zero => omega
  | succ n =>
    obtain ⟨d, hd⟩ := h.2 n (by omega)
    unfold Source.Typed.inferN
    dsimp only [Source.tryConst, Source.Syn.const, Option.orElse]
    simp only [hd]
    exact ⟨_, rfl⟩

private theorem assign_infers {names : List String} {Γ : Source.Ctx} {x : String}
    (hΓ : Γ.locals = names.map (fun y => (y, Source.STy.bool))) (hx : x ∈ names)
    {t : Source.Syn .expr} (h : InfersBool Γ t) : InfersBool Γ (.assign .assign (.ident x) t) := by
  refine ⟨rfl, ?_⟩
  intro n hn
  simp only [Source.Syn.nodes, List.length_cons, List.length_append, List.length_nil] at hn
  cases n with
  | zero => omega
  | succ n =>
    cases n with
    | zero => omega
    | succ n =>
      obtain ⟨dl, hl⟩ := bound_lval_infer hΓ hx n
      obtain ⟨dr, hr⟩ := h.2 (n + 1) (by omega)
      unfold Source.Typed.inferN
      dsimp only [Source.tryConst, Source.Syn.const, Option.orElse]
      simp only [hl, hr]
      exact ⟨_, rfl⟩

private theorem bin_infers {Γ : Source.Ctx} {e a b : Source.Syn .expr} {k : Source.BinKind}
    (hop : e.binOp? = some (k, a, b)) (hk : k = .logic ∨ k = .eq)
    (ha : a.const = none)
    (da : Source.Typed Γ a .bool) (db : Source.Typed Γ b .bool) :
    ∃ d : Source.Typed Γ e .bool,
      Source.inferBin Γ e a b k hop (some ⟨.bool, da⟩) (some ⟨.bool, db⟩) = some ⟨.bool, d⟩ := by
  rcases hk with rfl | rfl
  · exact ⟨.logic hop da db, rfl⟩
  · unfold Source.inferBin
    split
    · simp_all only [reduceCtorEq]
    · simp_all only [reduceCtorEq]
    · exact ⟨_, rfl⟩

private theorem and_infers {Γ : Source.Ctx} {a b : Source.Syn .expr}
    (ha : InfersBool Γ a) (hb : InfersBool Γ b) : InfersBool Γ (.and a b) := by
  refine ⟨rfl, ?_⟩
  intro n hn
  simp only [Source.Syn.nodes, List.length_cons, List.length_append] at hn
  cases n with
  | zero => omega
  | succ n =>
    obtain ⟨da, hda⟩ := ha.2 n (by omega)
    obtain ⟨db, hdb⟩ := hb.2 n (by omega)
    unfold Source.Typed.inferN
    dsimp only [Source.tryConst, Source.Syn.const, Option.orElse]
    rw [hda, hdb]
    exact bin_infers rfl (Or.inl rfl) ha.1 da db

private theorem or_infers {Γ : Source.Ctx} {a b : Source.Syn .expr}
    (ha : InfersBool Γ a) (hb : InfersBool Γ b) : InfersBool Γ (.or a b) := by
  refine ⟨rfl, ?_⟩
  intro n hn
  simp only [Source.Syn.nodes, List.length_cons, List.length_append] at hn
  cases n with
  | zero => omega
  | succ n =>
    obtain ⟨da, hda⟩ := ha.2 n (by omega)
    obtain ⟨db, hdb⟩ := hb.2 n (by omega)
    unfold Source.Typed.inferN
    dsimp only [Source.tryConst, Source.Syn.const, Option.orElse]
    rw [hda, hdb]
    exact bin_infers rfl (Or.inl rfl) ha.1 da db

private theorem eq_infers {Γ : Source.Ctx} {a b : Source.Syn .expr}
    (ha : InfersBool Γ a) (hb : InfersBool Γ b) : InfersBool Γ (.equality .eq a b) := by
  refine ⟨rfl, ?_⟩
  intro n hn
  simp only [Source.Syn.nodes, List.length_cons, List.length_append] at hn
  cases n with
  | zero => omega
  | succ n =>
    obtain ⟨da, hda⟩ := ha.2 n (by omega)
    obtain ⟨db, hdb⟩ := hb.2 n (by omega)
    unfold Source.Typed.inferN
    dsimp only [Source.tryConst, Source.Syn.const, Option.orElse]
    rw [hda, hdb]
    exact bin_infers rfl (Or.inr rfl) ha.1 da db

/-- Every domain expression is spelled and inferred as Boolean by Source. -/
theorem Expr.inferred {names : List String} {Γ : Source.Ctx}
    (hΓ : Γ.locals = names.map (fun x => (x, Source.STy.bool)))
    {raw : RawExpr} (h : Expr names raw) :
    ∃ t, Total.Spells.Expr raw t ∧ InfersBool Γ t := by
  induction h with
  | name hx => exact ⟨_, .name _, name_infers hΓ hx⟩
  | bool b => exact ⟨_, .bool b, bool_infers Γ b⟩
  | assign hx _ ih =>
    obtain ⟨t, ht, hi⟩ := ih
    exact ⟨_, .assign (.name _) ht, assign_infers hΓ hx hi⟩
  | not _ ih =>
    obtain ⟨t, ht, hi⟩ := ih
    exact ⟨_, .not ht, not_infers hi⟩
  | and _ _ iha ihb =>
    obtain ⟨a, ha, hia⟩ := iha; obtain ⟨b, hb, hib⟩ := ihb
    exact ⟨_, .binop rfl ha hb rfl, and_infers hia hib⟩
  | or _ _ iha ihb =>
    obtain ⟨a, ha, hia⟩ := iha; obtain ⟨b, hb, hib⟩ := ihb
    exact ⟨_, .binop rfl ha hb rfl, or_infers hia hib⟩
  | eq _ _ iha ihb =>
    obtain ⟨a, ha, hia⟩ := iha; obtain ⟨b, hb, hib⟩ := ihb
    exact ⟨_, .binop rfl ha hb rfl, eq_infers hia hib⟩

end Solidity.Correctness.Lowering.Sim.Coverage.BooleanDomain
