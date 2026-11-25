import Solidity.Correctness.Lowering.Sim.Coverage.BooleanSpelling

/-! Boolean caller-local resolution for `Solidity.Goals.loweringBySimulation`.
These facts use the actual Source resolver; names need not be distinct and
locals retain their normal precedence over declarations and builtins. -/
namespace Solidity.Correctness.Lowering.Sim.Coverage.BooleanDomain

private theorem index_bool {names : List String} {x : String} (h : x ∈ names) :
    ∃ i, names.idxOf? x = some i ∧
      (names.map (fun _ => Source.STy.bool))[i]? = some .bool := by
  induction names with
  | nil => simp only [List.not_mem_nil] at h
  | cons y ys ih =>
    by_cases hy : y = x
    · subst y
      exact ⟨0, by simp only [List.idxOf?_cons, BEq.rfl, ↓reduceIte], rfl⟩
    · have hx : x ∈ ys := (List.mem_cons.mp h).resolve_left (Ne.symm hy)
      obtain ⟨i, hi, ht⟩ := ih hx
      exact ⟨i + 1, by simp only [List.idxOf?_cons, beq_iff_eq, hy, ↓reduceIte, hi, Option.map_some], by simpa only [List.map_cons, List.getElem?_cons_succ, List.getElem?_map, Option.map_eq_some_iff, and_true] using ht⟩

/-- A bound Boolean caller name resolves to a Boolean local, even if repeated. -/
theorem bound_local {Γ : Source.Ctx} {names : List String} {x : String}
    (hΓ : Γ.locals = names.map (fun y => (y, Source.STy.bool))) (hx : x ∈ names) :
    ∃ i, Γ.resolve x = some (.loc i) ∧ Γ.tys[i]? = some .bool := by
  obtain ⟨i, hi, ht⟩ := index_bool hx
  refine ⟨i, ?_, ?_⟩
  · simp only [Source.Ctx.resolve, Source.Env.resolve, hΓ, List.map_map, Function.comp_def, List.map_id_fun', id_eq, hi]
  · simpa only [Source.Ctx.tys, hΓ, List.map_map, Function.comp_def, List.getElem?_map, Option.map_eq_some_iff, and_true] using ht

/-- Actual lvalue inference succeeds at every positive fuel on a bound name. -/
theorem bound_lval_infer {Γ : Source.Ctx} {names : List String} {x : String}
    (hΓ : Γ.locals = names.map (fun y => (y, Source.STy.bool))) (hx : x ∈ names)
    (n : Nat) : ∃ d : Source.LVal Γ (.ident x) .bool,
      Source.LVal.inferN (n + 1) Γ (.ident x) = some ⟨.bool, d⟩ := by
  obtain ⟨i, hr, ht⟩ := bound_local hΓ hx
  simp only [Source.LVal.inferN]
  split
  · rename_i j hj
    have ji : j = i := by simpa only [hr, Option.some.injEq, Source.Denot.loc.injEq] using hj.symm
    subst j
    split
    · rename_i τ hτ
      have tb : τ = .bool := by simpa only [ht, Option.some.injEq] using hτ.symm
      subst τ
      exact ⟨_, rfl⟩
    · simp_all only [reduceCtorEq]
  · simp_all only [Option.some.injEq, reduceCtorEq]
  · simp_all only [Option.some.injEq, Source.Denot.loc.injEq, imp_false, forall_eq']

/-- Actual expression inference selects the bound Boolean local. -/
theorem bound_typed_infer {Γ : Source.Ctx} {names : List String} {x : String}
    (hΓ : Γ.locals = names.map (fun y => (y, Source.STy.bool))) (hx : x ∈ names)
    (n : Nat) : ∃ d : Source.Typed Γ (.ident x) .bool,
      Source.Typed.inferN (n + 1) Γ (.ident x) = some ⟨.bool, d⟩ := by
  obtain ⟨i, hr, ht⟩ := bound_local hΓ hx
  unfold Source.Typed.inferN
  dsimp only [Source.tryConst, Source.Syn.const, Option.orElse]
  split
  · rename_i j hj
    have ji : j = i := by simpa only [hr, Option.some.injEq, Source.Denot.loc.injEq] using hj.symm
    subst j
    split
    · rename_i τ hτ
      have tb : τ = .bool := by simpa only [ht, Option.some.injEq] using hτ.symm
      subst τ
      exact ⟨_, rfl⟩
    · simp_all only [reduceCtorEq]
  · simp_all only [Option.some.injEq, reduceCtorEq]
  · simp_all only [Option.some.injEq, reduceCtorEq]
  · simp_all only [Option.some.injEq, Source.Denot.loc.injEq, imp_false, forall_eq']

end Solidity.Correctness.Lowering.Sim.Coverage.BooleanDomain
