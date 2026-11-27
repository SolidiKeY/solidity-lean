import Solidity.Source.Infer

/-!
One-step facts for the actual Source inference procedure. Child equations are
explicit local obligations, not a completeness assumption for producer inputs.
The successful-producer composition must discharge them at the required fuel.
-/
namespace Solidity.Correctness.Lowering.Total.Decode.SuccessfulExpr

open Source (Syn STy Ctx Typed LVal)

variable {Γ : Ctx} {n : Nat} {a : Syn .expr} {τ : STy}

/-- Prefix increment reads a numeric lvalue at the recursive fuel. -/
theorem inferN_preInc {l : LVal Γ a τ}
    (h : LVal.inferN n Γ a = some ⟨τ, l⟩) (hn : τ.isNumeric = true) :
    Typed.inferN (n + 1) Γ (.unaryPrefix .inc a) =
      some ⟨τ, .incDec (Or.inl rfl) l hn⟩ := by
  show (LVal.inferN n Γ a >>= _) = _
  simp [h, hn]

/-- Prefix decrement uses the same lvalue admission check. -/
theorem inferN_preDec {l : LVal Γ a τ}
    (h : LVal.inferN n Γ a = some ⟨τ, l⟩) (hn : τ.isNumeric = true) :
    Typed.inferN (n + 1) Γ (.unaryPrefix .dec a) =
      some ⟨τ, .incDec (Or.inr rfl) l hn⟩ := by
  show (LVal.inferN n Γ a >>= _) = _
  simp [h, hn]

/-- Both suffix operations preserve the inferred numeric lvalue type. -/
theorem inferN_suffix (op : Source.SuffixOp) {l : LVal Γ a τ}
    (h : LVal.inferN n Γ a = some ⟨τ, l⟩) (hn : τ.isNumeric = true) :
    Typed.inferN (n + 1) Γ (.unarySuffix op a) =
      some ⟨τ, .incDecSuffix l hn⟩ := by
  show (LVal.inferN n Γ a >>= _) = _
  simp [h, hn]

/-- A nonnumeric lvalue is refused, even if lvalue inference succeeds. -/
theorem inferN_suffix_refused (op : Source.SuffixOp) {l : LVal Γ a τ}
    (h : LVal.inferN n Γ a = some ⟨τ, l⟩) (hn : τ.isNumeric = false) :
    Typed.inferN (n + 1) Γ (.unarySuffix op a) = none := by
  show (LVal.inferN n Γ a >>= _) = _
  simp [h, hn]

/-- Deletion retains both Source refusal guards. -/
theorem inferN_delete {l : LVal Γ a τ}
    (h : LVal.inferN n Γ a = some ⟨τ, l⟩)
    (hm : τ.isMapping = false) (hp : Γ.deleteRefused τ a = false) :
    Typed.inferN (n + 1) Γ (.unaryPrefix .delete a) =
      some ⟨_, .delete l hm hp⟩ := by
  show (LVal.inferN n Γ a >>= _) = _
  simp [h, hm, hp]

/-- Inline arrays keep the inferred common type and all element-fit checks. -/
theorem inferN_inlineArray {xs : Syn (.list .expr)} {τs : List STy} {σ : STy}
    {d : Typed Γ a τ} {ds : Source.TypedArgs Γ xs τs}
    (ha : Typed.inferN n Γ a = some ⟨τ, d⟩)
    (hs : Source.TypedArgs.inferN n Γ xs = some ⟨τs, ds⟩)
    (hc : STy.commonOf Γ.isBase Γ.mapFree τ τs = some σ)
    (hw : σ.oneWord = true)
    (hf : Source.argsFit Γ.isBase Γ.mapFree (τ :: τs)
      (List.replicate (τs.length + 1) σ) = true) :
    Typed.inferN (n + 1) Γ (.inlineArray a xs) =
      some ⟨_, .inlineArray d ds hc hw hf⟩ := by
  show (Typed.inferN n Γ a >>= _) = _
  simp only [ha, hs, Option.bind_eq_bind, Option.bind_some]
  split
  · rename_i ρ hρ
    have he : ρ = σ := Option.some.inj (hρ.symm.trans hc)
    subst ρ
    simp [hw, hf]
  · rename_i hρ
    rw [hc] at hρ
    cases hρ

/-- Allocation checks the decoded memory type before inferring its size. -/
theorem inferN_newArray {t : Syn .typeName} {σ : STy} {d : Typed Γ a σ}
    (ht : t.ty Γ.env Γ.scope .memory = some τ) (hn : τ.newable = true)
    (ha : Typed.inferN n Γ a = some ⟨σ, d⟩) (hi : σ.isIndex = true) :
    Typed.inferN (n + 1) Γ (.call (.new t) (.positional (.cons a .nil))) =
      some ⟨τ, .newArray ht hn d hi⟩ := by
  change (match ht' : t.ty Γ.env Γ.scope .memory with
    | some ρ => if hn' : ρ.newable = true then do
        let ⟨σ', d'⟩ ← Typed.inferN n Γ a
        if hi' : σ'.isIndex = true then
          pure (⟨ρ, Typed.newArray ht' hn' d' hi'⟩ :
            Source.Inferred Γ (.call (.new t) (.positional (.cons a .nil)))) else none
      else none
    | none => none) = _
  split
  · rename_i ρ hρ
    have he : ρ = τ := Option.some.inj (hρ.symm.trans ht)
    subst ρ
    simp [hn, ha, hi]
  · rename_i hρ
    rw [ht] at hρ
    cases hρ

end Solidity.Correctness.Lowering.Total.Decode.SuccessfulExpr
