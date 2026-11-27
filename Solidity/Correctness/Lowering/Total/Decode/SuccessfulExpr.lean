import Solidity.Correctness.Lowering.Total.Decode.Calls
import Solidity.Syntax.Elab.Measure
import Solidity.Correctness.Lowering.Total.Versions.Self

/-!
One-step facts for the actual Source inference procedure. Child equations are
explicit local obligations, not a completeness assumption for producer inputs.
The successful-producer composition must discharge them at the required fuel.
-/
namespace Solidity.Correctness.Lowering.Total.Decode.SuccessfulExpr

open Source (Syn STy Ctx Typed LVal)

variable {Γ : Source.Ctx} {n : Nat} {a : Syn .expr} {τ : STy}

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

/-- Nonempty tuple tails use their inferred slot types, preserving mobility. -/
theorem inferN_tuple {b : Syn (.opt .expr)} {bs : Syn (.list (.opt .expr))}
    {σ : STy} {σs : List STy} {d : Typed Γ a τ}
    {ds : Source.TypedSlots Γ (.cons b bs) (σ :: σs)}
    (ha : Typed.inferN n Γ a = some ⟨τ, d⟩)
    (hs : Source.TypedSlots.inferN n Γ (.cons b bs) = some ⟨σ :: σs, ds⟩) :
    Typed.inferN (n + 1) Γ (.tuple (.some a) (.cons b bs)) =
      some ⟨_, .tuple d ds (List.cons_ne_nil σ σs)⟩ := by
  show (Typed.inferN n Γ a >>= _) = _
  simp [ha, hs]

/-- Builtin environment-member dispatch retains its admission and msg.value
context checks. These are resolution facts, not an inference assumption. -/
theorem tryMagic_of {g m feature : String} {b : Source.Builtin}
    (hr : Γ.resolve g = some (.builtin b))
    (hs : b.memberStatus m = some (.admitted feature)) (ht : b.memberTy m = some τ)
    (hv : (b == .msg && m == "value" && !Γ.msgValue) = false) :
    Source.tryMagic Γ g m = some ⟨τ, .magic hr hs ht hv⟩ := by
  unfold Source.tryMagic
  split
  · rename_i b' hb
    have he : b' = b := by rw [hr] at hb; cases hb; rfl
    subst b'
    split
    · rename_i feature' τ' hs' ht'
      have he : τ' = τ := Option.some.inj (ht'.symm.trans ht)
      subst τ'
      have he : feature' = feature := by rw [hs] at hs'; cases hs'; rfl
      subst feature'
      simp [hv]
    · simp_all
  · simp_all

/-- The actual expression inference procedure takes the admitted magic-member
branch before trying ordinary member access. -/
theorem inferN_magic {g m feature : String} {b : Source.Builtin}
    (hr : Γ.resolve g = some (.builtin b))
    (hs : b.memberStatus m = some (.admitted feature)) (ht : b.memberTy m = some τ)
    (hv : (b == .msg && m == "value" && !Γ.msgValue) = false) :
    Typed.inferN (n + 1) Γ (.member (.ident g) m) = some ⟨τ, .magic hr hs ht hv⟩ := by
  show (Source.tryMagic Γ g m).orElse _ = _
  rw [tryMagic_of hr hs ht hv]; rfl

/-- `this` inference uses actual builtin resolution and the current scope. -/
theorem inferN_this {c : String} (hr : Γ.resolve "this" = some (.builtin .this))
    (hc : Γ.scope = some c) :
    Typed.inferN (n + 1) Γ (.ident "this") = some ⟨_, .this hr hc⟩ := by
  show Option.orElse none _ = _
  simp only [Option.orElse]
  split
  all_goals try (rename_i h; rw [hr] at h; cases h)
  · simp only [dite_true]
    split
    · rename_i c' hc'
      have he : c' = c := Option.some.inj (hc'.symm.trans hc)
      subst c'; rfl
    · simp_all
  · simp_all

/-- Infer the landed self-address spelling with its existing derivation. -/
theorem inferN_thisAddress {c : String} (hr : Γ.resolve "this" = some (.builtin .this))
    (hc : Γ.scope = some c) : Typed.inferN (n + 2) Γ thisAddress =
      some ⟨.address false, Version.Self.typedAddress Γ hr hc⟩ := by
  show (Typed.inferN (n + 1) Γ (.ident "this") >>= _) = _
  rw [inferN_this hr hc]; rfl

/-- Infer the landed own-balance spelling with its existing derivation. -/
theorem inferN_thisBalance {c : String} (hr : Γ.resolve "this" = some (.builtin .this))
    (hc : Γ.scope = some c) : Typed.inferN (n + 3) Γ thisBalance =
      some ⟨.int Source.IntTy.u256, Version.Self.typedBalance Γ hr hc⟩ := by
  show (Typed.inferN (n + 2) Γ thisAddress >>= _) = _
  rw [inferN_thisAddress hr hc]; rfl

open CallSpellExt ElabControlProof

/-- Spelling each residual argument constructs the registered decoder's list,
including child calls claimed by its registry. -/
theorem exprs_of_each {T : Tables} {R : Registry} (es : List RawExpr)
    (h : ∀ e ∈ es, ∃ t, ExprX T R e t) :
    ∃ ts, ExprsX T R es ts ∧ Calls.exprs T R es = some ts := by
  induction es with
  | nil => exact ⟨.nil, .nil, rfl⟩
  | cons e es ih =>
    obtain ⟨t, ht⟩ := h e (by simp)
    obtain ⟨ts, hs, _⟩ := ih (fun x hx => h x (by simp [hx]))
    exact ⟨.cons t ts, .cons ht hs, Calls.of_spellings (.cons ht hs)⟩

/-- The registered bytes spelling recognizes every numeral list without
assuming decoding succeeds, including empty and non-byte-sized components. -/
theorem bytes_call {T : Tables} {R : Registry}
    (hr : R.lookup bytesLitName = some bytesSpelling) (bs : List Nat) :
    Calls.expr T R (.bytesLit bs) = some (BytesLiteral.spelling bs) := by
  have hb : (RawExpr.bytesLit bs).bytesLit? = some bs := by
    simp only [RawExpr.bytesLit, RawExpr.bytesLit?, beq_self_eq_true, ite_true]
    induction bs with
    | nil => rfl
    | cons b bs ih => simp [List.mapM_cons, ih]
  simp only [RawExpr.bytesLit, Calls.expr, hr]
  change ((RawExpr.bytesLit bs).bytesLit?).map BytesLiteral.spelling = _
  rw [hb]; rfl

/-- Source infers the normalized registered literal as its string-literal type.
Contextual conversion/range and value faithfulness remain separate obligations. -/
theorem inferN_bytes (bs : List Nat) :
    Typed.inferN (n + 1) Γ (BytesLiteral.spelling bs) =
      some ⟨_, .hexStr (BytesLiteral.bytes bs)⟩ := rfl

variable {T : Tables} {R : Registry} (C : Contract) [FreshNames]

/-- Actual capture preserves spelling: its successful result is the original
expression or a generated local name. No Source typing claim is made here. -/
theorem capture_spells {e : RawExpr} {t : Syn .expr} (he : ExprX T R e t) :
    ElabControlProof.Obs (captureExpr C e) (fun out => ∃ t, ExprX T R out.2 t) := by
  intro sc st m out st' m' run
  rcases ElabCallArgsGood.captureExpr_shape C e sc st m out st' m' run with h | ⟨x, h⟩
  · exact h ▸ ⟨t, he⟩
  · exact h ▸ ⟨.ident x, .name x⟩

/-- Effect-aware capture uses the same two spelling-preserving result forms. -/
theorem captureBefore_spells {e : RawExpr} {t : Syn .expr} (later : List RawExpr)
    (he : ExprX T R e t) :
    ElabControlProof.Obs (captureBefore C e later) (fun out => ∃ t, ExprX T R out.2 t) := by
  intro sc st m out st' m' run
  rcases ElabCallArgsGood.captureBefore_shape C e later sc st m out st' m' run with h | ⟨x, h⟩
  · exact h ▸ ⟨t, he⟩
  · exact h ▸ ⟨.ident x, .name x⟩

/-- Ordinary argument hoisting: the callback obligations concern its actual
successful runs, at every state, rather than an assumed decoder result. -/
theorem hoistArgs_spells (H : RawExpr → ElabM (SProg C × RawExpr))
    (args : List RawExpr)
    (hh : ∀ a ∈ args, ElabControlProof.Obs (H a) (fun out => ∃ t, ExprX T R out.2 t)) :
    ElabControlProof.Obs (hoistArgsWith C H args)
      (fun out => ∃ ts, ExprsX T R out.2 ts ∧ Calls.exprs T R out.2 = some ts) := by
  intro sc st m out st' m' run
  exact exprs_of_each _ (ElabCallArgsGood.ordinary_good C
    (fun e => ∃ t, ExprX T R e t) (fun x => ⟨_, .name x⟩)
    H args hh sc st m out st' m' run)

/-- Full call argument preparation, including captures and late reference
copies, composes the original-child and actual-callback spelling obligations. -/
theorem hoistCallArgs_spells (H : RawExpr → ElabM (SProg C × RawExpr))
    (stmt : RawStmt → ElabM (SProg C)) (f : String) (args : List RawExpr)
    (hin : ∀ a ∈ args, ∃ t, ExprX T R a t)
    (hh : ∀ a ∈ args, ElabControlProof.Obs (H a) (fun out => ∃ t, ExprX T R out.2 t)) :
    ElabControlProof.Obs (hoistCallArgsWith C H stmt f args)
      (fun out => ∃ ts, ExprsX T R out.2 ts ∧ Calls.exprs T R out.2 = some ts) := by
  intro sc st m out st' m' run
  exact exprs_of_each _ (ElabCallArgsGood.hoistCallArgsWith_preserves C
    (fun e => ∃ t, ExprX T R e t) (fun x => ⟨_, .name x⟩)
    H stmt f args hin hh sc st m out st' m' run)

end Solidity.Correctness.Lowering.Total.Decode.SuccessfulExpr
