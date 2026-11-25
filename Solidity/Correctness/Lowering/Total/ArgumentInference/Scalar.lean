import Solidity.Source.Infer

/-!
# Exact inference of literal, local and Boolean arguments

One step of the actual `Source.Typed.inferN`: a decimal literal infers to its
constant type (`inferN_num`), a Boolean literal to `bool` (`inferN_bool`), a name
resolving to local slot `i` of slot type `τ` to `τ` (`inferN_loc`), and `!`, `&&`,
`||`, `==`/`!=`, `?:` over Boolean operands to `bool`. `BoolArg` (arbitrary
nesting) and `ScalarArg` infer at every fuel above their node count to one fixed
derivation (`BoolArg.inferN`, `ScalarArg.inferN`): the bound comes from the
syntax, no monotonicity is assumed. Boundaries: an unresolved name, a non-Boolean
`!` operand (`inferN_ident_none`, `inferN_not_none`).
-/
namespace Solidity.Correctness.Lowering.Total.ArgumentInference

open Source (STy Syn Ctx Typed NumLit EqOp)

variable {Γ : Ctx} {k : Nat}

/-! ## One step of the actual inference -/

/-- A decimal literal is a constant: its exact value as its type. -/
theorem inferN_num (m f : Nat) (x : Int) :
    Typed.inferN (k + 1) Γ (.lit (.num (.dec m f x))) =
      some ⟨.rational (NumLit.dec m f x).value, .const rfl rfl rfl⟩ := rfl

theorem inferN_bool (b : Bool) :
    Typed.inferN (k + 1) Γ (.lit (.bool b)) = some ⟨.bool, .bool b⟩ := rfl

/-- A name resolving to local slot `i` of type `τ` reads at `τ`. -/
theorem inferN_loc {x : String} {i : Nat} {τ : STy} (hr : Γ.resolve x = some (.loc i))
    (ht : Γ.tys[i]? = some τ) : Typed.inferN (k + 1) Γ (.ident x) = some ⟨τ, .loc hr ht⟩ := by
  show Option.orElse none _ = _
  simp only [Option.orElse]; split
  · rename_i j hj; obtain rfl : j = i := by rw [hr] at hj; cases hj; rfl
    split
    · rename_i σ hσ; obtain rfl : σ = τ := by rw [ht] at hσ; cases hσ; rfl
      rfl
    · rename_i hσ; rw [ht] at hσ; cases hσ
  any_goals (rename_i h; rw [hr] at h; cases h)
  rename_i h _ _; exact (h i hr).elim

/-- Missing local: an unresolved name has no type. -/
theorem inferN_ident_none {x : String} (hr : Γ.resolve x = none) :
    Typed.inferN k Γ (.ident x) = none := by
  cases k; · rfl
  show Option.orElse none _ = _
  simp only [Option.orElse]; split
  any_goals (rename_i h; rw [hr] at h; cases h)
  rfl

variable {a b c : Syn .expr}

theorem inferN_not {d : Typed Γ a .bool} (h : Typed.inferN k Γ a = some ⟨.bool, d⟩) :
    Typed.inferN (k + 1) Γ (.unaryPrefix .not a) = some ⟨.bool, .not d⟩ := by
  show (Typed.inferN k Γ a >>= _) = _
  rw [h]; rfl

/-- Wrong type: `!a` with `a` inferred at a non-Boolean type fails. -/
theorem inferN_not_none {τ : STy} {d : Typed Γ a τ} (h : Typed.inferN k Γ a = some ⟨τ, d⟩)
    (hτ : τ ≠ .bool) : Typed.inferN (k + 1) Γ (.unaryPrefix .not a) = none := by
  show (Typed.inferN k Γ a >>= _) = _
  rw [h]; cases τ <;> first | rfl | exact absurd rfl hτ

theorem inferN_and {da : Typed Γ a .bool} {db : Typed Γ b .bool}
    (ha : Typed.inferN k Γ a = some ⟨.bool, da⟩) (hb : Typed.inferN k Γ b = some ⟨.bool, db⟩) :
    Typed.inferN (k + 1) Γ (.and a b) = some ⟨.bool, .logic rfl da db⟩ := by
  show Source.inferBin Γ (.and a b) a b .logic rfl (Typed.inferN k Γ a) (Typed.inferN k Γ b) = _
  rw [ha, hb]; rfl

theorem inferN_or {da : Typed Γ a .bool} {db : Typed Γ b .bool}
    (ha : Typed.inferN k Γ a = some ⟨.bool, da⟩) (hb : Typed.inferN k Γ b = some ⟨.bool, db⟩) :
    Typed.inferN (k + 1) Γ (.or a b) = some ⟨.bool, .logic rfl da db⟩ := by
  show Source.inferBin Γ (.or a b) a b .logic rfl (Typed.inferN k Γ a) (Typed.inferN k Γ b) = _
  rw [ha, hb]; rfl

theorem inferN_cond {dc : Typed Γ c .bool} {da : Typed Γ a .bool} {db : Typed Γ b .bool}
    (hc : Typed.inferN k Γ c = some ⟨.bool, dc⟩)
    (ha : Typed.inferN k Γ a = some ⟨.bool, da⟩) (hb : Typed.inferN k Γ b = some ⟨.bool, db⟩) :
    Typed.inferN (k + 1) Γ (.cond c a b) = some ⟨.bool, .cond dc da db rfl⟩ := by
  show (Typed.inferN k Γ c >>= _) = _
  rw [hc]; show (Typed.inferN k Γ a >>= _) = _
  rw [ha]; show (Typed.inferN k Γ b >>= _) = _
  rw [hb]; rfl

/-! ## The families -/

/-- **Boolean arguments**: Boolean literals and locals whose slot type is
`bool`, closed under `!`, `&&`, `||`, `==`/`!=` and `?:`, nested arbitrarily. -/
inductive BoolArg (Γ : Ctx) : Syn .expr → Prop
  | lit (b : Bool) : BoolArg Γ (.lit (.bool b))
  | loc {x : String} {i : Nat} : Γ.resolve x = some (.loc i) → Γ.tys[i]? = some .bool →
      BoolArg Γ (.ident x)
  | not {a : Syn .expr} : BoolArg Γ a → BoolArg Γ (.unaryPrefix .not a)
  | and {a b : Syn .expr} : BoolArg Γ a → BoolArg Γ b → BoolArg Γ (.and a b)
  | or {a b : Syn .expr} : BoolArg Γ a → BoolArg Γ b → BoolArg Γ (.or a b)
  | eq (op : EqOp) {a b : Syn .expr} : BoolArg Γ a → BoolArg Γ b → BoolArg Γ (.equality op a b)
  | cond {c a b : Syn .expr} : BoolArg Γ c → BoolArg Γ a → BoolArg Γ b → BoolArg Γ (.cond c a b)

/-- **Scalar arguments** with their inferred type: decimal number literals at
their constant type, locals at their slot type, Boolean arguments at `bool`. -/
inductive ScalarArg (Γ : Ctx) : Syn .expr → STy → Prop
  | num (m f : Nat) (x : Int) :
      ScalarArg Γ (.lit (.num (.dec m f x))) (.rational (NumLit.dec m f x).value)
  | loc {x : String} {i : Nat} {τ : STy} : Γ.resolve x = some (.loc i) → Γ.tys[i]? = some τ →
      ScalarArg Γ (.ident x) τ
  | bool {e : Syn .expr} : BoolArg Γ e → ScalarArg Γ e .bool

/-- The equality step over Boolean operands: the left operand is no constant
(`compareConst` does not fire), and `bool` has equality. -/
theorem inferBin_eq {e : Syn .expr} {hb : e.binOp? = some (.eq, a, b)} {da : Typed Γ a .bool}
    {db : Typed Γ b .bool} (ha : BoolArg Γ a) :
    Source.inferBin Γ e a b .eq hb (some ⟨.bool, da⟩) (some ⟨.bool, db⟩) =
      some ⟨.bool, .eq hb da db rfl rfl⟩ := by
  cases ha <;> rfl

/-- `a == b` and `a != b` over Boolean arguments. -/
theorem inferN_eq {op : EqOp} {da : Typed Γ a .bool} {db : Typed Γ b .bool} (hA : BoolArg Γ a)
    (ha : Typed.inferN k Γ a = some ⟨.bool, da⟩) (hb : Typed.inferN k Γ b = some ⟨.bool, db⟩) :
    Typed.inferN (k + 1) Γ (.equality op a b) = some ⟨.bool, .eq rfl da db rfl rfl⟩ := by
  show Source.inferBin Γ (.equality op a b) a b .eq rfl
    (Typed.inferN k Γ a) (Typed.inferN k Γ b) = _
  rw [ha, hb]; exact inferBin_eq hA

/-- Fuel above a bound is a successor. -/
theorem fuel_succ {P : Nat → Prop} {k : Nat} (h : ∀ m, k ≤ m → P (m + 1)) : ∀ m, k < m → P m
  | 0, hm => absurd hm (Nat.not_lt_zero _)
  | m + 1, hm => h m (by omega)

/-- **Boolean arguments infer to `bool`** at every fuel above their node count,
to one derivation. -/
theorem BoolArg.inferN {e : Syn .expr} (h : BoolArg Γ e) :
    ∃ d, ∀ m, e.nodes.length < m → Typed.inferN m Γ e = some ⟨.bool, d⟩ := by
  induction h with
  | lit b => exact ⟨.bool b, fuel_succ fun _ _ => inferN_bool b⟩
  | loc hr ht => exact ⟨.loc hr ht, fuel_succ fun _ _ => inferN_loc hr ht⟩
  | not _ iha =>
    obtain ⟨d, hd⟩ := iha
    exact ⟨.not d, fuel_succ fun m h => by
      simp [Source.Syn.nodes] at h; exact inferN_not (hd m (by omega))⟩
  | and _ _ iha ihb =>
    obtain ⟨da, hda⟩ := iha; obtain ⟨db, hdb⟩ := ihb
    exact ⟨.logic rfl da db, fuel_succ fun m h => by
      simp [Source.Syn.nodes] at h; exact inferN_and (hda m (by omega)) (hdb m (by omega))⟩
  | or _ _ iha ihb =>
    obtain ⟨da, hda⟩ := iha; obtain ⟨db, hdb⟩ := ihb
    exact ⟨.logic rfl da db, fuel_succ fun m h => by
      simp [Source.Syn.nodes] at h; exact inferN_or (hda m (by omega)) (hdb m (by omega))⟩
  | eq op ha _ iha ihb =>
    obtain ⟨da, hda⟩ := iha; obtain ⟨db, hdb⟩ := ihb
    exact ⟨.eq rfl da db rfl rfl, fuel_succ fun m h => by
      simp [Source.Syn.nodes] at h; exact inferN_eq ha (hda m (by omega)) (hdb m (by omega))⟩
  | cond _ _ _ ihc iha ihb =>
    obtain ⟨dc, hdc⟩ := ihc; obtain ⟨da, hda⟩ := iha; obtain ⟨db, hdb⟩ := ihb
    exact ⟨.cond dc da db rfl, fuel_succ fun m h => by
      simp [Source.Syn.nodes] at h
      exact inferN_cond (hdc m (by omega)) (hda m (by omega)) (hdb m (by omega))⟩

/-- **Scalar arguments infer to their type** at every fuel above their node
count, to one derivation. -/
theorem ScalarArg.inferN {e : Syn .expr} {τ : STy} (h : ScalarArg Γ e τ) :
    ∃ d, ∀ m, e.nodes.length < m → Typed.inferN m Γ e = some ⟨τ, d⟩ := by
  cases h with
  | num m f x => exact ⟨.const rfl rfl rfl, fuel_succ fun _ _ => inferN_num m f x⟩
  | loc hr ht => exact ⟨.loc hr ht, fuel_succ fun _ _ => inferN_loc hr ht⟩
  | bool hb => exact hb.inferN

/-- Ordered scalar arguments with their inferred types, position by position. -/
inductive ScalarArgs (Γ : Ctx) : List (Syn .expr) → List STy → Prop
  | nil : ScalarArgs Γ [] []
  | cons {e : Syn .expr} {σ : STy} {es : List (Syn .expr)} {σs : List STy} :
      ScalarArg Γ e σ → ScalarArgs Γ es σs → ScalarArgs Γ (e :: es) (σ :: σs)

theorem ScalarArgs.length_eq {es : List (Syn .expr)} {σs : List STy} (h : ScalarArgs Γ es σs) :
    σs.length = es.length := by
  induction h <;> simp_all

theorem ScalarArgs.get {es : List (Syn .expr)} {σs : List STy} (h : ScalarArgs Γ es σs) :
    ∀ {i : Nat} {a σ}, es[i]? = some a → σs[i]? = some σ → ScalarArg Γ a σ := by
  induction h with
  | nil => intro i a σ hi; simp at hi
  | cons he _ ih =>
    intro i a σ hi hσ
    cases i with
    | zero => simp at hi hσ; subst hi hσ; exact he
    | succ i => exact ih (by simpa using hi) (by simpa using hσ)

end Solidity.Correctness.Lowering.Total.ArgumentInference
