import Solidity.Source.Infer

namespace Solidity.Correctness.Lowering.Total.ArithmeticInference

open Source (STy Syn Ctx Typed BinKind Inferred Q)

/-- Why a spelled operator form has no inferred type. -/
inductive Reason where
  /-- `/` or `%` by a constant zero. -/
  | zeroDivisor
  /-- The operand types fail the family's check. -/
  | incompatible
  /-- Two constant operands that do not fold. -/
  | unfolded
  deriving DecidableEq, Repr

/-- The binary operator families of this module (`&&`, `||` excluded). -/
inductive Family where
  | arith | bit | shift | exp | order | eq
  deriving DecidableEq, Repr

/-- The Source family. -/
def Family.kind : Family → BinKind
  | .arith => .arith | .bit => .bit | .shift => .shift | .exp => .exp
  | .order => .order | .eq => .eq

/-- A comparison family. -/
def Family.cmp : Family → Bool
  | .order | .eq => true
  | _ => false

/-- The check `Source.inferBin` applies to inferred operand types. -/
def binTy (Γ : Ctx) (k : Family) (divMod bothConst : Bool) (τa τb : STy) : Except Reason STy :=
  match k with
  | .arith =>
    if divMod && τb.isZeroConst then .error .zeroDivisor
    else match STy.common? Γ.isBase Γ.mapFree τa τb with
      | some τ => if τ.isNumeric then .ok τ else .error .incompatible
      | none => .error (if bothConst then .unfolded else .incompatible)
  | .bit =>
    match STy.common? Γ.isBase Γ.mapFree τa τb with
    | some τ => if τ.isBits then .ok τ else .error .incompatible
    | none => .error (if bothConst then .unfolded else .incompatible)
  | .shift =>
    if τa.shiftTy.isBits && τb.isAmount then
      if bothConst then .error .unfolded else .ok τa.shiftTy
    else .error .incompatible
  | .exp =>
    if τa.shiftTy.isInt && τb.isAmount then
      if bothConst then .error .unfolded else .ok τa.shiftTy
    else .error .incompatible
  | .order =>
    match STy.common? Γ.isBase Γ.mapFree τa τb with
    | some τ => if τ.isOrdered then .ok .bool else .error .incompatible
    | none => .error .incompatible
  | .eq =>
    match STy.common? Γ.isBase Γ.mapFree τa τb with
    | some τ => if τ.hasEq then .ok .bool else .error .incompatible
    | none => .error .incompatible

/-- The check of unary `-`. -/
def negTy : STy → Except Reason STy
  | .int t => if t.signed then .ok (.int t) else .error .incompatible
  | .fixed f => .ok (.fixed f)
  | _ => .error .incompatible

/-- The check of `~`. -/
def bitNotTy (τ : STy) : Except Reason STy :=
  if τ.isBits then .ok τ else .error .incompatible

variable {Γ : Ctx} {n : Nat}

theorem inferN_zero {s : Syn .expr} : Typed.inferN 0 Γ s = none := by simp only [Typed.inferN]

theorem tryConst_none {s : Syn .expr} (h : s.const = none) : Source.tryConst Γ s = none := by
  unfold Source.tryConst; split
  · rename_i hc _ _; rw [h] at hc; cases hc
  · rfl

theorem tryConst_some {s : Syn .expr} {q : Q} (hc : s.const = some q)
    (ha : s.isAddressLit = false) (hx : s.hexLen? = none) :
    Source.tryConst Γ s = some ⟨.rational q, .const hc ha hx⟩ := by
  unfold Source.tryConst; split
  · rename_i q' hc' _ _; cases hc.symm.trans hc'; rfl
  · rename_i h; exact absurd hx (h q hc ha)

theorem inferN_const {s : Syn .expr} {q : Q} (hc : s.const = some q)
    (ha : s.isAddressLit = false) (hx : s.hexLen? = none) :
    Typed.inferN (n + 1) Γ s = some ⟨.rational q, .const hc ha hx⟩ := by
  rw [Typed.inferN, tryConst_some hc ha hx]; rfl

theorem inferN_bin {s a b : Syn .expr} {k : BinKind} (hb : s.binOp? = some (k, a, b)) :
    Typed.inferN (n + 1) Γ s =
      (Source.tryConst Γ s).orElse fun _ =>
        Source.inferBin Γ s a b k hb (Typed.inferN n Γ a) (Typed.inferN n Γ b) := by
  cases s <;> first | (cases hb; done) | skip
  all_goals (cases hb; rw [Typed.inferN])

theorem inferN_local {x : String} {i : Nat} {τ : STy} (hr : Γ.resolve x = some (.loc i))
    (ht : Γ.tys[i]? = some τ) :
    Typed.inferN (n + 1) Γ (.ident x) = some ⟨τ, .loc hr ht⟩ := by
  rw [Typed.inferN, show Source.tryConst Γ (.ident x) = none from rfl]
  dsimp only [Option.orElse]
  split
  · rename_i j hr'
    cases hr.symm.trans hr'
    split
    · rename_i τ' ht'; cases ht.symm.trans ht'; rfl
    · rename_i ht'; rw [ht] at ht'; cases ht'
  all_goals first | (rename_i hr'; rw [hr] at hr'; cases hr'; done) | (rename_i h1 _ _; exact (h1 i hr).elim)

theorem const_neg {a : Syn .expr} (hc : a.const = none) :
    (Syn.unaryPrefix .neg a : Syn .expr).const = none := by
  show a.const.map Q.neg = none
  rw [hc]; rfl

theorem inferN_neg_none {a : Syn .expr} (hc : a.const = none) (h : Typed.inferN n Γ a = none) :
    Typed.inferN (n + 1) Γ (.unaryPrefix .neg a) = none := by
  rw [Typed.inferN, tryConst_none (const_neg hc)]
  dsimp only [Option.orElse]
  rw [h]; rfl

theorem inferN_neg {a : Syn .expr} {τ τ' : STy} (hc : a.const = none) (da : Typed Γ a τ) (h : negTy τ = .ok τ') :
    ∃ d, ∀ n, Typed.inferN n Γ a = some ⟨τ, da⟩ →
      Typed.inferN (n + 1) Γ (.unaryPrefix .neg a) = some ⟨τ', d⟩ := by
  cases τ <;> simp only [negTy, reduceCtorEq] at h
  · rename_i t
    split at h
    · rename_i hs; cases h
      refine ⟨.neg da hs, fun n hn => ?_⟩
      rw [Typed.inferN, tryConst_none (const_neg hc)]
      dsimp only [Option.orElse]
      rw [hn]; simp [hs]
    · cases h
  · cases h
    refine ⟨.negFixed da, fun n hn => ?_⟩
    rw [Typed.inferN, tryConst_none (const_neg hc)]
    dsimp only [Option.orElse]
    rw [hn]; rfl

theorem inferN_neg_error {a : Syn .expr} {τ : STy} {r : Reason} (hc : a.const = none) {da : Typed Γ a τ}
    (h : negTy τ = .error r) (hn : Typed.inferN n Γ a = some ⟨τ, da⟩) :
    Typed.inferN (n + 1) Γ (.unaryPrefix .neg a) = none := by
  rw [Typed.inferN, tryConst_none (const_neg hc)]
  dsimp only [Option.orElse]
  rw [hn]
  cases τ <;> simp only [negTy, reduceCtorEq] at h <;> try rfl
  rename_i t
  split at h
  · cases h
  · rename_i hs; simp [hs]

theorem const_bitNot {a : Syn .expr} (hc : a.const = none) :
    (Syn.unaryPrefix .bitNot a : Syn .expr).const = none := by
  show (a.const.bind fun q => q.int?.bind fun k => _) = none
  rw [hc]; rfl

theorem inferN_bitNot_none {a : Syn .expr} (hc : a.const = none) (h : Typed.inferN n Γ a = none) :
    Typed.inferN (n + 1) Γ (.unaryPrefix .bitNot a) = none := by
  rw [Typed.inferN, tryConst_none (const_bitNot hc)]
  dsimp only [Option.orElse]
  rw [h]; rfl

theorem inferN_bitNot {a : Syn .expr} {τ : STy} (hc : a.const = none) (da : Typed Γ a τ)
    (h : τ.isBits = true) (hn : Typed.inferN n Γ a = some ⟨τ, da⟩) :
    Typed.inferN (n + 1) Γ (.unaryPrefix .bitNot a) = some ⟨τ, .bitNot da h⟩ := by
  rw [Typed.inferN, tryConst_none (const_bitNot hc)]
  dsimp only [Option.orElse]
  rw [hn]; simp [h]

theorem inferN_bitNot_error {a : Syn .expr} {τ : STy} (hc : a.const = none) {da : Typed Γ a τ}
    (h : τ.isBits = false) (hn : Typed.inferN n Γ a = some ⟨τ, da⟩) :
    Typed.inferN (n + 1) Γ (.unaryPrefix .bitNot a) = none := by
  rw [Typed.inferN, tryConst_none (const_bitNot hc)]
  dsimp only [Option.orElse]
  rw [hn]; simp [h]

/-! ## `inferBin` -/

section bin
variable {s a b : Syn .expr} {τa τb τ : STy}

/-- Enter `inferBin` past its constant-comparison alternatives. -/
local macro "bin_head" : tactic =>
  `(tactic| (unfold Source.inferBin
             split <;> first | (rename_i h _ _ _; cases h; done)
                              | (exfalso; simp_all [Family.cmp, Family.kind]; done) | skip))

theorem inferBin_none {k : Family} (hb : s.binOp? = some (k.kind, a, b))
    (hcc : (k.cmp && (a.const.isSome && b.const.isSome)) = false)
    {ra : Option (Inferred Γ a)} {rb : Option (Inferred Γ b)} (h : ra = none ∨ rb = none) :
    Source.inferBin Γ s a b k.kind hb ra rb = none := by
  cases k <;> bin_head <;>
  · cases ra with
    | none => rfl
    | some _ => cases rb with
      | none => rfl
      | some _ => simp at h

theorem inferBin_order_const {qa qb : Q} (hb : s.binOp? = some (.order, a, b))
    (hqa : a.const = some qa) (hqb : b.const = some qb)
    {ra : Option (Inferred Γ a)} {rb : Option (Inferred Γ b)} :
    Source.inferBin Γ s a b .order hb ra rb =
      some ⟨.bool, .compareConst hb (Or.inl rfl) hqa hqb⟩ := by
  unfold Source.inferBin
  split
  · split
    · rename_i h1 h2; cases hqa.symm.trans h1; cases hqb.symm.trans h2; rfl
    · rename_i h; exact (h _ _ hqa hqb).elim
  · rename_i h _ _ _; cases h
  · rename_i h _; exact (h _ _ _ rfl HEq.rfl hqa hqb).elim

theorem inferBin_eq_const {qa qb : Q} (hb : s.binOp? = some (.eq, a, b))
    (hqa : a.const = some qa) (hqb : b.const = some qb)
    {ra : Option (Inferred Γ a)} {rb : Option (Inferred Γ b)} :
    Source.inferBin Γ s a b .eq hb ra rb =
      some ⟨.bool, .compareConst hb (Or.inr rfl) hqa hqb⟩ := by
  unfold Source.inferBin
  split
  · rename_i h _ _ _; cases h
  · split
    · rename_i h1 h2; cases hqa.symm.trans h1; cases hqb.symm.trans h2; rfl
    · rename_i h; exact (h _ _ hqa hqb).elim
  · rename_i h; exact (h _ _ _ rfl HEq.rfl hqa hqb).elim

variable {da : Typed Γ a τa} {db : Typed Γ b τb}

theorem inferBin_arith (hb : s.binOp? = some (.arith, a, b))
    (hc : STy.common? Γ.isBase Γ.mapFree τa τb = some τ) (hn : τ.isNumeric = true)
    (hz : (s.isDivMod && τb.isZeroConst) = false) :
    Source.inferBin Γ s a b .arith hb (some ⟨τa, da⟩) (some ⟨τb, db⟩) =
      some ⟨τ, .arith hb da db hc hn hz⟩ := by
  unfold Source.inferBin
  split <;> first | (rename_i h _ _ _; cases h; done) | skip
  dsimp only
  split
  · rename_i τ' hc'; cases hc.symm.trans hc'; rw [dif_pos hn, dif_pos hz]
  · rename_i hc'; rw [hc] at hc'; cases hc'

theorem inferBin_bit (hb : s.binOp? = some (.bit, a, b))
    (hc : STy.common? Γ.isBase Γ.mapFree τa τb = some τ) (hn : τ.isBits = true) :
    Source.inferBin Γ s a b .bit hb (some ⟨τa, da⟩) (some ⟨τb, db⟩) =
      some ⟨τ, .bit hb da db hc hn⟩ := by
  unfold Source.inferBin
  split <;> first | (rename_i h _ _ _; cases h; done) | skip
  dsimp only
  split
  · rename_i τ' hc'; cases hc.symm.trans hc'; rw [dif_pos hn]
  · rename_i hc'; rw [hc] at hc'; cases hc'

theorem inferBin_shift (hb : s.binOp? = some (.shift, a, b))
    (h1 : τa.shiftTy.isBits = true) (h2 : τb.isAmount = true)
    (h3 : (a.const.isSome && b.const.isSome) = false) :
    Source.inferBin Γ s a b .shift hb (some ⟨τa, da⟩) (some ⟨τb, db⟩) =
      some ⟨τa.shiftTy, .shift hb da db h1 h2 h3⟩ := by
  unfold Source.inferBin
  split <;> first | (rename_i h _ _ _; cases h; done) | skip
  dsimp only
  rw [dif_pos h1, dif_pos h2, dif_pos h3]

theorem inferBin_exp (hb : s.binOp? = some (.exp, a, b))
    (h1 : τa.shiftTy.isInt = true) (h2 : τb.isAmount = true)
    (h3 : (a.const.isSome && b.const.isSome) = false) :
    Source.inferBin Γ s a b .exp hb (some ⟨τa, da⟩) (some ⟨τb, db⟩) =
      some ⟨τa.shiftTy, .exp hb da db h1 h2 h3⟩ := by
  unfold Source.inferBin
  split <;> first | (rename_i h _ _ _; cases h; done) | skip
  dsimp only
  rw [dif_pos h1, dif_pos h2, dif_pos h3]

theorem inferBin_order (hb : s.binOp? = some (.order, a, b))
    (hcc : (a.const.isSome && b.const.isSome) = false)
    (hc : STy.common? Γ.isBase Γ.mapFree τa τb = some τ) (hn : τ.isOrdered = true) :
    Source.inferBin Γ s a b .order hb (some ⟨τa, da⟩) (some ⟨τb, db⟩) =
      some ⟨.bool, .order hb da db hc hn⟩ := by
  unfold Source.inferBin
  split <;> first | (exfalso; simp_all; done) | skip
  dsimp only
  split
  · rename_i τ' hc'; cases hc.symm.trans hc'; rw [dif_pos hn]
  · rename_i hc'; rw [hc] at hc'; cases hc'

theorem inferBin_eq (hb : s.binOp? = some (.eq, a, b))
    (hcc : (a.const.isSome && b.const.isSome) = false)
    (hc : STy.common? Γ.isBase Γ.mapFree τa τb = some τ) (hn : τ.hasEq = true) :
    Source.inferBin Γ s a b .eq hb (some ⟨τa, da⟩) (some ⟨τb, db⟩) =
      some ⟨.bool, .eq hb da db hc hn⟩ := by
  unfold Source.inferBin
  split <;> first | (exfalso; simp_all; done) | skip
  dsimp only
  split
  · rename_i τ' hc'; cases hc.symm.trans hc'; rw [dif_pos hn]
  · rename_i hc'; rw [hc] at hc'; cases hc'

/-- **Success of the family check**: the derivation depends on the operands'
derivations only. -/
theorem inferBin_ok {k : Family} (hb : s.binOp? = some (k.kind, a, b))
    (hcc : (k.cmp && (a.const.isSome && b.const.isSome)) = false)
    (da : Typed Γ a τa) (db : Typed Γ b τb)
    (h : binTy Γ k s.isDivMod (a.const.isSome && b.const.isSome) τa τb = .ok τ) :
    ∃ d, Source.inferBin Γ s a b k.kind hb (some ⟨τa, da⟩) (some ⟨τb, db⟩) = some ⟨τ, d⟩ := by
  cases k <;> simp only [binTy] at h
  · split at h
    · cases h
    · rename_i hz
      split at h
      · rename_i τ' hc
        split at h
        · rename_i hn; cases h
          exact ⟨_, inferBin_arith hb hc hn (by simpa using hz)⟩
        · cases h
      · cases h
  · split at h
    · rename_i τ' hc
      split at h
      · rename_i hn; cases h; exact ⟨_, inferBin_bit hb hc hn⟩
      · cases h
    · cases h
  · split at h
    · rename_i h12
      split at h
      · cases h
      · rename_i h3; cases h
        simp only [Bool.and_eq_true] at h12
        exact ⟨_, inferBin_shift hb h12.1 h12.2 (by simpa using h3)⟩
    · cases h
  · split at h
    · rename_i h12
      split at h
      · cases h
      · rename_i h3; cases h
        simp only [Bool.and_eq_true] at h12
        exact ⟨_, inferBin_exp hb h12.1 h12.2 (by simpa using h3)⟩
    · cases h
  · split at h
    · rename_i τ' hc
      split at h
      · rename_i hn; cases h
        exact ⟨_, inferBin_order hb (by simpa [Family.cmp] using hcc) hc hn⟩
      · cases h
    · cases h
  · split at h
    · rename_i τ' hc
      split at h
      · rename_i hn; cases h
        exact ⟨_, inferBin_eq hb (by simpa [Family.cmp] using hcc) hc hn⟩
      · cases h
    · cases h

/-- **Failure of the family check** leaves no result. -/
theorem inferBin_error {k : Family} {r : Reason} (hb : s.binOp? = some (k.kind, a, b))
    (hcc : (k.cmp && (a.const.isSome && b.const.isSome)) = false)
    (h : binTy Γ k s.isDivMod (a.const.isSome && b.const.isSome) τa τb = .error r) :
    Source.inferBin Γ s a b k.kind hb (some ⟨τa, da⟩) (some ⟨τb, db⟩) = none := by
  cases k <;> simp only [binTy] at h <;> revert hb <;> dsimp only [Family.kind] <;> intro hb <;>
    bin_head <;> (try dsimp only) <;> (repeat' split) <;> first | rfl | (exfalso; simp_all; done)

end bin

end Solidity.Correctness.Lowering.Total.ArithmeticInference
