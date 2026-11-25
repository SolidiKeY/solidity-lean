import Solidity.Correctness.Lowering.Total.ArithmeticInference.Model

/-!
# The arithmetic argument family and its exact inference

`Infers Γ e τ` is given by explicit conditions on the model expression: a
folding constant, a local with its resolution and slot-type facts, a supported
operator whose operand types pass the family's check, a comparison of two
constants, `-` and `~`; no inference result is assumed. `Infers.sound` proves
it against the unchanged `Tables.expr` and the actual `Typed.inferN`: the
expression is spelled, and its spelling infers to `τ` with one derivation at
every fuel from `depth e` and to nothing below (`Infers.inferN`, with
`inferN_of_le`, `inferN_short`, `inferN_transport`). Per-family rules state the
common-type, signedness, shift-amount and division checks (`Infers.arith`,
`bit`, `shift`, `exp`, `order`, `eq`, `negInt`, `negFixed`, `bitNot'`).

Literals are the model's decimal naturals; a name that is not a local (a state
variable, an unresolved name) is not a leaf.

`Rejects Γ e r` keeps rejected forms with a classifying reason, through nesting
under the family's operators, for any spelling of the whole form
(`Rejects.sound`: no result at any fuel; `zeroDivisor`, `noCommon`,
`badAmount`, `negUnsigned`), and the wrapping operators are not decoded
(`expr_unspelled`, `binop_eq_none_iff`).

These are local family conditions for the decoder lane, not admission
conditions of `lowerLoopsCorrect`; Boolean-only recursion (`!`, `&&`, `||`,
Boolean literals), references, nested calls and mixed families are outside.
-/

namespace Solidity.Correctness.Lowering.Total.ArithmeticInference

open Source (STy Syn Ctx Typed BinKind Inferred Q)
open Decode (Tables)

/-- **The arithmetic argument family**, by explicit conditions on the model
expression: a folding constant; a local with its resolution and slot type; a
supported binary operator over the family whose operand types pass the
family's check; a comparison of two constants; `-` and `~`. A local leaf has
any slot type, so the checks, not the leaves, keep the family numeric. -/
inductive Infers (Γ : Source.Ctx) : RawExpr → STy → Prop
  /-- Folding wins: the exact constant. -/
  | const {e : RawExpr} {q : Q} : fold e = some q → Infers Γ e (.rational q)
  | local {x : String} {i : Nat} {τ : STy} : Γ.resolve x = some (.loc i) →
      Γ.tys[i]? = some τ → Infers Γ (.name x) τ
  | bin {op : BinOp} {k : Family} {a b : RawExpr} {τa τb τ : STy} : family op = some k →
      Infers Γ a τa → Infers Γ b τb → fold (.binop op a b) = none →
      (k.cmp && bothConst a b) = false →
      binTy Γ k (divMod op) (bothConst a b) τa τb = .ok τ → Infers Γ (.binop op a b) τ
  /-- A comparison of two constants is a boolean. -/
  | cmpConst {op : BinOp} {k : Family} {a b : RawExpr} {qa qb : Q} : family op = some k →
      k.cmp = true → fold a = some qa → fold b = some qb → Infers Γ (.binop op a b) .bool
  | neg {a : RawExpr} {τ τ' : STy} : Infers Γ a τ → fold a = none → negTy τ = .ok τ' →
      Infers Γ (.unop .neg a) τ'
  | bitNot {a : RawExpr} {τ : STy} : Infers Γ a τ → fold a = none → τ.isBits = true →
      Infers Γ (.unop .bnot a) τ

/-- **Rejected forms** of the family, with the reason: a failed check over
operands of the family, through nesting. Sufficient, not exhaustive: a form in
neither `Infers` nor `Rejects` (an operand outside the family, `~` of a
fractional constant) is not decided here. -/
inductive Rejects (Γ : Source.Ctx) : RawExpr → Reason → Prop
  | bin {op : BinOp} {k : Family} {a b : RawExpr} {τa τb : STy} {r : Reason} :
      family op = some k → Infers Γ a τa → Infers Γ b τb → fold (.binop op a b) = none →
      (k.cmp && bothConst a b) = false →
      binTy Γ k (divMod op) (bothConst a b) τa τb = .error r → Rejects Γ (.binop op a b) r
  | neg {a : RawExpr} {τ : STy} {r : Reason} : Infers Γ a τ → fold a = none →
      negTy τ = .error r → Rejects Γ (.unop .neg a) r
  | bitNot {a : RawExpr} {τ : STy} : Infers Γ a τ → fold a = none → τ.isBits = false →
      Rejects Γ (.unop .bnot a) .incompatible
  | left {op : BinOp} {k : Family} {a b : RawExpr} {r : Reason} : family op = some k →
      Rejects Γ a r → Rejects Γ (.binop op a b) r
  | right {op : BinOp} {k : Family} {a b : RawExpr} {r : Reason} : family op = some k →
      Rejects Γ b r → Rejects Γ (.binop op a b) r
  | negArg {a : RawExpr} {r : Reason} : Rejects Γ a r → Rejects Γ (.unop .neg a) r
  | bitNotArg {a : RawExpr} {r : Reason} : Rejects Γ a r → Rejects Γ (.unop .bnot a) r

variable {Γ : Source.Ctx} {T : Tables} {e : RawExpr} {τ : STy}

theorem depth_const {q : Q} (h : fold e = some q) : depth e = 1 := by
  cases e <;> simp [depth, h]

theorem foldBin_cmp {op : BinOp} {k : Family} {qa qb : Option Q} (hk : family op = some k)
    (hc : k.cmp = true) : foldBin op qa qb = none := by
  cases h : foldBin op qa qb with
  | none => rfl
  | some q =>
    obtain ⟨k', _, _, hk', hc', _⟩ := foldBin_some h
    cases hk.symm.trans hk'; rw [hc] at hc'; cases hc'

theorem cmpOp_family {op : BinOp} {k : Family} (hk : family op = some k) : cmpOp op = k.cmp := by
  simp [cmpOp, hk]

theorem depth_bin {op : BinOp} {k : Family} {a b : RawExpr} (hk : family op = some k)
    (hf : fold (.binop op a b) = none) (hcc : (k.cmp && bothConst a b) = false) :
    depth (.binop op a b) = max (depth a) (depth b) + 1 := by
  simp [depth, hf, cmpOp_family hk, hcc]

theorem depth_bin_le {op : BinOp} {k : Family} {a b : RawExpr} {n : Nat} (hk : family op = some k)
    (hf : fold (.binop op a b) = none) (hcc : (k.cmp && bothConst a b) = false) :
    depth (.binop op a b) ≤ n + 1 ↔ depth a ≤ n ∧ depth b ≤ n := by
  rw [depth_bin hk hf hcc, Nat.add_le_add_iff_right, Nat.max_le]

/-- **Exact inference of the family** at the actual `Typed.inferN`: the
expression is spelled, its spelling's constant is the model fold, and it
infers to `τ` with one derivation at every fuel from `depth e`, to nothing
below. -/
theorem Infers.sound (h : Infers Γ e τ) :
    ∃ s, T.expr e = some s ∧ s.const = fold e ∧ ∃ d : Typed Γ s τ,
      ∀ n, Typed.inferN n Γ s = if depth e ≤ n then some ⟨τ, d⟩ else none := by
  induction h with
  | @const e q hq =>
    obtain ⟨s, hs, hc, ha, hx⟩ := fold_spec (T := T) hq
    refine ⟨s, hs, hc.trans hq.symm, .const hc ha hx, fun n => ?_⟩
    rw [depth_const hq]
    cases n with
    | zero => exact inferN_zero
    | succ n => rw [inferN_const hc ha hx, if_pos (by omega)]
  | @«local» x i τ hr ht =>
    refine ⟨_, expr_name, rfl, .loc hr ht, fun n => ?_⟩
    cases n with
    | zero => exact inferN_zero
    | succ n => rw [ArgumentInference.inferN_loc hr ht, if_pos (by simp [depth])]
  | @bin op k a b τa τb τ hk _ _ hf hcc hty iha ihb =>
    obtain ⟨sa, hsa, hca, da, ha⟩ := iha
    obtain ⟨sb, hsb, hcb, db, hb⟩ := ihb
    obtain ⟨f, hf', hspec⟩ := binop_family hk
    obtain ⟨hbo, hdm, hc, _, _⟩ := hspec sa sb
    have hcs : (f sa sb).const = none := by rw [hc, hca, hcb]; exact hf
    have hbc : (sa.const.isSome && sb.const.isSome) = bothConst a b := by rw [hca, hcb]; rfl
    obtain ⟨d, hd⟩ := inferBin_ok hbo (by rw [hbc]; exact hcc) da db (by rw [hdm, hbc]; exact hty)
    refine ⟨_, expr_binop.mpr ⟨f, sa, sb, hf', hsa, hsb, rfl⟩, hcs.trans hf.symm, d, fun n => ?_⟩
    cases n with
    | zero => rw [if_neg (by rw [depth_bin hk hf hcc]; omega)]; exact inferN_zero
    | succ n =>
      have hiff := depth_bin_le (n := n) hk hf hcc
      rw [inferN_bin hbo, tryConst_none hcs, ha n, hb n]
      dsimp only [Option.orElse]
      by_cases h1 : depth a ≤ n <;> by_cases h2 : depth b ≤ n
      · rw [if_pos h1, if_pos h2, hd, if_pos (hiff.mpr ⟨h1, h2⟩)]
      all_goals
        rw [if_neg (show ¬ depth (.binop op a b) ≤ n + 1 from fun h => by have := hiff.mp h; omega)]
        exact inferBin_none hbo (by rw [hbc]; exact hcc) (by simp [h1, h2])
  | @cmpConst op k a b qa qb hk hc hqa hqb =>
    obtain ⟨sa, hsa, hca, _⟩ := fold_spec (T := T) hqa
    obtain ⟨sb, hsb, hcb, _⟩ := fold_spec (T := T) hqb
    obtain ⟨f, hf', hspec⟩ := binop_family hk
    obtain ⟨hbo, _, hcn, _, _⟩ := hspec sa sb
    have hfold : fold (.binop op a b) = none := by rw [fold]; exact foldBin_cmp hk hc
    have hcs : (f sa sb).const = none := by rw [hcn]; exact foldBin_cmp hk hc
    have hdepth : depth (.binop op a b) = 1 := by
      simp [depth, cmpOp_family hk, hc, bothConst, hqa, hqb]
    refine ⟨_, expr_binop.mpr ⟨f, sa, sb, hf', hsa, hsb, rfl⟩, hcs.trans hfold.symm, ?_⟩
    rw [hdepth]
    cases k <;> cases hc
    · refine ⟨.compareConst hbo (Or.inl rfl) hca hcb, fun n => ?_⟩
      cases n with
      | zero => exact inferN_zero
      | succ n =>
        rw [inferN_bin hbo, tryConst_none hcs, if_pos (by omega)]
        exact inferBin_order_const hbo hca hcb
    · refine ⟨.compareConst hbo (Or.inr rfl) hca hcb, fun n => ?_⟩
      cases n with
      | zero => exact inferN_zero
      | succ n =>
        rw [inferN_bin hbo, tryConst_none hcs, if_pos (by omega)]
        exact inferBin_eq_const hbo hca hcb
  | @neg a τ τ' _ hf hty ih =>
    obtain ⟨sa, hsa, hca, da, ha⟩ := ih
    have hcn : sa.const = none := hca.trans hf
    have hfold : fold (.unop .neg a) = none := by rw [fold, hf]; rfl
    obtain ⟨d, hd⟩ := inferN_neg hcn da hty
    refine ⟨_, expr_neg.mpr ⟨sa, hsa, rfl⟩, (const_neg hcn).trans hfold.symm, d, fun n => ?_⟩
    have hdepth : depth (.unop .neg a) = depth a + 1 := by simp [depth, hfold]
    rw [hdepth]
    cases n with
    | zero => rw [if_neg (by omega)]; exact inferN_zero
    | succ n =>
      by_cases h1 : depth a ≤ n
      · rw [hd n (by rw [ha n, if_pos h1]), if_pos (by omega)]
      · rw [inferN_neg_none hcn (by rw [ha n, if_neg h1]), if_neg (by omega)]
  | @bitNot a τ _ hf hty ih =>
    obtain ⟨sa, hsa, hca, da, ha⟩ := ih
    have hcn : sa.const = none := hca.trans hf
    have hfold : fold (.unop .bnot a) = none := by rw [fold, hf]; rfl
    refine ⟨_, expr_bnot.mpr ⟨sa, hsa, rfl⟩, (const_bitNot hcn).trans hfold.symm,
      .bitNot da hty, fun n => ?_⟩
    have hdepth : depth (.unop .bnot a) = depth a + 1 := by simp [depth, hfold]
    rw [hdepth]
    cases n with
    | zero => rw [if_neg (by omega)]; exact inferN_zero
    | succ n =>
      by_cases h1 : depth a ≤ n
      · rw [inferN_bitNot hcn da hty (by rw [ha n, if_pos h1]), if_pos (by omega)]
      · rw [inferN_bitNot_none hcn (by rw [ha n, if_neg h1]), if_neg (by omega)]

variable {s : Syn .expr}

/-- The family is spelled by every decoder version. -/
theorem Infers.spelled (h : Infers Γ e τ) : ∃ s, T.expr e = some s :=
  let ⟨s, hs, _⟩ := h.sound (T := T); ⟨s, hs⟩

/-- The spelling's constant is the model fold. -/
theorem Infers.const_eq (h : Infers Γ e τ) (hs : T.expr e = some s) : s.const = fold e := by
  obtain ⟨s', hs', hc, _⟩ := h.sound (T := T)
  cases hs.symm.trans hs'; exact hc

/-- **Exact inference with exact fuel**: `τ` with one derivation from fuel
`depth e` on, nothing below (so the result is transported along any fuel). -/
theorem Infers.inferN (h : Infers Γ e τ) (hs : T.expr e = some s) :
    ∃ d : Typed Γ s τ, ∀ n, Typed.inferN n Γ s = if depth e ≤ n then some ⟨τ, d⟩ else none := by
  obtain ⟨s', hs', _, hd⟩ := h.sound (T := T)
  cases hs.symm.trans hs'; exact hd

theorem Infers.inferN_of_le {n : Nat} (h : Infers Γ e τ) (hs : T.expr e = some s)
    (hn : depth e ≤ n) : ∃ d, Typed.inferN n Γ s = some ⟨τ, d⟩ :=
  let ⟨d, hd⟩ := h.inferN hs; ⟨d, by rw [hd, if_pos hn]⟩

/-- Insufficient fuel: below `depth e` there is no result. -/
theorem Infers.inferN_short {n : Nat} (h : Infers Γ e τ) (hs : T.expr e = some s)
    (hn : n < depth e) : Typed.inferN n Γ s = none :=
  let ⟨_, hd⟩ := h.inferN hs; by rw [hd, if_neg (by omega)]

/-- **Fuel transport** between any two sufficient fuels. -/
theorem Infers.inferN_transport {n m : Nat} (h : Infers Γ e τ) (hs : T.expr e = some s)
    (hn : depth e ≤ n) (hm : depth e ≤ m) : Typed.inferN n Γ s = Typed.inferN m Γ s :=
  let ⟨_, hd⟩ := h.inferN hs; by rw [hd, hd, if_pos hn, if_pos hm]

/-- The family's type is unique. -/
theorem Infers.unique {τ' : STy} (h : Infers Γ e τ) (h' : Infers Γ e τ') : τ = τ' := by
  obtain ⟨s, hs, _, d, hd⟩ := h.sound (T := Decode.tables1)
  obtain ⟨d', hd'⟩ := h'.inferN hs
  have := (hd (depth e)).symm.trans (hd' (depth e))
  simp only [Nat.le_refl, if_true, Option.some.injEq] at this
  exact congrArg Sigma.fst this

/-- A folding expression has only its constant's type. -/
theorem Infers.ty_of_fold {q : Q} (h : Infers Γ e τ) (hq : fold e = some q) : τ = .rational q :=
  h.unique (.const hq)

theorem fold_bin_none {op : BinOp} {a b : RawExpr} (h : bothConst a b = false) :
    fold (.binop op a b) = none := by
  rw [fold]
  cases ha : fold a with
  | none => exact foldBin_none_left
  | some _ => cases hb : fold b with
    | none => exact foldBin_none_right
    | some _ => simp [bothConst, ha, hb] at h

/-- Operands meeting at a common type are not both constants. -/
theorem bothConst_of_common {a b : RawExpr} {τa τb : STy} (ha : Infers Γ a τa)
    (hb : Infers Γ b τb) (hc : STy.common? Γ.isBase Γ.mapFree τa τb = some τ) :
    bothConst a b = false := by
  cases hfa : fold a with
  | none => simp [bothConst, hfa]
  | some x => cases hfb : fold b with
    | none => simp [bothConst, hfb]
    | some y =>
      cases ha.ty_of_fold hfa; cases hb.ty_of_fold hfb
      simp [STy.common?, STy.isConstTy] at hc

/-- A local's resolution fact from its position among the locals. -/
theorem resolve_local {x : String} {i : Nat} (h : (Γ.locals.map Prod.fst).idxOf? x = some i) :
    Γ.resolve x = some (.loc i) := by
  simp [Source.Ctx.resolve, Source.Env.resolve, h]

section families
variable {op : BinOp} {a b : RawExpr} {τa τb : STy}

/-- `+ - * / %` (`add sub mul div mod`): numbers at a common type, no
constant zero divisor. -/
theorem Infers.arith (hop : family op = some .arith) (ha : Infers Γ a τa) (hb : Infers Γ b τb)
    (hc : STy.common? Γ.isBase Γ.mapFree τa τb = some τ) (hn : τ.isNumeric = true)
    (hz : (divMod op && τb.isZeroConst) = false) : Infers Γ (.binop op a b) τ :=
  .bin hop ha hb (fold_bin_none (bothConst_of_common ha hb hc)) rfl
    (by simp only [binTy, hz, hc, hn]; rfl)

/-- `& | ^` (`band bor bxor`): integers or `bytesN` at a common type. -/
theorem Infers.bit (hop : family op = some .bit) (ha : Infers Γ a τa) (hb : Infers Γ b τb)
    (hc : STy.common? Γ.isBase Γ.mapFree τa τb = some τ) (hn : τ.isBits = true) :
    Infers Γ (.binop op a b) τ :=
  .bin hop ha hb (fold_bin_none (bothConst_of_common ha hb hc)) rfl
    (by simp only [binTy, hc, hn]; rfl)

/-- `<<` and `>>` (`shl`, and `shr` spelled `sar`): bits by an unsigned
amount, at the left operand's shift type; not two constants. -/
theorem Infers.shift (hop : family op = some .shift) (ha : Infers Γ a τa) (hb : Infers Γ b τb)
    (h1 : τa.shiftTy.isBits = true) (h2 : τb.isAmount = true) (h3 : bothConst a b = false) :
    Infers Γ (.binop op a b) τa.shiftTy :=
  .bin hop ha hb (fold_bin_none h3) rfl (by simp [binTy, h1, h2, h3])

/-- `**` (`pow`): an integer to an unsigned power; not two constants. -/
theorem Infers.exp (hop : family op = some .exp) (ha : Infers Γ a τa) (hb : Infers Γ b τb)
    (h1 : τa.shiftTy.isInt = true) (h2 : τb.isAmount = true) (h3 : bothConst a b = false) :
    Infers Γ (.binop op a b) τa.shiftTy :=
  .bin hop ha hb (fold_bin_none h3) rfl (by simp [binTy, h1, h2, h3])

/-- `< > <= >=` (`lt gt le ge`): ordered operands at a common type. -/
theorem Infers.order (hop : family op = some .order) (ha : Infers Γ a τa) (hb : Infers Γ b τb)
    (hc : STy.common? Γ.isBase Γ.mapFree τa τb = some τ) (hn : τ.isOrdered = true) :
    Infers Γ (.binop op a b) .bool :=
  have h := bothConst_of_common ha hb hc
  .bin hop ha hb (fold_bin_none h) (by simp [h]) (by simp only [binTy, hc, hn]; rfl)

/-- `== !=` (`eqB neB`): operands with equality at a common type. -/
theorem Infers.eq (hop : family op = some .eq) (ha : Infers Γ a τa) (hb : Infers Γ b τb)
    (hc : STy.common? Γ.isBase Γ.mapFree τa τb = some τ) (hn : τ.hasEq = true) :
    Infers Γ (.binop op a b) .bool :=
  have h := bothConst_of_common ha hb hc
  .bin hop ha hb (fold_bin_none h) (by simp [h]) (by simp only [binTy, hc, hn]; rfl)

/-- Unary `-` on a signed integer. -/
theorem Infers.negInt {t : Source.IntTy} (ha : Infers Γ a (.int t)) (hs : t.signed = true) :
    Infers Γ (.unop .neg a) (.int t) := by
  refine .neg ha ?_ (by simp [negTy, hs])
  cases hf : fold a with
  | none => rfl
  | some q => cases ha.ty_of_fold hf

/-- Unary `-` on a fixed-point number. -/
theorem Infers.negFixed {f : Source.FixTy} (ha : Infers Γ a (.fixed f)) :
    Infers Γ (.unop .neg a) (.fixed f) := by
  refine .neg ha ?_ rfl
  cases hf : fold a with
  | none => rfl
  | some q => cases ha.ty_of_fold hf

/-- `~` on bits. -/
theorem Infers.bitNot' (ha : Infers Γ a τ) (hn : τ.isBits = true) : Infers Γ (.unop .bnot a) τ := by
  refine .bitNot ha ?_ hn
  cases hf : fold a with
  | none => rfl
  | some q => cases ha.ty_of_fold hf; cases hn

end families

/-- **Rejected forms have no inferred type** at any fuel, and no constant. -/
theorem Rejects.sound {r : Reason} (h : Rejects Γ e r) :
    ∀ {s : Syn .expr}, T.expr e = some s → s.const = none ∧ ∀ n, Typed.inferN n Γ s = none := by
  induction h with
  | @bin op k a b τa τb r hk hia hib hf hcc hty =>
    intro s hs
    obtain ⟨f', sa, sb, hf', hsa, hsb, rfl⟩ := expr_binop.mp hs
    obtain ⟨f, hff, hspec⟩ := binop_family hk
    cases hf'.symm.trans hff
    obtain ⟨hbo, hdm, hc, _, _⟩ := hspec sa sb
    have hca := hia.const_eq hsa
    have hcb := hib.const_eq hsb
    obtain ⟨da, ha⟩ := hia.inferN hsa
    obtain ⟨db, hb⟩ := hib.inferN hsb
    have hcs : (f' sa sb).const = none := by rw [hc, hca, hcb]; exact hf
    have hbc : (sa.const.isSome && sb.const.isSome) = bothConst a b := by rw [hca, hcb]; rfl
    refine ⟨hcs, fun n => ?_⟩
    cases n with
    | zero => exact inferN_zero
    | succ n =>
      rw [inferN_bin hbo, tryConst_none hcs, ha n, hb n]
      dsimp only [Option.orElse]
      by_cases h1 : depth a ≤ n <;> by_cases h2 : depth b ≤ n
      · rw [if_pos h1, if_pos h2]
        exact inferBin_error hbo (by rw [hbc]; exact hcc) (by rw [hdm, hbc]; exact hty)
      all_goals exact inferBin_none hbo (by rw [hbc]; exact hcc) (by simp [h1, h2])
  | @neg a τ r hia hf hty =>
    intro s hs
    obtain ⟨sa, hsa, rfl⟩ := expr_neg.mp hs
    have hcn : sa.const = none := (hia.const_eq hsa).trans hf
    obtain ⟨da, ha⟩ := hia.inferN hsa
    refine ⟨const_neg hcn, fun n => ?_⟩
    cases n with
    | zero => exact inferN_zero
    | succ n =>
      by_cases h1 : depth a ≤ n
      · exact inferN_neg_error hcn hty (by rw [ha n, if_pos h1])
      · exact inferN_neg_none hcn (by rw [ha n, if_neg h1])
  | @bitNot a τ hia hf hty =>
    intro s hs
    obtain ⟨sa, hsa, rfl⟩ := expr_bnot.mp hs
    have hcn : sa.const = none := (hia.const_eq hsa).trans hf
    obtain ⟨da, ha⟩ := hia.inferN hsa
    refine ⟨const_bitNot hcn, fun n => ?_⟩
    cases n with
    | zero => exact inferN_zero
    | succ n =>
      by_cases h1 : depth a ≤ n
      · exact inferN_bitNot_error hcn hty (by rw [ha n, if_pos h1])
      · exact inferN_bitNot_none hcn (by rw [ha n, if_neg h1])
  | @left op k a b r hk _ ih =>
    intro s hs
    obtain ⟨f', sa, sb, hf', hsa, hsb, rfl⟩ := expr_binop.mp hs
    obtain ⟨f, hff, hspec⟩ := binop_family hk
    cases hf'.symm.trans hff
    obtain ⟨hbo, _, hc, _, _⟩ := hspec sa sb
    obtain ⟨hca, ha⟩ := ih hsa
    have hcs : (f' sa sb).const = none := by rw [hc, hca]; exact foldBin_none_left
    refine ⟨hcs, fun n => ?_⟩
    cases n with
    | zero => exact inferN_zero
    | succ n =>
      rw [inferN_bin hbo, tryConst_none hcs]
      exact inferBin_none hbo (by simp [hca]) (Or.inl (ha n))
  | @right op k a b r hk _ ih =>
    intro s hs
    obtain ⟨f', sa, sb, hf', hsa, hsb, rfl⟩ := expr_binop.mp hs
    obtain ⟨f, hff, hspec⟩ := binop_family hk
    cases hf'.symm.trans hff
    obtain ⟨hbo, _, hc, _, _⟩ := hspec sa sb
    obtain ⟨hcb, hb⟩ := ih hsb
    have hcs : (f' sa sb).const = none := by rw [hc, hcb]; exact foldBin_none_right
    refine ⟨hcs, fun n => ?_⟩
    cases n with
    | zero => exact inferN_zero
    | succ n =>
      rw [inferN_bin hbo, tryConst_none hcs]
      exact inferBin_none hbo (by simp [hcb]) (Or.inr (hb n))
  | @negArg a r _ ih =>
    intro s hs
    obtain ⟨sa, hsa, rfl⟩ := expr_neg.mp hs
    obtain ⟨hca, ha⟩ := ih hsa
    refine ⟨const_neg hca, fun n => ?_⟩
    cases n with
    | zero => exact inferN_zero
    | succ n => exact inferN_neg_none hca (ha n)
  | @bitNotArg a r _ ih =>
    intro s hs
    obtain ⟨sa, hsa, rfl⟩ := expr_bnot.mp hs
    obtain ⟨hca, ha⟩ := ih hsa
    refine ⟨const_bitNot hca, fun n => ?_⟩
    cases n with
    | zero => exact inferN_zero
    | succ n => exact inferN_bitNot_none hca (ha n)

/-- A rejected form is outside the family. -/
theorem Rejects.not_infers {r : Reason} (h : Rejects Γ e r) : ¬ Infers Γ e τ := fun hi => by
  obtain ⟨s, hs, _, d, hd⟩ := hi.sound (T := Decode.tables1)
  have := (h.sound hs).2 (depth e)
  rw [hd, if_pos (Nat.le_refl _)] at this
  cases this

section rejections
variable {op : BinOp} {a b : RawExpr} {τa τb : STy}

theorem family_divMod (h : divMod op = true) : family op = some .arith := by
  cases op <;> first | rfl | cases h

/-- **Constant zero divisor**: `/` or `%` by a zero constant, whatever the
dividend. -/
theorem Rejects.zeroDivisor (hop : divMod op = true) (ha : Infers Γ a τa) (hb : Infers Γ b τb)
    (hz : τb.isZeroConst = true) : Rejects Γ (.binop op a b) .zeroDivisor := by
  refine .bin (family_divMod hop) ha hb ?_ rfl (by simp [binTy, hop, hz])
  rw [fold]
  cases hfa : fold a with
  | none => exact foldBin_none_left
  | some x => cases hfb : fold b with
    | none => exact foldBin_none_right
    | some y =>
      cases hb.ty_of_fold hfb
      have hy : y.num = 0 := by simpa [STy.isZeroConst] using hz
      cases op <;> first | (cases hop; done) | simp [foldBin, Q.div, Q.mod, hy]

/-- **Incompatible operands**: no common type, in a family that needs one. -/
theorem Rejects.noCommon {k : Family} (hop : family op = some k)
    (hk : k ≠ .shift ∧ k ≠ .exp) (ha : Infers Γ a τa) (hb : Infers Γ b τb)
    (hc : STy.common? Γ.isBase Γ.mapFree τa τb = none) (hnc : bothConst a b = false)
    (hz : (divMod op && τb.isZeroConst) = false) : Rejects Γ (.binop op a b) .incompatible := by
  refine .bin hop ha hb (fold_bin_none hnc) (by simp [hnc]) ?_
  cases k <;> simp_all [binTy]

/-- **Wrong amount**: a shift amount or exponent that is not unsigned. -/
theorem Rejects.badAmount {k : Family} (hop : family op = some k)
    (hk : k = .shift ∨ k = .exp) (ha : Infers Γ a τa) (hb : Infers Γ b τb)
    (hm : τb.isAmount = false) (hnc : bothConst a b = false) :
    Rejects Γ (.binop op a b) .incompatible := by
  refine .bin hop ha hb (fold_bin_none hnc) (by simp [hnc]) ?_
  rcases hk with rfl | rfl <;> simp [binTy, hm]

/-- **Wrong signedness**: unary `-` on an unsigned integer. -/
theorem Rejects.negUnsigned {t : Source.IntTy} (ha : Infers Γ a (.int t))
    (hs : t.signed = false) : Rejects Γ (.unop .neg a) .incompatible := by
  refine .neg ha ?_ (by simp [negTy, hs])
  cases hf : fold a with
  | none => rfl
  | some q => cases ha.ty_of_fold hf

end rejections

/-! ## Unsupported spellings -/

/-- The wrapping operators are the ones with no Source spelling. -/
theorem binop_eq_none_iff {op : BinOp} :
    Decode.binop op = none ↔ op = .addW ∨ op = .subW ∨ op = .mulW ∨ op = .powW := by
  cases op <;> simp [Decode.binop]

/-- Outside the families: the wrapping operators, and `&&`, `||` (spelled, the
scalar lane's). -/
theorem family_eq_none_iff {op : BinOp} :
    family op = none ↔ Decode.binop op = none ∨ op = .and ∨ op = .or := by
  cases op <;> simp [family, Decode.binop]

/-- **Unsupported spelling**: a wrapping operator is not decoded. -/
theorem expr_unspelled {op : BinOp} {a b : RawExpr} (h : Decode.binop op = none) :
    T.expr (.binop op a b) = none := by
  cases hs : T.expr (.binop op a b) with
  | none => rfl
  | some s => obtain ⟨f, _, _, hf, _⟩ := expr_binop.mp hs; rw [h] at hf; cases hf

/-- An undecoded operand leaves the operator form undecoded. -/
theorem expr_binop_none {op : BinOp} {a b : RawExpr} (h : T.expr a = none ∨ T.expr b = none) :
    T.expr (.binop op a b) = none := by
  cases hs : T.expr (.binop op a b) with
  | none => rfl
  | some s =>
    obtain ⟨_, _, _, _, ha, hb, _⟩ := expr_binop.mp hs
    rcases h with h | h
    · rw [h] at ha; cases ha
    · rw [h] at hb; cases hb

end Solidity.Correctness.Lowering.Total.ArithmeticInference
