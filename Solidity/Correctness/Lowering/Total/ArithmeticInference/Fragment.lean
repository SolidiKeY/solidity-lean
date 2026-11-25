import Solidity.Correctness.Lowering.Total.ArithmeticInference.Model

namespace Solidity.Correctness.Lowering.Total.ArithmeticInference

open Source (STy Syn Ctx Typed BinKind Inferred Q)
open Decode (Tables)

/-- **The arithmetic argument family**, by explicit conditions on the model
expression: a folding constant; a local with its resolution and slot type; a
supported binary operator over the family whose operand types pass the
family's check; a comparison of two constants; `-` and `~`. -/
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

/-- **Rejected forms** of the family, with the reason. -/
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

theorem depth_pos : 0 < depth e := by
  cases e <;> simp only [depth] <;> (try split) <;> omega

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
    | succ n => rw [inferN_local hr ht, if_pos (by simp [depth])]
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

end Solidity.Correctness.Lowering.Total.ArithmeticInference
