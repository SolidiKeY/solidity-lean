import Solidity.Calculus.DecisionUIntGrammar

/-!
# Literal-linear uint formulas through both source polarities

Intrinsic source constructors, independent of coverage/decision success.
The resulting body grammar is the existing numeric source fragment.
-/
namespace Solidity

/-- Quantifier-free logical combinations of literal-linear uint equations. -/
inductive Fml.QFUIntLinear {C : Contract} {Γ : Ctx} : Fml C Γ → Prop where
  | tt : Fml.QFUIntLinear .tt
  | eq {a b : Tm C Γ (.val .uint)} : a.UIntLinear → b.UIntLinear → Fml.QFUIntLinear (.eq a b)
  | not {φ : Fml C Γ} : φ.QFUIntLinear → Fml.QFUIntLinear (.not φ)
  | and {φ ψ : Fml C Γ} : φ.QFUIntLinear → ψ.QFUIntLinear → Fml.QFUIntLinear (.and φ ψ)
  | imp {φ ψ : Fml C Γ} : φ.QFUIntLinear → ψ.QFUIntLinear → Fml.QFUIntLinear (.imp φ ψ)

namespace Decide

/-- Optional equality, including the case where both arithmetic terms halt. -/
theorem optEq_numeric_src {C : Contract} {p : PrimTy} {c w : Bool}
    {a b : LTm C (.val p)} (ha : a.Src c w .num) (hb : b.Src c w .num) :
    (LFml.optEq a b).Src c w :=
  .and (.imp (LFml.SrcL.ofNums ha ha)
      (.imp (LFml.SrcL.ofNums hb hb) (LFml.SrcL.ofNums ha hb)))
    (.and (.imp (LFml.SrcL.ofNums ha ha) (LFml.SrcL.ofNums hb hb))
      (.imp (LFml.SrcL.ofNums hb hb) (LFml.SrcL.ofNums ha ha)))

theorem uintLinear_eqAt_polarity {C : Contract} {Γ : Ctx}
    {a b : Tm C Γ (.val .uint)} (ha : a.UIntLinear) (hb : b.UIntLinear)
    (x y : LTm C (.val .uint)) (pos : Bool) :
    Fml.eqAt pos a b x y = Fml.eqAt true a b x y := by
  unfold Fml.eqAt
  rw [uintLinear_agrees ha, uintLinear_agrees hb]
  rfl

theorem uintLinear_eqAt_src {C : Contract} {Γ : Ctx}
    {a b : Tm C Γ (.val .uint)} (ha : a.UIntLinear) (hb : b.UIntLinear)
    {x y : LTm C (.val .uint)} (hx : x.Src false true .num) (hy : y.Src false true .num)
    (pos : Bool) : (Fml.eqAt pos a b x y).Src false true := by
  unfold Fml.eqAt
  rw [uintLinear_agrees ha, uintLinear_agrees hb]
  simp only [Bool.true_and, if_true]
  split
  · exact LFml.SrcL.ofNums hx hy
  · exact optEq_numeric_src hx hy

/-- Construct the actual translated formula, identically at both polarities. -/
theorem qfUIntLinear_toLS {C : Contract} {Γ : Ctx} {φ : Fml C Γ}
    (h : φ.QFUIntLinear) (ρ : SymS C Γ) (hρ : UIntSourceLocs ρ) :
    ∃ ψ : LFml C, φ.toLS true ρ = some ψ ∧ φ.toLS false ρ = some ψ ∧ ψ.Src false true := by
  induction h with
  | tt => exact ⟨.tt, rfl, rfl, .tt⟩
  | @eq a b ha hb =>
    obtain ⟨u, hu, hsu⟩ := uintLinear_toL ha ρ hρ
    obtain ⟨v, hv, hsv⟩ := uintLinear_toL hb ρ hρ
    refine ⟨Fml.eqAt true a b u v, ?_, ?_, uintLinear_eqAt_src ha hb hsu hsv true⟩
    · change (a.toL ρ).bind (fun x => (b.toL ρ).map (fun y => Fml.eqAt true a b x y)) = _
      rw [hu, hv]
      rfl
    · change (a.toL ρ).bind (fun x => (b.toL ρ).map (fun y => Fml.eqAt false a b x y)) = _
      rw [hu, hv]
      exact congrArg some (uintLinear_eqAt_polarity ha hb u v false)
  | @not φ h ih =>
    obtain ⟨ψ, hp, hn, hs⟩ := ih
    refine ⟨.not ψ, ?_, ?_, .not hs⟩
    · change (φ.toLS false ρ).map LFml.not = _
      rw [hn]
      rfl
    · change (φ.toLS true ρ).map LFml.not = _
      rw [hp]
      rfl
  | @and φ χ hφ hχ ihφ ihχ =>
    obtain ⟨ψ, hp, hn, hs⟩ := ihφ
    obtain ⟨θ, kp, kn, ks⟩ := ihχ
    refine ⟨.and ψ θ, ?_, ?_, .and hs ks⟩
    · change (φ.toLS true ρ).bind (fun x => (χ.toLS true ρ).map (LFml.and x)) = _
      rw [hp, kp]
      rfl
    · change (φ.toLS false ρ).bind (fun x => (χ.toLS false ρ).map (LFml.and x)) = _
      rw [hn, kn]
      rfl
  | @imp φ χ hφ hχ ihφ ihχ =>
    obtain ⟨ψ, hp, hn, hs⟩ := ihφ
    obtain ⟨θ, kp, kn, ks⟩ := ihχ
    refine ⟨.imp ψ θ, ?_, ?_, .imp hs ks⟩
    · change (φ.toLS false ρ).bind (fun x => (χ.toLS true ρ).map (LFml.imp x)) = _
      rw [hn, kp]
      rfl
    · change (φ.toLS true ρ).bind (fun x => (χ.toLS false ρ).map (LFml.imp x)) = _
      rw [hp, kn]
      rfl

/-- Source admission of every logical constructor, at either polarity. -/
theorem qfUIntLinear_target {C : Contract} {Γ : Ctx} {φ : Fml C Γ}
    (h : φ.QFUIntLinear) (w : Waivers) (pol n : Bool) : φ.target w pol n = true := by
  induction h generalizing pol with
  | tt => rfl
  | @eq a b ha hb =>
    change Bool.and (a.inTarget w (a.hashPair b)) (b.inTarget w (a.hashPair b)) = true
    rw [uintLinear_admitted_at ha w _, uintLinear_admitted_at hb w _]
    rfl
  | @not φ h ih => exact ih (!pol)
  | @and φ ψ hφ hψ ihφ ihψ =>
    change Bool.and (φ.target w pol n) (ψ.target w pol n) = true
    rw [ihφ pol, ihψ pol]
    rfl
  | @imp φ ψ hφ hψ ihφ ihψ =>
    change Bool.and (φ.target w (!pol) n) (ψ.target w pol n) = true
    rw [ihφ (!pol), ihψ pol]
    rfl

theorem qfUIntLinear_mapKeys {C : Contract} {Γ : Ctx} {φ : Fml C Γ}
    (h : φ.QFUIntLinear) : φ.mapKeys = [] := by
  induction h with
  | tt => rfl
  | eq ha hb =>
    simp only [Fml.mapKeys, uintLinear_mapKeys ha, uintLinear_mapKeys hb, List.nil_append]
  | not h ih => exact ih
  | @and φ ψ hφ hψ ihφ ihψ | @imp φ ψ hφ hψ ihφ ihψ =>
    change φ.mapKeys ++ ψ.mapKeys = []
    rw [ihφ, ihψ]
    rfl

theorem qfUIntLinear_negPairUnread {C : Contract} {Γ : Ctx} {φ : Fml C Γ}
    (h : φ.QFUIntLinear) (rd : List (Tm C Γ (.val .uint))) (pol : Bool) :
    φ.negPairUnread rd pol = false := by
  induction h generalizing pol <;> simp_all only [Fml.negPairUnread, Bool.false_or]

/-- The closed source class is admitted by the complete frozen source predicate. -/
theorem qfUIntLinear_inTarget {C : Contract} {φ : Fml C []}
    (h : φ.QFUIntLinear) (w : Waivers) : φ.inTarget w = true := by
  unfold Fml.inTarget
  rw [qfUIntLinear_target h w true false, qfUIntLinear_mapKeys h,
    qfUIntLinear_negPairUnread h _ true]
  rfl

end Decide
end Solidity
