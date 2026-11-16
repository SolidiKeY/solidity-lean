import Solidity.Goals.ProseCalibrated

namespace Solidity.Docs.ProseCalibrated

open Solidity.Goals.ProseCalibrated

theorem rational_refl (x : Rational) : x.le x := Nat.le_refl _

theorem rational_trans (x y z : Rational) (h : x.le y) (k : y.le z) : x.le z := by
  apply Nat.le_of_mul_le_mul_right (c := y.den) _ y.den_pos
  have h' := Nat.mul_le_mul_right z.den h
  have k' := Nat.mul_le_mul_right x.den k
  calc
    x.num * z.den * y.den = x.num * y.den * z.den := by ac_rfl
    _ ≤ y.num * x.den * z.den := h'
    _ = y.num * z.den * x.den := by ac_rfl
    _ ≤ z.num * y.den * x.den := k'
    _ = z.num * x.den * y.den := by ac_rfl

theorem exact : ∀ (w : Allowance) (n d : Nat),
    w.fits n d = true ↔ Allowance.Within w n d := by
  intro w n d
  simp only [Allowance.fits, decide_eq_true_eq, Allowance.Within, Rational.ofNat,
    Allowance.value, Rational.scale, Rational.add, Solidity.Goals.ProseRatio.Ratio.le,
    Nat.mul_one, Nat.mul_assoc]

theorem floorSum : ∀ (w : Allowance) (n d : Nat),
    n ≤ Allowance.lines w d ↔ w.Within n d := by
  intro w n d
  simp only [Allowance.lines, Allowance.Within, Rational.ofNat,
    Solidity.Goals.ProseRatio.Ratio.le, Nat.mul_one]
  exact Nat.le_div_iff_mul_le (w.value d).den_pos

theorem boundary : ∀ (w : Allowance) (d : Nat),
    w.fits (w.lines d) d = true ∧ w.fits (w.lines d + 1) d = false := by
  intro w d
  constructor
  · exact (exact w _ d).mpr ((floorSum w _ d).mp (Nat.le_refl _))
  · cases h : w.fits (w.lines d + 1) d
    · rfl
    · have := (floorSum w _ d).mpr ((exact w _ d).mp h)
      omega

theorem zeroEvaluation : ∀ (w : Allowance) (n : Nat),
    w.Within n 0 ↔ (Rational.ofNat n).le w.margin := by
  intro w n
  simp only [Allowance.Within, Allowance.value, Rational.scale, Rational.add,
    Rational.ofNat, Solidity.Goals.ProseRatio.Ratio.le, Nat.mul_zero, Nat.zero_mul,
    Nat.zero_add, Nat.mul_one]
  simpa only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using
    (Nat.mul_le_mul_right_iff w.ratio.den_pos :
      n * w.margin.den * w.ratio.den ≤ w.margin.num * w.ratio.den ↔
        n * w.margin.den ≤ w.margin.num)

theorem min_below (w v : Allowance) : (w.min v).le w ∧ (w.min v).le v := by
  have lower (x y : Rational) : (x.min y).le x ∧ (x.min y).le y := by
    unfold Solidity.Goals.ProseRatio.Ratio.min
    split
    · rename_i h
      exact ⟨rational_refl x, h⟩
    · rename_i h
      exact ⟨(Nat.le_total (x.num * y.den) (y.num * x.den)).resolve_left h, rational_refl y⟩
  exact ⟨⟨(lower w.ratio v.ratio).1, (lower w.margin v.margin).1⟩,
    ⟨(lower w.ratio v.ratio).2, (lower w.margin v.margin).2⟩⟩

theorem fits_antitone (w : Allowance) (n m d : Nat) (h : n ≤ m)
    (hm : w.fits m d = true) : w.fits n d = true := by
  apply (exact w n d).mpr
  apply (floorSum w n d).mp
  exact Nat.le_trans h ((floorSum w m d).mpr ((exact w m d).mp hm))

theorem byValue : ∀ (w v : Allowance), w.equiv v →
    ∀ n d, w.fits n d = v.fits n d := by
  intro w v h n d
  have scale_le (x y : Rational) (h : x.le y) (d : Nat) :
      (x.scale d).le (y.scale d) := by
    have hd := Nat.mul_le_mul_right d h
    simpa only [Rational.scale, Solidity.Goals.ProseRatio.Ratio.le,
      Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hd

  have add_le (x y u v : Rational) (h : x.le y) (k : u.le v) :
      (x.add u).le (y.add v) := by
    change (x.num * u.den + u.num * x.den) * (y.den * v.den) ≤
      (y.num * v.den + v.num * y.den) * (x.den * u.den)
    have h' := Nat.mul_le_mul_right (u.den * v.den) h
    have k' := Nat.mul_le_mul_right (x.den * y.den) k
    calc
      _ = (x.num * y.den) * (u.den * v.den) +
          (u.num * v.den) * (x.den * y.den) := by
        simp only [Nat.add_mul]; congr 1 <;> ac_rfl
      _ ≤ (y.num * x.den) * (u.den * v.den) +
          (v.num * u.den) * (x.den * y.den) := Nat.add_le_add h' k'
      _ = _ := by simp only [Nat.add_mul]; congr 1 <;> ac_rfl

  have value_le (w v : Allowance) (h : w.le v) (d : Nat) :
      (w.value d).le (v.value d) :=
    add_le _ _ _ _ (scale_le _ _ h.1 d) h.2
  have hwv : w.fits n d = true ↔ v.fits n d = true := by
    rw [exact, exact]
    exact ⟨fun hn => rational_trans _ _ _ hn (value_le w v h.1 d),
      fun hn => rational_trans _ _ _ hn (value_le v w h.2 d)⟩
  cases hw : w.fits n d <;> cases hv : v.fits n d <;> simp_all

private theorem margin_zero (r : Rational) (hr : r.num = 0) (h : List (Nat × Nat)) :
    (historicalMargin r h).equiv (Rational.ofNat ((h.map (·.1)).foldl Nat.max 0)) := by
  have history_zero (r : Rational) (hr : r.num = 0)
      (h : List (Nat × Nat)) (m : Rational) (a : Nat) (hm : m.num = a * m.den) :
      (h.foldl (fun m nd => let x := residual r nd.1 nd.2; if m.le x then x else m) m).num =
      ((h.map (·.1)).foldl Nat.max a) *
        (h.foldl (fun m nd => let x := residual r nd.1 nd.2; if m.le x then x else m) m).den := by
    induction h generalizing m a with
    | nil => exact hm
    | cons nd h ih =>
      have hc : m.le (residual r nd.1 nd.2) ↔ a ≤ nd.1 := by
        simp only [Solidity.Goals.ProseRatio.Ratio.le, residual, hr, Nat.zero_mul,
          Nat.sub_zero, hm]
        simpa only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using
          (Nat.mul_le_mul_right_iff (Nat.mul_pos m.den_pos r.den_pos) :
            a * (m.den * r.den) ≤ nd.1 * (m.den * r.den) ↔ a ≤ nd.1)
      simp only [List.foldl_cons, List.map_cons, Nat.max_eq_max]
      by_cases ha : a ≤ nd.1
      · rw [if_pos (hc.mpr ha), Nat.max_eq_right ha]
        apply ih _ nd.1
        simp only [residual, hr, Nat.zero_mul, Nat.sub_zero]
      · rw [if_neg (fun hx => ha (hc.mp hx)), Nat.max_eq_left (Nat.le_of_not_ge ha)]
        exact ih m a hm
  have he := history_zero r hr h Rational.zero 0 rfl
  constructor <;>
    simp only [Solidity.Goals.ProseRatio.Ratio.le, Rational.ofNat, Nat.mul_one]
  · exact Nat.le_of_eq he
  · exact Nat.le_of_eq he.symm

theorem zeroAnchor : ∀ (n : Nat) (h : List (Nat × Nat)),
    (calibrate n 0 h).ratio.equiv .zero ∧
    (calibrate n 0 h).margin.equiv (Rational.ofNat ((h.map (·.1)).foldl Nat.max 0)) := by
  intro n h
  simp only [calibrate, Nat.lt_irrefl, dite_false]
  exact ⟨⟨rational_refl _, rational_refl _⟩, margin_zero _ rfl h⟩

theorem zeroNumerator : ∀ (d : Nat) (h : List (Nat × Nat)),
    (calibrate 0 d h).ratio.equiv .zero ∧
    (calibrate 0 d h).margin.equiv (Rational.ofNat ((h.map (·.1)).foldl Nat.max 0)) := by
  intro d h
  unfold calibrate
  split
  · constructor
    · constructor <;> simp only [Solidity.Goals.ProseRatio.Ratio.le, Rational.zero,
        Nat.zero_mul, Nat.le_refl]
    · exact margin_zero _ rfl h
  · exact ⟨⟨rational_refl _, rational_refl _⟩, margin_zero _ rfl h⟩

end Solidity.Docs.ProseCalibrated
