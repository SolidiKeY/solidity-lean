import Solidity.Docs.ProseCalibrated.Allowance

namespace Solidity.Examples.Docs.ProseCalibrated

open Solidity.Goals.ProseCalibrated

-- Pin the complete arithmetic field types without assuming a Laws instance.
example : ∀ (w : Allowance) (n d : Nat),
    w.fits n d = true ↔ Allowance.Within w n d := Solidity.Docs.ProseCalibrated.exact

example : ∀ (w : Allowance) (n d : Nat),
    n ≤ Allowance.lines w d ↔ w.Within n d := Solidity.Docs.ProseCalibrated.floorSum

example : ∀ (w : Allowance) (d : Nat),
    w.fits (w.lines d) d = true ∧ w.fits (w.lines d + 1) d = false := Solidity.Docs.ProseCalibrated.boundary

example : ∀ (w v : Allowance), w.equiv v → ∀ n d,
    w.fits n d = v.fits n d := Solidity.Docs.ProseCalibrated.byValue

example : ∀ (w : Allowance) (n : Nat),
    w.Within n 0 ↔ (Rational.ofNat n).le w.margin := Solidity.Docs.ProseCalibrated.zeroEvaluation

example : ∀ (n : Nat) (h : List (Nat × Nat)),
    (calibrate n 0 h).ratio.equiv .zero ∧
    (calibrate n 0 h).margin.equiv (Rational.ofNat ((h.map (·.1)).foldl Nat.max 0)) :=
  Solidity.Docs.ProseCalibrated.zeroAnchor

example : ∀ (d : Nat) (h : List (Nat × Nat)),
    (calibrate 0 d h).ratio.equiv .zero ∧
    (calibrate 0 d h).margin.equiv (Rational.ofNat ((h.map (·.1)).foldl Nat.max 0)) :=
  Solidity.Docs.ProseCalibrated.zeroNumerator

example (x : Rational) : x.le x := Solidity.Docs.ProseCalibrated.rational_refl x

example (x y z : Rational) (h : x.le y) (k : y.le z) : x.le z :=
  Solidity.Docs.ProseCalibrated.rational_trans x y z h k

example (w v : Allowance) : (w.min v).le w ∧ (w.min v).le v := Solidity.Docs.ProseCalibrated.min_below w v

example (w : Allowance) (n m d : Nat) (h : n ≤ m) (hm : w.fits m d = true) :
    w.fits n d = true := Solidity.Docs.ProseCalibrated.fits_antitone w n m d h hm

end Solidity.Examples.Docs.ProseCalibrated
