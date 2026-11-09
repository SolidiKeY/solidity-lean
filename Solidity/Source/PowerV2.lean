import Solidity.Source.Value

/-! Versioned correction for the fixed 300-step power cutoff: an exponent-derived progress counter permits every natural exponent. Existing Source.powMod/intPow and evaluator remain V1. This operator API selects no production endpoint or admission domain. -/
namespace Solidity.Source.PowerV2

def powMod (base : Int) (exponent modulus : Nat) : Int :=
  Solidity.Source.powMod.go modulus exponent base exponent 1

def intPow {D : Layout} (t : IntTy) (checked : Bool) (base : Int) (exponent : Nat) :
    R (Val D (.int t)) :=
  if checked then Solidity.Source.intPow t checked base exponent
  else pure (intWrap t (powMod base exponent (2 ^ t.bits)))

end Solidity.Source.PowerV2
