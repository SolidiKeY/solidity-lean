import Solidity.Source.Value

/-! Versioned correction for the fixed 300-step power cutoff: an exponent-derived progress counter permits every natural exponent. Existing Source.powMod/intPow and evaluator remain V1. The typed shift dispatcher delegates all non-power/non-integer cases to V1. This operator API selects no production endpoint or admission domain. -/
namespace Solidity.Source.PowerV2

def powMod (base : Int) (exponent modulus : Nat) : Int :=
  Solidity.Source.powMod.go modulus exponent base exponent 1

def intPow {D : Layout} (t : IntTy) (checked : Bool) (base : Int) (exponent : Nat) :
    R (Val D (.int t)) :=
  if checked then Solidity.Source.intPow t checked base exponent
  else pure (intWrap t (powMod base exponent (2 ^ t.bits)))

def shiftVal {D : Layout} (checked : Bool) (op : BinOp) (exponent : Nat)
    {τ : STy} (value : Val D τ) : R (Val D τ) :=
  Val.casesOn (motive := fun kind _ => R (Val D kind)) value
    (fun {t} base bound =>
      if op = .exp then intPow t checked base exponent
      else Solidity.Source.shiftVal checked op exponent (.int base bound))
    (fun b => Solidity.Source.shiftVal checked op exponent (.bool b))
    (fun {_} a => Solidity.Source.shiftVal checked op exponent (.address a))
    (fun {_} {_} bs bound => Solidity.Source.shiftVal checked op exponent (.fixedBytes bs bound))
    (fun {_} x bound => Solidity.Source.shiftVal checked op exponent (.fixed x bound))
    (fun {_} i => Solidity.Source.shiftVal checked op exponent (.enum i))
    (fun {_} x => Solidity.Source.shiftVal checked op exponent (.udvt x))
    (fun {_} a => Solidity.Source.shiftVal checked op exponent (.contract a))
    (fun {_} {_} {_} d => Solidity.Source.shiftVal checked op exponent (.internalFn d))
    (fun {_} {_} {_} a sel bound => Solidity.Source.shiftVal checked op exponent (.externalFn a sel bound))
    (fun {_} h addr => Solidity.Source.shiftVal checked op exponent (.memRef h addr))
    (fun {_} h path => Solidity.Source.shiftVal checked op exponent (.storRef h path))
    (fun {_} h off len => Solidity.Source.shiftVal checked op exponent (.cdRef h off len))

end Solidity.Source.PowerV2
