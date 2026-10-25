import Solidity.Syntax.Splice
import Solidity.Semantics.Run

/-! Counterexamples to the requested uniform overflow/panic statement. -/
set_option maxRecDepth 2048

namespace Solidity.Bridge.Arith.Power

local instance : InContract := ⟨StandardExample⟩

/-- Explicit checked mode still reverts on full-width exponent overflow. -/
theorem checked_pow_reverts :
    Prog.run (State.init StandardExample)
      (sol{ checked { uint x = 2; uint y = 256; uint z = x ** y; }; }) = .error .revert := by
  rfl

example :
    Prog.run (State.init StandardExample)
      (sol{ checked { uint x = 2; uint y = 256; uint z = x ** y; }; }) ≠ .error .panic := by
  rw [checked_pow_reverts]
  intro h
  have hf : THalt.revert = THalt.panic := Except.error.inj h
  cases hf

/-- The primitive intermediate overflows before the narrow check can panic. -/
theorem checked_narrow_pow_reverts :
    Prog.run (State.init StandardExample)
      (sol{ checked { uint8 x = 2; uint y = 256; uint8 z = x ** y; }; }) = .error .revert := by
  rfl

example :
    Prog.run (State.init StandardExample)
      (sol{ checked { uint8 x = 2; uint y = 256; uint8 z = x ** y; }; }) ≠ .error .panic := by
  rw [checked_narrow_pow_reverts]
  intro h
  have hf : THalt.revert = THalt.panic := Except.error.inj h
  cases hf

/-- The smaller power reaches the width guard and does panic. -/
theorem checked_narrow_pow_panics :
    Prog.run (State.init StandardExample)
      (sol{ checked { uint8 x = 2; uint y = 8; uint8 z = x ** y; }; }) = .error .panic := by
  rfl

end Solidity.Bridge.Arith.Power

#print axioms Solidity.Bridge.Arith.Power.checked_pow_reverts
#print axioms Solidity.Bridge.Arith.Power.checked_narrow_pow_reverts
#print axioms Solidity.Bridge.Arith.Power.checked_narrow_pow_panics
