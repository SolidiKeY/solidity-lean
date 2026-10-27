import Solidity.Syntax.Scoped

/-! Existing intrinsic value constructors composed for checked signed power.
The unsigned exponent and signed base retain their distinct primitive types. -/
namespace Solidity.Val

private abbrev u {C : Contract} {Γ : Ctx} (n : Int) (h : PrimTy.uint.inRange n = true) :
    Val C Γ .uint := .simple (.lit n h)
private abbrev i {C : Contract} {Γ : Ctx} (n : Int) (h : PrimTy.int.inRange n = true) :
    Val C Γ .int := .simple (.lit n h)

def signedMagnitude {C : Contract} {Γ : Ctx} (a : Val C Γ .int) : Val C Γ .uint :=
  let word : Val C Γ .uint := .unop .toUint rfl rfl a
  .ternary (.binop .lt rfl rfl a (i 0 rfl))
    (.binop .subW rfl rfl (u 0 rfl) word) word

/-- Unit magnitudes avoid recursive evaluation at arbitrarily large exponents. -/
def magnitudePower {C : Contract} {Γ : Ctx} (m b : Val C Γ .uint) : Val C Γ .uint :=
  .ternary (.binop .le rfl rfl m (u 1 rfl))
    (.ternary (.binop .eqB rfl rfl b (u 0 rfl)) (u 1 rfl) m)
    (.binop .pow rfl rfl m b)

def powerNegative {C : Contract} {Γ : Ctx} (a : Val C Γ .int) (b : Val C Γ .uint) : Val C Γ .bool :=
  .binop .and rfl rfl (.binop .lt rfl rfl a (i 0 rfl))
    (.binop (p := .uint) .eqB rfl rfl (.binop .mod rfl rfl b (u 2 rfl)) (u 1 rfl))

/-- Admit 2^255 only for a negative result. The failing signed add preserves
arithmetic-overflow classification in the existing panic instrumentation. -/
def signedPowerResult {C : Contract} {Γ : Ctx} (negative : Val C Γ .bool)
    (power : Val C Γ .uint) : Val C Γ .int :=
  let bound : Val C Γ .uint := u ((2^255 : Nat) : Int) (by decide)
  let valid : Val C Γ .bool := .ternary negative
    (.binop .le rfl rfl power bound) (.binop .lt rfl rfl power bound)
  let result : Val C Γ .int := .unop .toInt rfl rfl
    (.ternary negative (.binop .subW rfl rfl (u 0 rfl) power) power)
  .ternary valid result (.binop .add rfl rfl (i ((2^255-1 : Nat) : Int) (by decide)) (i 1 rfl))

def checkedSignedPower {C : Contract} {Γ : Ctx}
    (a : Val C Γ .int) (b : Val C Γ .uint) : Val C Γ .int :=
  signedPowerResult (powerNegative a b) (magnitudePower (signedMagnitude a) b)
end Solidity.Val
