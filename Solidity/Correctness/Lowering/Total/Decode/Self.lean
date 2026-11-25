import Solidity.Correctness.Lowering.Total.Decode.Marked

/-!
# The running account: `address(this)` and its balance

`tablesT`: as the caller-aware `tablesS`, and the two remaining environment
reads are spelled. The keys are the model's own-address read
(`EnvKey.selfAddress`: the grammar's `this` where an address stands; the
surface `address(this)` is the raw call `address` of it, a cast, read by
`Decode.Casts`) and own-balance read (`EnvKey.selfBalance`). The model's
own-address read is the Source conversion
`address(this)`, an `address`; the model's `address(this).balance` is the
Source `address(this).balance`, a `uint256`. With these the environment table
has no gap: `envT_total`.

The decoder only spells. That the model's own address and own balance are the
Source frame's is a clause of the version state relation
(`Version.Relation.glob`), and the reads agree under it
(`Version.selfAddress_faithful`, `Version.selfBalance_faithful`).
-/
namespace Solidity.Correctness.Lowering.Total.Decode

open Source (Syn)

/-- The Source spelling of the model's own address: `address(this)`. -/
def thisAddress : Syn .expr :=
  .call (.elemType .address (by decide)) (.positional (.cons (.ident "this") .nil))

/-- The Source spelling of the model's own balance: `address(this).balance`. -/
def thisBalance : Syn .expr := .member thisAddress "balance"

/-- Environment reads with the caller, the own address and the own balance. -/
def envT : EnvKey → Option (Syn .expr)
  | .selfAddress => some thisAddress
  | .selfBalance => some thisBalance
  | k => envS k

/-- Every environment read is spelled. -/
theorem envT_total (k : EnvKey) : (envT k).isSome = true := by
  cases k <;> rfl

/-- Outside the two own-account reads the table is the caller-aware one. -/
theorem envT_envS {k : EnvKey} (address : k ≠ .selfAddress) (balance : k ≠ .selfBalance) :
    envT k = envS k := by
  cases k <;> first | rfl | contradiction

/-- The self-aware decoder's tables. -/
def tablesT : Tables := { tablesS with env := envT }

end Solidity.Correctness.Lowering.Total.Decode
