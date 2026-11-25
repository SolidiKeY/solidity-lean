import Solidity.Correctness.Lowering.Total.Decode.Marked

/-!
# The running account: `address(this)` and its balance

`tablesT`: as the caller-aware `tablesS`, with the two remaining environment
reads spelled. The own-address read (`EnvKey.selfAddress`: the grammar's
`this` where an address stands; the surface `address(this)` is a cast of it,
read by `Decode.Casts`) is the Source `address(this)`; the own-balance read
(`EnvKey.selfBalance`) is the Source `address(this).balance`. The environment
table then has no gap (`envT_total`). The decoder only spells: the state
relation's clauses and the faithfulness lemmas are in `Versions.Self`.
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

/-- The self-aware decoder's tables. -/
def tablesT : Tables := { tablesS with env := envT }

end Solidity.Correctness.Lowering.Total.Decode
