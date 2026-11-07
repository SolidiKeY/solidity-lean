"""Exact authorized source transformations. Unlisted bytes must remain at base.
The two original dependent definitions are restored; comparison fixtures are additive only.
"""
CHANGES = {
 "Solidity/Precompiles/Bls12381.lean": [
  ('/-- The MSM gas of `k` pairs', '/-- Structural lookup without the unused proof fields of an indexing instance. -/\nprivate def msmLookup (table : List Nat) (index cap : Nat) : Nat :=\n  List.casesOn table cap fun a tail =>\n    Nat.casesOn index a fun i => msmLookup tail i cap\n\nprivate theorem msmLookup_eq_getD (table : List Nat) (index cap : Nat) :\n    msmLookup table index cap = table.getD index cap := by\n  induction table generalizing index with\n  | nil => rfl\n  | cons a table ih =>\n    cases index with\n    | zero => rfl\n    | succ i => exact ih i\n\n/-- The MSM gas of `k` pairs'),
  ("theorem g1Discount_length : g1Discount.length = 128 := rfl", "theorem g1Discount_length : g1Discount.length = 128 := by decide +kernel"),
  ("theorem g2Discount_length : g2Discount.length = 128 := rfl", "theorem g2Discount_length : g2Discount.length = 128 := by decide +kernel")],
 "Solidity/Precompiles/PointEval.lean": [("| none => exact Option.noConfusion h", "| none => cases h")],

 "Solidity/Precompiles/Osaka.lean": [("  show pinned.stipend < 3000\n  decide", "  show pinned.stipend < 3000\n  exact @of_decide_eq_true _ (Nat.decLt _ _) rfl")]
}
def expected(data, path):
    text=data.decode()
    for old,new in CHANGES.get(path,[]):
        if text.count(old)!=1:raise ValueError("frozen source no longer matches authorized edit: "+path)
        text=text.replace(old,new)
    return text.encode()
