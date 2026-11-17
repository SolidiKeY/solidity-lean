/- Heartbeat collector fixture (`test_collect.py`): the `decide +kernel` proofs
are checked by the kernel only, so their heartbeats are counted only when
elaboration is synchronous (`Elab.async=false`). -/

def sumTo (n : Nat) : Nat := (List.range n).foldl (· + ·) 0

theorem heavy : sumTo 400 = 79800 := by decide +kernel

theorem light : sumTo 4 = 6 := by decide +kernel

example : True := trivial
