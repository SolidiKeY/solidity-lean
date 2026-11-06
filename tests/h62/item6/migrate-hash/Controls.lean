import tests.h62.item6.«migrate-hash».Adaptive

/- Finite kernel checks supplement the original universal proofs. These cases
   distinguish repeats from collisions, modular overlap/root hits, zero-width
   regions, and zero-query early stopping. No external EVM claim is made. -/
open Solidity.Hash

example : CollisionFree (fun _ : Nat => 0) [1, 1] := by decide +kernel
example : ¬ CollisionFree (fun _ : Nat => 0) [0, 1] := by decide +kernel
example : CollisionFree (fun _ : Nat => 0) [0] := by decide +kernel
example : RegionsDisjoint 8 0 (fun _ : Nat => 0) [0] [0, 1] := by decide +kernel
example : ¬ RegionsDisjoint 8 2 (fun x : Nat => x) [] [7, 0] := by decide +kernel
example : ¬ RegionsDisjoint 8 2 (fun _ : Nat => 7) [0] [0] := by decide +kernel
example : RegionsDisjoint 8 2 (fun x : Nat => x) [7] [0, 3] := by decide +kernel
example : Near 8 2 7 0 := by decide +kernel
example : Covers 8 2 7 0 := by decide +kernel
example : collisions 0 0 = 0 := by decide +kernel
example : collisions 2 2 = 2 := by decide +kernel
example : collisions 2 3 = 8 := by decide +kernel
example : collisions 3 2 = 3 := by decide +kernel
example : eagerCollides (fun _ : List Nat => 0) [0, 1] 3 [2, 2] = false := by decide +kernel
example : eagerCollides (fun t : List Nat => t.length) [0, 1, 2] 3 [0, 0, 1] = true := by decide +kernel
example : eagerCollides (fun t : List Nat => t.length) [0, 1] 0 [0, 0] = false := by decide +kernel
example : stepHit (fun _ : List Nat => 0) [0] repeatBad 1 [0] = false := by decide +kernel
example : eagerRegionsFail (fun _ : List Nat => 0) [0] 8 0 [] 3 [0] = false := by decide +kernel
example : eagerRegionsFail (fun _ : List Nat => 0) [0] 8 2 [0] 1 [0] = true := by decide +kernel
