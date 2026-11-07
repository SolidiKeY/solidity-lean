import Init
import Solidity.Roadmap.Evm

/-! Isolated exact subgoal from CollisionBound line 407. This does not import
or repair the owner module, or establish the two remaining arithmetic proofs. -/
namespace MigrateRoadmapFixtures

theorem contains_cons_function (x : Nat) (t : List Nat) :
    (fun a => (x :: t).contains a) = (fun a => (a == x) || t.contains a) := by
  funext a
  exact List.contains_cons

theorem countP_split (A t : List Nat) (x : Nat) :
    A.countP (fun a => (x :: t).contains a) =
      A.countP (fun a => (a == x) || t.contains a) := by
  congr 1
  exact contains_cons_function x t

theorem rejects_dropped_head :
    ([1, 2].countP (fun a => ([1] : List Nat).contains a)) ≠
      ([1, 2].countP (fun a => ([] : List Nat).contains a)) := by decide

theorem rejects_dropped_tail :
    ([1, 2].countP (fun a => ([1, 2] : List Nat).contains a)) ≠
      ([1, 2].countP (fun a => a == 1)) := by decide

#print axioms MigrateRoadmapFixtures.contains_cons_function
#print axioms MigrateRoadmapFixtures.countP_split
end MigrateRoadmapFixtures

/-! Compatibility candidates live only in this test module. Moving these exact
names into the existing Evm producer requires its owner's reply. -/
namespace Solidity.Roadmap.Evm

@[deprecated Fork.ctorIdx (since := "2025-08-25")]
protected abbrev Fork.toCtorIdx : Fork → Nat := Fork.ctorIdx

@[deprecated Precompile.ctorIdx (since := "2025-08-25")]
protected abbrev Precompile.toCtorIdx : Precompile → Nat := Precompile.ctorIdx

theorem beBytes._proof_2 (n : Nat) (h : n ≠ 0) :
    (invImage (fun x : Nat => x) (sizeOfWFRel : WellFoundedRelation Nat)).1 (n / 256) n := by
  change n / 256 < n
  exact Nat.div_lt_self (Nat.pos_of_ne_zero h) (by decide)

theorem legacy_fork_index (fork : Fork) : fork.toCtorIdx = 0 := by
  cases fork
  rfl

#print axioms Solidity.Roadmap.Evm.beBytes._proof_2
#print axioms Solidity.Roadmap.Evm.legacy_fork_index
end Solidity.Roadmap.Evm

open Solidity.Roadmap.Evm in
#guard Fork.osaka.toCtorIdx == 0

open Solidity.Roadmap.Evm in
#guard Precompile.ecrecover.toCtorIdx == 0

open Solidity.Roadmap.Evm in
#guard Precompile.sha256.toCtorIdx == 1

open Solidity.Roadmap.Evm in
#guard Precompile.ripemd160.toCtorIdx == 2

open Solidity.Roadmap.Evm in
#guard Precompile.identity.toCtorIdx == 3

open Solidity.Roadmap.Evm in
#guard Precompile.modexp.toCtorIdx == 4

open Solidity.Roadmap.Evm in
#guard Precompile.bnAdd.toCtorIdx == 5

open Solidity.Roadmap.Evm in
#guard Precompile.bnMul.toCtorIdx == 6

open Solidity.Roadmap.Evm in
#guard Precompile.bnPairing.toCtorIdx == 7

open Solidity.Roadmap.Evm in
#guard Precompile.blake2f.toCtorIdx == 8

open Solidity.Roadmap.Evm in
#guard Precompile.pointEvaluation.toCtorIdx == 9

open Solidity.Roadmap.Evm in
#guard Precompile.blsG1Add.toCtorIdx == 10

open Solidity.Roadmap.Evm in
#guard Precompile.blsG1Msm.toCtorIdx == 11

open Solidity.Roadmap.Evm in
#guard Precompile.blsG2Add.toCtorIdx == 12

open Solidity.Roadmap.Evm in
#guard Precompile.blsG2Msm.toCtorIdx == 13

open Solidity.Roadmap.Evm in
#guard Precompile.blsPairing.toCtorIdx == 14

open Solidity.Roadmap.Evm in
#guard Precompile.blsMapFpToG1.toCtorIdx == 15

open Solidity.Roadmap.Evm in
#guard Precompile.blsMapFp2ToG2.toCtorIdx == 16

open Solidity.Roadmap.Evm in
#guard Precompile.p256Verify.toCtorIdx == 17
