import Solidity.Calculus.DecisionHaltingOrBoundary
import Solidity.Examples.DecisionHaltingOrGaps

/-! # Inhabited partial-OR reason and preserved semantic controls
The source classifier does not inspect a verdict. Existing valid and false
mapping claims inhabit it, while covered Boolean OR controls stay outside.
-/
namespace Solidity.Examples.DecisionHaltingOrReason
open Solidity.Decide Solidity.Decide.ResidueReason
open Solidity.Examples.DecisionHaltingOrGaps
set_option Elab.async false

def roots : PartialOrRoots FloorProbe := ⟨"value", "balances", rfl, rfl⟩

def oneMember : PartialOrBlockAt roots (uintOfNat 0) (uintOfNat 1) (uintOfNat 0)
    (floorClaim 1) := ⟨.user "i", .user "j", rfl⟩
def zeroMember : PartialOrBlockAt roots (uintOfNat 0) (uintOfNat 0) (uintOfNat 0)
    (floorClaim 0) := ⟨.user "i", .user "j", rfl⟩
def badMember : PartialOrBlockAt roots (uintOfNat 0) (uintOfNat 1) (uintOfNat 1)
    floorBad := ⟨.user "i", .user "j", rfl⟩

theorem one_classified : (floorClaim 1).partialOrBlockAt roots
    (uintOfNat 0) (uintOfNat 1) (uintOfNat 0) = true := partialOrBlockAt_complete oneMember
theorem zero_classified : (floorClaim 0).partialOrBlockAt roots
    (uintOfNat 0) (uintOfNat 0) (uintOfNat 0) = true := partialOrBlockAt_complete zeroMember
theorem bad_classified : floorBad.partialOrBlockAt roots
    (uintOfNat 0) (uintOfNat 1) (uintOfNat 1) = true := partialOrBlockAt_complete badMember

theorem one_valid : Fml.Valid (floorClaim 1) := floorClaim_one_valid
theorem bad_countermodel : ¬ holds (State.init FloorProbe) floorBad := floorBad_countermodel

theorem actual_roots : (leafOf? (floorClaim 1)).map
    (fun ψ => (apfRoots .uint ψ).2.names) = some ["balances"] := by decide +kernel

/-- Exact original guard, through source preparation and the actual parser. -/
theorem actual_guard_refused (Bs : List Parameter) :
    ((floorGuard.toL (((SymS.init (C := FloorProbe)).pushQ .uint).pushQ .uint)).map
      (fun t => t.elim.condSimp)).bind (fun t =>
        (ApfTm.ofTerm? roots.roots false t).map (fun h => h.guardB .uint [0, 1] Bs)) = some false :=
  roots.translated_guard_refused Bs

/-- Guard occurrence extracted from the actual complete prepared source leaf. -/
theorem actual_leaf_guard_refused : ((leafOf? (floorClaim 1)).bind fun ψ =>
    match ψ with
    | .imp (.all _ _ (.all _ _ (.imp (.eq a _) _))) _ =>
      (ApfTm.ofTerm? roots.roots false a).map (fun h => h.guardB .uint [0, 1] [])
    | _ => none) = some false := by decide +kernel

def totalGuard : Tm FloorProbe [.val .uint, .val .uint] (.val .bool) :=
  .app2 (.binop .or rfl)
    (.app2 (.binop .and rfl) orderGuard
      (.app2 (.binop .lt (p := .uint) rfl) keyI scalar))
    (.app2 (.binop .le (p := .uint) rfl) keyI keyI)
theorem total_guard_accepted :
    ((totalGuard.toL (((SymS.init (C := FloorProbe)).pushQ .uint).pushQ .uint)).map
      (fun t => t.elim.condSimp)).bind (fun t =>
        (ApfTm.ofTerm? roots.roots false t).map (fun h => h.guardB .uint [0, 1] [])) = some true := by
  decide +kernel

def claimWith (g : Tm FloorProbe [.val .uint, .val .uint] (.val .bool)) : Fml FloorProbe [] :=
  .imp (.all (.user "i") .uint (.all (.user "j") .uint
    (.imp (.eq g (.app0 (.lit true))) (.eq (atKey keyI) (natLit 0)))))
    (.eq (atKey (natLit 1)) (natLit 0))

theorem total_guard_outside : (claimWith totalGuard).partialOrBlockAt roots
    (uintOfNat 0) (uintOfNat 1) (uintOfNat 0) = false := by decide +kernel
theorem no_or_outside : (claimWith (.app2 (.binop .and rfl) orderGuard partialGuard)).partialOrBlockAt roots
    (uintOfNat 0) (uintOfNat 1) (uintOfNat 0) = false := by decide +kernel

def closedOr : Fml FloorProbe [] := .eq
  (.app2 (.binop .or (p := .bool) rfl) (.app0 (.lit true)) (.app0 (.lit false))) (.app0 (.lit true))

theorem closed_outside : closedOr.partialOrBlockAt roots
    (uintOfNat 0) (uintOfNat 1) (uintOfNat 0) = false := by rfl
theorem closed_covered : closedOr.Covered = true := by decide +kernel
private def provedCheck : LeafVerdict FloorProbe → Bool
  | .proved => true
  | _ => false

theorem closed_proved : decideGoal closedOr = .proved := by
  have h : provedCheck (decideGoal closedOr) = true := by decide +kernel
  cases hd : decideGoal closedOr with
  | proved => rfl
  | refuted σ => rw [hd] at h; cases h
  | unknown => rw [hd] at h; cases h

theorem original_controls :
    (floorClaim 1).inTarget {} = true ∧ (floorClaim 1).Covered = false ∧
    decideGoal (floorClaim 1) = .unknown ∧ floorBad.inTarget {} = true ∧
    floorBad.Covered = false ∧ decideGoal floorBad = .unknown :=
  ⟨validAPF_target, validAPF_notCovered, validAPF_unknown,
    falseAPF_target, falseAPF_notCovered, falseAPF_unknown⟩

end Solidity.Examples.DecisionHaltingOrReason
