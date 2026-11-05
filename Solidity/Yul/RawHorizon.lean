import Solidity.Yul.RawFrame
import Solidity.Yul.HorizonAdapter

/-! The existing Source firstDone selector applied to actual raw-local Yul execution.
A failed finite horizon is timeout; unbounded noncompletion requires all horizons.
This module supplies no Source statement or compiler adequacy theorem. -/
namespace Solidity.Yul.RawFrame

/-- A genuine first completion selects the same complete raw outcome as the bound. -/
theorem firstDone_agrees : ∀ (ctx : Solidity.Source.Ctx) (control : Solidity.Yul.Control)
 (code : Solidity.Yul.Stmt [] (Solidity.Yul.localExternalTypes ctx) control 0)
 (policy : Solidity.Yul.Policy.StmtP .A code) (state : Solidity.Yul.RawFrame.State ctx),
 ∀ (bound chosen : Nat) (result : Except Solidity.Source.Halt (Solidity.Yul.RawFrame.Outcome ctx control) × Unit),
 Solidity.Source.firstDone (fun fuel => Solidity.Yul.Closed.sourceResult (Solidity.Yul.RawFrame.run code policy fuel state)) bound = some (chosen,result) →
 result = Solidity.Yul.Closed.sourceResult (Solidity.Yul.RawFrame.run code policy bound state) := by
  intro ctx control code policy state bound chosen result selected
  obtain ⟨hle, hr, hd⟩ := Solidity.Source.firstDone_spec selected
  cases completed : run code policy chosen state with
  | none =>
    rw [completed] at hd
    cases hd
  | some out =>
    have atBound := run_stable ctx control code policy state chosen bound hle out completed
    rw [hr, completed, atBound]

/-- No first completion at any bound is exactly actual word noncompletion at every fuel. -/
theorem firstDone_none_iff_word : ∀ (ctx : Solidity.Source.Ctx) (control : Solidity.Yul.Control)
 (code : Solidity.Yul.Stmt [] (Solidity.Yul.localExternalTypes ctx) control 0)
 (policy : Solidity.Yul.Policy.StmtP .A code) (state : Solidity.Yul.RawFrame.State ctx),
 (∀ bound, Solidity.Source.firstDone (fun fuel => Solidity.Yul.Closed.sourceResult (Solidity.Yul.RawFrame.run code policy fuel state)) bound = none) ↔
 ∀ fuel, Solidity.Yul.WordAdapter.run code policy fuel ⟨Fin.elim0,Solidity.Yul.RawFrame.view state⟩ = none := by
  intro ctx control code policy state
  rw [Closed.firstDone_none_iff]
  constructor
  · intro all fuel
    exact (run_none_iff ctx control code policy fuel state).mp (all fuel)
  · intro all fuel
    exact (run_none_iff ctx control code policy fuel state).mpr (all fuel)

/-- Finite failed selection is exactly timeout at that bound, not unbounded divergence. -/
theorem firstDone_none_iff_bound : ∀ (ctx : Solidity.Source.Ctx) (control : Solidity.Yul.Control)
 (code : Solidity.Yul.Stmt [] (Solidity.Yul.localExternalTypes ctx) control 0)
 (policy : Solidity.Yul.Policy.StmtP .A code) (state : Solidity.Yul.RawFrame.State ctx) (bound : Nat),
 Solidity.Source.firstDone (fun fuel => Solidity.Yul.Closed.sourceResult (Solidity.Yul.RawFrame.run code policy fuel state)) bound = none ↔
 Solidity.Yul.RawFrame.run code policy bound state = none := by
  intro ctx control code policy state bound
  constructor
  · intro absent
    simp only [Solidity.Source.firstDone, List.findSome?_eq_none_iff, List.mem_range] at absent
    have atBound := absent bound (Nat.lt_succ_self bound)
    cases actual : run code policy bound state with
    | none => rfl
    | some result =>
      rw [actual] at atBound
      cases atBound
  · intro exhausted
    simp only [Solidity.Source.firstDone, List.findSome?_eq_none_iff, List.mem_range]
    intro fuel within
    cases actual : run code policy fuel state with
    | none => rfl
    | some result =>
      have completed := run_stable ctx control code policy state fuel bound
        (Nat.le_of_lt_succ within) result actual
      rw [exhausted] at completed
      cases completed

/-- Exact completion is equivalent to genuine bounded selection of the same whole raw outcome. -/
theorem run_some_iff_firstDone : ∀ (ctx : Solidity.Source.Ctx) (control : Solidity.Yul.Control)
 (code : Solidity.Yul.Stmt [] (Solidity.Yul.localExternalTypes ctx) control 0)
 (policy : Solidity.Yul.Policy.StmtP .A code) (state : Solidity.Yul.RawFrame.State ctx)
 (bound : Nat) (result : Solidity.Yul.RawFrame.Outcome ctx control),
 Solidity.Yul.RawFrame.run code policy bound state = some result ↔
 ∃ chosen, Solidity.Source.firstDone
 (fun fuel => Solidity.Yul.Closed.sourceResult (Solidity.Yul.RawFrame.run code policy fuel state)) bound =
 some (chosen, Solidity.Yul.Closed.sourceResult (some result)) := by
  intro ctx control code policy state bound result
  constructor
  · intro completed
    cases selected : Solidity.Source.firstDone
        (fun fuel => Closed.sourceResult (run code policy fuel state)) bound with
    | none =>
      have absent := (firstDone_none_iff_bound ctx control code policy state bound).mp selected
      rw [completed] at absent
      cases absent
    | some found =>
      obtain ⟨chosen,observed⟩ := found
      have agrees := firstDone_agrees ctx control code policy state bound chosen observed selected
      rw [completed] at agrees
      exact ⟨chosen, congrArg (fun value => some (chosen,value)) agrees⟩
  · rintro ⟨chosen,selected⟩
    have agrees := firstDone_agrees ctx control code policy state bound chosen
      (Closed.sourceResult (some result)) selected
    cases actual : run code policy bound state with
    | none =>
      rw [actual] at agrees
      cases agrees
    | some out =>
      rw [actual] at agrees
      cases agrees
      rfl

/-- The actual selected horizon is least: every strict earlier raw execution exhausts fuel. -/
theorem firstDone_minimal : ∀ (ctx : Solidity.Source.Ctx) (control : Solidity.Yul.Control)
 (code : Solidity.Yul.Stmt [] (Solidity.Yul.localExternalTypes ctx) control 0)
 (policy : Solidity.Yul.Policy.StmtP .A code) (state : Solidity.Yul.RawFrame.State ctx)
 (bound chosen : Nat)
 (observed : Except Solidity.Source.Halt (Solidity.Yul.RawFrame.Outcome ctx control) × Unit),
 Solidity.Source.firstDone (fun fuel => Solidity.Yul.Closed.sourceResult (Solidity.Yul.RawFrame.run code policy fuel state)) bound = some (chosen,observed) →
 ∀ fuel, fuel < chosen → Solidity.Yul.RawFrame.run code policy fuel state = none := by
  intro ctx control code policy state bound chosen observed selected fuel before
  have within : chosen ≤ bound := (Solidity.Source.firstDone_spec selected).1
  cases actual : run code policy fuel state with
  | none => rfl
  | some out =>
    obtain ⟨earlier,earlySelection⟩ :=
      (run_some_iff_firstDone ctx control code policy state fuel out).mp actual
    have earlierWithin : earlier ≤ fuel := (Solidity.Source.firstDone_spec earlySelection).1
    have extended := Solidity.Source.firstDone_mono
      (fun horizon => Closed.sourceResult (run code policy horizon state))
      (Nat.le_trans (Nat.le_of_lt before) within) earlySelection
    have pairSame := Option.some.inj (extended.symm.trans selected)
    have indexSame : earlier = chosen := congrArg Prod.fst pairSame
    omega

end Solidity.Yul.RawFrame
