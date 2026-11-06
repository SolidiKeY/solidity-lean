import Solidity.Backend.FailurePaths.RelationalGuard
import Solidity.Backend.FailurePaths.Statements
import Solidity.Backend.PrimitivePackets.Comparisons.Controls

/-! Actual relational require observations in both pipelines. The published
comparison fixture supplies inhabited signed/unsigned layouts with saved77 and
nonempty source log/function locals. Every control consumes the general guard
agreement, rather than assuming its selected run. -/
namespace Solidity.Backend.FailurePaths.RelationalGuard.Controls
open Evm Evm.Memory Lowering.V07 PrimitivePackets.Comparisons

def Check (o : Order) (signed : Bool) (p : Roadmap.Pipeline) (x y : Int)
    (hx : (ty signed).lo ≤ x ∧ x ≤ (ty signed).hi)
    (hy : (ty signed).lo ≤ y ∧ y ≤ (ty signed).hi) : Prop :=
  let initial := PrimitivePackets.Comparisons.Controls.source signed x y hx hy
  let state := PrimitivePackets.Comparisons.Controls.target signed x y hx hy
  let machine := PrimitivePackets.Comparisons.Controls.machine signed x y hx hy
  let fragment := PrimitivePackets.Comparisons.Controls.fragment signed
  StateRepr 1 0 4 fragment state PrimitivePackets.Comparisons.Controls.addresses machine ∧
  (Source.execS (PrimitivePackets.Comparisons.Controls.global p)
      PrimitivePackets.Comparisons.Controls.frame 7 0 none
      (statement o signed .here (.there .here)) initial.1).run
      (Source.L0 PrimitivePackets.Comparisons.Controls.E,initial.2) =
    (if result o x y then (.ok (.normal initial.1),(Source.L0 _,initial.2))
     else (.error (.revert []),(Source.L0 _,initial.2))) ∧
  compileStmt 0 fragment (target (C:=PrimitivePackets.Comparisons.Controls.C) o signed .here (.there .here)) =
    some (selected 0 fragment o signed .here (.there .here)) ∧
  run (selected (C:=PrimitivePackets.Comparisons.Controls.C) 0 fragment o signed .here (.there .here)).code machine =
    (if result o x y then .ok machine 0 else .revert)

theorem checked (o : Order) (signed : Bool) (p : Roadmap.Pipeline) (x y : Int)
    (hx : (ty signed).lo ≤ x ∧ x ≤ (ty signed).hi)
    (hy : (ty signed).lo ≤ y ∧ y ≤ (ty signed).hi) : Check o signed p x y hx hy := by
  have represented := (PrimitivePackets.Comparisons.Controls.checked o signed p x y hx hy).1
  exact ⟨represented,agreement (PrimitivePackets.Comparisons.Controls.global p)
    PrimitivePackets.Comparisons.Controls.frame 0
    (PrimitivePackets.Comparisons.Controls.source signed x y hx hy).1
    (PrimitivePackets.Comparisons.Controls.source signed x y hx hy).2
    (PrimitivePackets.Comparisons.Controls.target signed x y hx hy)
    o signed .here (.there .here) .here (.there .here) x y hx hy rfl rfl rfl rfl represented⟩

theorem equality (o : Order) (signed : Bool) (p : Roadmap.Pipeline) :
    Check o signed p 7 7 (by cases signed <;> decide) (by cases signed <;> decide) :=
  checked o signed p 7 7 _ _

theorem sign_boundary (o : Order) (p : Roadmap.Pipeline) :
    Check o true p (-1) 0 (by decide) (by decide) :=
  checked o true p (-1) 0 _ _

theorem unsigned_maximum (o : Order) (p : Roadmap.Pipeline) :
    Check o false p (ty false).hi 0
      ⟨by decide,Int.le_refl _⟩ (by decide) :=
  checked o false p (ty false).hi 0 _ _

theorem signed_extremes (o : Order) (p : Roadmap.Pipeline) :
    Check o true p (ty true).lo (ty true).hi
      ⟨Int.le_refl _,PrimitivePackets.Comparisons.Controls.endpoints true⟩
      ⟨PrimitivePackets.Comparisons.Controls.endpoints true,Int.le_refl _⟩ :=
  checked o true p (ty true).lo (ty true).hi _ _

theorem equal_lt_reverts (p : Roadmap.Pipeline) :
    run (selected (C:=PrimitivePackets.Comparisons.Controls.C) 0
      (PrimitivePackets.Comparisons.Controls.fragment false) .lt false .here (.there .here)).code
      (PrimitivePackets.Comparisons.Controls.machine false 7 7 (by decide) (by decide)) = .revert :=
  (equality .lt false p).2.2.2

theorem negative_lt_zero_succeeds (p : Roadmap.Pipeline) :
    run (selected (C:=PrimitivePackets.Comparisons.Controls.C) 0
      (PrimitivePackets.Comparisons.Controls.fragment true) .lt true .here (.there .here)).code
      (PrimitivePackets.Comparisons.Controls.machine true (-1) 0 (by decide) (by decide)) =
      .ok (PrimitivePackets.Comparisons.Controls.machine true (-1) 0 (by decide) (by decide)) 0 :=
  (sign_boundary .lt p).2.2.2

theorem maximum_lt_zero_reverts (p : Roadmap.Pipeline) :
    run (selected (C:=PrimitivePackets.Comparisons.Controls.C) 0
      (PrimitivePackets.Comparisons.Controls.fragment false) .lt false .here (.there .here)).code
      (PrimitivePackets.Comparisons.Controls.machine false (ty false).hi 0
        ⟨by decide,Int.le_refl _⟩ (by decide)) = .revert :=
  (unsigned_maximum .lt p).2.2.2

theorem old_selector_refuses (p : Roadmap.Pipeline) (o : Order) (signed : Bool) :
    compileStatement (PrimitivePackets.Comparisons.Controls.global p) 0
      (statement (Γ:=[.int (ty signed),.int (ty signed)]) o signed .here (.there .here)) = none := rfl

theorem zero_horizon (p : Roadmap.Pipeline) :
    (Source.execS (PrimitivePackets.Comparisons.Controls.global p)
      PrimitivePackets.Comparisons.Controls.frame 0 0 none
      (statement .lt false .here (.there .here))
      (PrimitivePackets.Comparisons.Controls.source false 7 7 (by decide) (by decide)).1).run
      (Source.L0 _,PrimitivePackets.Comparisons.Controls.sourceState) =
      (.error .timeout,(Source.L0 _,PrimitivePackets.Comparisons.Controls.sourceState)) := rfl

/-- info: 'Solidity.Backend.FailurePaths.RelationalGuard.Controls.checked' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms checked
/-- info: 'Solidity.Backend.FailurePaths.RelationalGuard.Controls.equality' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms equality
/-- info: 'Solidity.Backend.FailurePaths.RelationalGuard.Controls.sign_boundary' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms sign_boundary
/-- info: 'Solidity.Backend.FailurePaths.RelationalGuard.Controls.unsigned_maximum' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms unsigned_maximum
/-- info: 'Solidity.Backend.FailurePaths.RelationalGuard.Controls.signed_extremes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms signed_extremes
/-- info: 'Solidity.Backend.FailurePaths.RelationalGuard.Controls.equal_lt_reverts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms equal_lt_reverts
/-- info: 'Solidity.Backend.FailurePaths.RelationalGuard.Controls.negative_lt_zero_succeeds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms negative_lt_zero_succeeds
/-- info: 'Solidity.Backend.FailurePaths.RelationalGuard.Controls.maximum_lt_zero_reverts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms maximum_lt_zero_reverts
/-- info: 'Solidity.Backend.FailurePaths.RelationalGuard.Controls.old_selector_refuses' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms old_selector_refuses
/-- info: 'Solidity.Backend.FailurePaths.RelationalGuard.Controls.zero_horizon' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms zero_horizon
end Solidity.Backend.FailurePaths.RelationalGuard.Controls
