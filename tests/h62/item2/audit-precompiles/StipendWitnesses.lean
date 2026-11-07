import Solidity.Stipend.Rule

/-! Guards against declaring the storage/read/loop/power stipend rule domains
empty, dropping rejection premises, or inferring compiler success from source
cost admission. One concrete intrinsic contract supplies a primitive storage
cell; each joint rejection witness constructs all syntax and premises together.
The actual G43 compiler-success theorem remains an external obligation. -/
namespace H62.AuditPrecompiles.Successor.Stipend
open Solidity Solidity.Stipend Solidity.Roadmap.Evm

def cell : Contract := { vars := [("x", .prim .uint)] }
def location : Loc cell [] (.prim .uint) := .root "x" rfl
def one : Val cell [] .uint := .simple (.lit 1 rfl)
def rejected : Stmt cell [] [] :=
  .transfer (.simple (.env .msgSender rfl)) one

-- Frozen source: Solidity.Stipend.fits_iff
theorem fits_iff_data : ∃ (C : Contract) (b : Body C), ((rule C).fits b ↔ ∃ c, progCost b.prog = some c ∧ c ≤ 40) := by
  exact ⟨cell, (⟨(.nil : Prog cell [] [])⟩ : Body cell), @Solidity.Stipend.fits_iff cell (⟨(.nil : Prog cell [] [])⟩ : Body cell)⟩

-- Frozen source: Solidity.Stipend.not_fits_cons
theorem not_fits_cons_joint : ∃ (C : Contract) (Γ₁ : Ctx) (out : Ctx) (s : Stmt C [] Γ₁) (P : Prog C Γ₁ out), stmtCost s = none ∧ (¬(rule C).fits ⟨.cons s P⟩) := by
  have h : stmtCost rejected = none := rfl
  exact ⟨cell, ([] : Ctx), ([] : Ctx), rejected, (.nil : Prog cell [] []), h, @Solidity.Stipend.not_fits_cons cell ([] : Ctx) ([] : Ctx) rejected (.nil : Prog cell [] []) h⟩

-- Frozen source: Solidity.Stipend.empty_fits
theorem empty_fits_data : ∃ (C : Contract) , ((rule C).fits ⟨(.nil : Prog C [] [])⟩) := by
  exact ⟨cell, @Solidity.Stipend.empty_fits cell ⟩

-- Frozen source: Solidity.Stipend.requireValue_fits
theorem requireValue_fits_data : ∃ (C : Contract) , ((rule C).fits ⟨(requireValue : Prog C [] [])⟩) := by
  exact ⟨cell, @Solidity.Stipend.requireValue_fits cell ⟩

-- Frozen source: Solidity.Stipend.transfer_not_fits
theorem transfer_not_fits_data : ∃ (C : Contract) , (¬(rule C).fits ⟨(.cons (.transfer (.simple (.env .msgSender rfl)) (.simple (.lit 1 rfl))) .nil :
      Prog C [] [])⟩) := by
  exact ⟨cell, @Solidity.Stipend.transfer_not_fits cell ⟩

-- Frozen source: Solidity.Stipend.loop_not_fits
theorem loop_not_fits_data : ∃ (C : Contract) (a : LoopAnn C []), (¬(rule C).fits ⟨(.cons (.loop a (.simple (.bool false)) .nil) .nil : Prog C [] [])⟩) := by
  exact ⟨cell, (.unwind 1), @Solidity.Stipend.loop_not_fits cell (.unwind 1)⟩

-- Frozen source: Solidity.Stipend.assign_not_fits
theorem assign_not_fits_data : ∃ (C : Contract) (T : Ty) (l : Loc C [] T) (r : Src C [] T), (¬(rule C).fits ⟨(.cons (.assign l r) .nil : Prog C [] [])⟩) := by
  exact ⟨cell, (.prim .uint), location, (Src.val one), @Solidity.Stipend.assign_not_fits cell (.prim .uint) location (Src.val one)⟩

-- Frozen source: Solidity.Stipend.read_not_fits
theorem read_not_fits_data : ∃ (C : Contract) (p : PrimTy) (l : Loc C [] (.prim p)), (¬(rule C).fits ⟨(.cons (.require (.binop .eqB rfl rfl (.read l) (.read l))) .nil :
      Prog C [] [])⟩) := by
  exact ⟨cell, PrimTy.uint, location, @Solidity.Stipend.read_not_fits cell PrimTy.uint location⟩

-- Frozen source: Solidity.Stipend.requires_cost
theorem requires_cost_data : ∃ (C : Contract) (n : Nat), (progCost (requires n : Prog C [] []) = some (4 * n)) := by
  exact ⟨cell, 1, @Solidity.Stipend.requires_cost cell 1⟩

-- Frozen source: Solidity.Stipend.requires_ten_fits
theorem requires_ten_fits_data : ∃ (C : Contract) , ((rule C).fits ⟨(requires 10 : Prog C [] [])⟩) := by
  exact ⟨cell, @Solidity.Stipend.requires_ten_fits cell ⟩

-- Frozen source: Solidity.Stipend.requires_eleven_not_fits
theorem requires_eleven_not_fits_data : ∃ (C : Contract) , (¬(rule C).fits ⟨(requires 11 : Prog C [] [])⟩) := by
  exact ⟨cell, @Solidity.Stipend.requires_eleven_not_fits cell ⟩

-- Frozen source: Solidity.Stipend.pow_not_fits
theorem pow_not_fits_joint : ∃ (C : Contract) (p : PrimTy) (x : Var) (a b : Val C [] p), ∃ (h : BinOp.pow.accepts p = true) (hq : BinOp.pow.ret p = .uint), (¬(rule C).fits ⟨(.cons (.declLocal .uint x (some (.binop .pow h hq a b))) .nil :
      Prog C [] [.val .uint])⟩) := by
  have h : BinOp.pow.accepts PrimTy.uint = true := rfl
  have hq : BinOp.pow.ret PrimTy.uint = .uint := rfl
  exact ⟨cell, PrimTy.uint, (.user "y"), one, one, h, hq, @Solidity.Stipend.pow_not_fits cell PrimTy.uint (.user "y") one one h hq⟩

/-- info: 'H62.AuditPrecompiles.Successor.Stipend.fits_iff_data' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms fits_iff_data
/-- info: 'H62.AuditPrecompiles.Successor.Stipend.not_fits_cons_joint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms not_fits_cons_joint
/-- info: 'H62.AuditPrecompiles.Successor.Stipend.empty_fits_data' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms empty_fits_data
/-- info: 'H62.AuditPrecompiles.Successor.Stipend.requireValue_fits_data' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms requireValue_fits_data
/-- info: 'H62.AuditPrecompiles.Successor.Stipend.transfer_not_fits_data' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms transfer_not_fits_data
/-- info: 'H62.AuditPrecompiles.Successor.Stipend.loop_not_fits_data' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms loop_not_fits_data
/-- info: 'H62.AuditPrecompiles.Successor.Stipend.assign_not_fits_data' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms assign_not_fits_data
/-- info: 'H62.AuditPrecompiles.Successor.Stipend.read_not_fits_data' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms read_not_fits_data
/-- info: 'H62.AuditPrecompiles.Successor.Stipend.requires_cost_data' depends on axioms: [propext] -/
#guard_msgs in
#print axioms requires_cost_data
/-- info: 'H62.AuditPrecompiles.Successor.Stipend.requires_ten_fits_data' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms requires_ten_fits_data
/-- info: 'H62.AuditPrecompiles.Successor.Stipend.requires_eleven_not_fits_data' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms requires_eleven_not_fits_data
/-- info: 'H62.AuditPrecompiles.Successor.Stipend.pow_not_fits_joint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms pow_not_fits_joint
run_cmd Lean.logInfo "CORE_APPLICABILITY_PASS module=Stipend original=12 guards=12"
end H62.AuditPrecompiles.Successor.Stipend
