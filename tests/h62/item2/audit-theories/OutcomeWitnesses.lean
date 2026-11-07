import Solidity.Theory.Progress.Outcome
import Solidity.Source.Semantics
import tests.h62.item2.«audit-theories».BridgeWitnesses
import tests.h62.item2.«audit-theories».CoreTotality

/-!
Joint inputs for every explicit unchanged Progress/Outcome statement. Source
NS is universal but accompanied by an actual local/state input and successful
run; core packets use a real bool declaration that succeeds. The negative
not_ends_stuck statement has no contradictory input hypothesis: its ordinary
Unit/String data coexist, and its negative conclusion is separately checked.
-/
namespace H62.AuditTheories
open Solidity Solidity.Source Solidity.Theory.Progress

/-- The minimal source environment, used with a nonempty bool local context. -/
def outcomeEnv : Solidity.Source.Env := ⟨[]⟩

/-- A genuine success satisfies the complete quantified non-stuck premise. -/
theorem outcome_notStuck_joint_witness :
    ∃ (α : Type) (r : Except Solidity.Source.Halt α),
      (∀ w, r ≠ .error (.stuck w)) ∧ Ends r :=
  ⟨Unit, .ok (), (by intro w h; cases h), .returns ()⟩

/-- Ends, the result and the post-premise string input coexist. -/
theorem outcome_ends_notStuck_joint_witness :
    ∃ (α : Type) (r : Except Solidity.Source.Halt α) (w : String),
      Ends r ∧ r ≠ .error (.stuck w) :=
  ⟨Unit, .ok (), "audit", .returns (), (by intro h; cases h)⟩

/-- All monadic inputs coexist; an actual populated local frame returns. -/
theorem outcome_ns_iff_joint_witness :
    ∃ (E : Solidity.Source.Env) (Γ : RCtx) (α : Type) (m : EM E Γ α)
      (x : Locals E.layout Γ × St E), NS m ∧ ∃ v, (m.run x).1 = .ok v :=
  ⟨outcomeEnv, [.bool], Unit, pure (), (.cons (.bool false) .nil, St.init _),
    NS.pure' (), (), rfl⟩

/-- The universal NS proof and a concrete compatible input hold together. -/
theorem outcome_ns_ends_joint_witness :
    ∃ (E : Solidity.Source.Env) (Γ : RCtx) (α : Type) (m : EM E Γ α)
      (x : Locals E.layout Γ × St E), NS m ∧ Ends (m.run x).1 :=
  ⟨outcomeEnv, [.bool], Unit, pure (), (.cons (.bool false) .nil, St.init _),
    NS.pure' (), .returns ()⟩

/-- Ordinary data are inhabited; the intentional negative conclusion needs
    no H69 impossible-input classification. -/
theorem outcome_stuck_negative_joint_witness :
    ∃ (α : Type) (w : String), ¬ Ends (.error (.stuck w) : Except Solidity.Source.Halt α) :=
  ⟨Unit, "audit", not_ends_stuck _⟩

/-- Core result classification has an actual successful value. -/
theorem outcome_core_joint_witness :
    ∃ (α : Type) (r : TRes α), CoreEnds r :=
  ⟨Unit, .ok (), .returns ()⟩

/-- The unrestricted core run's complete input exists and really succeeds. -/
theorem outcome_run_joint_witness :
    ∃ (C : Contract) (Γ Γ' : Solidity.Ctx) (σ : State C Γ) (P : Solidity.Prog C Γ Γ'),
      ∃ o, Solidity.Prog.run σ P = .ok o := by
  refine ⟨bridgeContract, [], [.val .bool], State.init _,
    CompilerAudit.boolProgram bridgeContract true, ?_⟩
  obtain ⟨o, h, _⟩ := CompilerAudit.bool_source_success bridgeContract true (State.init _)
  exact ⟨o, h⟩

/-- The fueled core program has compatible scope/state/fuel and succeeds. -/
theorem outcome_runF_joint_witness :
    ∃ (C : Contract) (Γ Γ' : Solidity.Ctx) (n : Nat) (P : Solidity.Prog C Γ Γ') (σ : State C Γ),
      ∃ o, Solidity.Prog.runF n P σ = .ok o :=
  ⟨bridgeContract, [], [.val .bool], 10, CompilerAudit.boolProgram bridgeContract true,
    State.init _, _, rfl⟩

/-- A real bool declaration witnesses the fueled-statement inputs. -/
theorem outcome_stmt_runF_joint_witness :
    ∃ (C : Contract) (Γ Γ' : Solidity.Ctx) (n : Nat) (s : Solidity.Stmt C Γ Γ') (σ : State C Γ),
      ∃ o, Solidity.Stmt.runF n s σ = .ok o :=
  ⟨bridgeContract, [], [.val .bool], 10,
    .declLocal .bool (.user "flag") (some (.simple (.bool true))), State.init _, _, rfl⟩

#print axioms outcome_notStuck_joint_witness
#print axioms outcome_ends_notStuck_joint_witness
#print axioms outcome_ns_iff_joint_witness
#print axioms outcome_ns_ends_joint_witness
#print axioms outcome_stuck_negative_joint_witness
#print axioms outcome_core_joint_witness
#print axioms outcome_run_joint_witness
#print axioms outcome_runF_joint_witness
#print axioms outcome_stmt_runF_joint_witness
end H62.AuditTheories
