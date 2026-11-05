import Solidity.Yul.RawFrame
import Solidity.Yul.WordAdapterLogic

/-! Concrete word-calculus interpretation for the existing raw LOCAL frame.
The initial frame parameter supplies the clean backup/world retained by capture.
Box and diamond quantify actual interpreter completions. No Source statement,
compiler adequacy, new calculus rule or SolKey taclet is supplied. -/
namespace Solidity.Yul.RawFrame.Logic

def holds {ctx control} (mode : Solidity.Modality)
    (code : Stmt [] (localExternalTypes ctx) control 0) (policy : Policy.StmtP .A code)
    (post : RawFrame.Outcome ctx control → Prop) (state : RawFrame.State ctx) : Prop :=
  match mode with
  | .box => ∀ fuel result, RawFrame.run code policy fuel state = some result → post result
  | .diamond => ∃ fuel result, RawFrame.run code policy fuel state = some result ∧ post result

def formula {ctx control} (mode : Solidity.Modality)
    (code : Stmt [] (localExternalTypes ctx) control 0) (policy : Policy.StmtP .A code)
    (post : RawFrame.Outcome ctx control → Prop) (state : RawFrame.State ctx) :
    Solidity.Yul.Logic.Fml (0 + wordCellCount (localExternalTypes ctx)) :=
  WordAdapter.formula mode code policy (fun result => post (RawFrame.Outcome.ofWord state result))


/-- The existing word formula interprets actual completed raw-frame runs exactly. -/
theorem formula_iff : ∀ (ctx : Solidity.Source.Ctx) (control : Solidity.Yul.Control) (mode : Solidity.Modality)
 (code : Solidity.Yul.Stmt [] (Solidity.Yul.localExternalTypes ctx) control 0)
 (policy : Solidity.Yul.Policy.StmtP .A code)
 (post : Solidity.Yul.RawFrame.Outcome ctx control → Prop) (state : Solidity.Yul.RawFrame.State ctx),
 (Solidity.Yul.RawFrame.Logic.formula mode code policy post state).holds
 (Solidity.Yul.WordState.pack ⟨Fin.elim0,Solidity.Yul.RawFrame.view state⟩) ↔
 Solidity.Yul.RawFrame.Logic.holds mode code policy post state := by
  intro ctx control mode code policy post state
  unfold formula
  rw [WordAdapter.formula_iff]
  cases mode with
  | box =>
    constructor
    · intro valid fuel result done
      obtain ⟨wordResult,finished,captured⟩ :=
        (RawFrame.run_some_iff ctx control code policy fuel state result).mp done
      have actual := valid fuel wordResult finished
      change post (RawFrame.Outcome.ofWord state wordResult) at actual
      rw [captured] at actual
      exact actual
    · intro valid fuel result done
      exact valid fuel (RawFrame.Outcome.ofWord state result)
        ((RawFrame.run_some_iff ctx control code policy fuel state _).mpr ⟨result,done,rfl⟩)
  | diamond =>
    constructor
    · rintro ⟨fuel,result,done,valid⟩
      exact ⟨fuel,RawFrame.Outcome.ofWord state result,
        (RawFrame.run_some_iff ctx control code policy fuel state _).mpr ⟨result,done,rfl⟩,valid⟩
    · rintro ⟨fuel,result,done,valid⟩
      obtain ⟨wordResult,finished,captured⟩ :=
        (RawFrame.run_some_iff ctx control code policy fuel state result).mp done
      refine ⟨fuel,wordResult,finished,?_⟩
      change post (RawFrame.Outcome.ofWord state wordResult)
      rw [captured]
      exact valid

/-- Soundness for the displayed premise of a concrete existing Rule.
The shallow word calculus and every original Rule side condition are unchanged. -/
theorem rule_premise_sound : ∀ (ctx : Solidity.Source.Ctx) (control : Solidity.Yul.Control) (mode : Solidity.Modality)
 (code : Solidity.Yul.Stmt [] (Solidity.Yul.localExternalTypes ctx) control 0)
 (policy : Solidity.Yul.Policy.StmtP .A code)
 (post : Solidity.Yul.RawFrame.Outcome ctx control → Prop) (state : Solidity.Yul.RawFrame.State ctx),
 ∀ (premise : Solidity.Yul.Logic.Fml (0 + Solidity.Yul.wordCellCount (Solidity.Yul.localExternalTypes ctx))),
 Solidity.Yul.Logic.Rule (Solidity.Yul.RawFrame.Logic.formula mode code policy post state) premise →
 (Solidity.Yul.RawFrame.Logic.holds mode code policy post state ↔
 premise.holds (Solidity.Yul.WordState.pack ⟨Fin.elim0,Solidity.Yul.RawFrame.view state⟩)) := by
  intro ctx control mode code policy post state premise rule
  exact (formula_iff ctx control mode code policy post state).symm.trans
    (Solidity.Yul.Logic.Rule.sound rule _)


/-- Deterministic completed outcomes let a successful diamond establish its box postcondition. -/
theorem diamond_implies_box : ∀ (ctx : Solidity.Source.Ctx) (control : Solidity.Yul.Control)
 (code : Solidity.Yul.Stmt [] (Solidity.Yul.localExternalTypes ctx) control 0)
 (policy : Solidity.Yul.Policy.StmtP .A code)
 (post : Solidity.Yul.RawFrame.Outcome ctx control → Prop) (state : Solidity.Yul.RawFrame.State ctx), Solidity.Yul.RawFrame.Logic.holds .diamond code policy post state → Solidity.Yul.RawFrame.Logic.holds .box code policy post state := by
  intro ctx control code policy post state actual
  obtain ⟨chosen,out,finished,valid⟩ := actual
  intro fuel result done
  have same := RawFrame.run_completed_unique ctx control code policy state
    fuel chosen result out done finished
  rw [same]
  exact valid

/-- A false-postcondition box is exactly noncompletion at every fuel, never one finite timeout. -/
theorem box_false_iff_none : ∀ (ctx : Solidity.Source.Ctx) (control : Solidity.Yul.Control)
 (code : Solidity.Yul.Stmt [] (Solidity.Yul.localExternalTypes ctx) control 0)
 (policy : Solidity.Yul.Policy.StmtP .A code)
 (state : Solidity.Yul.RawFrame.State ctx), Solidity.Yul.RawFrame.Logic.holds .box code policy (fun _ => False) state ↔ ∀ fuel, Solidity.Yul.RawFrame.run code policy fuel state = none := by
  intro ctx control code policy state
  constructor
  · intro valid fuel
    cases actual : RawFrame.run code policy fuel state with
    | none => rfl
    | some result => exact False.elim (valid fuel result actual)
  · intro all fuel result done
    rw [all fuel] at done
    cases done

/-- A diamond is termination plus its box postcondition for the actual deterministic raw interpreter. -/
theorem diamond_iff_termination_and_box : ∀ (ctx : Solidity.Source.Ctx) (control : Solidity.Yul.Control)
 (code : Solidity.Yul.Stmt [] (Solidity.Yul.localExternalTypes ctx) control 0)
 (policy : Solidity.Yul.Policy.StmtP .A code)
 (post : Solidity.Yul.RawFrame.Outcome ctx control → Prop) (state : Solidity.Yul.RawFrame.State ctx), Solidity.Yul.RawFrame.Logic.holds .diamond code policy post state ↔ Solidity.Yul.RawFrame.Logic.holds .diamond code policy (fun _ => True) state ∧ Solidity.Yul.RawFrame.Logic.holds .box code policy post state := by
  intro ctx control code policy post state
  constructor
  · intro actual
    obtain ⟨fuel,result,done,valid⟩ := actual
    exact ⟨⟨fuel,result,done,True.intro⟩,
      diamond_implies_box ctx control code policy post state ⟨fuel,result,done,valid⟩⟩
  · rintro ⟨⟨fuel,result,done,_⟩,valid⟩
    exact ⟨fuel,result,done,valid fuel result done⟩

end Solidity.Yul.RawFrame.Logic
