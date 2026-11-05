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

end Solidity.Yul.RawFrame.Logic
