import Solidity.Yul.ScopedSyntax
import Solidity.Yul.WordAdapterLogic
/-! Concrete scope-checker to raw-cell execution composition. The root function
environment and local map are actually empty, and cells use the proved concrete
packing. Supplied namespace/Source/JSON provenance and general admission remain
outside this adapter. -/
namespace Solidity.Yul.ScopedSyntax

def Prepared.rawProgram {X scope outside localNames body}
    (p : @Prepared X scope .A outside localNames body) :
    Logic.Program [] ClosedSyntax.rootControl (0 + wordCellCount X) :=
  WordAdapter.program p.typing.code p.policy

def Prepared.rawRun {X scope outside localNames body}
    (p : @Prepared X scope .A outside localNames body) (fuel : Nat) (cells : WordCells X) :
    Option (WordAdapter.Outcome X ClosedSyntax.rootControl 0) :=
  WordAdapter.run p.typing.code p.policy fuel ⟨Fin.elim0,cells⟩

theorem Prepared.rawRun_stable {X scope outside localNames body}
    (p : @Prepared X scope .A outside localNames body) (cells : WordCells X)
    {lo hi} (increasing : lo ≤ hi) {result}
    (done : p.rawRun lo cells = some result) : p.rawRun hi cells = some result :=
  WordAdapter.run_stable p.typing.code p.policy ⟨Fin.elim0,cells⟩ increasing done

/-- Actual ONE-STEP rule composition over the packed raw-cell state. No
model/closure agreement or RuleExists success premise is assumed. This is not
normalization, Source/G51 dispatch or compiler correspondence. -/
theorem Prepared.rawRule_exists {X scope outside localNames body}
    (p : @Prepared X scope .A outside localNames body) (mode : Solidity.Modality)
    (post : Closed.Flow ClosedSyntax.rootControl → Logic.Fml (0 + wordCellCount X)) :
    ∃ premise, Nonempty (Logic.Rule
      (.modal mode WordAdapter.model p.rawProgram post) premise) :=
  Logic.program_rule_exists mode WordAdapter.model p.rawProgram post

theorem Prepared.rawRule_sound {X scope outside localNames body}
    (p : @Prepared X scope .A outside localNames body) (mode : Solidity.Modality)
    (post : Closed.Flow ClosedSyntax.rootControl → Logic.Fml (0 + wordCellCount X)) :
    ∃ premise : Logic.Fml (0 + wordCellCount X), ∀ vars,
      (.modal mode WordAdapter.model p.rawProgram post : Logic.Fml (0 + wordCellCount X)).holds vars ↔
        premise.holds vars :=
  Logic.sound_program_rule_exists mode WordAdapter.model p.rawProgram post

theorem Prepared.rawState_rule_sound {X scope outside localNames body}
    (p : @Prepared X scope .A outside localNames body) (mode : Solidity.Modality)
    (post : WordAdapter.Outcome X ClosedSyntax.rootControl 0 → Prop) :
    ∃ premise : Logic.Fml (0 + wordCellCount X), ∀ cells : WordCells X,
      WordAdapter.rawHolds mode p.typing.code p.policy post ⟨Fin.elim0,cells⟩ ↔
        premise.holds (WordState.pack (X := X) (n := 0) ⟨Fin.elim0,cells⟩) := by
  obtain ⟨premise,sound⟩ := WordAdapter.rule_sound mode p.typing.code p.policy post
  exact ⟨premise,fun cells => sound ⟨Fin.elim0,cells⟩⟩

end Solidity.Yul.ScopedSyntax
