import Solidity.Yul.OpenCalculus
import Solidity.Yul.ScopedWordSyntax

/-! Actual existing checked scoped elaboration to independent direct execution.
Namespace/Source/solc-ID/span provenance and Body dispatch remain separate. -/
namespace Solidity.Yul.ScopedSyntax
def Prepared.openRun {X scope outside localNames body}
    (p : @Prepared X scope .A outside localNames body) (fuel : Nat) (cells : WordCells X) :
    Option (WordAdapter.Outcome X ClosedSyntax.rootControl 0) :=
  OpenRun.statement fuel .nil p.typing.code p.policy ⟨Fin.elim0,cells⟩

theorem Prepared.openRun_eq_rawRun {X scope outside localNames body}
    (p : @Prepared X scope .A outside localNames body) (fuel : Nat) (cells : WordCells X) :
    p.openRun fuel cells = p.rawRun fuel cells :=
  OpenRun.run_agrees fuel p.typing.code p.policy ⟨Fin.elim0,cells⟩

theorem Prepared.openState_rule_sound {X scope outside localNames body}
    (p : @Prepared X scope .A outside localNames body) (mode : Solidity.Modality)
    (post : WordAdapter.Outcome X ClosedSyntax.rootControl 0 → Prop) :
    ∃ premise : Logic.Fml (0+wordCellCount X), ∀ cells : WordCells X,
      OpenRun.holds mode p.typing.code p.policy post ⟨Fin.elim0,cells⟩ ↔
        premise.holds (WordState.pack (X := X) (n := 0) ⟨Fin.elim0,cells⟩) := by
  obtain ⟨premise,sound⟩ := OpenRun.rule_sound mode p.typing.code p.policy post
  exact ⟨premise,fun cells => sound ⟨Fin.elim0,cells⟩⟩
end Solidity.Yul.ScopedSyntax
