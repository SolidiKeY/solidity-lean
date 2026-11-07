import Solidity.Frontend.StatementGrammarH28.FixtureControls.Case00
import Solidity.Frontend.StatementGrammarH28.FixtureControls.Case01
import Solidity.Frontend.StatementGrammarH28.FixtureControls.Case02
import Solidity.Frontend.StatementGrammarH28.FixtureControls.Case03
import Solidity.Frontend.StatementGrammarH28.FixtureControls.Case04
import Solidity.Frontend.StatementGrammarH28.FixtureControls.Case05
import Solidity.Frontend.StatementGrammarH28.FixtureControls.Case06
import Solidity.Frontend.StatementGrammarH28.FixtureControls.Case07
import Solidity.Frontend.StatementGrammarH28.FixtureControls.Case08
import Solidity.Frontend.StatementGrammarH28.FixtureControls.Case09
import Solidity.Frontend.StatementGrammarH28.FixtureControls.Case10
import Solidity.Frontend.StatementGrammarH28.FixtureControls.Case11
import Solidity.Frontend.StatementGrammarH28.FixtureControls.Case12
import Solidity.Frontend.StatementGrammarH28.FixtureControls.Case13
import Solidity.Frontend.StatementGrammarH28.FixtureControls.Case14
import Solidity.Frontend.StatementGrammarH28.FixtureControls.Case15
import Solidity.Frontend.StatementGrammarH28.FixtureControls.Case16
import Solidity.Frontend.StatementGrammarH28.FixtureControls.Case17
import Solidity.Frontend.StatementGrammarH28.FixtureControls.Case18
import Solidity.Frontend.StatementGrammarH28.FixtureControls.Case19
import Solidity.Frontend.StatementGrammarH28.FixtureControls.Case20
import Solidity.Frontend.StatementGrammarH28.FixtureControls.Case21
import Solidity.Frontend.StatementGrammarH28.FixtureControls.Case22
import Solidity.Frontend.StatementGrammarH28.FixtureControls.Case23
import Solidity.Frontend.StatementGrammarH28.FixtureControls.Case24
import Solidity.Frontend.StatementGrammarH28.FixtureControls.Case25
import Solidity.Frontend.StatementGrammarH28.FixtureControls.Case26
import Solidity.Frontend.StatementGrammarH28.FixtureControls.Case27
import Solidity.Frontend.StatementGrammarH28.FixtureControls.Case28
import Solidity.Frontend.StatementGrammarH28.FixtureControls.Case29
import Solidity.Frontend.StatementGrammarH28.FixtureControls.Case30
import Solidity.Frontend.StatementGrammarH28.FixtureControls.Case31
import Solidity.Frontend.StatementGrammarH28.FixtureControls.Case32
import Solidity.Frontend.StatementGrammarH28.FixtureControls.Case33
import Solidity.Frontend.StatementGrammarH28.FixtureControls.Case34
import Solidity.Frontend.StatementGrammarH28.FixtureControls.Case35
import Solidity.Frontend.StatementGrammarH28.FixtureControls.Case36
import Solidity.Frontend.StatementGrammarH28.FixtureControls.Case37
import Solidity.Frontend.StatementGrammarH28.FixtureControls.Case38
import Solidity.Frontend.StatementGrammarH28.FixtureControls.Case39
import Solidity.Frontend.StatementGrammarH28.FixtureControls.Case40
import Solidity.Frontend.StatementGrammarH28.FixtureControls.Case41
import Solidity.Frontend.StatementGrammarH28.FixtureControls.Case42
import Solidity.Frontend.StatementGrammarH28.FixtureControls.Case43
import Solidity.Frontend.StatementGrammarH28.FixtureControls.Case44

/-! Finite closed-case certificates, combined without re-running the corpus.
This proves controls, not AST equality or universal completeness. -/
namespace Solidity.Frontend.StatementGrammarH28
open Solidity.Source Solidity.Frontend.Checked
theorem statement_fixtures_all_checked : statementFixtures.all statementFixtureCheck = true := by
  simp only [statementFixtures, List.all_cons, List.all_nil, statementFixture0_checked, statementFixture1_checked, statementFixture2_checked, statementFixture3_checked, statementFixture4_checked, statementFixture5_checked, statementFixture6_checked, statementFixture7_checked, statementFixture8_checked, statementFixture9_checked, statementFixture10_checked, statementFixture11_checked, statementFixture12_checked, statementFixture13_checked, statementFixture14_checked, statementFixture15_checked, statementFixture16_checked, statementFixture17_checked, statementFixture18_checked, statementFixture19_checked, statementFixture20_checked, statementFixture21_checked, statementFixture22_checked, statementFixture23_checked, statementFixture24_checked, statementFixture25_checked, statementFixture26_checked, statementFixture27_checked, statementFixture28_checked, statementFixture29_checked, statementFixture30_checked, statementFixture31_checked, statementFixture32_checked, statementFixture33_checked, statementFixture34_checked, statementFixture35_checked, statementFixture36_checked, statementFixture37_checked, statementFixture38_checked, statementFixture39_checked, statementFixture40_checked, statementFixture41_checked, statementFixture42_checked, statementFixture43_checked, statementFixture44_checked, Bool.true_and]

/-- An actual accepted checked-source tree witnesses this observed constructor
in its target function body. No AST equality or universal completeness claim. -/
def ObservedStatementCtor (c : StatementFixture) (ctor : Ctor) : Prop :=
  ∃ u : Syn .unit, parse (ascii c.source) = .ok u ∧ ctor ∈ fixtureBodyCtors u

theorem checked_fixture_observes (c : StatementFixture) (ctor : Ctor)
    (ha : c.accepts = true) (hr : ctor ∈ c.required)
    (hc : statementFixtureCheck c = true) : ObservedStatementCtor c ctor := by
  unfold statementFixtureCheck at hc
  cases hp : parse (ascii c.source) with
  | error e =>
    rw [hp] at hc
    simp only [ha, Bool.not_true, Bool.false_eq_true] at hc
  | ok u =>
    rw [hp] at hc
    simp only [Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem] at hc
    exact ⟨u, hp, hc.2 ctor hr⟩

/-- Constructor-complete finite kernel witnesses, obtained from the actual
case certificates rather than a declared/sample-only inventory. -/
theorem statement_constructor_fixture_witnesses (ctor : Ctor)
    (h : ctor ∈ requiredStatementCtors) :
    ∃ c ∈ statementFixtures, ObservedStatementCtor c ctor := by
  have inventory : ∀ tag ∈ requiredStatementCtors,
      statementFixtures.any (fun c => c.accepts && c.required.contains tag) = true := by
    simpa only [List.all_eq_true] using statement_fixture_constructor_inventory
  have selected : ∃ c ∈ statementFixtures, c.accepts = true ∧ ctor ∈ c.required := by
    simpa only [List.any_eq_true, Bool.and_eq_true, List.contains_iff_mem] using inventory ctor h
  obtain ⟨c, hm, ha, hr⟩ := selected
  have checked : ∀ c ∈ statementFixtures, statementFixtureCheck c = true := by
    simpa only [List.all_eq_true] using statement_fixtures_all_checked
  exact ⟨c, hm, checked_fixture_observes c ctor ha hr (checked c hm)⟩

#print axioms checked_fixture_observes
#print axioms statement_constructor_fixture_witnesses
#print axioms statement_fixtures_all_checked
end Solidity.Frontend.StatementGrammarH28
