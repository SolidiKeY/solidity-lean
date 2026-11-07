import Solidity.Frontend.StatementGrammarH28.FixtureData

namespace Solidity.Frontend.StatementGrammarH28
theorem statementFixture1_checked : statementFixtureCheck statementFixture1 = true := by decide +kernel
#print axioms statementFixture1_checked
end Solidity.Frontend.StatementGrammarH28
