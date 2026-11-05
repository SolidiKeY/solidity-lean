import Solidity.Frontend.StatementGrammarH28.FixtureData

namespace Solidity.Frontend.StatementGrammarH28
theorem statementFixture42_checked : statementFixtureCheck statementFixture42 = true := by decide +kernel
#print axioms statementFixture42_checked
end Solidity.Frontend.StatementGrammarH28
