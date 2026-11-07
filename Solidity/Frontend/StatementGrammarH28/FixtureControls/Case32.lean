import Solidity.Frontend.StatementGrammarH28.FixtureData

namespace Solidity.Frontend.StatementGrammarH28
theorem statementFixture32_checked : statementFixtureCheck statementFixture32 = true := by decide +kernel
#print axioms statementFixture32_checked
end Solidity.Frontend.StatementGrammarH28
