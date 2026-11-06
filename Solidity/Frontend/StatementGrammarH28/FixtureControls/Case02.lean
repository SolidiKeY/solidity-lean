import Solidity.Frontend.StatementGrammarH28.FixtureData

namespace Solidity.Frontend.StatementGrammarH28
theorem statementFixture2_checked : statementFixtureCheck statementFixture2 = true := by decide +kernel
#print axioms statementFixture2_checked
end Solidity.Frontend.StatementGrammarH28
