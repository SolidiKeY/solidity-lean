import Solidity.Frontend.StatementGrammarH28.FixtureData

namespace Solidity.Frontend.StatementGrammarH28
theorem statementFixture3_checked : statementFixtureCheck statementFixture3 = true := by decide +kernel
#print axioms statementFixture3_checked
end Solidity.Frontend.StatementGrammarH28
