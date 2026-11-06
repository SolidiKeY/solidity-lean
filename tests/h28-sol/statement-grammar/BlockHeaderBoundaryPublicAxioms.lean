import Solidity.Frontend.StatementGrammarH28.BlockHeaderBoundary

namespace Solidity.Frontend.StatementGrammarH28
#check atom_pair_no_named
/-- info: 'Solidity.Frontend.StatementGrammarH28.atom_pair_no_named' does not depend on any axioms -/
#guard_msgs in
#print axioms atom_pair_no_named
#check nonIdent_no_named_frame
/-- info: 'Solidity.Frontend.StatementGrammarH28.nonIdent_no_named_frame' does not depend on any axioms -/
#guard_msgs in
#print axioms nonIdent_no_named_frame
#check decl_head_no_named
/-- info: 'Solidity.Frontend.StatementGrammarH28.decl_head_no_named' does not depend on any axioms -/
#guard_msgs in
#print axioms decl_head_no_named
#check simple_statement_no_named
/-- info: 'Solidity.Frontend.StatementGrammarH28.simple_statement_no_named' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms simple_statement_no_named
#check revert_statement_no_named
/-- info: 'Solidity.Frontend.StatementGrammarH28.revert_statement_no_named' depends on axioms: [propext] -/
#guard_msgs in
#print axioms revert_statement_no_named
#check statement_no_named
/-- info: 'Solidity.Frontend.StatementGrammarH28.statement_no_named' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms statement_no_named
#check statement_all_root
/-- info: 'Solidity.Frontend.StatementGrammarH28.statement_all_root' depends on axioms: [propext] -/
#guard_msgs in
#print axioms statement_all_root
#check item_no_named
/-- info: 'Solidity.Frontend.StatementGrammarH28.item_no_named' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms item_no_named
#check item_list_no_named_body
/-- info: 'Solidity.Frontend.StatementGrammarH28.item_list_no_named_body' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms item_list_no_named_body
#check block_items_no_named_body
/-- info: 'Solidity.Frontend.StatementGrammarH28.block_items_no_named_body' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms block_items_no_named_body
#check block_yield_no_named_header
/-- info: 'Solidity.Frontend.StatementGrammarH28.block_yield_no_named_header' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms block_yield_no_named_header
#check postLoop_no_named_lookahead
/-- info: 'Solidity.Frontend.StatementGrammarH28.postLoop_no_named_lookahead' depends on axioms: [propext] -/
#guard_msgs in
#print axioms postLoop_no_named_lookahead
#check postLoop_yielded_block
/-- info: 'Solidity.Frontend.StatementGrammarH28.postLoop_yielded_block' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms postLoop_yielded_block
#check namedArgStart
/-- info: 'Solidity.Frontend.StatementGrammarH28.namedArgStart' does not depend on any axioms -/
#guard_msgs in
#print axioms namedArgStart
#check NoNamedFrame
/-- info: 'Solidity.Frontend.StatementGrammarH28.NoNamedFrame' does not depend on any axioms -/
#guard_msgs in
#print axioms NoNamedFrame
#check NoNamedParts
/-- info: 'Solidity.Frontend.StatementGrammarH28.NoNamedParts' does not depend on any axioms -/
#guard_msgs in
#print axioms NoNamedParts
#check BlockBodyParts
/-- info: 'Solidity.Frontend.StatementGrammarH28.BlockBodyParts' does not depend on any axioms -/
#guard_msgs in
#print axioms BlockBodyParts
#check SimpleNamedParts
/-- info: 'Solidity.Frontend.StatementGrammarH28.SimpleNamedParts' does not depend on any axioms -/
#guard_msgs in
#print axioms SimpleNamedParts
end Solidity.Frontend.StatementGrammarH28
