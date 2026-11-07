import Solidity.Frontend.StatementGrammarH28.G0List
import Solidity.Frontend.StatementGrammarH28.FixtureData
import Solidity.Frontend.StatementGrammarH28.NestedCoverage
import Solidity.Frontend.StatementGrammarH28.FramedItemList

/-! Every public theorem in each repaired source module, including unchanged
proof statements and new constructor equations. -/
open Solidity.Frontend.StatementGrammarH28
open Solidity.Source Solidity.Frontend.Checked

#check g0IsLiteralBase_eq
#print axioms g0IsLiteralBase_eq
#check g0Placeholders_eq
#print axioms g0Placeholders_eq
#check g0Nodes_eq
#print axioms g0Nodes_eq
#check g0Rejections_eq
#print axioms g0Rejections_eq
#check g0IsRethrow_eq
#print axioms g0IsRethrow_eq
#check statementFixtureCheck_profile
#print axioms statementFixtureCheck_profile
#check g0NodeCtors_eq_nodes
#print axioms g0NodeCtors_eq_nodes
#check g0ListCell_nil
#print axioms g0ListCell_nil
#check g0ListCell_cons
#print axioms g0ListCell_cons
#check g0ListValues_nil
#print axioms g0ListValues_nil
#check g0ListValues_cons
#print axioms g0ListValues_cons
#check g0ListLength_nil
#print axioms g0ListLength_nil
#check g0ListLength_cons
#print axioms g0ListLength_cons
#check root_blockStmt
#print axioms root_blockStmt
#check root_simpleStmt
#print axioms root_simpleStmt
#check root_ifStmt
#print axioms root_ifStmt
#check root_forStmt
#print axioms root_forStmt
#check root_whileStmt
#print axioms root_whileStmt
#check root_doWhile
#print axioms root_doWhile
#check root_continueStmt
#print axioms root_continueStmt
#check root_breakStmt
#print axioms root_breakStmt
#check root_tryStmt
#print axioms root_tryStmt
#check root_returnStmt
#print axioms root_returnStmt
#check root_emit
#print axioms root_emit
#check root_revert
#print axioms root_revert
#check root_assembly
#print axioms root_assembly
#check hasRoot_exists
#print axioms hasRoot_exists
#check hasRoot_unique
#print axioms hasRoot_unique
#check root_discriminate
#print axioms root_discriminate
#check root_allowed
#print axioms root_allowed
#check root_inhabited
#print axioms root_inhabited
#check root_inhabited_iff
#print axioms root_inhabited_iff
#check fixtureListCtors_zero
#print axioms fixtureListCtors_zero
#check fixtureListCtors_succ_nil
#print axioms fixtureListCtors_succ_nil
#check fixtureListCtors_succ_cons
#print axioms fixtureListCtors_succ_cons
#check fixtureBodyCtors_unit
#print axioms fixtureBodyCtors_unit
#check topBodyCtors_contract
#print axioms topBodyCtors_contract
#check statement_fixture_constructor_inventory
#print axioms statement_fixture_constructor_inventory
#check itemCount_nil
#print axioms itemCount_nil
#check itemCount_cons
#print axioms itemCount_cons
#check itemsAsList_nil
#print axioms itemsAsList_nil
#check itemsAsList_cons
#print axioms itemsAsList_cons
#check itemsAsList_inverse
#print axioms itemsAsList_inverse
#check leaf_step_return
#print axioms leaf_step_return
#check leaf_step_break
#print axioms leaf_step_break
#check leaf_step_continue
#print axioms leaf_step_continue
#check leaf_step_stop
#print axioms leaf_step_stop
#check leaf_items_token_length
#print axioms leaf_items_token_length
#check many_aux_none
#print axioms many_aux_none
#check many_aux_cons
#print axioms many_aux_cons
#check leaf_items_many_aux
#print axioms leaf_items_many_aux
#check leaf_items_many
#print axioms leaf_items_many
#check blockInput_eq
#print axioms blockInput_eq
#check leaf_block_coverage
#print axioms leaf_block_coverage
#check stmt_block_prefix
#print axioms stmt_block_prefix
#check leaf_block_stmt_coverage
#print axioms leaf_block_stmt_coverage
#check uncheckedInput_eq
#print axioms uncheckedInput_eq
#check item_unchecked_prefix
#print axioms item_unchecked_prefix
#check leaf_unchecked_coverage
#print axioms leaf_unchecked_coverage
#check unchecked_nested_refused
#print axioms unchecked_nested_refused
#check flat_list_yield_cons
#print axioms flat_list_yield_cons
#check leaf_items_yield
#print axioms leaf_items_yield
#check leaf_block_yield
#print axioms leaf_block_yield
#check leaf_block_toks
#print axioms leaf_block_toks
#check many_aux_cons_error
#print axioms many_aux_cons_error
#check leaf_items_many_underfuel
#print axioms leaf_items_many_underfuel
#check nested_items_count_le
#print axioms nested_items_count_le
#check locatedInput_append
#print axioms locatedInput_append
#check itemsAt_cons
#print axioms itemsAt_cons
#check block_of_itemsAt
#print axioms block_of_itemsAt
#check step_block_of_coverage
#print axioms step_block_of_coverage
#check step_unchecked_of_coverage
#print axioms step_unchecked_of_coverage
#check nested_items_at
#print axioms nested_items_at
#check nested_block_coverage
#print axioms nested_block_coverage
#check nested_block_stmt_coverage
#print axioms nested_block_stmt_coverage
#check nested_unchecked_coverage
#print axioms nested_unchecked_coverage
#check keyword_semi_balanced
#print axioms keyword_semi_balanced
#check nested_tokens_balanced
#print axioms nested_tokens_balanced
#check block_yield_of_flat
#print axioms block_yield_of_flat
#check nested_items_yield
#print axioms nested_items_yield
#check nested_block_yield
#print axioms nested_block_yield
#check nested_block_boundary
#print axioms nested_block_boundary
#check leaf_to_nested
#print axioms leaf_to_nested
#check FramedStatements_nil
#print axioms FramedStatements_nil
#check FramedStatements_cons
#print axioms FramedStatements_cons
#check statement_yield_nonempty
#print axioms statement_yield_nonempty
#check block_statement_prefix_split
#print axioms block_statement_prefix_split
#check framed_statement_prefix_split
#print axioms framed_statement_prefix_split
#check framed_statement_list_split
#print axioms framed_statement_list_split
#check statement_boundary_head
#print axioms statement_boundary_head
#check statement_boundary_prefix_refusal
#print axioms statement_boundary_prefix_refusal
#check unchecked_yield_decompose
#print axioms unchecked_yield_decompose
#check unchecked_yield_head
#print axioms unchecked_yield_head
#check FramedItem_stmtItem
#print axioms FramedItem_stmtItem
#check FramedItem_uncheckedItem
#print axioms FramedItem_uncheckedItem
#check FramedItems_nil
#print axioms FramedItems_nil
#check FramedItems_cons
#print axioms FramedItems_cons
#check item_yield_nonempty
#print axioms item_yield_nonempty
#check framed_item_prefix_split
#print axioms framed_item_prefix_split
#check framed_item_list_split
#print axioms framed_item_list_split
#check framed_block_item_segments
#print axioms framed_block_item_segments
#check g0ListCell
#print axioms g0ListCell
#check g0ListValues
#print axioms g0ListValues
#check g0ListLength
#print axioms g0ListLength
#check fixtureListCtors
#print axioms fixtureListCtors
#check functionBodyCtors
#print axioms functionBodyCtors
#check topBodyCtors
#print axioms topBodyCtors
#check fixtureBodyCtors
#print axioms fixtureBodyCtors
#check root
#print axioms root
#check itemCount
#print axioms itemCount
#check itemsAsList
#print axioms itemsAsList
#check FramedStatements
#print axioms FramedStatements
#check FramedItem
#print axioms FramedItem
#check FramedItems
#print axioms FramedItems
