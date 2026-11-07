# Resolved owner ticket SCOPE1: historical escalation record

Resolution: human H69 (2026-11-06) accepts a checked proof of joint impossibility
for intentionally contradictory negative controls, separation lemmas and refutations.
All five cases below are now `intentional-impossibility-checked`; none requests
a statement change or remains a scope blocker. Their checked proofs and reasons
are retained in LayoutAudit and coverage.json. The escalation text below is
historical, not a renewed request. TC1 is separately resolved: stay on v4.24.0.

Routing: coordinator to the frozen Evm/Layout area producer. No original-file edit is requested.

Source: H62 checkpoint 2, pinned module-map evm-compiler, exact frozen base.

Decision needed: retain the universal requirement with impossibility blockers, or define which public interface contracts need witnesses while retaining every helper in the census. Neither option changes a frozen theorem without owner authorization.

ESCALATE: Solidity.Evm.occ_members_disjoint; evidence: Solidity/Evm/Layout.lean:298, Solidity.H62.EvmCompilerAudit.occ_members_no_joint_witness (LayoutAudit.lean; final-LayoutAudit.log), exact joint hypotheses imply False. Options: retain literal witness requirement and this blocker; human clarify contract/helper classification while preserving the frozen theorem and census.

ESCALATE: Solidity.Evm.occ_entries_disjoint; evidence: Solidity/Evm/Layout.lean:310, Solidity.H62.EvmCompilerAudit.occ_entries_no_joint_witness (LayoutAudit.lean; final-LayoutAudit.log), exact joint hypotheses imply False. Options: retain literal witness requirement and this blocker; human clarify contract/helper classification while preserving the frozen theorem and census.

ESCALATE: Solidity.Evm.occ_elems_disjoint; evidence: Solidity/Evm/Layout.lean:329, Solidity.H62.EvmCompilerAudit.occ_elems_no_joint_witness (LayoutAudit.lean; final-LayoutAudit.log), exact joint hypotheses imply False. Options: retain literal witness requirement and this blocker; human clarify contract/helper classification while preserving the frozen theorem and census.

ESCALATE: Solidity.Evm.occ_felems_disjoint; evidence: Solidity/Evm/Layout.lean:339, Solidity.H62.EvmCompilerAudit.occ_felems_no_joint_witness (LayoutAudit.lean; final-LayoutAudit.log), exact joint hypotheses imply False. Options: retain literal witness requirement and this blocker; human clarify contract/helper classification while preserving the frozen theorem and census.

ESCALATE: Solidity.Evm.occ_len_elem; evidence: Solidity/Evm/Layout.lean:349, Solidity.H62.EvmCompilerAudit.occ_len_elem_no_joint_witness (LayoutAudit.lean; final-LayoutAudit.log), exact joint hypotheses imply False. Options: retain literal witness requirement and this blocker; human clarify contract/helper classification while preserving the frozen theorem and census.
