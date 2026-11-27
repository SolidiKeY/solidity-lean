| `Correctness/Lowering/Sim/CoverageBranch.lean` | Exact child execution receipts compose through lists, branch reader isolation and local restoration, and typed scope chaining; actual block-arm specialization requires `Goals.elabKernelTotal`. |
| `Examples/Lowering/Sim/CoverageBranch.lean` | Two effectful child executions retain fresh indices and memo updates, restore entry locals, observe the branch reader, and chain into a typed block. |

`Children` supplies individual executions with intermediate locals, counters
and memos. `chain_cons` checks placement at each exact context and outgoing
name list; `actual_scope` consumes a successful chain, not a coverage claim.
`actual_block` derives the `elabStmt1` block arm from producer equations with
an explicit kernel-totality hypothesis. Source acceptance, capture receipts,
assignment receipts, and the surrounding coverage theorem remain with LS3B.
These helpers assert neither unrestricted `Diagram.Total` nor external EVM
correctness.
