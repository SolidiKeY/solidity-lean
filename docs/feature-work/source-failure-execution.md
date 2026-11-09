# Failure-resource semantics

[Authoritative source](../../Solidity/Source/Machine.lean).

Source evaluation fuel, native target capacity and EVM gas are different resources. A horizon sufficient for a concrete component does not exclude longer source executions. Preserve actual failure states and evaluation order; caller rollback belongs to the call/transaction boundary, not every evaluator revert. Source-resource work remains subject to its recorded owner hold.
