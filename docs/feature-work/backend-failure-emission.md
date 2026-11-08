# Failure emission

[Authoritative source](../../Solidity/Backend/Failure).

Observe the full ordered return/revert bytes before caller unwind. Evaluator failure, EVM revert, resource exhaustion and caller rollback are distinct events; packet encoding alone must not conflate them. Runtime payload producers and call-frame/resource correspondence remain separate from local emitter laws.
