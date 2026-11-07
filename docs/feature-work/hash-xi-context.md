# Hash invocation world/context transport

`HashBridge/XiContextSetup.lean` groups only existing public Xi arguments in
`Inputs`. The actual fresh constructor supplies PC0, empty stack/memory and
active words; it uses the supplied world, snapshot, accrued state, created
accounts, genesis, blocks and complete environment. The checked prefix derives
two PUSH0 results and their charges with either permission value.

`XiContext.completed_invocation` proves actual Xi(fuel+6) success and a
singleton direct-query receipt for code `5f5f20` and gas34. All other arguments
are arbitrary, including nonempty worlds and distinct snapshots. Gas pays
2+2+30 and becomes0. The same world/created/accrued fields are returned, and
fallback STOP clears response bytes. This is a fixed-code kernel control,
not an all-program or all-gas theorem, source installation or native run.

`XiContext.prepared_message` supplies that producer from actual Theta
credit-before-debit and environment expressions. It keeps transfer value
separate from context value, all account/same-address cases and modular word
arithmetic, and the actual empty-map fallback. It explicitly selects CODE;
installed account selection, outer call guards and source this.g/ABI are not
proved. No selected child reply or desired reached state is a premise.

Controls distinguish pre-hash fuel exhaustion and gas-before-step failure.
The H7 reader law proves this zero-size query's byte list is empty; the receipt
still contains one query `[[]]`. No native KEC value, allocator compatibility,
random-oracle distribution or nested/global query completeness follows.

Only the exact ready `StopQueries` and `QueryPrepend` producer modules from
committed `5b6f05a3` are reused; no other unmerged hash/source/label files are
carried. Their full producer identity and module hashes are in the sealed
interface. No H22 `ExtCall` constructor/helper or H16-owned source evaluator
is changed. SS-AGREE simulation remains with the VY5 H16 dependency.
