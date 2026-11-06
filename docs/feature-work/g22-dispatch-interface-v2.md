# Reachable readonly dispatch interface V2

H69 replaces the unreachable branch split through an additive version, without changing source execution or frozen V1 proofs. Import `Solidity.Lowering.Readonly.SourceDispatchInterfaceV2` and use namespace `Solidity.Lowering.Readonly.SourceDispatchV2`.

`Selection G F input` has three constructors: function with actual selection and nonempty input; getter with no function and actual getter selection; special with neither selection. `classify` constructs this certificate for every actual global, frame and input. No selection oracle or future producer is assumed. Every selector has four bytes even for the arbitrary fixed hash word. Thus `pickFn_empty` and `pickGetter_empty` prove that empty input selects neither function nor getter.

The old `SourceHistory.dispatch_getter_empty_succ` and `dispatch_special_empty_succ` require a selected function and empty input. Their premises are contradictory. Those declarations, and all of `SourceDispatchEffects` and `SourceAllHistories`, remain frozen and unchanged. V2 does not export counterparts with those contradictory premises.

## Migration

| V1 use | V2 replacement |
| --- | --- |
| Five-way dispatch split | `Selection` / `classify`, three reachable cases |
| `SourceHistory.dispatch_succ` | `SourceDispatchV2.dispatch_succ` |
| `SourceHistory.all_at` | `SourceDispatchV2.all_at`, import `SourceAllHistoriesV2` |
| `SourceHistory.all_callbacks` | `SourceDispatchV2.all_callbacks` |
| `SourceHistory.static_call_storage` | `SourceDispatchV2.static_call_storage` |

The versioned 17-field horizon induction is re-proved through the reachable dispatch consumer. Owned `WorldCalls.ClosedSourceFrame`, `ClosedSourceConsumers`, `ClosedSourceControls` and `SourceExpressionConsumer` migrate without changing their statements or premises. Other lanes must explicitly switch imports and theorem references; V1 remains available and is not silently redirected.

`SourceDispatchInterfaceV2Controls` witnesses each constructor with actual selected equations: a callback function, a public counter getter and empty/unknown special dispatch. A getter-selection witness is not a successful getter-execution theorem. Kernel-observed empty revert, static callback-write refusal and zero-horizon exhaustion retain their behavior. Negative controls exclude function/getter selection at empty input. The controls instantiate the new history and callback consumers as well.

This repairs dispatch partition reachability. It proves Source journal/storage histories only. Frontend AST authenticity, Source/Core representation, native world-call execution and compiler adequacy remain separate obligations. No Core call or protected Source module is edited.
