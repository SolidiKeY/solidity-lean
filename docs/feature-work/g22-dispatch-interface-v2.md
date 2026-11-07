# Reachable readonly dispatch interface V2

H69 replaces the unreachable branch split through an additive version, without changing source execution or frozen V1 proofs. Import `Solidity.Lowering.Readonly.SourceDispatchInterfaceV2` and use namespace `Solidity.Lowering.Readonly.SourceDispatchV2`.

`Selection G F input` has three constructors: function with actual selection and nonempty input; getter with no function and actual getter selection; special with neither selection. `classify` constructs this certificate for every actual global, frame and input. No selection oracle or future producer is assumed. Every selector has four bytes even for the arbitrary fixed hash word. Thus `pickFn_empty` and `pickGetter_empty` prove that empty input selects neither function nor getter.

The old `SourceHistory.dispatch_getter_empty_succ` and `dispatch_special_empty_succ` require a selected function and empty input. Their premises are contradictory. Those declarations, and all of `SourceDispatchEffects` and `SourceAllHistories`, remain frozen and unchanged. V2 does not export counterparts with those contradictory premises.

## Versioned pair (H57)

| Version | Modules | Status |
| --- | --- | --- |
| V1 | `Lowering/Readonly/SourceDispatchEffects.lean`, `Lowering/Readonly/SourceAllHistories.lean` (namespace `SourceHistory`) | Frozen. Byte-identical to master (blobs `a6e9c998…`, `3eb1abb5…`); no statement, premise or proof edited. |
| V2 | `Lowering/Readonly/SourceDispatchInterfaceV2.lean`, `Lowering/Readonly/SourceAllHistoriesV2.lean` (namespace `SourceDispatchV2`) | Published. Additive; reuses the three reachable V1 branch lemmas, never the two vacuous ones. |

Both versions conclude the same `SourceHistory.At`/`Effect` predicates, so a V1 and a V2 consumer interoperate without adapters. V1 stays importable; nothing is silently redirected.

## Migration

| V1 use | V2 replacement |
| --- | --- |
| Five-way dispatch split | `Selection` / `classify`, three reachable cases |
| `SourceHistory.dispatch_succ` | `SourceDispatchV2.dispatch_succ` |
| `SourceHistory.dispatch_getter_empty_succ`, `dispatch_special_empty_succ` | none: premises unsatisfiable (`Controls.v1_getter_empty_vacuous`, `v1_special_empty_vacuous`) |
| `SourceHistory.all_at` | `SourceDispatchV2.all_at`, import `SourceAllHistoriesV2` |
| `SourceHistory.all_callbacks` | `SourceDispatchV2.all_callbacks` |
| `SourceHistory.static_call_storage` | `SourceDispatchV2.static_call_storage` |

Statements are identical up to the namespace; only the import and the qualified name change.

### Per consumer

Checked on 2026-11-06 against `origin/master` and the visible consumer branches (`cloud/move6-20261106/v13-abi`, `codex/solidity-h62-1-20261106/binding-fixtures`). On master the only V1 users outside `Lowering/Readonly/` are four `Backend/WorldCalls` modules (below); this branch migrates them, with unchanged statements and premises.

- **audit-readonly-calls** (H62 hypothesis audit). Count `SourceDispatchV2.Selection`'s three constructors as the dispatch partition, each with a joint-satisfiability witness (`Controls.function_jointly_satisfiable`, `getter_jointly_satisfiable`, `special_jointly_satisfiable`, each with `SourceHistory.At G 3` from `all_at`). Record the two V1 empty-selected lemmas as vacuous by `v1_*_empty_vacuous`, not as covered branches. Per Q-CALLBACK-INTENT, the static-callback refusal controls (`callback_write_refused`, `SourceDispatchControls.static_callback_refused`) are intentional no-callback controls: accept the impossibility and never count them as positive callback witnesses.
- **V13** (abi-world). Selector routing facts come from `SourceDispatchV2` (`selector_length`, `pickFn_empty`, `pickGetter_empty`, `classify`). When V13 merges master after this lane, its copies of `ClosedSourceFrame`, `ClosedSourceConsumers`, `ClosedSourceControls` and `SourceExpressionConsumer` take the V2 imports from this branch; take this side, since statements are unchanged. A V13 module that names `SourceHistory.all_at` should switch to `SourceDispatchV2.all_at` with the `SourceAllHistoriesV2` import.
- **V15** (evm-agreement). Source-side storage preservation is `SourceDispatchV2.static_call_storage`. The G42.02 producer ([g42-02-source-call-producer.md](g42-02-source-call-producer.md)) builds `WorldCalls.FetchedPremises` from one structure, `SourceCallProducer.ReturndataDuty`, a placeholder for V15's CALL/RETURNDATA correspondence. Its relation is unconstrained (inherited from `FetchedPremises.Returndata`). On `Evm.MachineV2`, `SourceCallProducerV2.Returndata` is the pinned relation, proved for every invocation under explicit callee-oracle agreement; relating the oracle to callee execution is V15's. P1 `InterfaceV3.Pending*` also remains open.
- **readonly-bind** (binding fixtures). Rebind fixture rows for `SourceHistory.all_at`, `all_callbacks`, `static_call_storage` and `dispatch_succ` to the `SourceDispatchV2` names; the V1 names stay valid and keep their pins. Fixtures for the two vacuous V1 lemmas are negative (impossibility) rows.

## Witnesses and negative controls

`SourceDispatchInterfaceV2Controls` witnesses each constructor with actual selected equations: a callback function, a public counter getter and empty/unknown special dispatch. A getter-selection witness is not a successful getter-execution theorem. Kernel-observed empty revert, static callback-write refusal and zero-horizon exhaustion retain their behavior. The controls instantiate the new history and callback consumers as well.

Joint satisfiability: `function_jointly_satisfiable`, `getter_jointly_satisfiable` and `special_jointly_satisfiable` give, for each V2 branch, one global, frame, input and bound at which every hypothesis of the branch lemma V2 routes through holds together. `dispatch_succ` itself has the single hypothesis `SourceHistory.At G n`, discharged for every `G` and `n` by `all_at`.

Negative controls: `empty_function_impossible` and `empty_getter_impossible` exclude selection at empty input; `v1_getter_empty_vacuous` and `v1_special_empty_vacuous` show that the premises of the two frozen V1 empty-selected lemmas are unsatisfiable for every environment, global, frame and input.

This repairs dispatch partition reachability. It proves Source journal/storage histories only. Frontend AST authenticity, Source/Core representation, native world-call execution and compiler adequacy remain separate obligations. No Core call or protected Source module is edited.
