# G22: typed source calls, callbacks and the static-world storage frame

Owning modules: `Backend/Passes/` (`SourceTypedCall`, `SourceCallBoundary`,
`SourceCallFrame`), `Lowering/Readonly/` and `Lowering/V08/SourceCallPhase.lean`
(lane compiler10/readonly-external). Each theorem is an equation about, or a
consequence of, the existing `Source.Eval` interpreter; no interpreter, syntax,
fixture, profile or decoder changes. Nothing here is compiler or native
adequacy; the compiler side is [G42](g42-world-call-consumers.md).

## Capture and call boundary (`Backend/Passes/`)

- `SourceTypedCall`: `CapturedAt` requires an actual capture run (a constructed
  `Captured` is not provenance). `eval_external` splits the resolved call into
  capture (target, value, arguments once, in order), encoding/code check and
  `resume`; `external_captured` hands the exact post-capture state to the
  callee; `external_capture_failure` keeps the failure and calls no callee.
- `SourceCallBoundary`: `call_zero`, `call_depth` (before value/static checks),
  `call_static_value`, `static_operation` (journal ops refused when static),
  `return_revert`, `return_short` (declared returns must fit even if discarded).
- `SourceCallFrame`: `enter_success`/`enter_revert`/`enter_halt` carry child
  `dispatch` results through `enterInstance`; a revert applies the *supplied*
  mark (`rolledBack`), not proved equal to the parent checkpoint (`live_mark`
  shows what `mark` records). Controls: `SourceCallControls`.

## Capture phases, failures, receiver, resume (`Lowering/Readonly/`)

- `CapturePhases.compose`: capture from per-phase equations (target, value,
  arguments, encoding, lookup, code admission), each from the previous state.
- `CaptureFailures`: `target_failed`, `value_failed`, `arguments_failed`,
  `encoding_failed`, `code_rejected`: the call never starts; failing state and
  halt are kept, prefix effects are not rolled back. Not claimed exhaustive.
- `CallerResume`: from the exact `callAddr` run, `success` runs `extReturn` with
  the original caller locals, `halted` skips decoding; `invocation` and
  `invocation_halted` compose them with `CapturedAt`.
- `ReceiverCapture`: `word`/`value` embed any 160-bit address as a `uint`
  literal (`faithful`, `evaluate`, `stable`); nothing about zero/self/code.
- Controls: `FullCaptureControls` (declared `g : uint`: canonical, empty and
  one-byte returns), `CaptureFailureControls`, `ReceiverControls`, `ResumeControls`.

## Environment loop (`Lowering/Readonly/`)

- `EnvironmentSteps`: `answer`, `refused` (depth/static-value callback recorded,
  loop continues), `child_success` (success or revert bytes), `child_halt`
  (skips the completion event), `missing_instance`; mode is
  `requested || inherited`, `checkpoint` precedes credit. `EnvironmentCredit`:
  `known`, `unknown`, `failed`, `callback_credit_failed`.
- `EnvironmentHistory`: `CallbackHistories global mode bound` is the explicit P1
  input, a `History` for each admitted callback below `bound` from the
  pre-credit parent to the `enterInstance` final state; it assumes static
  preservation for reentrant children. `loop` is a real horizon induction over
  `envLoop`; `storage` gives all-address storage equality when static.
- Controls: `EnvironmentControls`, `EnvironmentCreditControls` (static credit
  moves balance 0→5, storage fixed), `EnvironmentHistoryControls`. Only
  `credit_only_children` (non-reentering) and `one_step_children` (horizon-0
  child) inhabit the input; `balance_frame_false` refutes balance preservation.

## Static-world storage frame (`Lowering/Readonly/`)

- `StaticJournal.History entry mode final`: start, balance update, ordinary
  write (mode false only), child at `requested || mode`, guarded rollback.
  `History.storage` gives `SameStorage final entry` when static; also
  `credit_history`, `transfer_history`. It is an algebraic endpoint relation,
  not a trace; rollback labels are not authenticated. `JournalLeaves` gives
  leaf histories (`debit_history`, `operation_history`, `cell_history`) and
  composition (`chain`, `bind_history`, `sub_history`).
- `InvocationFrame`: `Invocation` holds global, frame, horizon, checked
  declaration, target/value/arguments, before/after, `captured` and
  `execution : CapturedAt …`; `mode := requested || frame.static`. `RawAt` is
  the exact pre-decoder `callAddr` result; `RuntimeFrames` (P1) is `static` plus
  `history`. `storage` gives caller storage equality from `RuntimeFrames` alone
  (`RawAt` unused); also `raw_unique`, `view_mode`, `pure_mode`.
  `StorageRepresentation` (`relates`, `unique`) is functional, not faithful (a
  constant relation satisfies it); `typed_storage`, `typed_resume` use it.
- `Controls`: `raw`, `read_reentry_raw` come from actual runs; `runtime` and
  `read_reentry_frames` are hand-built `History` terms. Also `balance_changes`,
  `callback_not_suppressed`, `ordinary_not_preserved`, `spoof_rejected`,
  `wrong_raw_rejected`, `static_cannot_write`, `typed_client`.

## Primitive lowering (`Lowering/Readonly/`)

- `PrimitiveValues` (uint/int/bool bijection, `faithful`) and `PrimitiveLocals`.
- `PrimitiveFields`: `Rel` reads actual storage, defaults included (`read_value`,
  `total`, `unique`, `select`); `representation` instantiates
  `StorageRepresentation`; `CallLayout` adds inheritance-checked `Owned`;
  `caller_exit` constructs the exit relation. Listed target fields only.
- `PrimitiveReads.root_expression` derives both `evalE` and `Val.evalT` runs;
  `ReadStatement.simulation` and `target_then` (following code kept).
- `CapturedArguments.arguments`: `Args` from captured values; nothing re-evaluated.
- `PrimitiveInitialization` and `PrimitiveCallable` (`complete`, `body_failure`,
  `wrong_frame`) reuse `Lowering/V08/SourceCallable.lean`; body run, frame fit
  and extraction stay premises. Controls: `LoweringControls` (enum/struct
  refused), `RootControls`, `ArgumentControls`, `CallableControls`.

## Raw call phase (`Lowering/V08/`)

- `SourceCallPhase`: `Request`, `raw` (one `callAddr` via `EM.sub`), `consume`.
  `raw_run`, `caller_locals`, `capture_run` expose the outcome before decoding;
  `external_phase` is the `extCall` equation of `evalE` (prefix, `raw`,
  `extReturn`); `consume_run`, `short_success`, `callee_revert`.
- `SourceCallPhaseControls`, `SourceExternalPhaseControls`: `typed_success`
  (signed word 5), `typed_short`, `typed_revert`, `no_code` on unknown calls.

## Open

- P1: `CallbackHistories`/`RuntimeFrames` for real reentrant, reverting and
  value-bearing children (today: non-reentering/exhausted children and
  `UnknownSourceCall.invocation_success` only).
- Faithful non-primitive representation, layout, whole-body lowering, call-site
  binding, Source-to-Core state; non-storage (balance, ledger, log, transient,
  world) preservation; compiler, EVM and native correspondence.
