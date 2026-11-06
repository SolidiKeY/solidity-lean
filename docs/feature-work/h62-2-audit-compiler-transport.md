# H62 item 2: compiler-transport empty-statement audit

Task: `solidity-h62-2-20261106/audit-compiler-transport`.
Frozen base: `c6f550e281a7e5affa9a99bc2cdaed556dec00e4`.
Assigned branch: `codex/solidity-h62-2-20261106/audit-compiler-transport`.
Only additive owned test/script/document paths are changed. No frozen interface,
root, module map, trust pin, heartbeat or dependency is changed.

## Current result: incomplete, scope decision pending

The source inventory accounts for all 122 first-column module-map entries and
560 declarations exactly once (539 public, 21 private). A prose reference to
`Evm/Signed.lean` is not an extra table entry. The scanner freezes both the map
and every original source file against the base. Signature spans, exact text,
source-prefix context spans, hashes and owner records are in external census
JSON. This source-level evidence is distinct from the completed theorem-constant
reflection below; semantic interface classification remains pending.

No positive theorem is reported witnessed until the additive proof passes Lean
and its exact hypothesis coverage is reconciled with the original statement.
Per-input feasibility and global premise structure inhabitation remain distinct;
Prop-versus-data reflection alone does not classify a semantic producer premise.

## Scope conflict and owner ticket

The [saved owner ticket](../../tests/h62/item2/audit-compiler-transport/owner-ticket.md)
records Q-NEG-01, exact frozen signature hashes, V09 consumer and V07/P12 producer
routing, and two decision options. These are intentional negative controls;
their incompatibility does not prove a positive interface vacuous. No criterion
change or owner edit is assumed authorized.

ESCALATE: Solidity.Backend.Passes.P12MemoryCapture.nonempty_revert_incompatible — frozen P12MemoryCapture.lean:75 concludes False, so simultaneous witnesses for its full hypothesis tuple are impossible; options: retain the exact statement and authorize joint-impossibility evidence for negative controls, or retain the literal witness criterion and await an owner-authorized interface plan (Q-NEG-01; V09/V07).
ESCALATE: Solidity.Backend.Passes.P12StorageCapture.nonempty_revert_incompatible — frozen P12StorageCapture.lean:64 concludes False, so simultaneous witnesses for its full hypothesis tuple are impossible; options: retain the exact statement and authorize joint-impossibility evidence for negative controls, or retain the literal witness criterion and await an owner-authorized interface plan (Q-NEG-01; V09/V07).

## Validated additive proof artifacts

- `tests/h62/item2/audit-compiler-transport/JointHypotheses.lean` existentially binds every original parameter together,
  in dependency order, ending in True. Its impossibility terms use the original
  False-conclusion theorem and existential elimination. No separate premise
  inhabitation is substituted for a joint witness.
- `tests/h62/item2/audit-compiler-transport/Audit.lean` retains the frozen P12 interfaces and gives unconditional public
  selection, source success, target success, full mapped output and allocator
  cursor 264 for two associations of the existing allocating scoped-call
  fixture, for every saved stack. Reject-all and always-revert candidates fail
  that strengthened audit contract. Actual public contracts are not edited.
- `tests/h62/item2/audit-compiler-transport/Witnesses.lean` places original acceptance, admission, payment freedom,
  source result, target result and selected map in one correlated tuple for
  the generic compiler boundary statements named in its docstring.
- `tests/h62/item2/audit-compiler-transport/Reflect.lean` writes exact elaborated types, raw Expr representations,
  universe parameters and binder types for imported theorem constants. Private
  kernel names and auxiliary declarations must be reconciled separately.

All four additive modules pass bounded serial Lean diagnostics. Their eleven
new theorems report only `[propext, Classical.choice, Quot.sound]`. No new
axiom, sorry, native_decide or raised heartbeat is present. The success family is finite and
intrinsic. It does not prove totality for every compiler-supported Source
program, inhabited global P12 producers, or the rest of the 560 statements.
The frozen abstract `Evm.Machine` explicitly has no gas or fork parameter;
its success/revert/resource results cannot establish bytecode gas/fork
adequacy. The final Nat in `Evm.Out.ok` is a pending jump skip, not gas. That boundary remains uncovered in this audit.

## Checks and resources

The actual frozen toolchain is Lean 4.24.0, commit
797c613eb9b6d4ec95db23e3e00af9ac6657f24b; Lake 5.0.0-src+797c613.
The v4.35.0 official archive pin in coordinator inputs is scoped to migration
lanes. This lane does not migrate or reuse a per-master cache.

Fresh KeySort: `lean -j1 --tstack=131072 Solidity/KeySort.lean`, exit 0,
2.7163 s, sampled direct-process peak RSS 257884160 bytes. An earlier attempt
could not invoke `/usr/bin/time` (absent); it is not counted as a passing gate.
The Python runner records the actual exit and bounded run separately.

`build_serial.py` checks the full dependency closure one file at a time with
`LEAN_NUM_THREADS=1`, explicit `-j1 -DElab.async=false`, original proof budgets, fresh external
OLEans and a 4 GiB available-memory guard. Inherited VM cap is 16 GiB;
RLIMIT_AS is 12 GiB per child. Host swap is zero. Sampled RSS is direct-child
only, not aggregate Lake/shell evidence. The lane holds the repository writer
lock for the build. No other worker is terminated and no systemd-run is used.

The initial async-default run aborted at unchanged Calculus/TermSize with a
native thread-creation error; the same-limit retry measured 44 threads and
11710242816 virtual bytes despite less than 1 GiB resident memory. The serial
elaboration retry passed in 32.7625 s, with five threads, 3029798912 virtual
bytes and 930349056 sampled resident bytes, without raising any limit. Both
failed attempts and the recovered passing check are retained externally. The
resume compares prefix sources with BASE and records current artifact hashes;
it checks artifact presence but has no earlier artifact digest to authenticate;
it does not use the pre-existing Lake cache. The matched timing gate uses
serial elaboration and symmetric target warmup on both sides. It measures
unchanged CompilerWholeScope checking, not whole-closure/end-to-end cost.

Source acceptance passes: nested comments, quoted fake declarations, inline
attributes, default-binder `:=`, frozen per-module hashes and counts, independent
token counts and rejection of a removed map row. Layer checking passes (857
core modules; zero paths to elaborators or checked parser adapters). Generated
root and fragment checks pass. The first 327 successful modules used async-default elaboration; the
remaining 323 use explicit serial elaboration after recovery. Every command
used `-j1`, and exact historical commands are retained in metrics.
Fresh diagnostics pass for the entire 650-module dependency closure and all
four additive modules. Reflection passes for all 122 mapped modules: 560
source theorems match exactly once; 554 additional kernel-generated theorem
constants are separately recorded. The optimized collector matches all 22
completed prior module outputs exactly. Final `./run-lean.sh` remains pending. No RUNTIME_GATE_PASS is claimed.

No production refactor is made. Original modules are byte-for-byte frozen.
The matched original-file median is 3.127804369 s before and 3.427619808 s
after, a 9.585492 percent increase (below the strict >10 percent stop boundary).
Both sides use three samples, symmetric warmup, the same original source/import
artifact hashes, CPU 0, Lean flags and resources. This narrow measurement is
not a whole-build performance claim. It was not repeated or cherry-picked.
Full affected/end-to-end measurements remain pending.

## Independent reviews

Read-only finder and skeptic used no Lean compiler or server. Both found and
confirmed fixes for the prose-reference scope error and absent frozen-map
comparison. Finder also confirmed inline-attribute and command-whitespace
handling; skeptic identified direct-child RSS limits and explicit VO1 ownership.
The corrected source acceptance passes. Follow-up reviews found no weakening
in the dependent existential construction or finite success controls. Skeptic
requested explicit right-associated source success; it has been added. All new Lean now passes compilation. Final reviewer findings also clarified
that resume records current artifact hashes and requested symmetric timing
warmup; both evidence corrections are applied. No review is represented as a proof.

## Remaining queue and handoff

1. Complete semantic interface/global/input classification. Exact elaborated
   types and owner records are available for 1,114 theorem constants, but
   reflection is syntactic and does not classify proof-valued definitions or
   distinguish every global semantic premise from input feasibility.
2. Obtain a criterion decision for Q-NEG-01 and prove remaining joint positive
   feasibility. Coverage currently records 5 verified joint witnesses, 2
   verified public impossibility certificates, 2 private negative controls,
   and 1,105 uncovered theorem constants (551 explicit, 554 generated).
3. Complete supported-family success/totality coverage and gas/fork boundary
   obligations. The finite family and both trivial-compiler controls pass.
4. Extend the existing once-only witness/type reconciliation to remaining
   statements, retain every uncovered declaration/owner, and finish full
   affected/final gates, end-to-end measurements and milestone reviews.

No H55 producer work is duplicated. No push, merge, PR, pre-gate, deployment or
publication occurred. The coordinator must register any eventual additive area
module; no central registration is performed by this audit lane.
