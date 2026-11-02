# V15 observable completion fence

Owned Work5 runtime checkpoint following modular head
c553cc0dc70cd16c9cfba8648d317d13ed08a853. No original goal, VM, branch, semantics,
profile, source expectation, dependency/toolchain pin or proof budget changes.
The EXP proposal files remain separate uncommitted, unregistered work; they are
not part of this runtime-only commit and are not counted checked.

The old Power03 monitor receipt remains FAIL125: the source compiler returned0,
but Docker top reported not-running after a running inspect. The old guard
correctly failed closed and did not promote the output. A dependent control
attempt was started before that guard result was inspected; its actual failed
receipt remains separate and contributes no passing evidence. No unchanged
failed runtime operation was retried or old failure relabelled green.

New lane-only scripts/roadmap-v15-bounded-completion.py leaves the entire active
Lifecycle.observe byte-identical to the frozen predecessor. Ten-second startup,
12GiB/swap0, H1 reserve4GiB, serialLEAN_NUM_THREADS1/explicit-j1,300s Lean and
5400s whole-command limits stay unchanged. Unknown inspect/top/identity/limits,
extra Lean workers or active observation gaps still fail closed. All cleanup
remains restricted to the exact own invocation CID; old runner/seals unchanged.

After the workload returns its real code and prints resource evidence, the
outer shell starts a fixed bounded timeout/bash fence. That actual inner fence
atomically writes nonce, workload result, its BASHPID and PPID. Marker is sampled
BEFORE successful active and completion process snapshots; its contents must
remain stable before acknowledgement. Exact-CID running/limits/serial checks
still precede completion handling. A separate PID/PPID snapshot requires one
bound main, one timeout and one fence bash, canonical commands and ancestry
main→timeout→bash→sleep/mv. Namespace IDs of those stable own processes are
read from /proc/status and must match the authenticated marker. Missing mappings,
unknown processes, duplicate roles and unbound lookalikes reject. Only an exact
in-flight marker move can remain pending; no unknown workload survivor is allowed.

Finder initially cleared argument-only helper matching, but skeptic correctly
found that an unrelated sleep0.05 could match it. Actual helper PID/parentage and
namespace binding were added before any probe. Synthetic negatives include that
same-command sleeper, missing/wrong lineage, duplicate roles and spoofed IDs.
Both independent read-only reviewers cleared the revised source and actual
probe receipts without Lean/Docker/build/test execution or writes.

Only after the fully observed no-workload fence passes does the monitor ACK.
Remaining container code can only finish that fixed fence and exit with the
already captured workload status; no workload command follows the marker.
Exact-CID wait/final original lifecycle validation/attach status must agree with
that result. Global deadline checks remain through final completion; a direct
exit without verified completion rejects. This prevents the terminal TOCTOU;
it does not accept an observation gap while any workload can execute.

Pure synthetic07 PASS27tests. Two earlier synthetic harness failures are retained
(shell-constant extraction/expected-format updates), not hidden. Harmless
completion-probe01 PASS0/attach0/guardnull/1.212s, noLeanRSS0, cap12884901888,
swap0,peak4702208. Actual bound host parent chain and namespace marker verified.
Negative completion-nonzero01 preserves raw exit17/attach17/guardnull/1.180s,
noLeanRSS0. Expected-nonzero protocol control is not a passing Lean workload.
Direct reclaim remains denied; no successful reclaim is implied by these runs.
All evidence is /workspace/v15-evm-agreement-evidence/completion-fence-20261102.

These are runtime tests/reviews, not kernel EVM proofs. Subsequent source checks
must pass their own normal admission, monitor and compiler gates before promotion.
All150 opcode rows and all original G46/G47 obligations remain open. Existing
Source.Horizon300s full-gate failure, raw/frozen docs debt, cold5400s124/403 and
historical evidence-loss disclosures remain retained. Existing goal stays blocked;
this does not establish automatic continuation or full runtime/semantic closure.
