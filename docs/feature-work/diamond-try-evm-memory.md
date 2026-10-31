# Actual try memory opcode and driver components

Checkpoint from authenticated clean905df9958839e80843659475ed3054114ab174b1,
same saved executor and codex/next10-diamond-try branch. This continues the
original task toward source/compiled-EVM correctness. It does not adopt the
held generic source-plan/conditional36 design, any vendor padding interface,
source admission or a profile change. Original native12working/8blocked strict
EXIT1 remains failure. P4/P5b/P8 and full-assignment integration remain open.

## Full unchanged goal and exact input identities

For EACH retained original malformed_panic.sol bundle (legacy AND viaIR), connect
the COMPLETE original declaration f7/body6/assembly5/uint parameter2 and caller
c105/try103/call79/literal78/Panic96/binder87/Return94/hidden slot74 to the actual
compiled execution in that SAME invocation. SourceUnit141/ownerC140 and member77
must resolve to the original f7, not a same-named body. No constant global f,
size36 admission condition, outcome/hcall certificate, reference byte premise,
source hash adequacy axiom or initialized-frame assumption closes that goal.
The separate [source construction design](diamond-try-source-construction-design.md)
is still held, not implemented by these modules.

Source SHA256522bfa3512517476f4f06cef823b176afe52978eb52393b25783e30d10ccc311;
compiler0.8.38+1835d247/SHA256
6c74ffba0ea4cf9521e78b16052a98208770bb7677616de08ced239f4312d390.
Both original bundles retain Osaka/optimizerfalse/runs200/appendCBORfalse and
[full input/output/creation/runtime/source-map identities](diamond-try-c36-path/bundle-identities.json).
Legacy runtime1673bytes/SHA256e335ea9f2867baaaf40c876fa250ffd2bece75a4b833be111d97f9d2c1b799cc;
viaIR1965bytes/SHA256faf0d96218acbf1285125e35959e2ab4babebd7f6e64446c25445aa203c90d52.
Complete inputs in the new proof module reconstruct BYTE-FOR-BYTE to those
compiler objects, not to expected/reference outputs. Their external artifact
provenance is checked separately from kernel reduction; hash equality is not a
compiler/source correctness theorem.

The full target goal includes all of the following, not just its happy path:

* Actual constructor/code installation and entry state, correct self/code/caller
  identities and source owner, ABI selector/parameter evaluation, STATICCALL
  context/value0, fresh child memory/prologue64=128 and the complete ordered
  stores at0/4 followed by revert(0,actual size). Caller logical live H/aliases
  must not be equated with physical empty child memory. Sender/value/storage/
  account state must not be normalized to make a correspondence hold.
* Derive stack operands, reached PCs, memory size/initialization, allocation/
  overlap/read/slice bytes, gas expansion/debits/EIP150/child allowance, actual
  returned failure data and caller rollback from those executions. Source and
  target must share this invocation; a same-looking independent ghost allocation
  is not a physical allocation/cost or a source-callee construction.
* Decode the actual raw Panic data using the approved decoder, bind67 from the
  computed36 payload, preserve handler scope and caller return slot74, and prove
  Return94 ends c's branch. Constructed normal_return's assignment alone cannot
  establish source early-return control or emitted RETURN bytes.
* Preserve original ordered a()/b()/c()/d() observations0,0,67,67 and complete
 32-byte result words in BOTH pipelines. a3/b6 use short actual raw slices and
  catch-all; c36 takes Panic; d256 has a distinct full raw256-byte slice (including
  initialized memory/zero tail) even though the decoder also binds67. f's uint
  parameter stays generic for all other n. No fallback outcome is invented.
* Preserve missing/invalid receiver/code/ABI/value/argument failures and timing;
  child/parent gas exhaustion, exceptional halt, fuel/host stop and divergence
  cannot become completed Solidity failure. Handler failure is not recaught;
  argument evaluation/source hoisting needs its real law before child attribution.
  Original gas100M, shared5M attempted-instruction cap and120s process bound remain.
  Vendor X fuel is NOT assumed equivalent to the modern runner's shared counter.

Source correctness, compiler artifact identity, native/reference observations,
and a proof about the independent EVMYul formal semantics are distinct evidence.
The current formal vendor has fixed gas definitions rather than an Osaka fork
parameter; whole-profile/driver adequacy cannot be inferred from common0x52
arithmetic or code tags. No source or target predicate was changed.

## Implemented in existing semantics

Only the optional Bridge package gains proof/data modules; core remains
independent. [TryMemory](../../Bridge/SolidityBridge/ExternalEvm/TryMemory.lean)
proves the ACTUAL vendored MSTORE dispatcher consumes address/value in order,
preserves the tail and increments PC; zero/one operands yield StackUnderflow.
It gives the exact vendor ByteArray.write memory expression (opaque padding
still present), retained gas/return buffers and ordered0/4 write expression.
Fresh-state record fields mirror the constructor used inside vendor Ξ: supplied
account map and executionEnv are retained while machine memory/stack/PC/active
words have their actual defaults. That record fact does NOT connect the original
source call to Ξ or prove its dispatch path.

Actual memory-expansion arithmetic is0→3words for offset64/width32, then3→3 for
stores0/4; the expansion component is9 then0/0 and the vendor base MSTORE fee3.
Wrong offset96 gives4words; opcode0x53 is MSTORE8, not MSTORE. These are real
vendor calculations, not total prefix gas bounds or X success certificates.

[TryMemoryCode](../../Bridge/SolidityBridge/ExternalEvm/TryMemoryCode.lean) stores
both COMPLETE immutable compiled runtimes as inputs, factored into48-byte chunks
and a balanced concatenation. Standard-library append/size/index proofs avoid
normalizing entire arrays at once. Kernel facts cover the actual prefix bytes
60/80/60/40/52, code lengths and decoded MSTORE/REVERT positions: prologuePC4
in both; legacy870/875/878; viaIR1659/1664/1666. They do not prove those PCs are
reached or supply their runtime operands. No reference return/revert vector is
used as a model producer or premise.

[TryMemoryDriver](../../Bridge/SolidityBridge/ExternalEvm/TryMemoryDriver.lean)
connects byte evidence to existing EVM.decode/fetch and EVM.step, including positive
fuel, execLength+1 and the actual passed modular fee debit. Both full-runtime
PC4 decode facts discharge the byte premise. The at4 equations EXPLICITLY
construct states with that code and PC; they are selected-input controls, not
original entry witnesses. They retain arbitrary supplied state, not normalized
sender/value. step/X fuel0 is OutOfFuel, not revert or expected Solidity FAILURE.
X's gas/stack precheck and actual original-call reachability remain unproved.
No new evaluator, source-memory interpretation, statement, callback rule or
vendor semantics is introduced. The original callback diamond counterexamples
and approved conditional source account are unchanged.

## First concrete missing EVM byte law

The exact inspected interface at pinned EVMYulLean
047f63070309f436b66c61e276ab3b6d1169265a is
[ffi.lean](../../Bridge/vendor/EvmYul/FFI/ffi.lean):

```text
@[extern "memset_zero"] opaque ffi.ByteArray.zeroes (n : USize) : ByteArray
EvmYul.UInt256.toByteArray (val : UInt256) : ByteArray
ByteArray.write (source : ByteArray) (sourceAddr : Nat)
  (dest : ByteArray) (destAddr len : Nat) : ByteArray
ByteArray.readWithPadding (source : ByteArray) (addr len : Nat) : ByteArray
```

Actual #check/#print output is retained in axioms.log. Wheels.toByteArray is
zeroes(32−BE.size) ++ BE. Thus128 and67 require31 zero padding bytes, and even
the full-width selector needs zeroes(0)=empty. writeWord then uses ByteArray.write,
whose source/destination padding also calls that opaque primitive. Padded reads
invoke it even when padding length is0. Providing an already allocated destination
or source-linked M1 bytes does not discharge word serialization.

The FIRST required existing-model contracts have these proposed TYPES only:

```text
zeroes_size (n : USize) : (ffi.ByteArray.zeroes n).size = n.toNat
zeroes_at (n : USize) (i : Nat) (hi : i < n.toNat) :
  (ffi.ByteArray.zeroes n).get? i = some 0
-- derive empty at0, exact32-byte big-endian UInt256 serialization,
-- then actual writeWord range/overlap/frame and readWithPadding slice laws
```

No such size/content theorem was found in the inspected vendor interface. The
public type alone permits arbitrary byte arrays: e.g. a function returning empty
at31 would serialize128 as its unpadded BE payload; nonempty padding at0 could
shift the selector prefix. This is an INTERFACE INSUFFICIENCY ARGUMENT, not a new
interpreter, implemented alternative semantics, runtime counterexample, or theorem
of absolute impossibility. Unfolding currently reaches the opaque call, not a
zero byte/width equation. The standard-only axiom audit of symbolic equations
also does NOT prove that primitive's behavior.

The retained53-module closure supplies no C implementation/refinement proof for
memset_zero. A minimal future owner action would be an explicitly reviewed,
proof-backed semantic body/contract preserving the intended native binding,
followed by size/content proofs, USize bounds, serialization32, copy/overlap and
snapshot laws over ACTUAL vendor operations. A kernel body using pure replicated
zeros would be a vendor semantic change requiring approval and provenance/native
binding validation; it is NOT implemented or inferred from the renewed request.
No new axiom, assumed padding hypothesis, expected-byte constant, alternate
scanner/interface, or replacement memory model is accepted as the original proof.
The existing held vendor/padding choice remains held; no duplicate generic
source-model or historical-runner question is sent.

After that law, the task still needs original prefix/callee/caller composition,
actual X resource/rollback proofs and the source-declaration realization/P8
consumer. Byte backend/compiler owners G46.02/R31 must provide the necessary real
MSTORE32/STATICCALL/resource simulation or a proved connection to these vendor
operations. Cached publishedb965d675 Failure.Slice.step is a different
Option(Machine × Option Outcome) PUSH/MSTORE8/RETURN/REVERT subset; it cannot
stand in for EVM.step's byte memory/gas/accounts/exception state. Its exact
published blob is retained; no unmerged code or new general foundation imported.
The original source still fails Body.memoryRethrow?'s singleton-rethrow shape
and directSelfTryContext's native InlineAssembly refusal. D3/P4/P5b/P8 remain.

## Actual verification, failures and remaining gates

Same-executor shell/HEAD/status authenticated905df995. Lean4.24.0 (797c613),
Lake5.0.0-src+797c613 actual version logs and lake build Solidity.KeySort exit0
are retained under memory.max12GiB/swap.max0. The absent ephemeral lock directory
was recreated after wake; the setup/user files were preserved. A shim version
option failure was retained before querying the actual Lake binary directly.

Ordinary Bridge dependency loading failed on missing pinned lean-auto (git128).
A runtime-only target configuration uses the SAME existing Mathlib pin and
unchanged EVMYul/Conform libraries; it does not update the tracked manifest or
replace a dependency tree. Initial omission of Conform was repaired from the
original config. A cold build stopped for cache repair retains actual137, not
pass; cache failures (missing curl, nested config/PATH, then actual Azure HTTP403)
are retained. No alternate network route was attempted after denial. Offline
compilation recovered the1052-job import closure at unchanged resource bounds.
This is Lean formal-library compilation, not a historical backend/runner build.

Initial proof attempts hit200000heartbeats and default recursion depth. Controlled
unfolding, ordinary list/array lemmas, chunk sharing and small certificates fixed
them without raising limits or dropping statements. All failed MCP/build outputs
remain. The MCP LAKE setup-file config-loss issue was repaired with an explicit
runtime server invocation, without changing installed tooling or tracked config.
No linter was disabled. The three owning files have final success=true,
partial=false, items=[], failed_dependencies=[]; targeted driver import-chain
build exit0. All29 public #print axioms results are standard-only or none,
including their transitive private helpers. The old vendor Xor warning is retained.

The edited registration root was also queried under the ordinary configuration:
MCP returned diagnostics_unavailable and is NOT known clean. Ordinary config load
has the separately recorded missing-auto failure. No full Bridge package pass is
claimed. Retained core/full/TestSuite/Corpus/strict/trust/310-audit checkpoint
results are historical; unchanged passing fixture groups are not replayed here.
New structural/trust/inventory/doc results and exact resources are linked below.

Per-original-row before/after: malformed_panic source/native remains blocked in
both pipelines; no new original pipeline replay or source verdict improvement.
All20 catalog rows stay present; native12/8 strictEXIT1 and the six physical/
reference plus two historical blockers remain. Both pre-Byzantium fixtures stay
blocked/unexecuted with literalgas8000 and original observations. The rejected
ABI lane, historical runner/profile, other-owner work and all original six gap
certificates/target/exclusion/callback/default/proof budgets are unchanged.
This component is not whole EVM correctness, original-assignment completion or
an integration delivery. Controller alone handles any eventual integration.

Read-only finder/skeptic inspected current modules, relevant vendor semantics and
actual log excerpts; neither found a concrete soundness/scope defect. Neither
ran checks, Lean/server/compiler/EVM/scripts or independently rehashed all code
arrays. Complete-input hashes and artifact integrity are worker-verified.
[Review scope](diamond-try-evm-memory/reviews.txt),
[actual axiom account](diamond-try-evm-memory/axiom-account.json),
[owning diagnostics](diamond-try-evm-memory/diagnostics.json),
[complete input identity](diamond-try-evm-memory/full-input-identity.json),
and [retained integrity](diamond-try-evm-memory/integrity.json).

Final static gates: vendor checksums, full-input/prior-artifact integrity, core
orphan/layer, strict automation, trust policy, generated inventory --check and
whitespace all exit0. Inventory is current (no hand edits/support inflation).
Documentation retains actual exit1:20missing and unchanged ambiguities; complete
pre-resource-footer output is byte-identical to the actual905df995 retained log,
zero new findings. No new full original source/fixture gate passed.

All completed bounded groups verify memory.max12,884,901,888/swap.max0 and no
max/OOM event. Largest COMPLETED group cgrouppeak1860042752bytes;
largest sampled aggregateRSS3613444KiB. The deliberately stopped
cold attempt137 lacks its final peak/footer and is not counted as a passing
resource gate; its peak remains unknown. OS MemAvailable stayed above16GiB in
observed probes, disk about21–22GiB free; caches remain on disk. Direct owning
Lean checks use-j1/threads1; all heavy work was serialized under the writer lock.
No proof/fuel/gas/host/test limit was raised. Temporary task configs were removed
only after byte-identical checks; tracked/user setup and all caches are preserved.
[Exact validation/resource account](diamond-try-evm-memory/validation.json),
[documentation comparison](diamond-try-evm-memory/documentation-comparison.json),
[cleanup](diamond-try-evm-memory/cleanup.json).
