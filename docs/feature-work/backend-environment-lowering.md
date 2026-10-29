# G31 environment and metadata opcode lowering

This preparation component selects real `Solidity.Backend.Instr` instructions.
It does not complete G31's parent source-to-bytecode theorem or the pinned
Osaka EVM correspondence. Source denotation remains the existing intrinsic
`Val.evalT` and `ContractWorld.World.balance`, independent of selection.

## Ownership and frozen inputs

- Branch: `codex/solidity-independent5-20261029/environment-lowering`.
- Exact base: `50658f41061b366d6e503d1e8a3a324a281e9fca`.
- Repository: `/workspace/scratch/environment-lowering-assigned`.
- Preserved original checkout: `/workspace/solidity-lean`, branch `work`,
  head `dedb3aee5743025aeb6d8f7219c9b6b9c1e00e5d`.
- Owned modules: `Solidity/Backend/Environment/`; this document and append-only
  imports/module-map/document registry rows. No other lane is imported or edited.

The manifest's actual IDs are `msgSender`, `msgValue`, `thisAddress`,
`addressBalance`, `blockTimestamp`, `keccakBuiltin` (not keccak256Builtin),
`erc7201Builtin`, `functionSelector`, `functionAddress`, `errorEventSelector`,
and the interface-ID metadata row. Decisions are those in
[solidity-scope.md](../solidity-scope.md), including G00 Q2, sender funding,
own balance from the ledger, forced credits and fixed cryptographic functions;
[decision impact](roadmap-decisions-impact.md) distinguishes narrower existing
runs from the eventual history-dependent source world. No excluded field,
code/log observation, new premise, verdict or target predicate is introduced.

## Baseline gap

`Evm/Compile.lean` rejects `Val.hash` in its core fragment and emits `[]` for it;
`Evm/Machine.lean` has symbolic crypto/storage operations and simplified
transaction inputs. `Backend/Opcode.lean` has the actual Osaka bytes but no
intrinsic environment adapter at the frozen base. The saved reproduction is
`/workspace/scratch/environment-lowering-evidence/gap.txt`.
Nontrivial control: BALANCE of `2^160+7` reads account 7; SELFBALANCE ignores
an existing stack word and reads self's ledger entry. Treating them alike
changes stack height and, on the inhabited sample, returns 73 instead of 41.

## Checkpoint 1: environment observations

Implemented in `Observations` and `ObservationsChecks`, namespace
`Solidity.Backend.Environment`.

| Existing constructor / anchor | Selection | Interpretation |
|---|---|---|
| `EnvKey.msgSender`, `Syntax/Raw.lean:38` | CALLER, 0x33 | bounded frame sender, zero extended |
| `EnvKey.msgValue`, `Syntax/Raw.lean:39` | CALLVALUE, 0x34 | exact uint256 payment |
| `EnvKey.timestamp`, `Syntax/Raw.lean:40` | TIMESTAMP, 0x42 | arbitrary uint256 timestamp |
| `EnvKey.selfBalance`, `Syntax/Raw.lean:41` | SELFBALANCE, 0x47 | ledger at self |
| `EnvKey.selfAddress`, `Syntax/Raw.lean:42` | ADDRESS, 0x30 | bounded deployment identity, zero extended |
| `ContractWorld.World.balance`, `Semantics/ContractWorld.lean:72` | BALANCE, 0x31 | pop word, truncate low 160 bits, read arbitrary ledger |

Headline results: `account_value`, `account_address`, `select_correct`,
`balance_correct`, `balance_address`, `own_balance`, `world_balance`,
`intrinsic_correct`. `Represents` requires exactly matching frame identity,
sender, value, time and own ledger balance. It quantifies over arbitrary typed
source states, including arbitrary storage, heap, locals, net deltas and
external-response tables. `world_balance` quantifies over arbitrary catalogs,
roles and funds under exact ledger agreement. It is an observation adapter,
not world execution composition. The older intrinsic state does not enforce
160-bit sender/self bounds or own-ledger agreement, so these boundaries are
explicit; invalid transactions and deployment provenance remain parent duties.

The local meaning has no gas/fuel, stack-capacity or exception accounting.
Real EVM use needs sufficient gas/fuel and stack room below 1024. Stack tails
are universally preserved. Wrong-address truncation, confusing own balance
with BALANCE, wrong CALLER/ADDRESS selection, and underflow have inhabited
controls. Excluded CHAINID/NUMBER/ORIGIN/EXTCODEHASH/LOG are refused locally;
this is not an importer admission theorem.

`represented_ok` inhabits the boundary for every existing state and frame,
retaining its oracle and net ledger. `sample_observations` uses distinct
nonzero identities, value, time and balances. `inhabited_certificate` instantiates
the intrinsic certificate on an actual typed initial state.

Axiom pins: `select_correct` and `account_address` use only
`[propext, Quot.sound]`; `intrinsic_correct` uses
`[propext, Classical.choice, Quot.sound]`. No new axiom or proof shortcut.

Finder and skeptic independently reviewed read-only without a Lean server.
Both requested an explicit `World.balance` connection. Skeptic also requested
resource boundaries and an executed high-address balance control. All three
were added; finder verified resolution. Saved review evidence accompanies the
handoff. No slower refactor was performed; earlier speed commits were inspected
and existing hot source definitions were reused without changes.

## Queue accounting

| Item | Status |
|---|---|
| 1 environment instruction slices | Proved and controlled; checkpoint gates below |
| 2 metadata | Pending |
| 3 intrinsic cryptographic builtin lowering | Pending |
| 4 composition certificate and mixed observations | Pending beyond checkpoint-1 expression certificate |
| A erased emits / sequence fallback | Pending interface investigation |
| B frame/stability and all observation/refusal regressions | Pending |

## Runtime and validation evidence

Lean 4.24.0 (797c613eb9b6d4ec95db23e3e00af9ac6657f24b), Lake
5.0.0-src+797c613; these match `lean-toolchain`. No Lean MCP connector is exposed,
so focused kernel builds provide per-file diagnostics. Builds use the observed
absolute toolchain, `LEAN_NUM_THREADS=1`, explicit Lean `-j1` in the untracked
alternate TOML, and serial topological prerequisites. A private disk artifact
cache reuses source/toolchain keyed entries. No LSP runs concurrently.

Systemd user and system scopes are unavailable (no user bus, PID 1 is not
systemd). A Docker cgroup is verified at **12884901888 bytes memory, zero swap**;
this is an aggregate cap for Lake and all children, not an RLIMIT per process.
The outer VM has a 16 GiB cgroup and no host swap. The remaining VM memory is
OS headroom, without an additional coordinator-host reserve inside this VM.
The repository writer lock is held for writes/checks.

Evidence directory: `/workspace/scratch/environment-lowering-evidence`.
The first KeySort attempt failed because the container's default cache path
was unwritable. Retained as failed. The corrected task-private cache run:
`lake -f lakefile.environment.toml build Solidity.KeySort` printed
`Build completed successfully (2 jobs).`, exit 0. This establishes the runtime
gate only. `checkpoint1-deps.log`: serial 29-target closure, exit 0, 100 seconds,
cgroup peak 1360814080 bytes. `checkpoint1-controls3.log`: focused module/control
build, exit 0, 2 seconds, cgroup peak 184881152 bytes. Cgroup memory includes
page cache; it is not an RSS measurement. Early failed proof iterations are
retained and are not passing gates. Final full/import closure and same-base
failure comparison remain required. No full-group completion is claimed.

Checkpoint-1 gate closure: both touched files have clean JSON diagnostics
(`cp1-diagnostics2.log`, exit 0, 2 seconds, sampled peak aggregate RSS
717612 KiB). Direct checking needs Lake's `--setup` mapping for cached imports;
the earlier mapping-free attempt failed and remains recorded. Layer check:
168 core modules, zero reach the elaborator. Orphan check: 768 reachable,
zero orphaned. Trust check: 783 sources, 241 inventoried sites, zero findings.
Documentation-path check fails with exactly the same 46 missing references
at the frozen base (`base-doc-paths2.log`) and this checkpoint
(`cp1-doc-paths.log`); no new finding. This inherited failure is not marked
passed. Both independent reviewers confirmed all findings resolved. Checkpoint
1 is complete locally; final full/import-closure validation remains open.

## Checkpoint 2: metadata constants

`Metadata` reuses `Backend.Assembler.toBytesBE` and its roundtrip theorem.
`constant_correct` proves actual PUSH immediate decoding, exact word value,
zero extension and stack-tail preservation for every width 0–32. `truncate_correct`
states the explicit low-byte modulus; `zero_extension` proves widening keeps
values. `selector_correct` preserves the source's low numeric four-byte value;
`selector_alignment` and `selector_abi_bytes` give the separate ABI-left-aligned
value and exact big-endian immediate. `address_correct`, `function_correct` and
`function_projections` preserve bounded receivers and the existing
`address*2^32+selector` representation.

`metadataSelector` reads `SourceFunction.callable`'s existing canonical
`SourceCallable.abi`/`getter` selector. `declaration_correct` lifts any resolved
selector to code; `selector_intrinsic` connects it to existing `Val.evalT` literal
denotation. Missing ABI metadata, constructors and other non-ABI roles are
refused. No canonical signature is reconstructed from a generated model name.

The bounded `metadataBytes` adapter covers the existing four-byte interface/error
selectors and 32-byte event digests supplied by the importer. Their resolution
and interface XOR computation stay in `Frontend/SolcJson/Body.lean:1060–1095`;
this module does not replace or certify that frontend. `typeName` is also
accounted for: the core `Contract` does not retain its name, so the existing
importer resolves the String first. `nameCode` then materializes the standard
UTF-8 encoder's structural byte-array contents (`toUTF8.data.toList`) through
actual PUSH1/PUSH32/MSTORE8. `materialize_correct`, `writeBytes_at`,
`read_written` and `writeBytes_frame` prove exact bytes/order, stack preservation,
and unchanged memory outside a precisely bounded, nonwrapping interval.
Full string-object layout and allocator integration remain parent obligations.
This is a component-local target slice, not a duplicate source or memory IR.

Both independent reviewers found missing byte-name coverage and requested explicit
declaration/function adapters. Those were implemented and both reviewers verified
resolution without Lean/server/build use. The concrete UTF-8 witness includes
`Aλ`, both neighboring memory bytes and a nonempty stack. Exact byte regressions
cover PUSH4 numeric/ABI selector alignment, PUSH20 address, PUSH24 packing,
PUSH0/truncation, four-/32-byte metadata and PUSH/MSTORE8. Wrong selector alignment
has an inhabited counterexample. `MetadataChecks` pins headline axiom sets to
only propext/Classical.choice/Quot.sound (or the appropriate subset).

`cp2-controls4.log`: focused build passes (36 jobs), exit 0, 2 seconds, sampled
aggregate RSS 784232 KiB, cgroup peak 239304704 bytes. Earlier failed iterations
are retained; none is counted green. No proof/resource budget was raised.

Checkpoint-2 closure: `cp2-diagnostics.log` is clean on all three new Lean
files, exit 0, 4 seconds, sampled aggregate RSS 770068 KiB. Layer/orphan/trust
gates pass: 168 core modules with zero elaborator reach, 771 reachable modules
with zero orphans, 786 source files and zero trust findings. The global layer
checker enumerates core names explicitly; the new modules' import closure is
also reviewed and will receive the task-specific closure check in final gates.
`cp2-doc-paths.log` retains exactly the same 46 inherited path findings as the
exact base, zero new findings. Both independent reviews are closed. Checkpoint
2 is locally complete; full/import closure remains pending.
