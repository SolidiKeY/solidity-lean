# EVMYulLean instruction semantics

The 53 modules listed in `UPSTREAM_SHA256SUMS` are the project-local import
closure of `EvmYul/EVM/Semantics.lean` and `EvmYul/Semantics.lean` from
[NethermindEth/EVMYulLean](https://github.com/NethermindEth/EVMYulLean), commit
`047f63070309f436b66c61e276ab3b6d1169265a`. `LICENSE` is that commit's
`license.txt` (Apache-2.0). Paths in the upstream checksum list are relative
to that repository; the build checksum list is relative to `Bridge/`.

The upstream package uses Lean/Mathlib 4.22.0. `Conform/Wheels.lean` needs
two mechanical changes for Lean
4.24's JSON object representation: `TreeMap.Raw.toArray` with `Prod.fst`,
and explicit `Json.str` on the key passed to the JSON decoder. The exact
changes are in `lean-4.24.patch`; the original hashes are retained.
`EvmYul/EVM/Semantics.lean` also needs an explicit `UInt256` annotation
on its existing zero literal in the account-creation branch. This type
inference compatibility edit is recorded in the same patch. All other
EvmYul modules are unchanged.

The closure includes the upstream EVM state, stack, PC update, opcode
dispatcher, gas/halting driver and `execBinOp` transformer. It also contains upstream FFI declarations and
an IO debugging helper. The original arithmetic agreement does not require FFI correctness; its pinned
axiom audits in `SolidityBridge/Checks.lean` show only `propext`,
`Classical.choice` and `Quot.sound`. The optional bounded memory refinement
explicitly assumes a named zero-allocation correctness contract, with no
claimed inhabitant. Its separate `scripts/check-external-memory.sh` observation
fixture links only the verbatim pinned `memset_zero` function and a generated
ABI wrapper. This neither replaces these Lean declarations nor proves that
contract. No hashing C library or upstream conformance executable is linked
or run by the bridge gate.

`SolidityBridge/ExternalEvm.lean` relates its operations to the repository's
actual numeric stack instructions, proves a CSLib simulation, and connects
the shared stack observation to the actual upstream EVM transformer
(`upstream_step`). Extensions under `SolidityBridge/ExternalEvm/` connect
additional operations to the upstream dispatcher and record checked
obstructions to treating core macro instructions as single opcodes.
The original fragment's `Op` type is not a coverage inventory of all core
instructions. This does not prove equivalence of the two full EVM interpreters.

## H7 bounded scanner and padding patch

Human decision H7 ("Implement") authorizes one further local patch,
`h7-bounded-scanner-padding.patch`, recorded with the original and patched
input hashes in `h7-bounded-scanner-padding-pin.json`. It changes two files:

- `EVM/Semantics.lean`: the old partial jump-destination scanner is kept
  verbatim as `D_J_aux_unbounded`. A terminating natural-PC scan `D_J_scan`
  with the same parser, widths and accumulator order is added, and `D_J_aux`
  selects it when `c.size + 33 < UInt256.size` (where no PC wraps), with
  `D_J_aux_bounded` stating that choice. Outside that bound the original
  partial computation is unchanged; no totalization is claimed.
- `FFI/ffi.lean`: `ByteArray.zeroes` keeps its `memset_zero` extern symbol,
  and its `opaque` declaration gets the logical body `Array.replicate n 0` with
  size, empty and element laws. Native allocation and the correspondence of
  `memset_zero` to that body stay separate obligations.

`UPSTREAM_SHA256SUMS` keeps the upstream hashes; `SHA256SUMS` has the patched
ones. To replay, check the original hashes in the pin record, then
`git apply --binary --unidiff-zero` the patch from the repository root.

To refresh, choose an explicit upstream commit, copy the modules listed in
`UPSTREAM_SHA256SUMS` and the license, apply the documented compatibility
patch in `Bridge/vendor/`, update this pin and both checksum lists, and
rerun `scripts/check-bridge.sh`. The
checksums are verified by that script so local edits cannot silently turn
the independent reference into another transcription of our implementation.
