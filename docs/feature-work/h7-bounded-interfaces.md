# H7 bounded scanner and padding interfaces

The vendored revision is `047f6307+h7-bounded-scanner-padding-v1`; its exact
patch and original/patched hashes are recorded in
`Bridge/vendor/EvmYul/h7-bounded-scanner-padding-pin.json` and `VENDOR.md`.

- `PaddingInterface.lean` proves the existing logical `PaddingCorrect` contract.
  `paddingCorrect_of_host_bound` needs only `bound < USize.size`; the 64-bit
  reader bound follows on both supported host widths. `paddingCorrect_bounded`
  retains its earlier signature for clients. `paddingCorrect32`, zero-length
  reader and word-serialization laws consume the proved contract.
- `BoundedScannerInterface.lean` connects the published parse/next-PC paths to
  actual `D_J_aux` when `code.size + 33 < UInt256.size`.
  `BoundedScannerPrefix.lean` supplies byte-step and accumulator-membership
  transport. Outside that bound the original partial traversal is retained.
- `H7InterfaceChecks.lean` proves the actual table for `60 5b 5b` is `[2]`:
  offset1 is PUSH1 payload, not a jump destination. It also consumes the reader
  and serialization interfaces.

These are kernel laws over the adopted logical definitions. They do not prove
native allocation/extern compatibility, successful source invocation, installed
code or compiler adequacy. The native zeroes fixture/provenance is separate
implementation evidence. Patch/pin-file coverage in `check-bridge.sh` is a
separate DT-owned trust-check follow-up; this checkpoint does not change it.
