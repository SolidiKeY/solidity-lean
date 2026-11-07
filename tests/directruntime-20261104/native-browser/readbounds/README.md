# ReadBounds consumer wrappers

The scripts in this directory retain reviewable build, closure, axiom and
functional-check commands for the native/browser ReadBounds consumer. They use
external pinned source, toolchain, cache and request inputs; inspect each script
before use. Historical absolute paths describe its original execution layout.
A wrapper being present does not establish that its inputs exist or that its
checks pass on the current tree.

Qualification records, exact wrapper inventories, source/binary provenance and
failure logs are archived in the private coordination repository under
`evidence/solidity-directruntime-20261104/native-browser/`. Bulk runtime and
cache packs remain on the original VM for coordinator pull. Consult the sealed
private handoff for exact hashes and source revisions before reuse.

Ordinary executable checks and optional certificates remain separate. Preserve
all recorded failures and timing STOPs; these wrappers do not authorize an
unchanged stopped rerun or establish whole-assignment acceptance.
