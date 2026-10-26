# Calldata slice values

A slice remains a finite descriptor of its stable array base and captured
start/end offsets. Reading an element, reading `.length` and `abi.decode`
read that descriptor directly. A local declared `calldata` retains the view;
its source type and element widths are checked against the base. The compiler
import preserves this location instead of printing every local as `memory`.
Ordinary struct and fixed-array calldata aliases keep their existing path.

Whole-value uses of a slice with primitive elements now allocate a fresh
dynamic memory array and copy its elements with the existing typed loop,
allocation and indexing statements. No slice constructor is added to the core,
and no recursive shape representation or external Lean dependency is added.
The length can be determined at runtime; this is not literal-length unrolling.

```solidity
uint[] calldata v = xs[1:3];
uint[] memory m = v;
m[0] = 99;                 // xs and v retain their original values
uint n = mutate(v);        // a memory parameter receives its own fresh copy
uint k = read(xs[1:3]);    // a calldata reader receives the same finite values
stored = v;               // existing memory-to-storage copying
rows.push(xs[1:3]);
bytes32 h = keccak256(data[1:4]);
```

The same materialization supports memory returns and existing ABI/hash
consumers, including `sha256` and `ripemd160`. At an internal calldata call
boundary a primitive snapshot represents the immutable values observed by
the callee; the core does not expose a separate calldata pointer or gas cost.
Readonly direct indexing, length and decoding retain their loop-free lowering.

The base is captured before endpoints; each nonconstant endpoint is read once.
The existing relative range checks execute before the copy allocates. A copy
opens at the expression's evaluation position, including inside lazy branches.
Its loop starts at zero, copies `base[off + j]` while `j < length`, then
increments the index. Checked bounds give `off + j < end`, with no extra
relative-index capture or invalid offset addition. Empty copies allocate an
empty array and make no element read. Numeric widths, Boolean kinds, fixed
bytes and address markers are preserved. Source-only markers survive the
hidden base capture, so unsupported enum/function elements fail closed.

Readonly origin analysis stops alias propagation at explicit materialization:
primitive elements retain no source references. It still visits effects
inside descriptors and endpoints. Ordinary whole-calldata aliases keep their
previous restrictions. Slice write targets, increments, deletes, pushes and
rebinding are refused before expression rewriting, including inline targets.
A slice read inside an otherwise writable target's index is allowed.

## Tests and proof boundary

`Examples/Tactics/SliceCopies.lean` supplies native execution certificates and
rejection regressions. `Examples/Tactics/SliceCopiesImport.lean` imports the
modern pinned `tests/solc/SliceCopies.ast.json` fixture and exercises source
location admission, copying, internal calls, returns, storage writes, hashes,
narrow primitives, ordinary non-array aliases and a false assertion.

The proof scripts compute finite `Prog.runF` certificates in the kernel and
lift observations to `Prog.run` with the existing `Prog.runF_approx` theorem.
Divergence cannot satisfy the observation. Negative observations distinguish
ordinary revert and assertion panic; running out of fuel cannot pass them.
No native proof shortcut, new axiom, placeholder or heartbeat override is used.
These are concrete executions, not a general slice-lowering equivalence theorem
or a symbolic copy-loop invariant. Symbolic source proof search may stay open.

The optional `scripts/check-slice-copies.mjs SOLJSON SHA256 MODULES_DIR` uses the
exact Solidity 0.8.38 compiler and an independently supplied EthereumJS VM.
It does not add a dependency to Lake or write outputs. It executes both legacy
and via-IR bytecode and checks source rejections. The fixture records AST
analysis provenance, not compiler/lowering equivalence.

This continuation is integrated; combined validation is **in progress** and
tracked in [feature-work/integration.md](feature-work/integration.md). Its worker
handoff was `patch_ready_unvalidated`: that worker ran independent reference
checks against temporary files without Lean or shared-checkout writes. Those
preparation results are separate from the primary's combined Lean, axiom and
repository gates. Existing view proofs spell their local `calldata` location
so that their programs remain loop-free.

## Remaining interfaces

Reference-element materialization is refused: a shallow copy would expose
writable aliases. Enum/function/UDVT nominal identities, recursive shapes,
external reference arguments, general whole-calldata writable copies and
uninitialized/rebound calldata view locals and computed calldata-local
initializers involving views remain separate work. Native
model tests can supply memory arrays as calldata inputs and can slice those
model arrays; source import still requires solc to admit actual calldata
slicing. This does not enable memory-array slicing in Solidity.

View locals remain virtual source names. They have no new specification
binder: the type-checking alias is private, so a postcondition cannot silently
observe the whole base as if it were the sliced array. Materialize into a
named memory local when its value must remain available outside source
rewriting. The aggregate group and feature catalog remain incomplete.
