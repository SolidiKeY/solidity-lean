# Calldata slice values

A slice remains a finite descriptor of its stable array base and captured
start/end offsets. Reading an element, reading `.length` and `abi.decode`
read that descriptor directly. A local declared `calldata` retains the view;
its source type and element widths are checked against the base. The compiler
import preserves this location instead of printing every local as `memory`.
Ordinary struct and fixed-array calldata aliases keep their existing path.

Whole-value uses of a slice with primitive elements allocate a fresh
dynamic memory array and copy its elements with the existing typed loop,
allocation and indexing statements. No slice constructor is added to the core,
and no recursive shape representation or external Lean dependency is added.
The length can be determined at runtime; this is not literal-length unrolling.

Slices of fixed primitive rows (`uint8[2][]`, `int8[2][]`, `bool[2][]`,
`bytes2[2][]`, and address rows) also materialize independently. An outer
copy iteration allocates a fresh fixed row, fills its primitive leaves with an
inner loop, then installs that row into the result. No source row reference
is installed in the result, even if native model inputs share row identities.
Both loops use the existing intrinsic allocation, index and assignment
constructs. Inline arrays can contain direct, named or nested slice copies:
`[xs[1:3]][0]` retains the slice's inferred type and widths. Type inference
peels descriptors without opening them. Pending projection checks run after
hoisting, before destination binding or argument capture, so neither a target
nor a formal parameter can supply a different reference element width. Fixed-byte markers and numeric widths survive hidden captures.
Address rows preserve the existing address carrier and ABI marker; this does
not add native nominal address, payable capability or contract-type separation.
Source compiler admission remains responsible for rejecting incompatible
address/integer aggregate conversions.

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
admitted elements retain no source references. It still visits effects
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

`Examples/Tactics/SliceReferenceCopies.lean` checks independently compiled
legacy/via-IR fixed-row source programs, including shared native source rows,
captured-base rebinding, endpoint effects, lazy untaken failure, calls/returns,
storage copies, signed/byte/address kinds and precise model failure classes.
The optional `scripts/evm-reference/slice-reference-copies.mjs` separately
checks bytecode observations, exact revert data and stateful rollback with the
repository's existing pinned optional EVM dependencies.

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

View proofs spell their local `calldata` location so that their programs
remain loop-free.

## Remaining interfaces

Other reference-element materialization is refused with
`sliceReferenceCopyUnsupported`: structs, nested reference rows and dynamically
sized rows need further deep-copy interfaces. A shallow copy would expose
writable aliases. Source slicing of nominal enum/UDVT elements is refused
before type erasure, including readonly views; the native enum/function marker
checks remain. Neither retained nested identifiers nor historical fixtures
without those identifiers bypass this refusal. Enum/function/UDVT nominal
identities, recursive shapes,
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

## Calldata origins and aliases

An ordinary `T calldata v = e` (not an explicit slice) is a read-only alias of
a known calldata origin, never an unchecked memory alias. This is frontend
preprocessing only: no core statement and no new simulation theorem.

### Supported

- `RawStmt.sliceViews` takes the known calldata roots (empty for standalone
  raw programs); `contract!` passes the function's calldata parameter names
  before parameter expansion drops their locations.
- An ordinary declaration's initializer must be a stable name/member/index
  place rooted in a known origin, with pure indices. The alias keeps that
  origin, so aliases of aliases are read-only too. Shadowing clears origins,
  and nested scopes restore both the origins and the slice descriptors.
- A calldata pointer may be rebound to another admitted stable calldata place.
  A slice captured earlier keeps its original base.
- Struct and fixed-array aliases of calldata parameters keep their typed
  memory-alias representation and read behaviour.
- Explicit slice descriptors keep their native reading (an interpreter
  example may give a read-only slice a memory-backed array); materializing an
  admitted slice allocates an independent array
  (above).

Regressions: `Examples/Tactics/SliceCopies.lean` (transitive aliases, writes
through array/struct/fixed-array aliases, scope exit, memory bindings
disguised as calldata, effectful initializers).

### Refused

- Writes through an ordinary alias, in statements and nested expressions.
  Write-target detection follows assignment results and both branches of
  reference conditionals, so neither can hide a calldata origin.
- A memory origin introduced by a bare or nested assignment.
- Rebinding a virtual slice descriptor.
- Effectful or conditional initializers (calls, effects, conditional
  references): an explicit elaboration limit, though some are valid Solidity.

`calldataCheck` still checks copies, return bindings and calls to memory
parameters. Its memory-return alias pruning keeps the recursive
memory-argument and nested-assignment checks conservative.
