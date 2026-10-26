# Declarations and metadata

Compiler-resolved declaration metadata, synthesized public getters and source
ABI identities. Inventory status: partial.
`Examples/Tactics/DeclarationMetadata.lean` and `tests/solc/DeclarationMetadata.sol`
pin the metadata; `Examples/Tactics/PublicGetters.lean` and
`scripts/public-getters.test.mjs` pin the getters.

## Metadata (`Frontend/SolcJson/Body.lean`)

- `type(C).name` is the contract's name as a UTF-8 string literal.
- `type(I).interfaceId` XORs the selectors of the ordinary external/public
  functions declared in `I`, its own overloads and overrides included.
  Inherited methods and receive/fallback contribute nothing.
- Error selectors (four bytes) and non-anonymous event selectors (32 bytes) come
  from solc's canonical ABI metadata, resolved by declaration ID (qualified
  declarations with the same short name included). The parser returns
  `Fin (2^(8*bytes))`. Malformed widths or digits fail closed; anonymous event
  selectors are refused.
- Static declaration selectors and `this.f.selector` fold to literals. A
  dynamic receiver's selector is a fresh pure helper that consumes the receiver,
  so it is evaluated once in place; Boolean and conditional arms stay lazy.
- Unnamed input parameters get names derived from declaration IDs. Unnamed
  returns keep the return-frame naming.
- Generated helpers carry an `#internalEntry` marker in the width metadata
  table (`#` cannot start a Solidity identifier). Function-value construction,
  both dispatch forms and the dynamic call graph exclude them; direct generated
  calls still work, and function-tag indexes are kept.

No selector uniqueness or hash injectivity is assumed. Compiler-invalid
contexts (an ambiguous overloaded reference, a public function's own
declaration selector inside its contract) are left to solc.

## Public getters

- `FunDecl.sourceDecl` is defaulted source metadata: local versus ABI
  functions, selected versus retained base bodies, getters, special entries and
  implementation helpers. ABI selectors are `Fin (2^32)`. Canonical signatures
  are computed before enum/UDVT/contract/struct lowering, so model names never
  feed a selector. Modern serialization keeps every public/external selector.
- A public state variable synthesizes a function beside its storage root.
  Mapping keys and array indexes become parameters; terminal elementary values
  become results; a terminal struct keeps its non-mapping, non-array fields in
  order. Supported types are elementary bool, address, integer and fixed bytes.
  Explicit `uint256`/`int256` indexes are canonicalized.
- Getters share dependency ordering, elaboration and self-call inlining with
  source functions. Scalar, mapping and fixed/dynamic/nested array getters run
  through external self calls; primitive struct tuples through
  `try … returns (…)`. Public variables overriding interface functions resolve
  through solc's `baseFunctions`. Named mapping-key arguments reorder to the
  declared order.
- A getter is recognized only as an external member (`this.x`, `c.x`): a bare
  identifier keeps its storage identity, and a function-valued slot's
  `x.selector` does not fold to its getter's selector.
- **Out-of-bounds getters revert with empty data**, while an ordinary array
  read panics (both pinned compilers, both pipelines). Each generated array step
  is `require(index < path.length)` before the read. Getter bodies skip the
  `withPanics` pass, which would add unreachable `Panic(0x32)` catch
  alternatives.
- Internal function values exclude external declarations, getters and special
  entries; external values exclude local/free/library helpers. Selector dispatch
  and self-body lookup admit selected entries and getters; retained overridden
  base bodies stay available to direct internal calls.
- Generated function, getter and constructor aliases avoid source names,
  generated local/state aliases and printed struct renamings. Constructor
  helpers join `internalFuns` with implementation roles.

## Narrow self returns and byte prefixes

- Narrow primitive external returns are accepted for a static `this` receiver
  once its typed self frame resolves. Range checks reject invalid values before
  the success body, and such a decoder failure reverts the caller with empty
  data outside its catch clauses. The callee's source result kind must match
  the binding: fixed byte widths exactly, no byte/integer crossing; same-sign
  numeric widening keeps the caller-side range checks.
- Dynamic `bytes` to `bytesN` evaluates the receiver once, extracts at most N
  guarded bytes and right-pads with zero; storage operands are materialized
  first. The prefix is a lowering builtin, hoisted whole at an initializer or
  assignment. `bytes(string)` stays valid; both branches of a conditional must
  keep the bytes kind.
- An unused bare scalar identifier is dropped only when it resolves to a
  `VariableDeclaration` of known scalar type.

## Refused, and why

- Getters with nominal (enum/UDVT/contract) or function types, dynamic
  `bytes`/`string` keys or results, or nested aggregate results. An unsupported
  returned field refuses the whole getter: `bytes`/`string` are not silently
  omitted as arrays. Narrow or fixed-byte constants the `uint` constant
  collector does not recognize.
- Narrow returns from an unknown address: world `bytesN` words differ in
  padding from typed self values.
- Byte prefixes of arbitrary `uint8` arrays, and direct `string` conversions.
- Abstract-contract `.interfaceId` (only interfaces are supported).

## Cost

`FunDecl.sourceDecl` touches low syntax, so changing it rebuilds broadly. It
keeps `1a7d5b0e`'s one-body-per-callee memoization and segmented contract
compilation.

## Left

- Import/remapping resolution across source units.
- Reference-valued getters (they need the world's return-value interface) and
  tuple external returns; nominal getter types; struct omissions in exact
  getters.
- Inherited external function values with renamed model declarations (the
  function-value packer hashes model names): one shared ABI identity for
  source declarations and model functions.
- Broader `using for`, qualified custom-error reverts, receive/fallback/world
  registration, remaining constructor/immutable/visibility distinctions,
  and the erasure of mutability in function types.
- `#verify`, `#counterexample` and `#difftest` may still show generated helper
  obligations; the source testing API does not.
