# Intrinsic representation

Keep statements, programs, formulas, terms, states and values intrinsically
typed. Locals are typed positions in their context. Elaborators emit that
syntax directly; do not introduce an untyped intermediate representation.
Source declarations, not historical milestone inventories, define the APIs.

## Gate G0: kernel-evaluated code

These restrictions protect kernel reduction cost. Before a representation
refactor, warn about possible checking slowdown, inspect prior performance
changes, and measure under matched limits.

1. Kernel-evaluated functions over indexed families must use `casesOn`/`rec`
   with motives generalizing the indices, avoiding equation-compiler casts.
   Do not introduce indexed `match` outside the measured once-per-link exemptions.
   `match` remains suitable for parameter-only families, types and elaboration.
2. A `rec` implementation may have an `@[implemented_by]` structural twin for
   code generation; every twin requires a proved equality linking both bodies.
3. Labels stay outside context indices; printers carry names separately.
4. Compute local environments from contexts and recurse on typed positions.
5. Scope ends are suffixes; general thinning is for weakening.
6. Avoid administrative calculus steps; premises carry continuation and frames.
7. Quotations share/hash-cons contexts rather than duplicating trees.

Keep explicit constructor equations for recursor definitions instead of broad
`simp [f]` loops. Avoid rewrites that accidentally unfold large word-range
checks. Existing once-per-link merge/update/rewrite exemptions are measured
exceptions, not permission to put indexed `match` in every hot step.

## What stays extrinsic, on purpose

Target-fragment admission is a property of compilation, not a new source type.
Raw external syntax is checked into intrinsic syntax; it is not an alternative
untyped semantic layer. Contract-held bodies cannot be indexed circularly by
the contract containing them; admitted calls carry their typed bodies.
Persistent claims still require explicit semantic/representation premises.

Canonicity, tightness and fit beyond storage shape remain explicit run
hypotheses. Narrow-width checks belong to elaboration. Formula heap identities
are sort-indexed naturals, not globally heap-indexed values; EVM slot offsets
and Theory lengths are mathematical naturals. Do not silently replace those
representations with bounded source words. Decode external ABI responses at
their declared types; undecodable data reverts.
