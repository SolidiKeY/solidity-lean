# Static frontend checkers G12–G14

Lane V06 (static half). S01 ([source-s00-s01.md](source-s00-s01.md#s01-static-typing-resolution-and-constants))
gives resolution and typing as relations over one source unit. G12–G14 give
executable checkers proved against those relations, and the relations S01
lacks (several units, overloads across bases, inheritance checks), as new
modules:

| Module | Content |
|---|---|
| `Solidity/Source/Units.lean` | G12 relations: programs, paths, remappings, identities, the file-level scope `Sees`, the judgment `UnitsOK` |
| `Solidity/Source/Overloads.lean` | G12 relation: overload sets across bases, `InheritedFn` |
| `Solidity/Frontend/Static/Closure.lean` | Reachability by saturation, sound and complete (`iter_sound`, `iter_complete`) |
| `Solidity/Frontend/Static/Units.lean` | G12 checker: the import resolver and the program check |
| `Solidity/Frontend/Static/Overloads.lean` | G12 checker: `Env.inheritedFns`, `selectOverload` |
| `Solidity/Frontend/Static/UnitsExamples.lean` | G12 controls |
| `Solidity/Frontend/Static/Certificates.lean` | G05 `Checker` instances |

New relations live under `Solidity/Source/` and import only `Solidity.Source.*`
(the non-circularity whitelist); checkers live under
`Solidity/Frontend/Static/`. No existing `Solidity/Source/*.lean` file is
edited (lane-semantics owns them); changes they need are listed in each
checkpoint's Handoff.

## G12: imports, identities, scopes and overloads

### The relations

**Programs.** A compilation input is a `Program`: source units by source
unit name, each an S00 tree `Syn .unit`. Import directives are read off the
tree (`Syn.imports`), one `Import` per imported name: `all p`
(`import "p";`), `ns p N` (`import "p" as N;`, `import * as N from "p";`)
and `sym p a b` (`import {a as b} from "p";`, `b = a` without `as`).

**Paths.** `Program.target R u p` resolves the path `p` imported by unit
`u` as solc's `CompilerStack` does: `Path.absolute` (solc's
`absolutePath`: a path whose first segment is `.` or `..` is relative to
`u`'s directory) then `Remapping.apply` (solc's `ImportRemapper::apply`:
the longest matching context wins, then the longest prefix; a later
remapping wins a tie). solc's path sanitizing is not modelled: units are
named by already-normalized source unit names.

**Identities.** `DeclId` is a unit name and a position in the unit's
`Syn.decls`, S00's identity extended across units; `Program.decl?` reads
it back.

**The file-level scope.** `Sees P R u x σ`: in unit `u`, the name `x`
denotes `σ`, a declaration identity or a unit (a namespace). Its four
constructors are solc's rules: own file-level declarations; `import "p"`
brings `p`'s whole file-level scope, including what `p` imports itself;
`ns` binds a namespace; `sym` binds `b` to whatever `a` denotes in `p`. It is
a least fixpoint, so import cycles are allowed (solc allows them) and an
alias reachable only through a cycle of aliases denotes nothing.

**The judgment.** `UnitsOK P R`: distinct unit names, every import names a
unit of the program (`ImportsResolve`; solc: "Source not found"), every
`{a as b} from "p"` finds `a` in `p`'s scope (`SymsResolve`; solc error 2904,
also for a cycle of aliases), and no clash (`ScopeOK`): two different
symbols one name denotes are overloadable declarations of one kind, two
functions or two events (solc's `DeclarationContainer::conflictingDeclaration`:
"Identifier already declared" otherwise). The same identity reached along
two routes is one symbol, so a diamond of imports is no clash.

**Overloads across bases** (S01's "Overloads across bases" gap).
`InheritedFn E c x d`: `d` is a function named `x` visible from contract `c`
(not a base's `private` member) and callable there by name (not `external`,
S01's `Decl.callableFrom`), declared in scope `b` of `c`'s
linearization `pre ++ b :: post`, and no function named `x` visible in a
scope of `pre` has its parameter types (`Decl.sameParams`, S01's
`STy.sameList`). That is solc's inherited scope: every inherited function,
minus the ones a more derived function with the same parameters overrides.

### The checkers

- **Saturation** (`Closure.lean`). `iter succ n S` adds the successors of
  `S` to it `n` times, without duplicates. `iter_sound`: everything added
  is reachable. `iter_complete`: given a list `U` closed under `succ` that
  contains the start, `U.length + 1` rounds reach every reachable node. The
  proof counts: a round that adds nothing leaves a closed set, a round that
  adds something adds a node of `U`, and a duplicate-free list inside `U` is
  no longer than `U` (`Nodup.length_le_of_subset`).
- **The resolver** (`Frontend/Static/Units.lean`). `Program.globals P R u x`
  saturates the graph of `(unit, name)` nodes from `(u, x)`: `import "p"`
  keeps the name, `{a as x}` renames to `a`. Its result is the leaves of the
  reached nodes (own declarations, namespaces). The bound `U` is
  `Program.nodes`: unit names and import targets crossed with `x` and every
  aliased symbol (`nodes_closed`).
  - `globals_sound`, `globals_complete` (`mem_globals`): the resolver
    returns exactly `Sees`, so it terminates on cycles and misses no route.
  - `Sees.decl_exists`: a declaration identity a name denotes, along any
    route, names a file-level declaration of the program.
  - `lookup_sub_globals`: with any imports, every declaration S01's
    file-level `Env.lookup` finds in a unit is in the resolver's answer, at
    its own identity (the resolver is conservative over S01).
    `globals_lookup`: in a unit without imports the two are equal.
- **The program check.** `Program.unitsOK` checks distinct names, every
  import, every imported symbol (`Program.symFound`), and no clash over every unit and every declared or aliased name
  (`Program.allNames`; `Sees.name_mem` shows no other name is in a scope).
  `unitsOK_iff`: it decides `UnitsOK` exactly (sound and complete).
- **Overloads** (`Frontend/Static/Overloads.lean`). `Env.inheritedFns E c x`
  walks the linearization most derived first and keeps each visible
  function unless an earlier scope has one with its parameter types.
  `mem_inheritedFns` decides `InheritedFn` exactly; `lookup_sub_inheritedFns`
  shows it extends S01's lookup: every callable function `Env.lookup` finds
  in a contract scope is in it. `selectOverload` is solc's overload resolution
  of a call: the candidates whose parameters accept the argument types,
  resolved only when exactly one does (`selectOverload_unique`), the filter
  S01's `Typed.callInternal` applies to its own candidates.
- **G05.** `unitsChecker : Checker (Program × List Remapping) Unit …` is a
  value of G05's generic `Checker` structure for `UnitsOK`, complete
  (`unitsChecker_complete`). It is not wired into a `FrontendSpec`/`Chain`:
  no `FrontendSpec` instance exists yet (G15). `Program.libraries` gives the
  `(unit name, library name)` pairs G05's `LinksResolved` reads.

### Controls (`Frontend/Static/UnitsExamples.lean`, all by `decide`)

| Theorem | Statement |
|---|---|
| `cycle_resolves`, `cycle_ok` | `a.sol` and `b.sol` import each other: each sees the other's contract and its own; the program is accepted |
| `diamond_one_identity`, `diamond_ok` | `D` reached through two routes is one identity; accepted |
| `clash_refused` | two different contracts `T` imported into one unit: refused |
| `alias_renames`, `alias_hides_original` | `import {T as U}` binds `U` only |
| `missing_refused` | an import of an absent unit: refused |
| `missingSym_refused` | `import {Nope} from "x.sol"` with no `Nope` in `x.sol`: refused (solc 2904) |
| `aliasCycle_empty`, `aliasCycle_refused` | `a.sol` takes `y` from `b.sol` as `x` and `b.sol` takes `x` from `a.sol` as `y`: the aliases denote nothing; refused |
| `freeOverloads_ok`, `freeOverloads_both` | free functions `f(bool)` and `f(uint8)` from two units overload in a third |
| `fnEvent_refused` | a free function and an event named `f` in one scope: refused |
| `namespace_binds` | `import "x.sol" as N` binds `N` to the unit (re-exported by `import "a.sol"`) and none of `x.sol`'s names |
| `remapped`, `relative_parent`, `remap_context` | a remapping; `../x.sol` from `src/a/b.sol` is `src/x.sol`; the longer context beats the longer prefix |
| `shadowed_member`, `shadowed_global`, `shadow_ok` | in contract `C` the member `T` shadows the file-level contract `T` (S01's lookup; solc warns, 2519); at file level `T` is the contract |
| `ambiguous_refused`, `exact_selected` | `f(uint8)`/`f(uint16)` called with `1`: both fit (the filter has length 2) and the call is refused; with a `uint16` exactly `f(uint16)` is selected |
| `crossBase_merged`, `crossBase_s01`, `override_hides` | `f(bool)` in `B is A` and `f(uint256)` in `A` form one set where S01's lookup sees only `B`'s; an override hides the base function |

### What G12 does not do

- **Typing across units.** S01's `Ctx`/`Env` is per unit and names
  user types by `DeclName` (scope and name), which two units declaring the
  same contract name would collapse. The resolver gives every file-level
  name its identity across units (`DeclId`), conservatively over S01
  (`lookup_sub_globals`); feeding the identities into S01's typing (a
  program-wide `Env` keyed by identity) is a handoff to lane-semantics. A
  contract whose bases live in another unit is linearized over identities
  by G14.
- **Overloads in typing.** `InheritedFn`/`Env.inheritedFns` and
  `selectOverload` provide the relation and its checker; S01's
  `Typed.callInternal` still filters `Env.lookup`'s first scope
  (`crossBase_s01`). Switching it is a handoff.
- **Cycles, as solc processes them.** solc copies an imported unit's scope
  as it stands when the importing unit is processed (depth first), so
  inside an import cycle the unit processed first sees only the other's own
  declarations. `Sees` gives every unit of a cycle the whole least fixpoint:
  it can see a name solc reports undeclared, and refuse a clash solc never
  forms. Recorded as a deviation; acyclic imports agree.
- **Clashes not refused.** Two namespace imports binding one alias to the
  same unit (`import "p" as N; import "p" as N;`) are one symbol here, while
  solc declares each directive separately. Free functions with the same
  parameter types imported from two units are not refused (solc may refuse
  them in `ContractLevelChecker`; not checked against the pinned tests).
- **Overload hiding.** A public state variable overriding a base function
  (its getter) and a non-function member do not hide base functions in
  `InheritedFn`; overrides are checked by G14.
- **Namespaces.** `Sees` binds `N` to a unit; resolving `N.x` is
  `Program.globals` at that unit, but no rule of S01's typing reads it yet.
- **Paths.** solc's path sanitizing, base path and include paths are not
  modelled; a remapping without context is the remapping with context `""`.
- **Identity.** `DeclId` is a position, like S00's `Syn.graph` (Gate G0:
  these are static checks evaluated once per input, never kernel hot code).

### Gates (G12)

Recorded in [Handoff (G12)](#handoff-g12).

### Review (G12)

A read-only finder and a separate skeptic (neither using the Lean server)
reviewed the first G12 revision.

Fixed:

| Finding | Fix |
|---|---|
| `import {Nope} from "x.sol"` accepted, alias cycles accepted (both) | `SymsResolve` in `UnitsOK`, decided by `Program.symFound`; `missingSym_refused`, `aliasCycle_refused` |
| a free function and an event of one name accepted (both) | `ScopeOK` requires the same kind; `fnEvent_refused` |
| agreement with S01 shown only without imports (skeptic) | `lookup_sub_globals` for any imports; the doc states what is and is not related to S01 |
| `lookup_sub_inheritedFns` did not mention `Env.lookup` (both) | restated as `d ∈ E.lookup (some c) x → … → d ∈ E.inheritedFns c x` |
| `external` functions counted as overloads (skeptic) | `Env.visibleFns` filters by `Decl.callableFrom` |
| `ambiguous_refused` could hold with zero fitting overloads; `exact_selected` did not pin the choice (both) | the filter has length 2; the selected parameters are `[uint16]` |
| `shadowed_member` used a unit unrelated to `shadow` (finder) | one unit with a file-level and a member `T`, both sides shown |
| missing controls: namespace import, overloads across units (skeptic) | `namespace_binds`, `freeOverloads_ok`, `freeOverloads_both` |
| the G05 instance overstated (skeptic); `Program.libraries` docstring said identities | wording: a `Checker` value, not wired into a `Chain`; `libraries` filters file-level libraries |

Recorded, not fixed (under What G12 does not do): solc's depth-first scope
snapshot in import cycles (finder M2), duplicate namespace aliases (finder
L5), getter and non-function hiding (finder M3), same-signature free
functions across units (finder L4, unconfirmed), typing across units and
overloads in S01's typing (skeptic), `DeclId` versus `DeclName` (skeptic).

Answered: `Sees` mirrors the checker's edges one for one, by design: it is
solc's four import rules as an inductive least fixpoint, and the checker is
a saturation whose agreement is the theorem. Independent evidence against
solc's own import resolution (`Frontend/SourceUnits.lean` records solc's
`absolutePath`s) is G15's adapter.

### Handoff (G12)

**Revision**: the G12 commit on `cloud/roadmap-l2-20261029/lane-static`.

**Theorems**: `iter_sound`, `iter_complete`, `mem_reachable` (Closure);
`globals_sound`, `globals_complete`, `mem_globals`, `Sees.decl_exists`,
`globals_lookup`, `lookup_sub_globals`, `unitsOK_iff` (Units);
`mem_inheritedFns`, `lookup_sub_inheritedFns`, `selectOverload_unique`
(Overloads); `unitsChecker_complete` (Certificates); the controls above.
All on the standard axioms (pins in `UnitsExamples.lean`; `TrustAudit.lean`'s
G12 block).

**Premises**: none beyond the relations' definitions; no `sorry`, axiom,
`native_decide`, `implemented_by` or heartbeat option.

**Checks**: `lean_diagnostic_messages` clean on every new file;
`node scripts/check-g07.mjs`: 0 new failures (check-trust 0 findings,
check-layers 0 reach the elaborator, check-orphans 0 orphaned,
check-noncircular 0 violations over 18 source modules, check-axiom-pins 0
errors after recording the new pins, check-doc-paths 46 = baseline). The
full `./run-lean.sh` gate runs at the end of the lane.

**For lane-semantics (existing `Solidity/Source/` files)**:

- `Typing.lean`: `Typed.callInternal` should take its candidates from
  `Env.inheritedFns` (`Solidity/Source/Overloads.lean`) instead of
  `Ctx.functions` (first scope only), keeping its `filter … = [d]`.
- A program-wide environment: `Env` keyed by `DeclId` (or `DeclName` with
  the unit), built from `Program.globals`, so that `Syn.tys`, `Env.userTy`
  and `Env.linearize` see imported declarations.
- `Typing.lean`'s `Env.lookupPath` for `N.x` through a namespace import:
  `Program.globals` at the unit `N` names.

**For G15**: assemble a `FrontendSpec` whose `Resolves` includes `UnitsOK`
(checked by `unitsChecker`) and `libraries := Program.libraries`; relate
`Program.target` to the `absolutePath`s solc records
(`Frontend/SourceUnits.lean`, `checkTree`) for imported fixtures.
