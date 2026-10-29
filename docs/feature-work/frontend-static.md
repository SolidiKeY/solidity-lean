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
| `Solidity/Source/ConstCheck.lean` | G13 relations: compile-time constant initializers (`PureS`, `ConstInitsPure`), named constants (`NamedConst`, `ConstVal`), array lengths (`ArrayLenOK`) |
| `Solidity/Source/UserOps.lean` | G13 relations: user-defined value type operators, `wrap`, `unwrap` (`UdvtTyped`) |
| `Solidity/Frontend/Static/Infer.lean`, `InferComplete.lean` | G13: expression inference over S01's `Typed`/`LVal`, sound by construction and complete |
| `Solidity/Frontend/Static/InferStmt.lean`, `InferStmtComplete.lean` | G13: statement and block checking over `StmtD`/`ItemsD`, sound and complete |
| `Solidity/Frontend/Static/WellFormedCheck.lean` | G13: S01's `WellFormed` decided |
| `Solidity/Frontend/Static/Consts.lean`, `Solidity/Frontend/Static/UserOps.lean` | G13 checkers for the new relations |
| `Solidity/Frontend/Static/InferExamples.lean` | G13 controls |
| `Solidity/Source/Inheritance.lean` | G14 relations: overrides, required overrides, implementations, base constructors, modifier invocations, `using for`, constructor order, callable identity |
| `Solidity/Frontend/Static/Inheritance.lean`, `Solidity/Frontend/Static/C3.lean` | G14 checkers; the C3 specification and S01's linearization proved against it |
| `Solidity/Frontend/Static/InheritanceExamples.lean` | G14 controls from solc's syntax tests |
| `Solidity/Frontend/Static/Certificates.lean` | G05 `Checker` values |

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

## G13: type inference, constants, user-defined value types

### Expression inference (`Solidity/Frontend/Static/Infer.lean`, `InferComplete.lean`)

S01's typing `Typed Γ e τ` is a relation: one expression can have several
types (a hexadecimal zero is its constant and every `bytesN`), and several
rules can apply. `infer Γ s` returns **every derivation shape**: a list of
results `Res Γ c s`, which for an expression are S01 derivations
`Typed Γ e τ` and lvalue derivations `LVal Γ e τ`, and for argument lists,
tuple slots and positional arguments their `TypedArgs`/`TypedSlots`
derivations. `Res Γ c s` is indexed by the tree, so the checker is **sound
by construction**: every result is a derivation of that very expression,
ready for S01's `Typed.toR` into the resolved layer.

`infer` walks every syntactic category (a function over the fixed index
`Syn .expr` alone would not be structural; S00's `Syn.collect` does the
same), with one result family for all of them. Every one of S01's
41 `Typed` and 6 `LVal` rules is generated at the syntax it names: constants
(`constRes`, at every expression), literals, locals, state variables and
`this` (`identRes`), parentheses and tuples (`tupleOne`), unary operators,
the seven binary families (`binPair`, one per `BinKind`) and the comparison
of two constants, `? :`, assignments, indexing, `length`, `balance`, magic
members, conversions, `payable`, internal calls with S01's unique-overload
filter, and builtin calls.

**Completeness** (`typed_complete`, `lval_complete`, `args_complete`,
`slots_complete`): for every derivation of S01's `Typed`/`LVal`/`TypedArgs`/
`TypedSlots`, its type is among the types `infer` returns
(`inferTys Γ e`), by mutual structural recursion on the derivation, one
membership lemma per rule. `hasType_iff`: `HasType Γ e τ ↔ τ ∈ inferTys Γ e`.

### Statement checking (`InferStmt.lean`, `InferStmtComplete.lean`)

`inferS C s L` returns every S01 statement derivation `StmtD C L s L'` and
block derivation `ItemsD`, with the locals as an argument (a declaration
extends them for the rest of its block). It covers every `StmtD` rule:
expression statements, `_`, declarations with and without initializer
(solc's location rule `locOK`), blocks, `unchecked` blocks, `if`, the three
loops (a `for` initializer is checked as the statement `simpleStmt i`),
`break`/`continue`, the three `return` forms, `emit`, `revert E(…)` and the
canonical rethrow (its local is searched among the locals).
`stmt_complete`/`items_complete` prove completeness; `stmtOK_iff`,
`itemsOK_iff` state the decision.

### Well-formedness decided (`WellFormedCheck.lean`)

`wellFormedB r` checks every field of S01's `WellFormed` (its own structure,
`Solidity/Source/WellFormed.lean`): bases and linearization, clashes,
pragmas, declared types, placement, constants with initializers, every
initializer's type by `infer`, every body's frame, distinct names and
statements by `inferS`. `wellFormed_iff` proves it decides `WellFormed`
exactly; `inProfileSyntaxB_iff` decides S00's syntax verdict. So S01's
well-formedness of a unit is computed, not written by hand:
`counter_checked` re-proves S01's `counter_wellFormed` by `decide`.

### Compile-time constants (`Solidity/Source/ConstCheck.lean`, `Solidity/Frontend/Static/Consts.lean`)

- **Compile-time initializers.** `PureS Γ .expr e` is solc's purity
  (`TypeChecker`, error 8349, "Initial value for constant variable has to
  be compile-time constant"): literals, constants, operators, `? :`,
  tuples, conversions and the pure builtins (`keccak256`, `sha256`,
  `ripemd160`, `ecrecover`, `addmod`, `mulmod`, `erc7201`).
  `ConstInitsPure r` requires it of every constant. `pureP` returns the
  purity proof (sound by construction); `pureB_iff` and `constInitsB_iff`
  decide them. S01's `WellFormed` accepts `uint256 constant T =
  block.timestamp;` (`timestamp_wellFormed`); G13 refuses it
  (`timestamp_refused`).
- **Named constants, typed.** `TEval`/`NamedConst` are solc 0.8's
  `ConstantEvaluator`: a literal-only expression folds exactly by S01's
  `Syn.const` (so its bounds and refusals apply); a named integer constant
  has its declared type, its initializer's value converted to it
  (`Q.toIntTy?`, solc's `convertType`: out of range is no value, a fraction
  is truncated toward zero); an operation with a typed operand takes solc's
  result type (`ConstOp.resultTy`: the wider of two integer types, an integer
  type and a constant that fits it; the left type for `**` and shifts),
  folds exactly and converts. So `uint256 constant A = 7;` gives
  `A / 2 * 2 = 6` (`typed_division`), and with `uint8 constant C = 255;`,
  `C + 1` has no value (`overflow_length`). `ArrayLenOK` reads array lengths
  through it. `tevalP`/`nconstP` compute the derivations (sound by
  construction); `teval_complete`/`nconst_complete` prove every value is
  found with enough levels; `arrayLenB_sound`.
- **Cycles.** `ConstsAcyclic E`: no constant depends on itself through the
  constants its initializer names (solc: "The value of the constant … has
  a cyclic dependency"). `acyclicB` decides it with `Closure.lean`'s
  saturation (`acyclic_iff`); `cyclic_refused` refuses `A = B + 1;
  B = A + 1`, and `cyclic_noValue` proves, on the relation, that `A` has no
  value at all.

### Conversions and overload selection

Implicit and explicit conversions are S01's (`STy.implicit`,
`STy.explicit`, the fixed-point rows of the second round); `infer` applies
them exactly where S01's rules do, and its completeness covers every
conversion S01 types (`convElem`, `convUser`, `payable`, the implicit
conversions of arithmetic, assignment, return, call and event arguments).
Overload selection is S01's: `Typed.callInternal`, `emit` and `revert E(…)`
require exactly one candidate accepting the argument types **of one
argument typing**. That differs from solc, which refuses a call when two
overloads accept the arguments under any of their typings:
`hexCall_typed` shows `f(0x01)` with `f(uint8)` and `f(bytes1)` getting two
derivations, one per callee, where solc reports "No unique declaration
found after argument-dependent lookup". The checker decides S01's relation
faithfully, deviation included (Handoff). With a decimal `1`, which has no
`bytesN` typing, the call is refused (G12's `ambiguous_refused`).

### User-defined value types (`Solidity/Source/UserOps.lean`, `Solidity/Frontend/Static/UserOps.lean`)

S01 types no operation on a value type. `UdvtTyped Γ u e τ` adds solc's:

- an operator on two operands of type `T` (one for `-`, `~`) calls the
  unique function bound to it by a global file-level `using {f as op} for
  T global;` (`Syn.usingOps`), whose signature is `(T, T) → T` (or `bool`
  for comparisons): `opBindings`;
- `T.wrap(x)` from the underlying type (implicitly converted) to `T`;
  `T.unwrap(x)` back.

`UsingOpsOK` refuses a unit with an ill-formed binding (wrong signature,
not `pure`, not global, not at file level; `usingOpsB_iff`,
`badBinding_refused`), as solc does, so `opBindings`' signature filter
hides no binding of an accepted unit. `udvtRes` returns each type with its
derivation (sound by construction); `udvt_complete` proves completeness
(`udvt_iff`).

### The G05 metadata stage, and which compiler trust it removes

`metadataChecker : Checker Resolution Unit (fun r _ => WellFormed r ∧
InProfileSyntax r)` has the shape of G05's `Chain.metadata`, decided
exactly (`metadataChecker_complete`). It is the syntax and typing component
of G05's metadata stage: the settings and link obligations of
`FrontendSpec.SettingsRespected` (`i.Ok`, `LinksResolved`) stay G15's.
`strictMetadataChecker` adds `StaticOK` (compile-time initializers, acyclic
constants, well-formed operator bindings), which S01's `WellFormed` lacks.

The solc-JSON route reads solc's type metadata and trusts it: each
expression's type (`typeDescriptions.typeString`/`typeIdentifier`,
`Solidity/Frontend/SolcJson/Body.lean:199-206`), each identifier's
declaration (`referencedDeclaration`, `Body.lean:195`), and the common type
of binary operations (`commonType`, `Solidity/Frontend/SolcJson/Admission.lean:274,309,388`).
For a unit given as S00 syntax and inside S01's typed fragment, the
checkers compute all three from source: `infer` derives each expression's
type and resolution (a local by position, a state variable or callee by
declaration, the unique overload), and the binary rules derive the common
type (`STy.common?`). The trust is **removable, not yet removed**: the
solc-JSON route still reads the annotations, nothing in the pipeline calls
`metadataChecker` yet, and units using S01's untyped forms (structs,
`abi.*`, external calls) cannot take the S00 route. Once G15 routes the
frontend through S00 syntax and these checkers, the trusted base for typing
becomes S01's rules (and the parse, G08–G11).

### Controls (`InferExamples.lean`, all by `decide` unless noted)

| Theorem | Statement |
|---|---|
| `counter_checked` | S00's counter is `WellFormed` and in the syntax profile, computed |
| `clashing_checked`, `sameSig_checked`, `ifaceBody_checked`, `twoCtors_checked`, `noVisibility_checked` | S01's five ill-formed units refused by `wellFormedB` |
| `tooBig_checked`, `fits_checked` | `uint8 x = 300;` has no statement derivation; `uint8 x = 255;` has one |
| `shl18_checked`, `gasleft_checked`, `msgValue_checked` | `1 << 8` has only its folded type; `gasleft()` and `msg.value` in a non-payable public body have none |
| `zero_types`, `addLit_types`, `cond_types`, `require_checked` | `0x00` has 33 types; `a + 1` and `b ? a : a` one each; `require(b, "no");` is a statement |
| `named_value`, `named_length` | `N = 3; M = N * 2 + 1` gives `M = 7`; the length expression `M` gives 7 |
| `typed_division`, `overflow_length` | `A = 7`: `A / 2 * 2` is 6; `uint8 C = 255`: `C + 1` is no length |
| `cyclic_refused`, `cyclic_noValue` (by the mutual recursor), `named_acyclic` | `A = B + 1; B = A + 1` refused, and `A` has no value; `N`, `M` acyclic |
| `timestamp_wellFormed`, `timestamp_refused`, `keccak_pure` | `block.timestamp` as a constant passes S01, is refused here; `keccak256("x")` is compile-time |
| `udvt_add`, `udvt_noBinding`, `udvt_wrap`, `udvt_unwrap`, `udvt_bindings_ok`, `badBinding_refused` | `a + b` on `Fixed` with a binding; `a - b` without one has no type; `Fixed.wrap(1)`, `Fixed.unwrap(a)`; the bindings are well formed; binding `add` (returning `Fixed`) to `<` is refused |
| `hexCall_typed` | the recorded overload deviation: `f(0x01)` has two derivations |

### What G13 does not do

- **S01 itself.** The checkers decide S01's relations as they stand,
  including their recorded gaps ("What S01 does not do": data locations of
  parameters, `abi.*`, structs, external calls, named arguments, a second
  declaration of a name in one block) and the overload deviation above.
  New rules lane-semantics adds to `Typed`/`StmtD` need matching cases in
  `infer`/`inferS`; their completeness proofs then fail to elaborate until
  the cases are added, which is the intended signal.
- **Integration into S01.** `ConstInitsPure`, `ConstsAcyclic`,
  `ArrayLenOK`, `UdvtTyped` and `UsingOpsOK` are separate relations: S01's
  `WellFormed`, `Syn.tys` and `Typed` do not read them (Handoff). So S01
  still refuses `uint256[M] a;`, and a value-type operation is typed only by
  `UdvtTyped`, not inside larger S01 expressions.
- **UDVT composition.** `UdvtTyped`'s operands are typed by S01's
  `HasType`, so `a + b + c`, `-(a + b)` and `Fixed.unwrap(Fixed.wrap(1))`
  have no type here (solc accepts them); it composes once S01's `Typed`
  reads `UdvtTyped` (Handoff). `T` defined in the same file and the
  function's purity are checked by `UsingOpsOK`; the same-file rule is not.
- **Constants.** A rational base with a typed exponent or shift amount
  (`2 ** A`) and non-integer named constants have no value here; solc gives
  the former the base's mobile type. Purity of member and index accesses
  (`type(T).max`, `"abc".length`) is not modelled. That
  `E.decls.length + 1` levels of named constants suffice for every acyclic
  definition is not proved (completeness is with enough levels), and
  `arrayLenB` has soundness only.
- **Speed.** `infer` enumerates every derivation: an expression's result
  list is the product of its operands' type lists filtered by the rules. A
  literal has up to 33 types, so a call with several `0x00` arguments
  enumerates up to 33 to the power of their number. The checker is never
  kernel hot code; elaboration times are in the Handoff.

### Gates (G13)

Recorded in [Handoff (G13)](#handoff-g13).

### Review (G13)

A read-only finder and a separate skeptic (neither using the Lean server)
reviewed the first G13 revision.

Fixed:

| Finding | Fix |
|---|---|
| named constants folded over rationals, ignoring declared types: `A / 2 * 2` gave 7, `uint8 C = 255; C + 1` accepted (both) | `TEval`/`NamedConst` follow solc's `ConstantEvaluator` (types, `convertType`); `typed_division`, `overflow_length` |
| cyclic constants accepted by every check (finder) | `ConstsAcyclic`, `acyclic_iff`, `cyclic_refused`; in `strictMetadataChecker` |
| `cyclic_none` showed only the checker's verdict at one level bound (both) | `cyclic_noValue` on the relation, by the mutual recursor |
| "an ambiguous call has no type" false: `f(0x01)` with `f(uint8)`/`f(bytes1)` (skeptic) | the claim corrected; `hexCall_typed` records S01's per-typing uniqueness as a deviation (two derivations, two callees); Handoff to lane-semantics |
| wrong-signature, non-global bindings silently filtered (finder) | `UsingOpsOK`, `usingOpsB_iff`, `badBinding_refused` |
| `erc7201` missing from the pure builtins (finder, unconfirmed against solc) | added, following `docs/solidity-scope.md`'s compile-time folding of `erc7201` |
| trust removal read as done; `InProfileSyntax` weaker than G05's `InProfile` (skeptic) | the trust paragraph and `Certificates.lean` say "removable", and name the metadata checker the syntax and typing component |
| `HasType ↔ τ ∈ inferTys` cited but not stated (finder) | `hasType_iff` |
| array lengths "closed", no completeness (both); `named_length` docstring named a contract that was not there (finder) | wording: a relation and a sound checker, S01 not yet reading it; the docstring fixed |
| UDVT non-compositional, unrecorded (both) | recorded under What G13 does not do |

Recorded, not fixed: S01 integration of the new relations, UDVT
composition, `2 ** A`, purity of member and index accesses, the level
bound, `arrayLenB` completeness, enumeration cost (all above).

### Handoff (G13)

**Revision**: the G13 commit on `cloud/roadmap-l2-20261029/lane-static`.

**Theorems**: `typed_complete`, `lval_complete`, `args_complete`,
`slots_complete`, `hasType_iff` (InferComplete); `stmt_complete`,
`items_complete`, `stmtOK_iff`, `itemsOK_iff` (InferStmtComplete);
`wellFormed_iff`, `inProfileSyntaxB_iff` (WellFormedCheck); `pureB_iff`,
`constInitsB_iff`, `teval_complete`, `nconst_complete`, `evalConst_sound`,
`arrayLenB_sound`, `acyclic_iff` (Consts); `udvt_iff`, `usingOpsB_iff`
(UserOps); `metadataChecker_complete` (Certificates); controls as above.
All on the standard axioms (`pureB_iff` on none), pinned in
`InferExamples.lean`/`Certificates.lean` and listed in `TrustAudit.lean`'s
G13 block.

**Premises**: none; no `sorry`, axiom, `native_decide`, `implemented_by`
or heartbeat option.

**Checks**: `lean_diagnostic_messages` clean on every new file;
`node scripts/check-g07.mjs`: 0 new failures. The full build runs at the
end of the lane.

**For lane-semantics (existing `Solidity/Source/` files)**:

- `Typing.lean`, overloads: S01's per-typing uniqueness gives `f(0x01)`
  two derivations with different callees (`hexCall_typed`); solc requires a
  unique overload across all argument typings. Either `callInternal`
  (and `emit`, `revertError`) should require the candidate set over every
  typing of the arguments to be a singleton, or derivations need a
  canonical choice; S02's meaning depends on it.
- `Typing.lean`: read `UdvtTyped` (operators, `wrap`, `unwrap`) as
  `Typed` rules so they compose; `Syn.tys`'s `arrayLen` should read
  `ArrayLenOK` (named constants, solc's typed evaluation).
- `WellFormed.lean`: add `ConstInitsPure`, `ConstsAcyclic` and
  `UsingOpsOK` (`StaticOK`) as fields.
- Any new `Typed`/`StmtD` rule needs a case in `infer`/`inferS`
  (`Solidity/Frontend/Static/Infer.lean`, `InferStmt.lean`) and in their
  completeness proofs.

**For G15**: `metadataChecker`/`strictMetadataChecker` are the typing part
of `Chain.metadata`; the settings and links part (`SettingsRespected`)
remains. Relating solc's `typeDescriptions`/`referencedDeclaration` to
`infer`'s derivations for an imported unit is the check that would retire
that trust on the solc-JSON route.

## G14: inheritance, overrides, constructors, modifiers, `using for`

### The relations (`Solidity/Source/Inheritance.lean`)

S01 linearizes contracts (`Env.linearize`, C3) and checks none of solc's
contract-level rules ("What S01 does not do"). `InheritanceOK r` states
them for one unit, each field named by the solc error it is:

- **Linearization** (`linearizes`): every contract linearizes. Every other
  relation reads `Env.chain`, which falls back to `[c]` when C3 fails, so
  without this field an inconsistent hierarchy would pass vacuously.
- **Base functions.** `Env.baseFns E c d`: for each direct base `B` of the
  contract `c` declaring `d`, the most derived function of `B`'s
  linearization with `d`'s name and parameter types up to data locations
  (`Decl.sameSig`, `STy.sameUpToLoc`: a `memory` parameter overrides a
  `calldata` one), not `private`, one per declaring contract
  (`dedupScope`).
- **Overrides** (`FnOverrideOK`, `OverridesOK`): `override` when there
  are base functions, unless the only one is an interface function (9456,
  solc 0.8.8's exemption, `Env.singleIface`), and not without (7792);
  every base function `virtual`, interface functions implicitly (4334);
  with two or more base contracts the `override(…)` list names each
  (4327), names only them (2353) and names none twice (4520); visibility
  kept or `external` to `public` (9098); mutability only stricter (6959,
  `mutOK`); return types kept up to locations (4822); an implemented base
  function is not overridden by an unimplemented one (4593).
- **Required overrides** (`MustOverride`, 6480): if the direct bases'
  most derived versions of one signature come from two or more contracts,
  the contract declares it.
- **Implementations** (`ImplOK`): a function without body outside an
  interface is `virtual` (5424); a non-abstract contract's most derived
  version of each function it has is implemented (3656).
- **`virtual` declarations** (`VirtualDeclOK`): not `private` (3942), not
  in a library (7801).
- **Base constructors** (`CtorArgsOK`): for each base in the linearization
  whose constructor has parameters, arguments are given at most once along
  the linearization, in `is` specifiers or constructor modifier lists
  (3364), exactly once unless the contract is abstract (3415), and with the
  constructor's parameter count where the contract gives them (7927, 2973).
- **Modifier invocation resolution** (`ModInvOK`, 4659, 2973, 1563): an
  invocation names a modifier visible from the declaration (S01's lookup)
  with matching argument count (none without parentheses, `invCount`), or,
  in a constructor, a base contract, with parentheses (1563). Binding a
  `virtual` modifier to its most derived override is not done.
- **`using L for T`** (`UsingLibOK`, 4357): `L` names a library. Attached
  functions (`using {f, g} for T`, `for *`) are not resolved.
- **Constructor order** (`Env.ctorOrder`): the linearization reversed.
- **Callable identity** (`CallableId`): a function is identified by its
  contract, name and parameter types (S01's location-sensitive
  `sameParams`).
- **C3** (`C3Lin`): see below.

Except for `C3Lin`, the relations are stated over the same computed helpers
their checkers use (`Env.baseFns`, `Env.inheritedVersion`, `dedupScope`,
`Env.argsFor`, `Env.chain`). The `*_iff` theorems therefore prove that the
checkers decide them, not agreement with an independent specification; the
relations' fidelity to solc rests on their text (each field cites its solc
error) and on the solc samples below.

### The checkers (`Solidity/Frontend/Static/Inheritance.lean`, `Solidity/Frontend/Static/C3.lean`)

Each relation has a Boolean checker proved to decide it exactly:
`fnOverrideB_iff`, `overridesB_iff`, `mustOverrideB_iff`, `implB_iff`,
`virtualDeclB_iff`, `ctorArgsB_iff`, `modInvsB_iff`, `usingLibB_iff`, and
`inheritance_iff` for the whole judgment. `inheritanceChecker` is the G05
`Checker` value, with `inheritanceChecker_complete` (`Certificates.lean`).

**Callable identity** (`callable_unique`): in an S01-`WellFormed` unit, two
named functions (`d.name ≠ ""`, which excludes S01's unnamed declarations)
with one identity are one declaration (same position). The proof restates
S01's no-clash field for this key; identity across contracts (an inherited
function's identity in the inheriting contract), which G20's lowering will
need, is not stated.

**C3.** `C3Lin E c L` specifies a C3-consistent linearization
declaratively: `L = c :: M`, `M` duplicate-free, holding *some*
C3-consistent linearization of each base (an existential witness, not
`Env.chain b`) and the direct bases (most derived first) as ordered
sublists, and nothing else. It omits C3's leftmost-head choice, so several
`L` can satisfy it (`X is P, Q`, `P is A`, `Q is B` admits `X, Q, P, A, B`
as well as C3's `X, Q, B, P, A`), and it does not state `c ∉ M`.
`linearize_sound`: S01's `Env.linearize` returns only such
linearizations; behind it, the merge laws `merge_sub`, `merge_nodup`,
`merge_sublist`. `ctorOrder_spec`: the constructor order is the reversed
linearization (by definition), ends with the contract, and runs every
direct base before it; it says nothing about indirect bases' relative
order.

### Cross-check with solc (`Solidity/Frontend/Static/InheritanceExamples.lean`, all by `decide`)

Each control transcribes a test of the pinned solc 0.8.38 test tree
(`tests/upstream/solidity-0.8.38.tar.gz`, under
`test/libsolidity/syntaxTests/`) as S00 syntax (bodies emptied, state
variables dropped; they do not bear on these checks), and the checker's
verdict equals the test's expectation block. Paths below are under
`inheritance/` unless they start with `nameAndTypeResolution/`.

| Theorem | Upstream test (dropped parts) | solc's verdict |
|---|---|---|
| `missingVirtual_refused` | `override/override_missing_virtual.sol` | 9456 (`test`), 4334 (`test2`): both functions fail |
| `override_ok` | `override/override.sol` | accepted |
| `lessStrict_refused` | `override/override_less_strict_mutability.sol` | 6959 on `C`, `D`, `F`; `B`, `E` pass |
| `stricter_ok` | `override/override_stricter_mutability.sol` (`A`, `B` only) | accepted |
| `noCommonBase_refused` | `override/no_common_base_and_unique_implementation.sol` | 6480 |
| `sharedBase_ok` | `override/override_shared_base_simple.sol` | accepted |
| `sharedBase_override_ok` | `override/override_shared_base.sol` | accepted |
| `sharedBase_unlisted_refused` | not upstream: the previous test with `override` and no list | 4327 (solc's rule) |
| `externalPublic_ok` | `override/external_turns_public_no_params.sol` | accepted |
| `dupList_refused`, `dupListFixed_ok` | `override/override_multiple_duplicated.sol`; the same deduplicated | 4520 on both functions; accepted |
| `calldataMemory_ok` | `override/calldata_memory.sol` (`dummy` dropped); negative: `uint8[]` in `B` | accepted; 7792 |
| `overridesSingle_ok` | `interface/overrides_single.sol`; negative: the bases as abstract contracts | accepted; 9456 |
| `implThenUnimpl_refused` | `override/override_implemented_with_unimplemented_then_implemented.sol` | 4593 on `B`, `C` passes |
| `virtualDecl_refused` | `override/virtual_private.sol`, `virtual/library_err.sol`; the library without `virtual` | 3942, 7801; accepted |
| `unimplementedNonVirtual_refused` | `unimplemented_without_virtual.sol` | 5424 |
| `abstractNeeded_refused` | `nameAndTypeResolution/029_create_abstract_contract.sol` (`base` only) | 3656 |
| `argsTwice_refused` | `duplicatedConstructorCall/base.sol` | 3364 |
| `argsTwice_paths_refused` | `duplicatedConstructorCall/{ancestor,base_multi,base_multi_no_constructor,base_multi_no_constructor_modifier_style}.sol` | 3364 (each) |
| `argsMissing_refused` | `nameAndTypeResolution/061_missing_base_constructor_arguments.sol` | 3415 |
| `argsCount_refused` | `too_few_base_arguments.sol` | 7927 (`Derived`), 2973 (`Derived2`) |
| `nonBaseCtor_refused` | `reference_non_base_ctor.sol` | 4659 |
| `modStyleBare_refused` | `disallow_modifier_style_without_parentheses.sol`; with `A()` | 1563; accepted |
| `modArgs_count` | not upstream: `modifier m(uint)` invoked as `m`, `m(1, 2)`, `m(1)` | 2973, 2973, accepted (solc's rule) |
| `ctorModifiers_ok` | `modifiers_in_constructor_context.sol` | accepted |
| `usingNotLibrary_refused` | `nameAndTypeResolution/252_using_for_not_library.sol` | 4357 |
| `diamond_c3`, `diamond_ctorOrder` | not upstream: S01's diamond `D is B, C` | `D, C, B, A`, C3-consistent; constructors `A, B, C, D` |

The transcriptions are by hand: no parser connects these files to S00
syntax yet (G08–G11), so the cross-check covers the cases listed, not the
directories.

### What G14 does not do

- **solc's override-graph pruning for 6480.** `checkAmbiguousOverridesInternal`
  removes, at each cut vertex of the override graph, the functions it
  overrides and an unimplemented cut-vertex function before requiring a
  declaration. `MustOverride` does not, so it refuses programs solc
  accepts: `override/triangle_no_impl.sol`,
  `override/common_base_and_unique_mention.sol`,
  `override/nonintermediate_common_base_and_unique_implementation.sol` (and
  its `_unimplemented` variant), `override/correct_choice_for_base_function.sol`.
  The rule is conservative (it refuses more), not unsound for S02.
- **Every base function reachable through a base.** `baseFns` keeps the
  most derived function of each direct base's linearization; solc keeps
  every not-yet-overridden function reachable through it. So
  `override/interface_and_base_override_fine.sol` (`override(IBase, Base)`
  where `Base` implements `IBase`) is refused (2353), and
  `override/interface_and_base_override_err.sol` is refused through 9456
  rather than solc's 4327.
- **Base-constructor arguments in detail.** `CtorArgsOK.once` considers
  only bases whose constructor has parameters; solc also reports 3364 for
  duplicate modifier-style calls of a parameterless constructor. `is A()`
  with empty parentheses counts as given here; solc ignores it.
- **Several units.** The relations read one unit's environment, like S01;
  a base imported from another unit is resolved by G12 but not linearized
  here (Handoff).
- **Public state variables** that implement or override functions
  (`implement_*_by_public_variable.sol`, `override_public_vars.sol`):
  getters are not functions here, so they neither override nor hide.
- **Fallback and receive** are not override-checked (`Env.ownFns` keeps
  only functions): `fallbackReceive/fallback_without_override.sol` (9456)
  is accepted.
- **Modifiers.** Modifier overriding (`virtual`/`override` on modifiers,
  `modifier_ambiguous*.sol`) and binding a `virtual` modifier to its most
  derived override are not checked; only invocations are resolved.
- **Override lists** are matched by each path's last component, so two
  qualified names with one last component are not told apart; the
  `interfaceException/` cases, `super` calls, and diagnostics' order and
  multiplicity are not modelled (a refusal is one verdict).
- **C3 completeness**: `linearize_sound` shows S01's result is consistent;
  that C3 fails only when solc reports "Linearization of inheritance graph
  impossible" is solc's definition, not a theorem here.
- **Library calls.** `UsingLibOK` checks that attached names are
  libraries; resolving `x.f()` to a library function (by its first
  parameter type) is not typed by S01 and is left with external calls
  (lane-semantics).

### Gates (G14)

Recorded in [Handoff (G14)](#handoff-g14).

### Review (G14)

Finder and skeptic reviews, read-only and without the Lean server, over
the pre-review commit. Confirmed and fixed:

| Finding | Source | Fix |
|---|---|---|
| Modifier with parameters invoked without parentheses, and modifier-style base call without parentheses, accepted (2973, 1563) | both | `invCount`; base disjunct requires parentheses; `modArgs_count`, `modStyleBare_refused` |
| Duplicate `override(…)` entries accepted (4520) | both | `FnOverrideOK.distinct`; `dupList_refused` |
| `InheritanceOK` passes non-linearizable hierarchies vacuously | skeptic | `linearizes` field |
| `calldata`/`memory` parameters do not override each other | finder | `Decl.sameSig` (`STy.sameUpToLoc`); `calldataMemory_ok` |
| solc 0.8.8's single-interface exemption from `override` missing | finder | `Env.singleIface`; `overridesSingle_ok` |
| 4593, 3942, 7801 have no field | finder | `keepsBody`, `VirtualDeclOK`; `implThenUnimpl_refused`, `virtualDecl_refused` |
| `C3Lin` (a relation) in a Frontend file | skeptic | moved to `Solidity/Source/Inheritance.lean` |
| No `inheritanceChecker_complete` | skeptic | added and pinned |
| `*_iff` theorems decide relations stated over the same helpers; not said | skeptic | stated in the module docstring and above |
| Modifier binding, `using for` and callable identity over-claimed; `C3Lin` existential witnesses, non-uniqueness and `c ∉ M`; `ctorOrder_spec`'s content; `callable_unique`'s `d.name ≠ ""` | both | wording above |
| Imprecise citations (`duplicatedConstructorCall/`, dropped contracts) and uncovered 3364/2973 cases | both | exact files, dropped parts listed; `argsTwice_paths_refused`, `Derived2`, full `lessStrict` |
| Fallback/receive, 6480 pruning, reachable base functions, `CtorArgsOK` details, last-component override matching unlisted | both | listed under "What G14 does not do" |

### Handoff (G14)

**Revision**: the G14 commit on `cloud/roadmap-l2-20261029/lane-static`.

**Theorems**: `fnOverrideB_iff`, `overridesB_iff`, `mustOverrideB_iff`,
`implB_iff`, `virtualDeclB_iff`, `ctorArgsB_iff`, `modInvsB_iff`,
`usingLibB_iff`, `inheritance_iff`, `callable_unique` (Inheritance);
`merge_sub`, `merge_nodup`, `merge_sublist`, `linearize_sound`,
`ctorOrder_spec` (C3); `inheritanceChecker_complete` (Certificates); the
controls above. All on the standard axioms, pinned in
`InheritanceExamples.lean`/`Certificates.lean` and listed in
`TrustAudit.lean`'s two G14 blocks.

**Premises**: none; no `sorry`, axiom, `native_decide`, `implemented_by`
or heartbeat option.

**Checks**: `lean_diagnostic_messages` clean on every new file;
`node scripts/check-g07.mjs`: 0 new failures. Elaboration (full build of the pre-review
commit): `InheritanceExamples.lean` 8.4 s, `Certificates.lean` 4.0 s.

**For lane-semantics (existing `Solidity/Source/` files)**:

- `WellFormed.lean`: S01 accepts every program `InheritanceOK` refuses;
  adding `InheritanceOK` (or its fields) to `WellFormed` would let S02
  assume overrides, implementations and constructor arguments are
  consistent. Nothing in S01/S02 reads it yet.
- `Typing.lean`: a call through `super`, a call of an inherited function
  and a library call `x.f()` need typing rules; their callee should be the
  `Env.baseFns`/`finalVersion` choice here, so the meaning dispatches as
  solc does.
- Modifiers: S01 has no modifier semantics; binding a `virtual` modifier
  to its most derived override (`finalVersion` over modifiers) is the
  missing piece.

**For later groups**:

- Several units: linearize over G12's `Program` (identities `DeclId`)
  instead of one unit's `Env`, so a base imported from another unit is
  checked.
- Getters: a public state variable should count as an external function
  for `baseFns`/`MustOverride` (`override_public_vars.sol`).
- G20 (callable lowering) needs identity across contracts: an inherited
  function's identity in each inheriting contract and its dispatch target.

**For G15**: `inheritanceChecker` is the contract-level part of the
admission check; on the solc-JSON route, solc's `linearizedBaseContracts`,
`baseFunctions` and `overrides` annotations can be compared with
`Env.chain` and `Env.baseFns` instead of trusted.

## Backfill item 5: fixed-point mobile constants

The decision (`docs/coverage-plan.md`, backfill queue, item 5; question QL2
of `docs/feature-work/fixed-point-semantics.md`): a standalone fractional
constant takes solc's mobile type with truncation, also as an ABI argument.

### The reference semantics (`Solidity/Language/FixedPoint/Literals.lean`)

- `Fx.mobileConst? q`: the mobile type `mobileFx? q` (solc's
  `RationalNumberType::fixedPointType`) and the constant truncated toward
  zero at its digits; `none` without a mobile type.
  - `Fx.mobileConst?_eq`, `Fx.mobileConst?_eq_none`: its two cases.
  - `Fx.mobileConst?_explicit`: the value is the explicit conversion to the
    mobile type; `Fx.mobileConst?_trunc`: toward zero, within one unit of
    the last digit.
  - `Fx.mobileConst?_exact`: where the constant converts implicitly to its
    mobile type (its digits suffice), the value is that conversion.
- `Fx.abiConst? q`: a fractional ABI argument is the word encoding of that
  value (`abi.encode(0.1)` is `abi.encode(ufixed8x1(0.1))`). solc 0.8.38
  refuses it (6090, `types/encoding_fractional.sol`); this is an intended
  deviation, recorded in the fixed-point document's conformance table.
  `Fx.abiConst?_decode`: one word, decoding at the mobile type to the
  value; `Fx.abiConst?_eq_none`: no mobile type, no encoding.
- Worked values (by `decide +kernel`): `1/3` at `ufixed256x77` holds
  `(10^77 − 1)/3`; `0.1` at `ufixed8x1` holds `1`; `-0.5` at `fixed8x1`
  holds `-5`; `2^256 + 0.5` has none. Encodings: `0.1` is the word `1`,
  `-0.5` the word `2^256 − 5` (31 bytes `0xff`, then `0xfb`), `2^256 + 0.5`
  is refused. Negative: `3 · v ≠ 10^77` for `1/3`; `0.1` is not the zero
  word.

### The G13 rule (`Solidity/Frontend/Static/Standalone.lean`)

S01 types a constant by its exact rational, and its `STy.mobile` leaves a
fractional one rational (a type no value has).

- `STy.standalone`: S01's mobile type, except that a fractional constant
  with a mobile fixed-point type takes it (`FxTy.toFixTy`: S01's `FixTy`
  has `FxTy`'s fields; `Q.toRat` reads S01's rational as a `Rat`).
- Relations over S01's `HasType`: `StandaloneTyped Γ e τ` (`e : σ` and
  `σ.standalone = τ`) and `AbiArgTyped`, only the constant-type restriction
  on ABI arguments (not a constant-only type, `STy.isConstTy`); solc's other
  restrictions on `abi.encode` arguments (mappings, internal function
  types, storage references, tuples) are not in it.
- Checkers over G13's inference: `standaloneTys`, `abiArgTys`;
  `standalone_iff`, `abiArg_iff` show they decide these relations (from
  `hasType_iff`). The rule is a map over inferred types: no S01 rule
  consumes it yet.
- Values: `standalone_value` (a constant standing at `.fixed f` is
  fractional, and `Fx.mobileConst?` gives its value at a type `m` with
  `f`'s fields; it unfolds `STy.standalone`); `standalone_toFixedExplicit`
  (S01's own explicit conversion `Q.toFixedExplicit?` to `f` is that value,
  for S01's unreduced rational); `standalone_abi` (end to end: S01's value
  at `f` and the ABI word `Fx.abiConst?`).
- Controls (`InferExamples.lean`): `oneThird_standalone` (`1 / 3` stands at
  `ufixed256x77` exactly, is an ABI argument, and S01's own `STy.mobile`
  leaves it rational); `tooBigFrac_refused` (`2**256 + 1/2` has no
  standalone fixed-point type and is no ABI argument, nor is `2**256`; `5`
  stands at `uint8`); `unreduced_standalone` (`4 / 2` at `uint8`, `2 / 6`
  at `ufixed256x77`); `oneThird_value`. In Literals: wrong words for `0.1`
  (`10`, and its `ufixed256x77` word) are refused.

### What backfill item 5 does not do

- **Positions inside S01's types.** The rule applies to a whole
  expression (an ABI argument, an inline-array element). S01's tuple and
  conditional rules still take `STy.mobile`, so `(1/3, 2)` keeps a rational
  component and `c ? 0.5 : 0.25` meets at a rational common type, if any;
  `STy.standalone` does not recurse into tuples.
- **Inline arrays, `abi.encode` calls.** S01 types neither; the rule is
  stated for their arguments, not for the calls (lane-semantics is adding
  `abi.*`).
- **Packed encoding** (`abi.encodePacked(0.1)`): not stated; the reference
  semantics has `Fx.encodePacked` at a type, so it is `Fx.encodePacked` at
  the mobile type when wanted.

### Gates (backfill item 5)

Recorded in [Handoff (backfill item 5)](#handoff-backfill-item-5).

### Review (backfill item 5)

Finder and skeptic reviews, read-only and without the Lean server, over
the pre-review commit. Checked and confirmed: `STy.standalone` agrees with
solc's `mobileType` (integral constants through S01's `Q.mobileInt?`, `Q.isInt`
correct on unreduced rationals, `Q.toRat` normalizes); the `-0.5` word;
the 6090 deviation stated consistently. Fixed:

| Finding | Source | Fix |
|---|---|---|
| `standalone_value` only restates `Fx.mobileConst?_eq`; no link to S01's value | skeptic | `standalone_toFixedExplicit` (S01's `Q.toFixedExplicit?`), `standalone_abi` |
| No theorem from an ABI argument's type to its bytes | finder | `standalone_abi` |
| Literals header names tuple components and conditional branches as positions, which S01 does not adopt; "four ways" over five bullets | both | header qualified, "five ways" |
| `AbiArgTyped` read as full ABI-argument typing | both | docstrings and the text above: the constant-type restriction only |
| `mobileConst?` silent on integral input | finder | docstring: `q` fractional |
| Conformance summary: count not updated; the packed files called deviations though solc also refuses them with 7279 | skeptic | 5 deviating files; the packed files "not decided" |
| `[1/3]` row said "The same" though S01 has no inline arrays | skeptic | qualified |
| Controls: `5` checked only "not fixed"; no unreduced constants; a weak wrong-word control; no `2**256` ABI refusal | both | `tooBigFrac_refused` (`uint8`, `2**256`), `unreduced_standalone`, wrong words `10` and the `ufixed256x77` word |
| Queue entry not marked done | skeptic | marked |

Recorded, not changed: `docs/coverage-plan.md`'s precompiles paragraph
calls the stipend cost rule "backfill item 5", but the queue numbers it 6
(another lane's line).

### Handoff (backfill item 5)

**Revision**: the backfill commit on `cloud/roadmap-l2-20261029/lane-static`.

**Theorems**: `Fx.mobileConst?_eq`, `Fx.mobileConst?_eq_none`,
`Fx.mobileConst?_explicit`, `Fx.mobileConst?_trunc`,
`Fx.mobileConst?_exact`, `Fx.abiConst?_eq`, `Fx.abiConst?_decode`,
`Fx.abiConst?_eq_none` (Literals); `standalone_iff`, `abiArg_iff`,
`standalone_value`, `standalone_toFixedExplicit`, `standalone_abi`
(Standalone); `oneThird_standalone`, `tooBigFrac_refused`,
`unreduced_standalone`, `oneThird_value` (InferExamples). All on the
standard axioms, pinned, listed in `TrustAudit.lean`'s two backfill blocks.

**Premises**: none; no `sorry`, axiom, `native_decide`, `implemented_by`
or heartbeat option. `decide +kernel` evaluates the 77-digit values.

**For lane-semantics**: S01's tuple and conditional rules (`Typing.lean`)
should take `STy.standalone` instead of `STy.mobile`, inline arrays and
`abi.encode` should type their elements and arguments by it (`AbiArgTyped`
plus solc's other argument restrictions), and S02's meaning of a
standalone constant is `Fx.mobileConst?`'s value
(`standalone_toFixedExplicit`: S01's explicit conversion to that type).

**For G15**: a fractional `abi.encode` argument compiles here but not with
solc 0.8.38 (6090), so the solc-JSON route cannot certify such a program;
G15's classification should mark it as outside solc's accepted set.
