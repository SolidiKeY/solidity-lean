# Roadmap G05 — frontend, provenance and checked certificate interfaces

Base revision `caf52ecd4dde5d37cbc0098d47de1a01aa218285` (2026-10-29). G05
in [coverage-plan.md](../coverage-plan.md): "Audit current frontend/provenance/unsafe
elaborator paths and define checked certificate interfaces for raw source,
parsed syntax and resolved metadata. Digests prove identity only."

Deliverables: this document and the statements-only module
`Solidity/Roadmap/Frontend.lean`. No frontend code changed. Every claim about
the code is about the base revision; `Solidity/Frontend/**` is edited by
in-flight lanes. The user decisions followed are the table in
[solidity-scope.md](../solidity-scope.md#user-decisions-2026-10-29): G00 Q3 (Osaka),
Q4 (all eight `EvalOrder` combinations, solc 0.8.38 profile, 0.8.34 SolKey
only), Q5 (code constants from this compiler's artifact table), G01 Q3
(per-run hash premise) and Q8 (linked libraries are part of the compiled system).

## 1. Audit: what admits source and what each path trusts

### 1.1 The pipeline as it runs

`solc_import "f.ast.json" hash 0x… as N` (`Solidity.Frontend.elabSolcImport`,
`Solidity/Frontend/Import.lean:638`) runs at elaboration time:

1. **External analysis** (not Lean). `scripts/solc-ast.mjs` or
   `scripts/solc-unit.mjs` checks the SHA-256 of a soljson binary against two
   pins (`scripts/solc-ast.mjs:126-145`), runs `--standard-json` with
   `outputSelection` AST only, trims the AST and writes a fixture with a
   header (`solcVersion`, `sourceSha256`, `compilerSha256`, `settings`,
   `acceptedPragmas`). The source text is **not** in the fixture; only its
   SHA-256, computed by Node. Parsing, name resolution and type checking are
   solc's; nothing in Lean repeats them.
2. **Fixture identity.** The command reads the file (`IO.FS.readBinFile`,
   `Import.lean:649`), recomputes FNV-1a 64 (`Solidity.Frontend.fnv1a64`,
   `:140`) and refuses another value than the literal. Purpose: Lake does not
   track the data file, so the hash literal forces re-checking. FNV-1a is
   not collision resistant; it is a staleness check, not authentication.
3. **Provenance reading** (`Solidity.Frontend.Source.read`,
   `Solidity/Frontend/Source.lean:203`; `readCompilationUnit`,
   `Solidity/Frontend/SourceUnits.lean:63`). Checks JSON shape, compares
   `solcVersion` with the two pins (`parseCompiler`, `:154`), compares the
   *recorded* `compilerSha256` string with the pinned constant, checks that
   `sourceSha256` is 64 hex digits (`digest`, never recomputed: Lean never
   sees the source bytes), validates settings (`validateSettings`, `:169`),
   compares the recorded pragmas with the AST's, and for schema 2 checks
   source locations and import targets by compiler identity (`checkTree`,
   `SourceUnits.lean:31`).
4. **Feature scan** (`Solidity.Frontend.Admission.scan`,
   `Solidity/Frontend/SolcJson/Admission.lean:418`). Produces a `ScopeScan`;
   `ScopeScan.within` (`Source.lean:299`) proves, in the kernel, that an
   admitted scan's *reported* feature list is `WithinProfile`. Completeness
   of the extraction (every feature used is reported) is not proved.
5. **Reading and printing** (`SolcJson/{Contract,Body,Getters}.lean`). Bodies
   are printed as `sol` text, re-parsed by Lean's parser
   (`Parser.runParserCategory`) and expanded by the `sol_raw!` macros to
   `List RawStmt` terms. No relation between the JSON and the printed text is
   stated.
6. **Evaluation in compiled code.** The contract and all bodies are evaluated
   at once (`unsafe evalExpr (Contract × List (List RawStmt))`,
   `Import.lean:779`); the typed elaborator `elabProgAtS.go` (`:802`) runs as
   compiled code, with the compiled-only memos `CallMemo.bodyImpl?`
   (`Solidity/Syntax/Elab/Values.lean:567`, an `unsafeCast` checked by
   pointer equality), `QMemo.findImpl` (`Solidity/Syntax/Quote.lean:291`)
   and `RecThunk.get` (`opaque` with `implemented_by`,
   `Solidity/Syntax/Elab/Context.lean:1330`).
7. **Kernel re-check of the output.** `Prog.define`
   (`Solidity/Syntax/Quote.lean:501`) quotes the typed program
   (`Prog.quoteShared`) and adds it with `addDecl`, so the kernel checks
   `N.f : Prog N Γ Γ'`: intrinsic typing of the result (scoping, types,
   storage well-formedness via `Contract`'s proof fields). The contract
   itself is defined through `defineImportedContract` (`Import.lean:239`)
   with an `Eq.refl` certificate that the segmented table equals the
   original, and `N.report` likewise.

So the kernel checks that the output is *some* well-typed intrinsic program;
it checks nothing relating that program to the source text, to solc's AST, or
to a source grammar or static semantics. The compiled elaborator, the Lean
parser and macro expansion, the JSON reader and the external solc run are all
trusted for *which* program is produced.

### 1.2 Path inventory

Source: `bash scripts/check-trust.sh` at the base (`trust: 748 sources, 241
inventoried implementation/recovery sites, 0 findings`) and
`tests/trust-inventory.json`, restricted to paths that admit or transform
source.

| Path | Trust site (`check-trust` kind) | What it trusts | Digest only | Kernel-checked |
|---|---|---|---|---|
| `scripts/solc-ast.mjs`, `scripts/solc-unit.mjs`, `scripts/solc-code.mjs` | outside Lean | soljson 0.8.34/0.8.38 binaries (SHA-256 checked by Node), Node, the trimming code | `sourceSha256`, `compilerSha256` written by Node | nothing |
| `Solidity/Frontend/Import.lean` `elabSolcImport` | `unsafe evalExpr` ×2 (`:670` evaluation order, `:779` contract and bodies), `unsafe evalConst`/`evalExpr` in `#solc_show` (`:881`, `:885`) | compiled elaborator, Lean parser and macros, JSON reader | fixture FNV-1a 64 (recomputed); `sourceSha256`/`compilerSha256` recorded strings, compared with constants only | typing of each `N.f`, `N.constructor`; `_inputEq` reflexivity certificates of the contract and the report |
| `Solidity/Frontend/Source.lean` (`read`, `validateSettings`, `readCompilerCode`) | none (`import Lean`, ordinary defs) | JSON reader; the recorded header | as above; `compilerCode` hashes compared with the provenance strings | `ScopeScan.within` for the reported features only |
| `Solidity/Frontend/SourceUnits.lean` | none | that solc's ids and `absolutePath`s are the source's | per-unit `sourceSha256` recorded | nothing |
| `Solidity/Frontend/SolcJson/**` | none | the reader's classification and printing | — | nothing (a body that does not print/parse is a row) |
| `Solidity/Frontend/WorldImport.lean` (`solc_world_factory`, `solc_world_library`) | `unsafe evalConst` (`:264`) | as `solc_import`, plus the fragment recognizers (`WorldLinked.read`, `:310`) | FNV-1a 64 | the generated world definitions, by elaboration of the emitted commands |
| `Solidity/Frontend/Problems.lean`, `Cli.lean`, `Testing.lean` | `unsafe evalExpr`/`evalConst` (4, 3, 1) | they read already imported constants (`N.report`, `Contract`, `Fml`) | — | the stated obligations `N.f.problem`; proofs `N.f.proved` when they exist |
| `Solidity/Syntax/Splice.lean` `elabAgainstWith` (`sol[C]{ … }`) | `unsafe evalExpr` (`:103`) | compiled elaborator | — | typing of the quoted result |
| `Solidity/Syntax/Elab/Values.lean` `CallMemo` | `unsafe` ×2, `implemented_by` ×2 | pointer-equality memo; logically `none` | — | the reference implementation is the logical one; the output is re-checked |
| `Solidity/Syntax/Quote.lean` `QMemo` | `unsafe` ×2, `implemented_by` ×2 | pointer-equality memo | — | output re-checked |
| `Solidity/Syntax/Elab/Context.lean` `RecThunk.get` | `opaque`, `implemented_by`, `unsafe` | `unsafeCast` at the elaborated contract | — | output re-checked |
| `Solidity/Tools/Upstream.lean` | `unsafe evalExpr Json` | `solc_import` and the interpreter, reporting observations | FNV-1a 64 via `solc_import` | nothing: reports, not proofs |

No source-admitting path uses `skipKernelTC` (`Calculus/Notation.lean` and
`Calculus/Chains/Strategy.lean` use it for formulas and chain strategies, not
source), `native_decide`, `ofReduceBool` or a new axiom (check-trust
forbids them).

### 1.3 Findings against the decisions

| # | Finding | Decision it bears on |
|---|---|---|
| F1 | No Lean code computes SHA-256 of source or binary. `sourceSha256` is format-checked only; `compilerSha256` is compared with a constant string. Digests are recorded identity claims of the external step. | "Digests prove identity only" |
| F2 | `validateSettings` refuses every `libraries` entry (`Source.lean:183`); `readCompilerCode` and `scripts/solc-code.mjs` refuse unlinked bytecode. | G00 disagreement 6, G01 Q8 |
| F3 | Modern imports take evaluation order only from the solc pipeline: legacy gives `EvalOrder.mk false false false`, via-IR `EvalOrder.viaIR`; an explicit `evalOrder` is refused (`Import.lean:727`). Only 2 of the 8 combinations reach imported modern source. | G00 Q4 |
| F4 | `readCompilerCode` admits solc's `creationCode`/`runtimeCode` bytes as static constants. Under G00 Q5 the constants are this compiler's artifact bytes, so solc's bytes are an oracle/fixture input only. | G00 Q5 |
| F5 | Both pins are accepted by `parseCompiler`. 29 fixtures under `tests/solc` record 0.8.34 (22 historical headers, 7 schema 1 or 2), including non-SolKey sources (for example `CloudIntegration`, `ContractWorld`, `DeclarationMetadata`, `source-units/SourceUnits0834`). | G00 Q4 |
| F6 | `evmVersion` admits 14 targets (`homestead`…`osaka`); the AST step does not depend on it, but provenance would record a non-Osaka target unremarked. | G00 Q3 |
| F7 | Mixed legacy ABI modes across inherited units are refused (`solidity.compilationUnitAbiModes`, `SourceUnits.lean:43`). | abicoder v1/v2 |
| F8 | Feature-scan completeness is unproved: `ScopeScan.within` certifies only the reported list. | `InProfile` |

Counts: fixture headers were counted by reading every JSON file under
`tests/` with a top-level `header` object and grouping by `solcVersion`
prefix and `provenanceVersion`. 0.8.38: 67 headers (`tests/solc`,
`tests/abi-0.8.38`, `tests/operators-0.8.38`, `tests/upstream`); 0.8.34: 29,
all in `tests/solc`. None records a non-empty `libraries`. (G00's count of 36
0.8.34 files includes 7 validation records under `tests/upstream` that are not
fixtures.)

## 2. Certificate interfaces

`Solidity/Roadmap/Frontend.lean` (namespace `Solidity.Roadmap.Frontend`)
imports `Solidity.Frontend.Source` and `Solidity.Syntax.Raw` only, not
`Solidity.Roadmap.Contracts`; it repeats the fields G01's contract 1 reads.
All declarations below are definitions or proved shape lemmas; no instance
exists.

### 2.1 Stages

| Stage | Lean | Checked judgment |
|---|---|---|
| Raw input | `Input` (`units : List SourceUnit`, `main`, `settings`), `Input.Ok`, `Chain.raw`/`raw_sound` | distinct unit names, `main` among them, `Settings.Ok` |
| Raw identity | `Digests`, `Named`, `Input.Matches` | digests recomputed from the bytes the checker holds |
| Parse | `Chain.parse : Checker Input F.Syntax F.Parses` | `Parses` (S00, the pinned grammar) |
| Resolution | `Chain.resolve : Checker F.Syntax F.Resolved F.Resolves` | `Resolves` (S01) |
| Metadata | `Chain.metadata : Checker F.Resolved Unit (fun r _ => F.WellFormed r ∧ F.InProfile r)` | well-formedness and profile, including settings and links (`FrontendSpec.SettingsRespected`) |
| Whole | `Chain.Cert` (`parsed`, `parse`, `resolve`, `metadata`), `Chain.check` | conjunction of the stages |

`Checker A B J` has `Cert`, `check : A → B → Cert → Bool` and
`sound : check a b c = true → J a b`. The certificate formats are open by
design (a parse derivation, a declaration-reference and type map, a feature
list with its extraction proof); each stage's owner chooses one.

### 2.2 Theorems and their premises

| Name | Statement | Premises |
|---|---|---|
| `Digests.identity` | two `Named` with equal `recorded` have equal bytes | `CollisionFreeOn [a.bytes, b.bytes]` (per-run, G01 Q3) |
| `Digests.identity_list` | `xs.map digest = ys.map digest → xs = ys` | no collision between an element of `xs` and one of `ys` |
| `Input.Matches.identity` | two inputs matching one digest list have the same unit bytes | the same per-run premise |
| `Digests.only_invariant` | a check `check (digest b)` sound for `P` gives `P b'` for every `b'` with the same digest | none: this is the "identity only" limit |
| `CoderMode.agrees` | for `p.compilation = .analysed q s`, `p.effectiveCoder = some ((CoderMode.ofPipeline q).coderOf p.requestedCoder)` | none; ties the interface to `Provenance.effectiveCoder` |
| `Settings.ok_order`, `Settings.ok_coder` | changing `order` (any of 8) or `coder` keeps `Settings.Ok` | `s.Ok` |
| `Settings.ok_compiler` | `s.Ok → s.compiler ≠ .solkey0834` | `s.Ok` |
| `Chain.checked` | `ch.check i r c = true → i.Ok ∧ F.Admitted i r` | none (axioms: `propext`) |
| `Chain.frontend` | a chain and an untrusted producer, accepted and complete, form a `Checked F` | `accepted`, `complete` |

`Digests.only_invariant` is how "digests prove identity only" is checked:
since no frontend relation is invariant under digest collisions, a digest
can never discharge `Parses`, `Resolves`, `WellFormed` or `InProfile`; it can
only pin which bytes the other certificates are about.

### 2.3 Mapping to G01 (`Solidity/Roadmap/Contracts.lean`)

| G05 | G01 |
|---|---|
| `Input` | `SourceSpec.Input` (instantiated by this type) |
| `FrontendSpec.Syntax`, `Resolved`, `Parses`, `Resolves`, `WellFormed`, `InProfile` | the `SourceSpec` fields of the same names |
| `FrontendSpec.Admitted` | `SourceSpec.Admitted` (same body) |
| `Checked F` | `CheckedFrontend S` (same fields) |
| `Chain.frontend` | constructs `CheckedFrontend`; `CheckedFrontend` gives `Admission` given unambiguity (`SourceSpec.Unambiguous`) |
| `FrontendSpec.settingsOf`, `libraries`, `SettingsRespected` | new: obligations on `Resolves`/`InProfile` so `SourceSpec.meaning` reads the order and coder |

The sibling revision of `Contracts.lean` keeps `Admission` and `SourceSpec`;
the adapter `FrontendSpec.ofSourceSpec` (and `Chain.frontend` read as a
`CheckedFrontend`) is a child obligation once G01 is frozen (C1 below).
`Chain.checked` adds `i.Ok`: raw-input well-formedness is not part of
`SourceSpec.Admitted`, so `InProfile` must imply it through
`SettingsRespected` (settings) and `Parses` (unit names).

## 3. Link settings (G00 disagreement 6)

**Resolution.** Link settings are recorded in admitted settings
(`Settings.links : List Link`, `Link := {unit, library, address}`), checked at
two stages, and read only by deployment:

1. **Raw stage** — `LinksWellFormed`: nonzero 160-bit addresses, one entry per
   (unit, library), no address shared.
2. **Metadata stage** — `LinksResolved (F.libraries r) links`: every entry
   names a library declaration of the resolved input (by unit and name, as
   solc's `libraries` setting spells it). Required by
   `FrontendSpec.SettingsRespected` from `InProfile`.
3. **Source semantics** — link-blind: `SettingsRespected`'s third conjunct says
   `Parses` does not read `links`; a linked library call is a call between two
   instances of the compiled system (G01's `Event` docstring, G01 Q8), so the
   meaning never reads an address either.
4. **Deployment** — the EVM side reads the map: the artifact's unresolved
   references (`CodeUnit.links` in `Contracts.lean`) are filled with these
   addresses, and the session installs this compiler's library code at
   them. With an empty map the session deploys each library of the input
   and links the addresses it obtains. Either way the library code is the
   compiled system's, as G01 Q8 requires; no foreign code at a link address
   is admitted, and no environment premise is added.

This keeps provenance and the AST step unchanged: solc's AST analysis does not
depend on `libraries`. The code change (accepting a `libraries` object in
`validateSettings` and recording it in `Provenance`, plus the metadata-stage
check that needs resolved library ids) touches `Source.lean`,
`SourceUnits.lean` and the reader, files G00 lists as edited by in-flight
lanes; it is not a small local change, so it is child obligation C3.

## 4. Settings: evaluation order, ABI coder, compiler pins

- **Evaluation order.** `Settings.order : EvalOrder` is an input field
  ranging over all eight flag combinations (`Settings.ok_order`), so a public
  theorem quantified over admitted inputs covers each. solc's pipeline fixes
  only the importer's default (`defaultOrder`, matching `Import.lean:727-731`);
  six combinations have no solc setting and need none: the AST step does not
  depend on it, and the semantics reads `order` from the resolved input
  (`settingsOf`). Admission must be order-blind (`SettingsRespected`). F3 is
  child obligation C4.
- **ABI coder.** The requested coder is per source unit (pragma, read by
  `readPragmas`) and belongs to the syntax; the setting is `CoderMode`:
  `pragma` (solc legacy: each unit's own) or `forceV2` (solc via-IR).
  `CoderMode.coderOf` is the effective coder, and `CoderMode.agrees` proves it
  equals `Provenance.effectiveCoder` for every analysed provenance. Both modes
  are admitted with every order (`Settings.ok_coder`), so a v1 unit under the
  via-IR schedule (`coder := .pragma`, `order := EvalOrder.viaIR`) is an
  admitted input although no solc setting produces it. Mixed-mode inheritance (F7)
  stays refused until C5.
- **Compiler.** `Settings.Ok` requires `compiler = .catalog0838`; a 0.8.34
  analysis is never an admitted input (`Settings.ok_compiler`). 0.8.34
  fixtures stay valid for SolKey compatibility (`docs/solkey-migration.md`),
  never as evidence for the public theorem (C6).
- **EVM target.** `EvmTarget` has the single constructor `osaka` (G00 Q3).
  Provenance's `evmVersion` stays a record of the oracle run (F6, C7).

## 5. Child obligations

| # | Obligation | Owner |
|---|---|---|
| C1 | Adapter from G01's frozen `SourceSpec`/`CheckedFrontend` to `FrontendSpec`/`Checked`, after g01-contracts-rev lands | G01, then G05 follow-up |
| C2 | Parse and resolution relations with certificate formats and checkers (`Chain.parse`, `Chain.resolve`) | S00, S01, G08–G11 |
| C3 | Accept and record `libraries` in `validateSettings`/`Provenance`; check `LinksResolved` against resolved library ids; artifact linking and library deployment in `EvmSpec.load` | frontend lane owner, G42.04, G44.02, G06 |
| C4 | Let modern imports take any `EvalOrder` independently of the solc pipeline (F3) | G08–G15 (importer) |
| C5 | Admit mixed legacy ABI modes across inherited units (F7) | G15, S04.02 |
| C6 | Re-generate or mark the 29 0.8.34 fixtures: SolKey ones stay compatibility checks; local ones move to 0.8.38 | G53 |
| C7 | Refuse or flag non-Osaka `evmVersion` in admitted provenance (F6) | G06 |
| C8 | Replace solc `compilerCode` constants by this compiler's artifact table in the source semantics (F4) | G44.02, G01 |
| C9 | Feature-extraction completeness: `InProfile r ↔` the scan's feature list is within the profile, with combinations (F8) | G15 |
| C10 | Recompute source SHA-256 in the checker from source bytes in the fixture (F1); today the fixture holds no source text | G08 |

## 6. Gates

Run at the head of `cloud/roadmap-w1-20261029/g05-frontend`; results are in
the handoff below.

## 7. Review

See the handoff; finder and skeptic reviews (read-only subagents, no Lean
server) and their confirmed findings are recorded there.

## Handoff

Pending.
