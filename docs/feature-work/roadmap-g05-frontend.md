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
   `scripts/solc-unit.mjs` checks the SHA-256 of a soljson binary against the
   SolKey checkout's `build.gradle` pin or an explicit `--compiler-sha256`
   (`scripts/solc-ast.mjs:126-129`) and, for modern provenance only, against
   the two-pin list (`:145-146`; skipped for `--legacy-fixture`, the path
   behind the 22 historical headers), runs `--standard-json` with
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
| `Solidity/Syntax/Contract.lean` `contract!{ … }` (`:96`, expanded at `:358`) | none: a `macro_rules` expansion | Lean parser and macro expansion of hand-written source | — | the `Contract` literal (its proof fields by `decide`/`rfl`) |
| `Solidity/Syntax/Splice.lean` `sol{ … }` (`:87`, `sol[InContract.contract]{ … }`) | as `sol[C]{ … }` below | as below | — | as below |
| `Solidity/Syntax/Splice.lean` `elabAgainstWith` (`sol[C]{ … }`) | `unsafe evalExpr` (`:103`) | compiled elaborator | — | typing of the quoted result |
| `Solidity/Syntax/Elab/Values.lean` `CallMemo` | `unsafe` ×2, `override` (`implemented_by`) ×2 | pointer-equality memo; logically `none` | — | the reference implementation is the logical one; the output is re-checked |
| `Solidity/Syntax/Quote.lean` `QMemo` | `unsafe` ×2, `override` (`implemented_by`) ×2 | pointer-equality memo | — | output re-checked |
| `Solidity/Syntax/Elab/Context.lean` `RecThunk.get` | `override` (`implemented_by`), `opaque`, `unsafe` | `unsafeCast` at the elaborated contract | — | output re-checked |
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
prefix and `provenanceVersion`: 94 headers. 0.8.38: 65 headers (`tests/solc`,
`tests/abi-0.8.38`, `tests/operators-0.8.38`, `tests/upstream`); 0.8.34: 29,
all in `tests/solc`. None records a non-empty `libraries`. (G00's count of 36
0.8.34 files includes 7 validation records under `tests/upstream` that are not
fixtures.)

## 2. Certificate interfaces

`Solidity/Roadmap/Frontend.lean` (namespace `Solidity.Roadmap.Frontend`)
imports `Solidity.Frontend.SourceUnits` and `Solidity.Syntax.Raw` only, not
`Solidity.Roadmap.Contracts`; it repeats the fields G01's contract 1 reads.
All declarations below are definitions or proved shape lemmas; no instance
exists.

### 2.1 Stages

| Stage | Lean | Checked judgment |
|---|---|---|
| Raw input | `Input` (`units : List SourceUnit`, `main`, `settings`), `Input.Ok`, `Chain.raw`/`raw_sound` | distinct unit names, `main` among them, `Settings.Ok` (profile compiler, empty link map) |
| Raw identity | `Digests`, `Named`, `Input.Matches` | digests recomputed from the bytes the checker holds; not part of `Chain` (no stage reads a digest) |
| Parse | `Chain.parse : Checker Input F.Syntax F.Parses` | `Parses` (S00, the pinned grammar) |
| Resolution | `Chain.resolve : Checker F.Syntax F.Resolved F.Resolves` | `Resolves` (S01) |
| Metadata | `Chain.metadata : Checker F.Resolved Unit (fun r _ => F.WellFormed r ∧ F.InProfile r)` | well-formedness and profile; with the obligation `FrontendSpec.SettingsRespected`, also settings and links (`Chain.checked_settings`) |
| Whole | `Chain.Cert` (`parsed`, `parse`, `resolve`, `metadata`), `Chain.check` | conjunction of the stages |

`Checker A B J` has `Cert`, `check : A → B → Cert → Bool` and
`sound : check a b c = true → J a b`. The certificate formats are open by
design (a parse derivation, a declaration-reference and type map, a feature
list with its extraction proof); each stage's owner chooses one.

### 2.2 Theorems and their premises

| Name | Statement | Premises |
|---|---|---|
| `Digests.identity` | two `Named` with equal `recorded` have equal bytes | `CollisionFreeOn [a.bytes, b.bytes]`: the per-run form of the G01 Q3 decision, applied here to input digests (an extension of its wording, which is about the hashes an execution prefix computes; no random-oracle bound is stated for input digests) |
| `Digests.identity_list` | `xs.map digest = ys.map digest → xs = ys` | no collision between an element of `xs` and one of `ys` |
| `Input.Matches.identity` | two inputs matching one digest list have the same unit bytes | the same per-run premise |
| `Digests.only_invariant` | a check `check (digest b)` sound for `P` gives `P b'` for every `b'` with the same digest | none: this is the "identity only" limit |
| `CoderMode.agrees` | for `p.compilation = .analysed q s`, `p.effectiveCoder = some ((CoderMode.ofPipeline q).coderOf p.requestedCoder)` | none; ties the interface to `Provenance.effectiveCoder` |
| `CoderMode.agrees_atNode` | the same for `p.atNode node`, the provenance of any source unit of a compilation (`Solidity/Frontend/SourceUnits.lean`) | none |
| `Settings.ok_order`, `Settings.ok_coder` | `Settings.Ok` does not read `order` or `coder` | `s.Ok` |
| `FrontendSpec.admits_order` | an admitted input stays admitted, with that order carried, under each of the eight orders | `F.AllSettings`, `i.settings.Ok` |
| `Settings.ok_compiler` | `s.Ok → s.compiler ≠ .solkey0834` | `s.Ok` |
| `Chain.checked` | `ch.check i r c = true → i.Ok ∧ F.Admitted i r` | none (axioms: `propext`) |
| `Chain.checked_settings` | an accepted input's resolution carries its settings, which are `Ok`, and its links name library declarations | `F.SettingsRespected` |
| `Chain.frontend` | a chain and an untrusted producer, accepted and complete, form a `Checked F` | `accepted`, `complete` |

`Digests.only_invariant` is the formal limit of "digests prove identity
only": a check reading only a digest certifies only properties shared by every
input with that digest. It holds for any function; it is a limit, not a
security claim (for an injective `digest` the limit is empty). The interfaces
therefore never let a digest discharge `Parses`, `Resolves`, `WellFormed` or
`InProfile`: `Chain` has no digest field, its stages read the input bytes, and
`Digests.identity` only pins which bytes a recorded digest names, under the
per-run premise. No theorem here depends on that premise.

**Obligations, not fields.** `FrontendSpec.SettingsRespected` (a resolution
carries the input's settings; `InProfile` implies `Input.Ok` and resolved
links) and `FrontendSpec.AllSettings` (admission is stable under every
admitted settings value) are `Prop`s about the relations that S00/S01/G15
must prove. `Chain.checked` does not need them, and `Chain.checked_settings`
and `FrontendSpec.admits_order` take them as premises. `Checked` alone can
be inhabited vacuously (`Parses := False`, `produce := fun _ => none`); the
non-vacuity check is G01's `SourceSpec.NonVacuous` on the same relations.

### 2.3 Mapping to G01 (`Solidity/Roadmap/Contracts.lean`)

| G05 | G01 |
|---|---|
| `Input` | `SourceSpec.Input` (instantiated by this type) |
| `FrontendSpec.Syntax`, `Resolved`, `Parses`, `Resolves`, `WellFormed`, `InProfile` | the `SourceSpec` fields of the same names |
| `FrontendSpec.Admitted` | `SourceSpec.Admitted` (same body) |
| `Checked F` | `CheckedFrontend S` (same fields) |
| `Chain.frontend` | constructs `CheckedFrontend`. `Contracts.lean` states no lemma from `CheckedFrontend` to `Admission`; one holds without `SourceSpec.Unambiguous` (`frontend i := (produce i).map Prod.fst`, since `complete` already allows one admitted resolution per input) and is part of C1 |
| `FrontendSpec.settingsOf`, `libraries`, `SettingsRespected`, `AllSettings` | new: obligations on `Resolves`/`InProfile`; `SourceSpec.meaning` must factor through `settingsOf` for `order` and `coder` and not read `links` (C1) |

The sibling revision of `Contracts.lean` keeps `Admission` and `SourceSpec`;
the adapter `FrontendSpec.ofSourceSpec` (and `Chain.frontend` read as a
`CheckedFrontend`) is a child obligation once G01 is frozen (C1 below).
`Chain.checked` adds `i.Ok`, but `Checked.checked` (like `CheckedFrontend`)
returns only `Admitted`: raw-input well-formedness is not part of
`SourceSpec.Admitted`, so the second conjunct of `SettingsRespected` makes
`InProfile` imply it.

## 3. Link settings (G00 disagreement 6)

**Resolution.** Link maps are recorded and checked, and the admitted
profile takes the empty map:

1. **Record** — `Settings.links : List Link` (`Link := {unit, library,
   address}`) holds solc's `libraries` setting. `Settings.LinksRecorded`
   (`LinksWellFormed`): nonzero 160-bit addresses, none an Osaka precompile
   (`Precompile`: `0x01`–`0x11`, `0x100`; the precompile follow-up decision),
   one entry per (unit, library), no address shared.
2. **Metadata stage** — `LinksResolved (F.libraries r) links`: every entry
   names a library declaration of the resolved input (by unit and name, as
   solc spells it). Required from `InProfile` by `SettingsRespected`.
3. **Source semantics** — link-blind. A linked library call is a call between
   two instances of the compiled system (G01's `Event` docstring, G01 Q8), so
   `meaning` reads no address (C1).
4. **Admitted profile** — `Settings.Ok` requires `links = []`. The session
   deploys each library of the input as this compiler's code and fills the
   artifact's references (`CodeUnit.links` in `Contracts.lean`) with the
   addresses those deployments return. This needs no premise on the initial
   world and keeps every library inside the compiled system (G01 Q8).

A non-empty map fixes addresses before deployment. The EVM cannot place code
at a chosen address (creation addresses follow sender and nonce; salted
creation is excluded), so admitting one needs a premise on the initial world:
the code at each address is this compiler's runtime for that library. That
premise is a new environment assumption, and is question Q1 below. Until then
a non-empty map is recordable (oracle fixtures) but not admitted.
`Link` is keyed by unit and library name while `CodeUnit.links` uses
positions in `Artifact.contracts`; the map between them is the artifact
table's declaration index (C3).

This keeps provenance and the AST step unchanged: solc's AST analysis does not
depend on `libraries`. The code change (accepting a `libraries` object in
`validateSettings` and recording it in `Provenance`, plus the metadata-stage
check that needs resolved library ids) touches `Source.lean`,
`SourceUnits.lean` and the reader, files G00 lists as edited by in-flight
lanes; it is not a small local change, so it is child obligation C3.

## 4. Settings: evaluation order, ABI coder, compiler pins

- **Evaluation order.** `Settings.order : EvalOrder` is an input field.
  `Settings.Ok` does not constrain it, and under the obligation
  `FrontendSpec.AllSettings` every admitted input stays admitted with each of
  the eight orders (`FrontendSpec.admits_order`), so a public theorem
  quantified over admitted inputs covers all eight. solc's pipeline fixes
  only the importer's default (`defaultOrder`, matching `Import.lean:727-731`);
  six combinations have no solc setting and need none: the AST step does not
  depend on it, and the semantics reads `order` from the resolved input
  (`settingsOf`). F3 is child obligation C4.
- **ABI coder.** The requested coder is per source unit (pragma, read by
  `readPragmas`) and belongs to the syntax; the setting is `CoderMode`:
  `pragma` (solc legacy: each unit's own) or `forceV2` (solc via-IR).
  `CoderMode.coderOf` is the effective coder. `CoderMode.agrees` and
  `CoderMode.agrees_atNode` prove it equals `Provenance.effectiveCoder` for
  every analysed provenance and every unit of a compilation. G00 Q4 decides
  the eight orders, not how the coder pairs with them. The interface keeps
  `coder` independent (both modes under every order: a superset of solc's two
  pairings). Whether the public theorem covers the pairings no solc setting
  produces, such as a v1 unit under the via-IR order, is question Q2. Mixed-mode inheritance (F7)
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
| C1 | Adapter from G01's frozen `SourceSpec`/`CheckedFrontend` to `FrontendSpec`/`Checked`, after g01-contracts-rev lands; `meaning` factors through `settingsOf` (`order`, `coder`) and ignores `links` | G01, then G05 follow-up |
| C2 | Parse and resolution relations with certificate formats and checkers (`Chain.parse`, `Chain.resolve`); proofs of `SettingsRespected` and `AllSettings` | S00, S01, G08–G11, G15 |
| C3 | Accept and record `libraries` in `validateSettings`/`Provenance` (refusing non-empty maps for admitted inputs until Q1); check `LinksResolved` against resolved library ids; library deployment and linking through the artifact's declaration index in `EvmSpec.load` | frontend lane owner, G42.04, G44.02, G06 |
| C4 | Let modern imports take any `EvalOrder` independently of the solc pipeline (F3) | G08–G15 (importer) |
| C5 | Admit mixed legacy ABI modes across inherited units (F7) | G15, S04.02 |
| C6 | Re-generate or mark the 29 0.8.34 fixtures: SolKey ones stay compatibility checks; local ones move to 0.8.38 | G53 |
| C7 | Refuse or flag non-Osaka `evmVersion` in admitted provenance (F6) | G06 |
| C8 | Replace solc `compilerCode` constants by this compiler's artifact table in the source semantics (F4) | G44.02, G01 |
| C9 | Feature-extraction completeness: `InProfile r ↔` the scan's feature list is within the profile, with combinations (F8) | G15 |
| C10 | Recompute source SHA-256 in the checker from source bytes in the fixture (F1); today the fixture holds no source text | G08 |

## 6. Open scope questions

These arise from the work; they reopen no recorded decision.

- **Q1 [Link map]** G01 Q8 puts linked libraries in the compiled system, so
  their code is this compiler's. Should an input whose solc `libraries`
  setting pre-assigns addresses be admitted?
  - *Empty map only*: the session deploys and links every library itself; no
    new premise; a pre-assigned map is recorded but refused (current interface).
  - *Admit pre-assigned maps*: adds a premise on the initial world that each
    address holds this compiler's runtime for that library.
- **Q2 [Coder pair]** G00 Q4 decides the eight `EvalOrder` combinations but not
  their pairing with the ABI coder mode. Which pairings does the public
  theorem cover?
  - *Independent*: both coder modes under every order (16 pairings, a superset
    of solc's two; current interface).
  - *Forced with via-IR order only*: `forceV2` exactly when the order is
    `EvalOrder.viaIR`, pragma coders otherwise (8 pairings).

## 7. Gates

Run at the head of `cloud/roadmap-w1-20261029/g05-frontend`; results are in
the handoff below.

## 8. Review

Two read-only subagents, neither using the Lean server, reviewed commit
`35f80a6` (the first version): a finder (facts against the repository) and a
skeptic (soundness and vacuity of the interfaces).

Skeptic, confirmed and fixed:

1. *Unsound obligation.* The first `SettingsRespected` had a conjunct making
   `Parses` stable under a settings change, plus one carrying
   `settingsOf r = i.settings`. Together they force `Admitted` to be empty
   whenever two orders differ. Fixed: settings stability moved to a separate
   obligation on `Admitted` (`FrontendSpec.AllSettings`, with
   `FrontendSpec.admits_order`), and the parse conjunct removed.
2. *All eight orders did not follow.* `Settings.ok_order` only shows that
   `Settings.Ok` ignores the order. Fixed as in 1; the doc now attributes
   the eight-order coverage to `AllSettings`.
3. *`SettingsRespected` unused.* Now a premise of `Chain.checked_settings`,
   and its second conjunct also gives `Input.Ok` (skeptic 10, finder 5).
4. *Meaning and non-vacuity.* Recorded: `meaning` must factor through
   `settingsOf` (C1); `Checked` alone is inhabitable vacuously, and
   non-vacuity is G01's `SourceSpec.NonVacuous` (§2.2).
5. *Environment premise smuggled in by pre-assigned links; precompile
   addresses.* Fixed: `Settings.Ok` requires `links = []`, a non-empty map is
   question Q1, and `LinksWellFormed` excludes Osaka precompiles (`Precompile`).
6. *`Link` vs `CodeUnit.links`* (also finder 10). Recorded in §3 and C3.
7. *Coder agreement for the main unit only.* Added `CoderMode.agrees_atNode`
   (imports `Solidity.Frontend.SourceUnits`).
8. *Coder/order pairing undecided.* Now question Q2.
9. *Digest statements overstated.* §2.2 now says what `only_invariant` does
   and does not show, that no theorem depends on the per-run premise, and
   that applying the G01 Q3 premise to input digests extends its wording
   (also finder 7).

Finder, confirmed and fixed: 0.8.38 fixture headers are 65, not 67 (94
in all) (1); trust-site kinds use the inventory's `override` (2); the
metadata-stage and order-blindness claims (3, 4, 5) were corrected with the
Lean changes above; the `Admission`-from-`CheckedFrontend` claim no longer
cites `Unambiguous` (6); the solc-ast pin check is described per path (8);
`contract!{ … }` and `sol{ … }` rows added to the inventory (9). All other
cited lines, counts and decisions were confirmed.

## Handoff

Pending.
