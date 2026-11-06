# SOL-CB: G13 constant depth (and the G35-INT-RAW-1105 refill)

Lane `constant-depth`, moved from a Codex VM to a Claude VM on 2026-11-05.
Branch `cloud/moved4-20261105/constant-depth`; base `aec9adf1`; start
`cloud/constant-depth-move` (`06e61bc0`, the Codex lane head with the RawInt
increment `0c6d40e2`). The Codex wrappers `tests/calldata-packets-1105/RawInt/{lake,bounded.py}`
(Docker caps, `/workspace` toolchain) were dropped; no Codex tooling is used.

## Result

`Solidity/Frontend/Static/Consts.lean` documents that `levels E = E.decls.length + 1`
suffices for acyclic constants as unproved. It is proved here, without new premises,
under the existing contract: the clash-free projection
`E.decls.Pairwise (·.clash E · = false)` (exactly `WellFormed.noClash`) and
`ConstsAcyclic E` (already in the existing certificate).

| Module | Content |
|---|---|
| `ConstantDepth/Rank.lean` (on master) | `rank E a`: entries of `constNodes E` reachable from `a`; `rank_le_decls`, `rank_lt` (every graph edge drops rank), `rank_mono`, `rank_lt_path`, `walk_length_lt_decls` |
| `ConstantDepth/Lookup.lean` (on master) | a resolved constant normalizes to itself (`lookup_constant_canonical`); `rank_resolved_dependency_lt` |
| `ConstantDepth/Complete.lean` (on master) | `nconst_rank_complete` (rank many levels suffice), `nconst_levels_complete`, `evalConst_complete`, `evalConst_iff`, `evalConst_none_iff` (overflow refusals included), `arrayLenB_complete/iff/none_iff`, and the `*_resolved_complete` corollaries taking `WellFormed (resolveUnit s u)` |
| `ConstantDepth/Correspondence.lean` (new, backfill) | `constDeps_declared_iff` (a declared constant's edges are exactly its initializer's resolved constant paths), `rank_declared_dependency_lt`, `depPath_rank_no_return`, `teval_unique`, `nconst_unique`, `arrayLen_unique`, `arrayLen_static_value` |
| `ConstantDepth/Determinism.lean` (new, backfill) | `teval_det`, `nconst_det`, `arrayLen_det`: deterministic in every environment, no premise (mutual recursion on the derivations) |
| `ConstantDepth/Controls.lean` (new, item 4) | kernel `decide` controls on the real `evalConst`/`nconstP`/`rank`/`acyclicB`; exact axiom pins of all 83 lane theorems |

The original bound is therefore **true**; no counterexample or additive evaluator
was needed. Work-queue items 1–3 were on master (including the arrayLenB
corollaries, which the handoff listed as missing); item 4 and the backfill are
this increment.

### Controls (`Controls.lean`)

| Family | Theorems | Shows |
|---|---|---|
| chain at the declaration count | `chain_decls`, `chain_rank`, `chain_value`, `chain_rank_tight`, `chain_teval` | `C0=1, C(i+1)=C(i)+1`, 6 declarations: rank of `C5` = 6 = `decls.length`; `nconstP` succeeds with 6 levels and refuses with 5, so `levels` is loose by exactly one |
| chain near it | `near_rank`, `near_rank_tight`, `near_teval` | `C0…C4` plus unrelated `U`: rank 5 = `decls.length - 1`; 5 levels suffice, 4 refuse |
| shared diamond | `diamond_rank`, `diamond_value`, `diamond_teval` | `D = B + C`, both from `A`: rank 4 (the shared node counted once), value 4 |
| scopes and shadowing | `scoped_values`, `scoped_member_hidden`, `scoped_no_teval`, `scoped_teval` | `K.X = 5` shadows file `X = 100` in `K` and in `L is K`; `L.Z = 12`; file `W = X + 1 = 101`; members invisible at file level |
| duplicates | `duplicate_clashes`, `duplicate_refused` | two file-level `X`: the existing clash refusal; no value |
| cycles | `cyclic_refused`, `cyclic_values`, `unused_cycle_value`, `unused_cycle_teval` | `A↔B` and `S = S + 1`: not acyclic, no value; unrelated `M = N + 1 = 4` still evaluates (and is a `TEval` value by soundness) |
| qualified member | `qualified_no_edge`, `qualified_refused` | `V = K.X`: `Syn.paths` of a member access is `K`, so no edge and (no `TEval` member rule) no value — existing behaviour, recorded, not changed |
| overflow | `overflow_values`, `overflow_no_teval`, `overflow_lengths`, `overflow_length_refused` | `uint8 D = C + 1` with `C = 255` refused, as `evalConst = none`, no `TEval`, no `ArrayLenOK`; `uint8 F = 300 - 100 = 200` (exact rational folding, then conversion) |

## RawInt refill (G35-INT-RAW-1105)

See `calldata-packets-1105-RawInt.md`, section "Claude-VM increment".

## Acceptance and pins

`python3 scripts/check-sol-constant-depth.py` reads `tests/sol-constant-depth/manifest.json`
and checks: every module exists, is in `Solidity.lean` and has a module-map row; every
lane theorem has exactly one `#guard_msgs` pin with standard axioms only, and the pin
file pins nothing else; the same pin block closes `Controls.lean` (so `lake build`
enforces it); every headline theorem and every control family member is declared;
no `sorry`/`admit`/`native_decide`/`maxHeartbeats`/`axiom`/`unsafe`; and the seven
read-only inputs match their sha256 pins. A deleted pin is rejected (mutation-checked).

Pin registration in `scripts/g07-axiom-pins.json` stays with the coordinator (Q-PIN-1):
after integration run `node scripts/check-axiom-pins.mjs --write`; the proposal is
`tests/sol-constant-depth/Axioms.lean` (83 pins, regenerated from the current
declarations; the old 79-pin packet is superseded) and
`tests/calldata-packets-1105/RawInt/Axioms.lean` (55 pins).

## Reviews (Claude VM, read-only, no Lean server)

ConstantDepth finder — confirmed and fixed: module-map row over-claimed (rewritten);
`rank_reach_antisymm` did not state its rank claim (now `depPath_rank_no_return`,
concluding `rank b < rank a ∧ ¬Reach b a`); `chain_levels` was a definitional
restatement (removed); missing "near" chain (added `near_*`); unused-cycle value
not tied to `TEval` (added `unused_cycle_teval`); "qualified paths included" was
vacuous for expressions (docstring corrected, `qualified_*` controls added).
Suspected: the uniqueness theorems do not need the contract — confirmed by
proving `teval_det`/`nconst_det`/`arrayLen_det` with no premise (`Determinism.lean`);
the contract versions are kept unchanged.

ConstantDepth skeptic — ACCEPT-WITH-FINDINGS: premises are projections of the
existing contract; controls run the real checkers; Rank/Lookup/Complete unchanged.
Findings: the antisymmetry naming (fixed above); cycle members' lack of a `TEval`
value is shown only as `evalConst = none` here (the iff lemmas need acyclicity;
the existing `InferExamples.cyc_nc` proves absence for a separate `A ↔ B` unit).

Second round (on the fixes), finder and skeptic — skeptic ACCEPT-WITH-FINDINGS.
Fixed: `entry_large_length_copy` docstring now says which branch it cannot
isolate and that offset/length words are read; "structural" dropped from the
determinism description (Lean may choose well-founded recursion; the statements
are the same); `qualified_no_edge` now also shows `K.X = 5` in `K`; the controls
docstring was tidied and no longer credits `cyc_nc` with `cyclicE`; a stale pin
count and a wrong theorem name in docs were corrected; the checker now finds
attribute-prefixed/`protected` theorems and `axiom` declarations, compares the
inline pin block exactly, and covers RawInt (pins, mirror, forbidden tokens).

RawInt reviews: see the RawInt document.

## Gates (Claude VM, head before this commit `ffab0c15`)

- Lean MCP diagnostics, `severity=error`, clean on every touched file:
  RawInt `Execution`/`Controls`, ConstantDepth `Determinism`/`Correspondence`/`Controls`,
  and both pin files `tests/calldata-packets-1105/RawInt/Axioms.lean` and
  `tests/sol-constant-depth/Axioms.lean` (their `#guard_msgs` pass).
- `./run-lean.sh`: `lake build` of the default targets and `SolkeyTestSuite`
  passed ("Build completed successfully (5827 jobs)", 36m44s wall after a
  container restart resumed the cache). The script then exits 1 in its final
  `scripts/check-solkey.sh` step: the environment's `../solkey` checkout is at
  `b8d5f88`, newer than the repository's pin `473da8944c`
  (`tests/migration/solkey.pin.json`), giving 167 drift reports. Against the
  pinned commit's rule file the same check passes:
  `scripts/check-solkey.sh --key <pinned solidityProgramRules.key>` →
  "solkeycheck: OK — annotations match". This lane touches no Calculus,
  annotation or SolKey file.
- `register.sh --check`, `fragments.sh --check`: pass. `node scripts/check-orphans.mjs`:
  "5811 reachable, 0 orphaned, 0 not allowed". `node scripts/check-layers.mjs`: pass.
  `bash scripts/check-trust.sh`: "0 findings". `python3 scripts/check-sol-constant-depth.py`:
  ACCEPT (ConstantDepth 6 modules, 83 theorems, 83 pins; RawInt 2 modules, 55 theorems,
  55 pins; 8 control families; 7 input pins).
- `#print axioms`: every headline theorem uses at most `propext`,
  `Classical.choice` and `Quot.sound`.
- Module times (4-way parallel build): `ConstantDepth.Controls` 116 s and
  `RawInt.Controls` 163 s, both above 60 s; they are new control modules that only
  evaluate concrete units/byte strings in the kernel and nothing imports them,
  so no existing module slows. The other touched modules were elaborated by the
  Lean server in seconds and were already up to date for the build.
- `check-doc-paths.sh` fails with one pre-existing missing reference (also on the
  base `aec9adf1`); `check-axiom-pins.mjs` reports thousands of pre-existing
  unrecorded pins on master; registering this lane's pins is coordinator-owned.

## Limitations

- Absence of a `TEval` value for the members of `Controls.cyclicE` is not proved
  (only `evalConst = none`).
- No general family of environments with rank = `decls.length` for every size: the
  tightness is a witness (6 declarations), the bound itself is general.
- A qualified constant reference (`K.X`) is no graph edge and has no typed value in
  the existing semantics (`Syn.paths`, `TEval`), unlike solc; `Solidity/Source/**`
  is VY5's, so this is recorded, not changed.

## Register (coordinator / integrator)

- Roots: `Determinism`, `Correspondence` and `Controls` under
  `Solidity/Frontend/ConstantDepth/` are in `Solidity.lean` via `register.sh`
  (regenerate after merge).
- Module map: rows in `docs/module-map/frontend.d/constant-depth.md`. Proposed
  replacements for the placeholder RawInt rows in `docs/module-map/v08-adapters.d/00-base.md`
  (not this lane's fragment): `RawInt/Execution.lean` — "raw intN/uintN calldata to
  memory: width-specific accepted words, exact copy run, dirty-word revert with
  rollback, frame-bound guarded entry"; `RawInt/Controls.lean` — "raw intN controls:
  negative bytes at mixed offsets, near-width, padding, entry guards, selector
  shift; exact axiom pins". The `Rank.lean` row sits in `v08-adapters.d/00-base.md`
  and could move to the frontend area.
- Axiom pins: `node scripts/check-axiom-pins.mjs --write` after integration
  records `tests/sol-constant-depth/Axioms.lean` (83), `tests/calldata-packets-1105/RawInt/Axioms.lean`
  (55) and the identical inline blocks closing both `Controls.lean` files.
