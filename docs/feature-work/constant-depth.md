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
| `ConstantDepth/Controls.lean` (new, item 4) | kernel `decide` controls on the real `evalConst`/`nconstP`/`rank`/`acyclicB`; exact axiom pins of all 80 lane theorems |

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
`tests/sol-constant-depth/Axioms.lean` (80 pins, regenerated from the current
declarations; the old 79-pin packet is superseded) and
`tests/calldata-packets-1105/RawInt/Axioms.lean` (55 pins).

## Reviews (Claude VM, read-only, no Lean server)

ConstantDepth finder — confirmed and fixed: module-map row over-claimed (rewritten);
`rank_reach_antisymm` did not state its rank claim (now `depPath_rank_no_return`,
concluding `rank b < rank a ∧ ¬Reach b a`); `chain_levels` was a definitional
restatement (removed); missing "near" chain (added `near_*`); unused-cycle value
not tied to `TEval` (added `unused_cycle_teval`); "qualified paths included" was
vacuous for expressions (docstring corrected, `qualified_*` controls added).
Suspected and recorded: the uniqueness theorems may not need the contract
(determinism by induction is not proved here).

ConstantDepth skeptic — ACCEPT-WITH-FINDINGS: premises are projections of the
existing contract; controls run the real checkers; Rank/Lookup/Complete unchanged.
Findings: the antisymmetry naming (fixed above); cycle members' lack of a `TEval`
value is shown only as `evalConst = none` here (their absence of `TEval` is the
existing `InferExamples.cyc_nc`; the iff lemmas need acyclicity).

RawInt reviews: see the RawInt document.

## Gates

Recorded in the RawInt document's increment section (one build covers both).

## Limitations

- No general family of environments with rank = `decls.length` for every size: the
  tightness is a witness (6 declarations), the bound itself is general.
- Determinism of `TEval`/`NamedConst` without the contract is not proved.
- A qualified constant reference (`K.X`) is no graph edge and has no typed value in
  the existing semantics (`Syn.paths`, `TEval`), unlike solc; `Solidity/Source/**`
  is VY5's, so this is recorded, not changed.
