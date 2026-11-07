# Abstraction pilot: anti-unification deduplication

Batch `abstraction-20261106`, lane `pilot`. The question was whether
`scripts/coord-tools/au.py` (least general generalisation over indentation
blocks, ranked by MDL saving = (k−1)·const_tokens − k·holes) finds clone
clusters worth folding, and what folding them really saves in lines, tokens
and check time. Every edit is **statement-preserving** (H82): no existing
statement, definition, rule or docstring changed. Each one adds `private`
helper lemmas and rewrites proofs to call them.

## Method

- **Predicted saving.** `python3 -I scripts/coord-tools/au.py 10 FILE` on the
  base commit `706e3682`. MDL figures are in tokens.
- **Achieved saving.** Lines and tokens of the whole file, and of the touched
  declarations plus their helpers. Tokens use au.py's tokenizer
  (`TOK`) on non-blank lines.
- **Check time.** `lake lean FILE -- --tstack=131072` (what
  `gate.sh per-file` runs) on copies of the old and new file, three
  interleaved old/new pairs on one VM (4 cores), with the imports already
  built. The Lean server and other builds were idle while timing ran.
- **Correctness.** Lean MCP diagnostics are clean (errors and warnings) on
  each touched file. HashKinds' trailing `#guard_msgs` axiom check
  (`Fml.tk_validH`: `propext, Classical.choice, Quot.sound`) still passes.
  The checkpoint and full gates are listed under [Gates](#gates).

## Results per cluster

| File | Cluster (au.py rank, predicted) | Abstraction | Lines (file) | Tokens (file) | Tokens (region) | Check time (mean of 3) |
|---|---|---|---|---|---|---|
| `Calculus/FlattenTotality.lean` | `flattenFuel?_Src` arms. Ranks 1, 2, 3, 6: 1147 + 998 + 950 + 551, overlapping blocks of the same arms | 3 lemmas: `flattenFuel?_Src_bin` (20 arms), `_un` (5), `_leaf` (6). Definitional side facts are `rfl` autoParams | 2777 → 2233 (−544) | 42 877 → 33 116 (−22.8%) | −7 588 (13 722 → 6 134) | **25.9 s → 14.9 s (−43%)** |
| same | `*.restrict` membership projections. Ranks 4, 5, 8: 936 + 567 + 528 | 2 lemmas `allL`/`allR` (`List.forall_mem_append`), 57 sites | (in the row above) | (in the row above) | −2 342 (4 319 → 1 977) | (in the row above) |
| `Calculus/CutTotality.lean` | `LTm.cut_src` `cut2_default` binop arms. Ranks 1–3: 1102 / 966 / 491, overlapping | 1 lemma `LTm.cut_src_binop` (12 arms). Side condition `hop` is a `decide` autoParam | 721 → 674 (−47) | 11 556 → 10 265 (−11.2%) | −1 331 | 10.7 s → 9.6 s (−10%) |
| `Calculus/HashKinds.lean` | `hLevels_hashIn` witness lifting. Ranks 1, 5: 327 + 115 | 1 lemma `lvlLift` (16 sites) | 2852 → 2846 (−6) | 39 107 → 38 987 (−0.3%) | −171 | 13.6 s → 13.1 s (noise) |
| `Calculus/MemSwap.lean` | `Tm.mx_eval`/`mx_denote` `orLook` arms. Rank 1: 174 | 2 lemmas `MxRel.orLook_eval`/`_denote` (20 arms) | 2208 → 2181 (−27) | 27 856 → 27 856 (±0) | −52 | 10.1 s → 9.9 s (noise) |

Raw timings in seconds (old/new by round): FlattenTotality 26.1/14.6,
26.4/15.5, 25.2/14.5. CutTotality 11.5/9.9, 10.3/9.4, 10.2/9.6. HashKinds
14.5/13.6, 13.0/13.0, 13.4/12.6. MemSwap (final version) 10.7/10.0,
9.9/9.9, 9.6/9.8. No change slowed checking. Only FlattenTotality's speed-up
is clearly outside noise.

### Why FlattenTotality got faster

Each of its 31 arms re-ran the same `omega` calls (six to eight per binary
arm) and `simp only … at hd hr hb hs` over the concrete constructor's
`depth`/`nodes`/`atomBound`. The helper proves that arithmetic once, over
abstract `x`, `y` and `T`. The arms now only check `rfl` side facts
(`flattenFuel?` unfolding, `nodes`, `atomBound`, `words`) and apply the
fragment constructor. This is the "one declaration is one core" effect of
the lean-verify skill applied within one proof. The induction is still
serial, but each arm is cheap.

## What generalised well

- **Helper lemma whose side facts are definitional `autoParam`s** (`:= by
  intros; rfl`, `:= by decide`). This was the strongest pattern. Each call
  site is one line naming the constructor's builder and fragment lemma, and
  stays readable: `exact flattenFuel?_Src_bin ihx ihy (Flattened.app2
  (.binop .add h)) (fun _ _ => LTm.Num.add h)`. If a future definition
  change breaks a side fact, the error appears at the autoParam of that one
  arm, with the failing equation shown.
- **Membership projections** (`allL`/`allR`). These are small, but they
  replaced 57 two-line `fun q hq => hP q (by simp only …; exact Or.inl hq)`
  closures. Unification sees through `LTm.parameters`/`Inputs.termKeys` of a
  constructor without help.
- **No tactic macro was needed.** Every cluster here was a whole-arm clone or
  a clone with a common prefix, and a lemma served both. A macro would have
  kept the per-arm elaboration cost, which caused FlattenTotality's
  slowness.

## Pitfalls met

- **Argument order matters for elaboration.** The fragment kind of the IH
  (`kx`) must be fixed before the `hok` argument is elaborated, or `FlatOK
  l ?kx …` cannot unfold to `LTm.Num …`. Fix: put `ihx ihy` before `mk hok`.
- **Higher-order patterns.** `lvlLift` first abstracted the hash predicate
  as `A (hashInput R id) (hashId k R id)`. That is not a Miller pattern, and
  `Tm.HashIn σ k inp out t` has the term last, so nothing unified. Fix: take
  the predicates over `R id` (`A B : RefTy → Nat → Prop`), which are
  patterns.
- **Docstring placement.** A script that inserts a helper before a theorem
  must insert it before that theorem's docstring.

## False positives and weak predictions

- **au.py splits one family into several groups.** It groups by line-length
  shape and the first token, so one structural family (the 20 binary arms)
  appears as several overlapping groups. The top group had only 4
  instances, and the predictions overlap (blocks nested inside blocks). On
  FlattenTotality it **under-predicts**: the top four groups sum to 3 646
  tokens, and 7 588 were saved.
- **2-line clusters do not pay.** HashKinds (predicted 327) saved 171
  tokens in the region and 120 in the file. A 2-line `obtain`/`exact` pair
  becomes a 1-line call, and the helper costs about 10 lines.
- **Prefix clusters save lines, not tokens.** MemSwap's `orLook` prefix
  (predicted 174) saved 27 lines and 0 file tokens. What remains in each arm
  is different, and the helper costs as much as it saves. It is kept
  because each arm now starts with one line saying it goes through the
  lookup table. It is a readability change, not a compression.
- **Shared fragments that are not clones.** au.py also ranks clusters whose
  holes are the interesting part, for example HashKinds rank 2
  (`State.get_lift` arms, 5×, 1 hole, predicted 167). There, the varying
  constructor is the whole content. These were left alone.

## Remaining clusters (not taken)

- FlattenTotality: `ReadExpr.ofTerm?` `change … rw [hea, heb]; rfl` arms
  (14×, predicted 543) and `LTm.SrcL.readExpr` (8×, 500). Each arm needs a
  different `change` target, so a lemma would need the `ofTerm?` unfolding
  as a hypothesis. Possible, but smaller. The four lit-operand arms
  (`mulL`/`mulR`/`zmulL`/`zmulR`) and the formula arms of
  `flattenFormulaFuel?_Src` (`eqB`/`eqN`, `and`/`imp`, `defDiv*`, 2–7×
  each) take the same bin-helper shape with a lit operand.
- CutTotality: `cut1_default` unop arms (3×) and `addW`/`subW` (2×).

## Semantic redesign proposals (signature-only pass; not applied)

These change definitions or statements, so H82 rules them out for this
lane. Only declarations were read.

1. **`Fml.allN` vs `Fml.allNsw`** (`Calculus/HashKinds.lean:652, 2162`, with
   `envOf`/`envOfSw` at 633/2168 and `holds_allN`/`holds_allNsw` at
   2196/2184). `allNsw` is `allN` at `Ctx.sw Γ`. The two differ only
   because `Ctx.sw (replicate m u ++ Γ)` (a `List.map`) is not
   definitionally `replicate m u ++ Ctx.sw Γ` for variable `m`.
   *Proposal:* generalise `allN`/`envOf` over a context former that commutes
   by `rfl` (one recursive `Ctx.ext m Γ` with `Ctx.sw (Ctx.ext m Γ) =
   Ctx.ext m (Ctx.sw Γ)` true by `rfl` after `induction m`), or derive
   `allNsw` as a cast of `allN` with one transport lemma. *Payoff:* about
   25 lines (2 defs, 2 `holds_*` lemmas), and one place to fix later.
   *Risk:* a cast in a formula's index makes `Fml`'s intrinsic typing
   carry an equation (Gate G0, `docs/intrinsic.md`). The call sites in
   `HashKinds3.lean`, `HashMove.lean` and `HashKinds.lean` (5 uses of
   `holds_allNsw`) would change their statements. Low payoff for the risk;
   **not recommended** unless the swap machinery grows.
2. **One generic node fold for `vRoots`/`hLevels`/`memNodes`**
   (`HashKinds.lean:57–85, 1064–1100, 1117–1156`). The **term** levels are
   one fold: recurse through `netOf`/`app1`/`app2`/`app3` and collect at
   `app2` from an `Op2` node function (`isAtR`/`rootName?`, `nodeLevel?`,
   `memNode`). `memNodes` uses `&&` where the others use `++`, so the fold
   must be monoid-generic (or `memNodes` becomes `(fold …).all id`). The
   **formula** levels are not one fold: `Fml.vRoots` skips
   `havoc`/`bind`/`anon`/`allocAll`/`grow`, `Fml.hLevels` enters them, and
   `Fml.memNodes` answers `false` on them. The differences are semantic.
   *Payoff:* one membership lemma (`x ∈ t.foldNodes f ↔ ∃ node of t …`)
   would replace the per-function inductions (`Tm.hLevels_hashIn`, the
   `vRoots` lemmas, `memNodes` lemmas; 142 mentions in `HashKinds.lean`, 33
   in `HashKinds3.lean`). *Risk:* these functions run in the decision
   procedure (`Calculus/Decision.lean` mentions them). An extra closure
   argument can slow kernel reduction in `decide` proofs. Statements that
   unfold them by `simp only [Tm.hLevels]` would need the fold's equation
   lemmas. **Recommended only as a separate lane**, with `Decision`/example
   check times measured before and after.
3. **Shared `variable` header for `mxWrite_*`** (`MemSwap.lean:1446, 1504,
   1509, 1516`). Three of the four (`mxWrite_same`/`frame`/`lenId`) repeat
   `{H} {m m'} {R} {q} {id} {a} {k} {x}` and the hypothesis `h :
   m.writeT (MAddrT.index id a k) x = some m'`. A `section` with those
   `variable`s saves about 6 lines. *Risk:* `variable` binders enter in
   declaration order, and only the ones used are included. The statements
   stay the same when the order is kept, but `@mxWrite_frame …` call sites
   (if any) must be checked. Payoff too small to justify a lane; fold it
   into any later MemSwap edit.

## Recommended lane shape for a wider rollout

- **Target structural induction proofs with ≥ 10 arms of ≥ 8 lines whose
  bodies differ only in a constructor and its fragment lemma.** That is
  where both the token saving (11–23% of a file) and the check-time saving
  are. Find them with au.py, but **merge its groups by enclosing
  declaration** before ranking: sum the instances inside one `induction …
  with`, and drop clusters of ≤ 2 lines.
- **Route mechanical clusters to a script plus one Lean check.** The
  rewrites here were Python template matches (exact text of the old arm
  with holes, replaced only on an exact match). Lean checked only the
  result, once per file. A worker can do this without the Lean server
  except for the final diagnostic. It took about 15–40 minutes of agent
  time per cluster family, most of it waiting on checks.
- **Areas, in order:**
  1. Calculus totality and soundness inductions (`*Totality`, `Sound*`,
     `LeafTotality`, `FlattenReads`): same style as FlattenTotality.
     Expect FlattenTotality-like savings on the files with per-constructor
     arithmetic.
  2. The architecture audit's copied families
     (`docs/audits/architecture.md` on `cloud/audit-20261106/architecture`):
     144 exact-copy files (137 in Yul) and the 7–8-way `Yul/Views`
     `*Ownership*` families (76 files, 5,976 lines). Those are **file-level**
     copies. They need a generic definition (a semantic change, findings
     3–5 of that audit), not proof abstraction, and are outside H82.
     Anti-unification would only shave each copy.
  3. The audit's 340 duplicated-lemma groups (about half real). Move each
     to one shared module and delete the copies. That is a cheap
     mechanical lane (S–M) and does not need au.py.
- **Expected payoff per VM-hour:** on files like FlattenTotality, about 500
  lines and 40% of check time per hour. On average Calculus files, 30–50
  lines and a check time within noise. Below about 8 instances × 4 lines,
  a cluster does not repay its helper.
- **Guard rails:** keep H82 (no statement changes). Time three interleaved
  pairs per file and do not keep a slowdown above 10% without saying so.
  Keep autoParams to `rfl`/`decide`. Order helper arguments so that the
  indices of later arguments are fixed first.

## Finder and skeptic reviews

Two read-only reviews covered every applied abstraction, without the Lean
server: a finder over `git diff 706e3682..HEAD` and a skeptic arguing for
reverting.

- **Statement preservation.** Both reviews confirmed it independently. The
  only added declarations are the nine `private` helpers. No header,
  `variable`, attribute or docstring of an existing declaration changed.
  No arm was lost: every removed arm calls a helper with the same
  constructor and fragment proof.
- **Fixed** (commit "review fixes"):
  - `lvlLift`'s docstring claimed every `hLevels_hashIn` case used it.
  - `LTm.cut_src_binop`'s docstring said `mk` rebuilds the node.
    `cut2_default` does; `mk` only puts it in the fragment.
  - The `hop` autoParam restates `cut2_default`'s 12-way side condition.
    The docstring now says it must stay in step. Naming the condition in
    `QuotientCut.lean` would change `cut2_default`'s statement, which H82
    excludes, so it is left as a follow-up.
  - An identity repack of `nodeLevel?_spec` in HashKinds.
  - Lambda binders that shadowed `h` in HashKinds.
  - Seven new lines over 100 characters.
  - Redundant parentheses around `Flattened.seq` and `.and`/`.or`/`.eqB`/`.neB`.
- **Kept, with the skeptic's verdict.**
  - FlattenTotality and CutTotality: kept. These are real abstractions.
  - HashKinds: kept. It costs nothing to keep, and reverting is churn.
  - MemSwap: kept, though marginal. It is a readability change only. Most
    of its diff is re-indentation, which moves `git blame`; with
    whitespace ignored the diff is +53/−80.
- **Missed clusters** the finder listed are recorded under
  [Remaining clusters](#remaining-clusters-not-taken), plus:
  - CutTotality's "cut a, then b, then `defs_append`" bodies in
    `zseq`/`zadd`/`zsub`/`zcmp`/`key`/`seq*` (8×).
  - The `pvV`/`pvS`/`pvZ` fallbacks in MemSwap (2 lines each).

## Gates

- **Lean MCP diagnostics.** Errors and warnings are clean on all four
  touched files, after the review fixes.
- **`GATE_BASE=706e3682 gate.sh checkpoint`.**
  - Passed: `build-touched` (2025 s), `library` (`lake build Solidity`,
    2257 s; the cache re-fetch failed after a container restart, so the
    build was mostly cold), `examples`, `trust`, `orphans`, `layers`,
    `roots`, `fragments`.
  - `doc-paths` FAIL. Five missing paths, all in
    `docs/feature-work/h62-*.md`, `scripts/h62/` and `tests/h62/`, none in
    files this lane touched.
  - `axiom-pins` FAIL. "0 errors, 99 unrecorded changes": new pins in
    `GenericP10`/`Migrate*` fixtures, none in this lane's modules.
  - Both failures predate this lane.
  - The first checkpoint attempt died when the container was restarted
    (exit 137). Peak memory on the rerun was 10.4 GB.
- **`./run-lean.sh`**: PASS: "Build completed successfully (6546 jobs)", rc=0, no `error:` lines in the log (its pre-steps check layers, roots and fragments).
- **No new `sorry`, `axiom` or `maxHeartbeats`.** The finder checked every
  added line.
