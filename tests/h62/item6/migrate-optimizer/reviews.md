# Independent read-only reviews

Agents `/root/finder` and `/root/skeptic` were explicitly requested by the
assignment and AGENTS. Neither edited files nor invoked Lean or a Lean server.
These are evidence/reproduction/tooling reviews, not independent theorem replay.

## Initial census/baseline milestone

Both reviewers checked the four original modules, all 35 explicit declarations,
20-module closure and source hashes. They confirmed the old baseline success and
that its sampled aggregate RSS is not an exact peak. Findings and fixes:

- Exception/interrupt could leave container running after lock release: added
  try/finally cleanup before returning, and retained abnormal-exit evidence.
- Existing jobs not checked: reject pre-existing Lean/Lake processes.
- Container name alone could identify another invocation: use Docker's CID file
  created inside the fresh run directory; cleanup targets only that CID.
- Ordered universe parameters missing from type dump: added `info.levelParams`.
- Monitoring failures could leave zero samples: require successful samples.
- Current source census alone does not bind base: compare every source hash with
  `git show c6f550e281a7e5affa9a99bc2cdaed556dec00e4:<path>` before builds.
- Source-line declaration inventory is not elaborated types: added the full old
  environment audit and explicitly limited the new fixture interface claim.

The kernel RSS helper compiled warning-free and propagated a failing child exit.
The resource profile stayed fixed across versions. Original sources stayed frozen.

## Final blocked migration/backfill handoff

Finder independently checked all pinned source hashes, all 16 external dependency
records, saved samples, and 27 matching explicit generic interface hashes. It
found three omitted incoming consumers (PipelineControls, YulValidatorControls,
ValueValidatorControls under tests/fullscope-20261104/vo1). All are now listed in
the dependency report and handoff as read-only with new validation pending.

Skeptic independently recomputed every saved interface-record SHA256 and all
regressions. Counts: 59 full old constants; 27 explicit generic declarations match;
eight generated APIs change, two are added. Deltas: host wall +121.931942%, shell
wall +74.365573%, maximum child RSS +40.820205%. No new correctness issue found.

Both confirmed that failed new dependency builds cannot support a successful
full timing comparison, and that the mandatory STOP prevents further Lean checks.
Full migration, intrinsic/Roadmap validation and final/root gates remain pending.
The source owner requests and performance disposition are real blockers. Final
artifacts must exist before reporting them as supplied; the final export step
records the actual committed head and absolute paths.

## H44/H112 correction

The generated Generic/Isolated copies and five generated JSON reports are now
archived off Git with path/size/SHA256 in BULK-MANIFEST.json. Acceptance.lean and
Interfaces.lean import the real optimizer module and remain unchanged. Historical
copy-fixture results above do not validate the real module on the new toolchain.
Required full gates, STOP, proof budgets, retirement and open waits are unchanged.
Read-only split review and static verification are recorded in the split handoff.

Final split finder/skeptic reviews confirmed byte-exact preservation, unchanged
canonical fixture imports and production/resource settings, deterministic archive,
and retained STOP. Both found the summary output-directory name shadowed by its
record dictionary; fixed by using output_directory, then checked byte-identical
historical report reproduction. Finder also found stale dependency-report paths;
those now resolve to archived files and BULK-MANIFEST.json. Final finder found no
additional defect after the fixes. No Lean/server calls or reviewer edits.
