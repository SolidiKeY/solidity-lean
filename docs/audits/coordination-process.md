# Coordination process audit (2026-11-06, read-only)

Window: poll.log 11-03 09:07 → 11-06 21:35 (454 polls, 130 lanes); pregate.log 11-05 17:57 → 11-06 21:40;
raw/ recentTurns (138 lanes, 3380 turns); sends/ (4581); master first-parent since 11-02. Scripts in a local scratch directory.

## 1. Where lane wall-clock goes
- **Turn-level (raw recentTurns): lanes ran turns 23.9% of their wall-clock** (981 of 4103 lane-h). Turns: median 8.1 min, p90 37 min; 30% (1016) under 3 min. Gaps between turns: median 9 min, p90 178 min.
- Poll-event view (2580 lane-h): blocked 49.9%, active 38.1%, paused 6.7%, goal=None 5.3%.
- Blocked intervals: 1304 closed, **median 0.19 h, p90 1.68 h**, but the tail holds the time: 73 blocks ≥4 h (5.6%) = **55% of blocked lane-h**; 14 blocks ≥12 h = 28%.
- **The tail is mostly ghosts:** 10 of 34 idle-blocked lanes now are Codex threads whose work moved to Claude (vy5, v07-lowering, v09, vo1, vt1, statement-grammar, literal-grammar, qualified-units, expression-uniqueness, constant-depth). 8 of the 9 blocks over 12 h are moved lanes; the 9th is terra-mechanical (pilot, 72 h). They also produce 24 of 49 SILENT alerts (16 moved + 8 terra).
- Blocks by cause, with timing where the logs allow it: question to next send median 0.19 h, p90 1.36 h. Waits on other lanes (deps.json, 278 items, 68 lanes): age median 2.7 h, p90 4.7 h. After a pregate FAIL, the next PASS came median 0.59 h later (n=7); after a CONFLICT, median 0.9 h (n=15). OOM holds: 5 (vx1 held 0.8 h). 16 lanes are still FAIL/CONFLICT; the oldest is v14 (CONFLICT since 11-05 17:57, about 28 h).
- Wait graph: 84 of 278 waits (30%) point at two h62-6 lanes (root-gate 45, syntax 39; syntax is paused). 73 (26%) point at names poll does not track, such as `claudecloud/move5…` or "CR"; 54 of those hold 14 *blocked* lanes. 97 (35%) run from paused or retired lanes to paused or retired lanes (dead entries).

## 2. Pipeline latency
- Pre-gate: 796 distinct heads in 27.8 h; PASS 710 (median 2.0 min), FAIL 62 (median 21 min), CONFLICT 24.
- **The gate is saturated:** 52.9 gate-h in 27.8 h, an average of 1.9 concurrent runs against the H81 cap of 2.
- **309 of the 796 gated heads (39%) are master→lane relay merges** (automerge.log). 37 of the 62 FAILs are on relay heads.
- **Two lanes ate 36% of gate time:** v14-payments-bytecode (24) and vx1 (8) failed `rc=1` 32 times, 29 of them on relay merges, for 19.4 gate-h. The same compile errors (e.g. Horizon.lean:983 unsolved goals) were re-gated on every master relay from 11-05 19:06 to 11-06 13:00.
- PASS→first master commit containing the head: median 0.58 h, p75 1.66 h, p90 3.74 h (n=483). 227 PASS heads (32%) never landed because a newer head from the same lane replaced them.
- Merge cadence: 46 publish clusters on 11-06, gap median 0.6 h.
- CONFLICTs: 8 of 26 touch only .md/.json bookkeeping (docs/module-map fragments, g07-axiom-pins.json, TERRA-TODO.md).

## 3. Rework and churn
- Auto-continues: 1505 across 25 lanes. Only 14 (0.9%) repeated the previous head. vy2-physical alone took 241 auto-continues and 359 sends, and got 26 of its 52 PASS heads into master.
- Questions: 140 QUESTION lines, 138 distinct, so only 2 were re-asked verbatim. The duplication is across lanes instead: the 15:20 triage turned 37 open questions into about 14 distinct answers. The v4.35 toolchain scope was asked by 5 lanes, perf/RSS STOP by 6 + 2, owner scope by 7.
- **INVALID:** 2115 lines, all after 16:29 on 11-06 (H71 rollout), across 132 lanes. 95% are "$.owner_tickets: required" (the field H71 added); 68% repeat a stale result with no new turn in between. **Relays sent: 0.** poll.py sends the fix-up only to the 11 lanes in validator-lanes.json (poll.py:97-103), and every lane has `invalidRelayed` empty. The other 122 lanes are never told that their block was rejected.
- Retired: 87 (h82-retiring.json). Moved Codex→Claude: 24 catalog tasks (moved, moved2–4, move5, move6). Of the 11 moved on 11-05, 5 are integrated. Fresh-scoped Claude batches (modes, semantics): 7 of 7 integrated.

## 4. Human load
- 89 decision entries (28 before 11-05, 15 on 11-05, 46 on 11-06). The file was rewritten 31 times between 11-05 23:00 and 11-06 20:44, including 03:46.
- On 11-06, about 29 of 46 decisions are about the coordination machinery itself (gates, CI, GitHub, budget, fleet, schema, listening). About 16 are about lane content.
- Numbering collisions: H88 and H90 each appear twice; H75 and H79 have the same subject ("spend remaining Claude budget").
- Open-question triage (15:20): 19 already answered by an existing decision, 10 coordinator lookups, 7 human, 1 other. **78% did not need the human**, and the 7 human questions reduce to 2 themes.
- **30 of the 37 open questions came from H62 lanes launched that day.** 89 of the 138 distinct questions came on 11-06, against 13–22 per day before.
- escalate.log: 75 entries. 8 of the 19 merge escalations are the same root cause: the permission sandbox denying `lake`/warm build (11-05 22:40 and 22:54, then 11-06 04:55, 05:57, 07:40, 11:25, 18:45, plus the Bridge build). 12 router escalations at 20:39–21:33 are CLAUDE-OWNER notices, not decisions.

## 5. Claude batch cost against outcome
- `$` appears in the evidence of only 24 of 67 tasks, totalling $514.48. **No 11-05 or 11-06 batch records cost** except 3 tasks.
- Done and integrated: 17 costed tasks, $286 (about $17 mean, $13 median).
- Partial: 4 costed tasks, $191. lane-semantics alone cost $118.95 (partial, not continued), which is 42% of all integrated spend.

## Top changes by measured payoff (after skeptic pass)
1. **Do not re-gate relay merges onto a lane whose last gate FAILed rc=1 until the lane pushes its own commit.** Payoff: about 17 gate-h/day (36% of a saturated 2-slot gate) goes back to PASS-bound heads. First step: in pregate, skip START when HEAD^2 is master, the last result is FAIL rc=1, and the lane-side parent is unchanged; log SKIP-STALE.
2. **Pre-answer the batch's own rules in launch notices and broadcast each answer batch-wide.** Payoff: 30 of 37 open questions were h62 same-day, collapsing to about 14 answers. First step: add toolchain scope, owner scope and perf-STOP rules to the h62 notice template, and send each A/B triage answer to every lane in the same batch.
3. **Resolve wait targets that name Claude branches.** 54 items hold 14 blocked lanes on targets poll cannot see, so nothing releases them automatically. First step: map `claudecloud/<batch>/<task>` in deps.json to the catalog's `integrated` sha; release the wait when that sha reaches master.
4. **Add one permission rule for the merge job's warm/Bridge build** (`systemd-run --user … lake build`). Payoff: 8 of the 19 merge escalations, and Bridge heads held under H45. First step: add the rule to the coordinator's settings, scoped to the merge worktree.
5. **Mark Codex threads of moved lanes `moved` in poll-state and metrics.** They are 29% of the idle-blocked lanes (10 of 34), 8 of the 9 blocks over 12 h, and 24 of the 49 SILENT alerts; today they inflate block_age p90. First step: H76's skip list feeds metrics.py and the SILENT check.
6. **Relay the H71 schema error once per lane, and dedupe INVALID logging by (lane, resultTurnId).** Payoff: 0 relays for 122 lanes; 1441 duplicate log lines in 5 h. First step: drop the validator-lanes.json gate on the relay branch, or make owner_tickets optional for legacy lanes.
7. **Auto-resolve conflicts confined to generated bookkeeping** (module-map fragments, pins JSON) by regenerating them with fragments.sh. Payoff: 8 of 26 conflicts, median 0.9 h each to recover, about 6 lane-h/day. First step: extend the existing AUTO-RESOLVED path (7 uses) to these globs.
8. **Allocate decision IDs with a script and batch process changes.** Evidence: duplicate H88/H90, the same-subject H75/H79, and 31 rewrites in 22 h. First step: `decide.sh` appends the next free H-number under a lock.
9. **Record `$` in every claudecloud journal close and cap each task at about 3× the median ($40).** First step: make the catalog writer refuse a state change without cost.

Dropped by the skeptic pass:
- (a) "Short coordinator-started turns are waste." 41% of the 1749 coordinator-started turns are under 3 min, against 7% of auto turns, but no message text survives to show they are acknowledgements, and they total under 20 lane-h over 4.7 days.
- (b) "The H71 validator silenced lanes." AUTO fell from 233 to 1 after 16:29, but the 14 previously auto-continued lanes still received 132 sends and worked 6.2 lane-h/h against 5.3 before. Item 6 keeps only the relay and log defect.
- (c) "Clean the dead waits." The 97 dead items cost no lane-hours, because their waiters are paused or retired.

Notes from the skeptic pass on items that survived:
- Item 1: the gate might be catching master-induced regressions. It is not: v14 re-failed 24 times identically over 18 h.
- Item 5: this saves no lane-hours. It survives on metric correctness only.
- Item 9: the payoff is unmeasurable today because the data is missing. That is the finding.

## Things that look bad but are fine
- 1505 auto-continues: 99.1% advanced the head, so lanes are not spinning.
- Median block 0.19 h: these are short pauses between auto-continues, not stalls.
- 32% of PASS heads never merged: a newer head from the same lane replaced each one.
- The 26.9 h "merge gap" on 11-04: master took squash "Add … increment" commits that day.
- Metrics 19:00 active=108: a transient H82b consolidation burst.
- Question latency: median 0.19 h; only 2 verbatim re-asks.
