# H35 VM validation: blocked cache delivery

Owned branch codex/solidity-sol2-20261104/c3-exactness; original base
6f3eedf0788ee1f8a3bcf230558c712ecdca04d5. Checked source checkpoint
e495bac0c6cd2c002e17d58b09bae78a85876d89. Final immutable seal records the
subsequent exact committed head. No Lean source/producer/premise/budget changed.

All nine owned modules build on this VM with explicit Lean -j1. This is a warm
0.314 s replay. Fresh per-file MCP Audit diagnostics re-elaborated all236
guarded #print axioms/signature entries in13.33s, with no errors; exact sets
remain standard propext/Classical.choice/Quot.sound subsets, with no new axiom
or sorry. Fresh Controls and GraphControls diagnostics pass (1.31s/6.07s).
Pinned compiler fixtures (nine) and comparator controls (six) pass2.31s; full
fixture/declaration acceptance and30packet rejection controls pass4.08s.
KeySort passes1.81s:377taclets,131read-bearing,tablecovers131,solkeycheck OK.
Actual Lean4.24.0/Lake5.0.0-src+797c613 and runtime receipts are saved. All Lean
checks used the unchanged12GiB cgroup/no-swap/oneCPU/LEAN_NUM_THREADS=1, parsed
-j1/stack131072, writer lock and4GiB H1 reserve. No Lean server remains active.

H35's installed scripts/coord-tools/ship-cache.sh actually exits2 on the
non-master checkout. SHIP_ALLOW_HEAD is a supported mechanical override, but
it does not supply the absent coordinator poll-state/catalog/vmexec transport
files. The installed tool documents coordinator-to-VM shipments; this VM has
no configured reverse-delivery destination. No script policy was modified,
no remote writes/transfer attempted, and no shipment receipt fabricated.

Q-H35-CACHE-1 [H35; ship-cache.sh]: Which supported delivery route should this
VM use? (1) Provide a VM-capable script/configuration so the worker can ship
and obtain a receipt; (2) coordinator retrieves the sealed prepared cache
packet and supplies the import receipt. This is an operational dependency,
not approval of an exclusion, premise or weakened validation.

The prepared packet is tests/sol-c3-exactness/.artifacts/h35-cache-e495bac0-v3.
It contains72artifacts/104333465bytes and exact24dependency mappings/traces for
the nine owned modules. Archive SHA256:
95342ae5f29dc9999bbfbeea80df80ba7d079aa8e16d447d0afed1a30a8cee32.
Its receipt explicitly says prepared_not_shipped. prepare-cache.py locks the
writer/Lake client/input map, reads only owned regular cache artifacts and
retains originals. Local verification binds exact producing Git source bytes
and toolchain, trace→mapping→artifact coverage, counts/preparer, required VM
gate statuses/heads/resources/log/source hashes, and all transport checksums.
Fifteen negative controls pass. --verify requires the producing checkout/build;
portable SHA checks do not certify import, shipment or kernel correctness.

Finder and skeptic independently reviewed data and tooling. Confirmed verifier
metadata/coverage gaps were fixed and v3 regenerated; v1/v2 remain historical
immutable preparations. Both now approve only this blocked prepared handoff
after saved15control output and fresh KeySort evidence. The final seal must
be regenerated/verified, and cache transfer receipt remains outstanding.

H35 checkpoint remains blocked, never done. Existing coordinator-owned shared
registration and integrated driver/gates/readiness obligations remain open.
Commands/exits/timings/RSS and gate/cache receipts are in evidence/h35-gates.json;
RSS is maximum process/child, not aggregate tree RSS. No RUNTIME_GATE_PASS or
full-lane completion is claimed.


## H41 amendment and received-cache receipt (2026-11-05)

H41 supersedes the earlier worker-shipping requirement: retain verified packs
on this VM, record path/SHA, never run ship-cache.sh on a VM, and mark delivery
coordinator-pending. The coordinator reports pulling the H35 archive and
verifying SHA256 95342ae5f29dc9999bbfbeea80df80ba7d079aa8e16d447d0afed1a30a8cee32.
Receipt: /home/guilherme/.local/state/cloudvm-coord/receipts/c3-exactness-cache-received-20261105T020449Z.json
This remote receipt is user-supplied coordinator evidence, not a file read on
this VM. Local archive bytes independently match. No import success was reported.

Current delivery status is coordinator-pending. Q-H35-CACHE-1 is resolved by
H41; no shipping configuration/permission is requested. The original immutable
H35 packet remains untouched. Its historical prepared_not_shipped label is
not rewritten into an unsupported worker shipment/import claim.

Fresh origin/master observation is 1d14f57a3a048bb1c1969c4c2c958d010ab84cb5,
which still has the same four C3 modules. All six producer pins and those
published files match the previous reported publication. Five modules plus
the Controls backfill still need coordinator integration; original shared
registration and integrated driver/gates/readiness obligations remain open.
Proof/source/toolchain/budgets are unchanged, so existing VM gate receipts
remain bound to identical inputs. See evidence/h41-cache-delivery.json and
evidence/h41-master-observation.json. No ship-cache.sh invocation, new goal,
goal reset, merge, push or shared-root edit occurred in this H41 turn.
