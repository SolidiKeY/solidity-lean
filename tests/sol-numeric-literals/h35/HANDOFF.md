# H35 VM validation and cache handoff

Status: BLOCKED. The VM gates pass, but no cache-delivery receipt exists; this
checkpoint is not done under H35. Original registration/full runtime obligations
also remain open. No theorem, premise, exclusion, refusal or proof budget changed.

Original base: 6f3eedf0788ee1f8a3bcf230558c712ecdca04d5
Validated proof source head: 7bb0d3a1d63f9ce28ffbad0a5fdc5f3da9d08cdf
Repository: /workspace/solidity-lean
Branch: codex/solidity-sol2-20261104/numeric-literals

## VM gates actually run

- Owned-module build: all 42 modules, 49 jobs, cache replay; exit 0. Lean -j1 and
  LEAN_NUM_THREADS=1,12 GiB memory/no swap,CPU 1,monitored4 GiB parent reserve.
  0.446935 seconds; maximum child RSS59892 KiB. This was not a clean recompilation.
- PrintAxioms.lean: all 627 authored theorem names are taken from the acceptance
  inventory. Per-file MCP returned complete diagnostics,zero errors,all 627
  #print axioms messages. 49.614 seconds; the existing 300 second diagnostic timeout was unchanged.
- validate-axioms.py: exact print source/name list,complete result coverage and
  every axiom set checked against pins. Full inventory also checks808 theorem
  constants / 991 owned constants,including generated helpers. No new axiom,
  unsafe declaration or proof escape; only unchanged standard primitive sets.
- Controls:32 inhabited constructors,68 scanner controls,42 typed/compiler fixtures,
  all 18 accepted exact values and all 5 stage differences. Negative controls pass.
  1.109682 seconds; maximum child RSS180932 KiB. Kernel controls are checked through
  the owned build; external compiler/Python checks are separate evidence.
- Every command/exit/timing/resource record is in evidence/h35-*.json and logs.
  The cgroup peak is cumulative from this owned container,not fresh process RSS.
  No resource stop occurred. Idle MCP was stopped after the axiom gate.

The initial MCP-schema inspection tried to parse the bridge's plain tool-name
list as JSON and failed. That probe is preserved; it is not a failed proof gate.
The installed diagnostic schema was then inspected and the complete real call
above succeeded. No required final gate failure is hidden.

## Cache preparation versus delivery

The required ship-cache.sh was run in documented --dry-run preflight mode with
SHIP_ALLOW_HEAD=1 for the assigned branch,LAKE_CACHE_DIR pointing at the actual
VM cache,and a private SHIP_STATE. It found1947 artifacts(2.19 GB),653 mappings,
zero unresolved traces,then exited1 because coordinator polling state is absent.
The installed script is coordinator-to-lane; its VMEXEC and batch catalog are
also absent in the execution context. Current fetched master contains the exact
same script. No destination was invented and no transfer was performed.

The failure receipt is evidence/h35-cache-receipt.json. It explicitly has no
successful delivery receipt. A verified local asset is prepared at
/workspace/sol-numeric-literals-h35-owned-cache/owned-cache.tar.gz:
126 artifact files,42 mappings,all 42ownedmodules. Every artifact hash and size
matches the required script's shipment manifest,and archive contents were
re-read and verified. The archive is14150989 bytes, SHA256
24587e1ae5f27f1c56de497d0647a2455d928bd0384c77a16893e7229e3cdd5d.
This asset is NOT cache shipping and does not satisfy the delivery gate.

Q-H35-SHIP1 [H35;ship-cache.sh;h35-cache-preflight.log]: which supported transport
and configuration will produce the required cache-delivery receipt?
1. Supply a supported VM-side invocation and destination configuration,then
   rerun the required tool and verify actual delivery.
2. Supply coordinator-side retrieval and required ship-cache invocation for
   the prepared archive,then return a verified delivery receipt.
No option waives H35. No new checkpoint is reported done while this is open.

Original immutable packets remain unchanged. New validation files are confined
to the assigned tests directory. The original goal was not created or reset.

The additional PrintAllAxioms.lean gate executes #print axioms on all 808
theorem constants, including generated equations and private helpers, by their
actual Lean Names. Complete output: 808 unique messages, 25.581 seconds, no
errors. The validator checks every printed axiom set against the full inventory.
No new proof declarations are added by either print file.

Final separate finder and skeptic reviews PASS for the H35 gate and cache
preparation code, including all 808 actual theorem prints. Neither used Lean
server or wrote files. Both independently verified the complete cache archive
(including its metadata) and confirmed no cache delivery receipt exists.
See evidence/h35-reviews.json. The transport question remains open.

Default completion now enforces H35: it revalidates both print outputs and
all four VM source/resource records, then actually runs non-dry ship-cache.sh.
A new current-head shipment with nonempty all-ok receivers is required. Missing,
skipped, failed, stale or dry-run receipts cannot satisfy completion. The local
implementation flag does not run shipment or claim completion. The controls
were rerun after this enforcement change and pass. Transport is still blocked.
