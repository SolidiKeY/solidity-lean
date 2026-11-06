# V07 local-family feasibility backfill

IntegerLocalFamilyWitness.lean guards two regressions: equal contents are not
alias reflection, and an empty index domain is not an informative joint witness.
The general positive lemma constructs both family fields over two distinct slots
for arbitrary bounded integers and existing Source/target local carriers. Its
negative control has equal values but collapses the target positions and proves
that the alias field cannot hold.

The imported IntegerLocalFamily.write theorem is applied to that same family.
An exact-copy lemma retains both full local carriers. A concrete u8 witness uses
a nonempty Boolean index domain and values7/9, and inhabits all14 leading inputs
of the current write telescope. A private typed signature guard fails if the
imported telescope changes. These are local-state results, not global producer
feasibility, whole-compiler totality/success or a full V07 interface audit.

Masterf160e517f was fetched and inspected before this item; no existing witness
module was present there. The unchanged import built in10.575s. The guarded
module passed the serial per-file check in1.561s on liveLean4.24.0 under the
existing12GiB/no-swap/4GiB-reserve envelope. All five printed theorem axiom sets
contain only propext/Classical.choice/Quot.sound. Finder and skeptic read-only
reviews passed. Exact commands/logs are outside Git at:
/workspace/sol-numeric-literals-gate-output/v07-family-import.json and
/workspace/sol-numeric-literals-gate-output/v07-family-witness-guarded.json.
No producer source, existing statement, proof budget or G07 pin was changed.
