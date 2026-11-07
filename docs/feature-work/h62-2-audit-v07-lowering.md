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

## Condition contract nonvacuity

The existing controls already demonstrate assignment success. The new
ConditionContractWitness.lean reuses their exact model and relations rather
than reproducing those controls. Its general theorem proves that any public
Condition for a local Boolean assignment cannot reject every target input:
initial_nonempty supplies an actual aligned input, intrinsic Boolean values
supply the choice, Source assignment completes at horizon two, and the unchanged
success field forces a successful target result. No extra feasibility premise
is added. A concrete tuple jointly supplies the producer, alignment and completed
Source run. The horizon control distinguishes timeout at zero from completion
at two; this concerns evaluation horizons, not EVM gas or global termination.

The module passes the bounded per-file gate in2.062s; its six printed theorem
axiom sets use only the standard three axioms. Finder and skeptic reviews pass.
Logs remain outside Git at v07-condition-contract-general.json and
v07-condition-contract-general-files/1.log in the gate-output directory.
This covers the specified expression shape, not admission, a full condition
producer, whole compilation, or the complete V07 interface census.


## Pair-assignment family feasibility

IntegerPairFamilyWitness.lean audits the imported IntegerLocalFamily.assign_pair
contract using three distinct slots. For either pipeline, one concrete tuple
jointly inhabits all 23 telescope entries and derives the actual postfamily.
A private typed guard checks the complete imported signature. General lemmas
retain arbitrary bounded integers and both existing local carriers, distinguish
legacy and viaIR effects when operand reads differ, and demonstrate that the
two destinations may alias. Only the original first-destination/second-RHS
separation premise is required.

Master 2a43bf4fc was fetched and inspected before this item. The import gate
passed in 14.077s, including KeySort and actual tool versions. The final guarded
module passed in 2.083s with serial Lean 4.24.0, 12GiB/no swap and the existing
4GiB headroom guard. Its seven printed theorem axiom sets contain only the
standard three axioms; source_orders_differ is axiom-free. Logs are outside Git
at /workspace/sol-numeric-literals-gate-output/v07-pair-family-guarded.json and
the corresponding guarded-files/1.log. These are local-carrier feasibility and
order results, not whole-program termination, gas, compiler success, or a full
V07 census. Production sources, frozen statements and budgets are unchanged.

Independent read-only finder and skeptic reviews passed with no findings; neither
reviewer used Lean or a server. The global documentation check retains the three
previously routed Theory/StructuredFlow missing references.


## Reached-RHS separation boundary

PairSeparationBoundary.lean guards removal of the existing pair separation
premise by executing the actual assignAssignPrefix with the first destination
equal to the second RHS. For arbitrary legal integer widths/signs and bounded
values, viaIR captures x twice after overwriting the RHS; legacy captures its
initial z twice. When x differs from z, the completed prefix runs differ by an
observable captured local. The premise is inhabited, for example by u8 values
7 and 9. This is a boundary of the operational prefix theorem, not a claim that
IntegerLocalFamily.assign_pair itself fails without separation.

Master 94f9862b6 was fetched, inspected and merged before implementation; no
corresponding audit was present. The final serial Lean 4.24.0 per-file check
passed in 1.583s under the unchanged 12GiB/no-swap/4GiB-reserve policy. Four
printed theorem axiom sets use only propext, Classical.choice and Quot.sound.
An intermediate output-projection type error was repaired by supplying the
explicit intrinsic output type; its failed log remains preserved. Independent
read-only finder and skeptic reviews passed without findings or Lean/server use.
Logs are /workspace/sol-numeric-literals-gate-output/v07-pair-separation-checked.json
and the corresponding checked-files/1.log. These local completed-prefix results
do not establish gas, compiler totality, or a full interface census. No producer,
frozen statement, budget, axiom set or exclusion was changed.


## Assignment-family execution binding

AssignmentFamilyExecutionWitness.lean connects the existing two-slot value/alias
family to assignment_family_transport. Its general theorem supplies the family
on the same initial Source state and target state used by the actual runs, and
derives both successful executions and the postfamily together. It covers every
legal integer type, bounded pair of values, and either choice of written/RHS slot,
with arbitrary Source world/frame and target base. A separate existing-model u8
7/9 tuple inhabits the environment, globals, frame, world, target and family
inputs together. The reject-all control uses an actual successful target run.
No relation between arbitrary global worlds is asserted.

Master 94f9862b6 was fetched and inspected before this item. Serial bounded Lean
4.24.0 passed in 57.633s, including rebuilding uncached imports of the existing
concrete world example. The three printed theorem axiom sets use only the
standard three axioms. This is not a comparable before/after timing or a full
runtime gate. Finder and skeptic read-only reviews passed without findings;
neither used Lean/server. Exact evidence is outside Git at
/workspace/sol-numeric-literals-gate-output/v07-family-execution.json and
v07-family-execution-files/1.log. Local successful assignment is not whole-program
termination, compiler totality, gas or a complete V07 interface census. No
production statement, definition body, proof budget or G07 pin was changed.
