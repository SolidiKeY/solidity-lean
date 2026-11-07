# VY5-owned V16 assembly correctness consumers

H10 assigns this instance-construction work to VY5 while V16 works on G18/P8.
Development is on the existing help branch; no other owner's implementation is
changed. Actual G01 contracts are reused, with identical source hashes to the
previously staged V16 dependency closure. No new AST, evaluator or IR is defined.

## Interface and proved construction

`Solidity.Yul.Composition.CorrectnessInstances.Stages S I Asm V` contains the
actual `Admission S`, `Lowering S I`, `Compilation I Asm` and `Execution Asm V`.
Each contract includes its real proof fields. Constructing Stages does not supply
missing assembly producers: none are postulated, synthesized or axiomatized.

- `compileAt` computes the frontend result and emits through the registered
  lowering/compiler/assembler bodies. Exact admission coverage follows from the
  actual frontend soundness/completeness; no fragment predicate is introduced.
- `need` names the nested bound of the three certificates. `forward`, `backward`,
  `refines` and `completed` retain Allowed/Admissible/Forward/Guard premises and
  preserve the complete ordered Prefix, including all success/revert bytes.
- The source reads an artifact table. `Linked` and `TablesLinked` explicitly
  require emitted bytes to be that table; compilation does not silently identify
  them or use choice to solve the linking fixed point. `compiler` is executable
  given a table generator; `specTransfer` derives G01's actual SpecTransfer only
  with all stage certificates and this linking proof.
- `PublicBoundary` retains both-pipeline coverage, fixed/session agreement,
  creation-table provenance, source-determined hash/slot preimages, decoded-world
  reachability and cumulative-hash resumed refinement. `publicCorrectness`
  constructs G01's actual PublicCorrectness record, deriving admission coverage,
  environment surjectivity and full execution refinement from the stages. It
  does not take PublicCorrectness itself as a premise.

Controls use G01's existing toy SourceSpec/IntrinsicSpec/EvmSpec, actual encoding
and decoding, with concrete stage certificates and linked tables. Full nonempty
success and revert bytes, malformed admission, same-length wrong payload,
always-revert artifact and stale table are discriminating kernel controls under
both pipeline settings. The public-constructor control reuses the existing toy
public theorem only for its residual boundary facts; this is a compatibility
check, not new assembly execution evidence.

## Exact remaining premises

Concrete admitted assembly SourceSpec/frontend/raw session dispatch and semantics
remain VY1 inputs; physical allocation/layout/MemOK/refinement remain VY2 inputs;
concrete lowering/compilation/opcode/pass certificates remain VY3 inputs; unified
log/emit observation/G01 and raw world/frame coupling remain VY4 inputs. G01's
existing Event type has not been amended here: the required unified log/emit
extension is still open. Compiler artifact-table linking and actual decoded-world
facts must be proved for those exact bodies. SourceSpec.Approved,
EvmSpec.Approved, Fixed.Keccak and nonvacuity remain separate final obligations.
No conditional result is registered as a concrete assembly producer proof.

All24 original full Y10 obligations and six general Source combinations remain
open; fullProofGate=pending. HOST1's separate56-call finite native evidence is
not a premise or proof of any Lean theorem here. No native fixture is rerun for
this kernel-only change. Original docs/G03 failures and strict native journal
failure remain preserved; zero regression never means those gates pass.

## Checked checkpoint

All four modules and the registered Solidity root pass per-file MCP diagnostics.
Actual Lean4.24.0 / Lake5.0.0-src+797c613; passing KeySort, registered1179-job
build and286-job SolkeyTestSuite, sort annotations377/131/131, strict491 automatic /
61 budgeted /0 manual /11 refuted /0 pending, complete-input trust1231sources /
258 inventoried sites /0 findings. Strict classification does not check cumulative
timing. All42 scoped declarations use only propext and Quot.sound (or none),
with no sorryAx. Read-only finder and skeptic accepted the actual sources/docs.

The first joint command failed from build-only flags on the version query;
the next failed from server-only flags on a build command. The complete source
run then failed only at trust because the container had no git/file list. The
next composite failed only at a standalone artifact-cache-unaware signature
probe. These remain failed invocations. Corrected host-generated complete trust
input and Lake's setup-aware lean command produce final-policy-v2 EXIT0.
Raw logs/resource receipts and all failures are retained under
/workspace/vy5-composition/evidence/correctness-instances-20261102-*.
Both-pipeline admission is not an assertion that pipeline outcomes are equal.
Concrete table generators and certificate bounds still need their own
computability/provenance audit. No new native comparison is claimed.
