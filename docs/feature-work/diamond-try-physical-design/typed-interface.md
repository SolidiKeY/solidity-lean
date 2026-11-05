# Proposed intrinsic interfaces (DESIGN, no declarations implemented)

The following signatures are reviewable Lean-like schemas, NOT compiled Lean,
axioms, sorry scaffolding, imported code or a claim all referenced obligations
already exist. Every new name here is proposed; existing names are identified
in README/proof-plan. No global State/Stmt/Fml/ValidT/inTarget change is proposed
for the proof-only first milestone. Later source admission is a separate decision.

## Data, bounds and frame-visible ownership

`U256 := PrimTy.uint.Denote` is the existing intrinsic unsigned word, not an
untyped integer. `nat u` uses its nonnegativity/range proof. Byte cells hold
UInt8. Input addresses/lengths are U256; natural end=nat offset+nat length is
NOT modular addition. Capacity is a Nat witness, not fuel, gas, test budget or
a new global bound. Capacity may exceed2^256 in a *representation request*;
normal feasibility/engine gas must be proved separately. No wrapped end is
accepted as a shorter slice. Zero length neither expands nor dereferences its
offset, even if that offset is outside the resident prefix.

```text
structure ByteSpan (capacity : Nat) where
  offset length : U256
  fits : nat length = 0 ∨ nat offset + nat length ≤ capacity

structure WordSpan (capacity : Nat) where
  offset : U256
  fits32 : nat offset + 32 ≤ capacity

structure FrameKey where
  invocationId : Nat
  depth : Nat
  sourceContract : ContractIdentity
  sourceDeclaration : DeclarationIdentity
```

Identities above carry exact bundle/source/declaration provenance, not variable
labels in Γ. Invocation identity is proof/runtime metadata; equal call depth is
NOT enough to identify sibling frames. No identity is picked from expected EVM
bytes. Source/compiler bundle identities are parameters of certificates, not
new context indices or runtime contract fields.

```text
FrameReach (σ : State C Γ) {R : RefTy} (r : HRef σ.H R) : Prop
```

FrameReach is to be defined by roots at actual typed memory positions
`Idx Γ (.mem R)` with TEnv lookup=some r and typed MPath/heap reachability from
those roots, including explicit return slots. It is NOT arbitrary heap membership.
A self external callee with scalar size/no reference results has no incoming
visible memory roots although current typed TRun.call may retain caller heap
objects. Those unreachable HRef values must NOT be laid out in fresh callee
physical memory. Distinct external frames have disjoint physical images; source
internal-call alias semantics are different and cannot be silently reused.

```text
structure Layout (σ : State C Γ) (f : FrameKey) (capacity : Nat) where
  base : ∀ {R}, (r : HRef σ.H R) → FrameReach σ r → U256
  repr : ∀ {R} r hr, ObjectBytes R (σ.heap.get r) (base r hr) ...
  alias : equal typed object identities have equal bases
  separated : distinct mutable owned objects occupy disjoint footprints; only proven read-only empty-sentinel views may share the reserved zero slot
  reserved : mutable Owned/allocated Pending footprints avoid reserved live compiler regions; a proven read-only EmptySentinel view of the zero slot is allowed
  pending : exact caller/return-slot ownership and allocation status

structure FrameMem (C : Contract) (Γ : Ctx) where
  st : State C Γ
  key : FrameKey
  capacity : Nat
  data : Fin capacity → UInt8
  highWaterWords : Nat
  layout : Layout st key capacity
  protocol : LayoutProtocol layout data highWaterWords
```

ObjectBytes is computed by RefTy/field order (not an untyped object sum).
For these rows only packed bytes/string objects are needed: length word at base,
actual byte payload at base+32, allocation-rounded padding. RefTy bytesR is an
array of uint; require a byte-bounded/projection relation, not the false assumption
that every intrinsic uint element is already≤255. A materialized snapshot uses
existing byteWord and therefore supplies that bound. Arrays of uint in the
existing EVM word compiler are *not* automatically packed bytes arrays.

Protocol distinguishes valid allocator/free-word/zero-slot facts from raw
write permissions. It is a data+proof record, not a new global semantic target.
After Error stores overwrite byte64..95, allocator validity is **invalidated**;
only snapshot-and-halt is permitted until a restoration theorem, which these
callee bodies do not need. No proof is retained merely because source heap is
unchanged. Zero-slot writes96..99 must be proved to write zeros for this exact
Error word, not justified by disjointness. Scratch updates preserve typed heap/
env/storage while possibly invalidating physical compiler-region facts.

## Exact byte operations and typed capture

These are pure, typed image operations/proof relations, not a new Yul/EVM
instruction interpreter or untyped IR. A future implementation must obtain
operands from `Val C Γ p` or typed Idx values; AST JSON is only elaboration-time
provenance and never an erased runtime term/state.

```text
expandZero : (μ : FrameMem C Γ) → (neededEnd : Nat) →
  ExpansionWitness μ neededEnd → FrameMem C Γ
store32 : (μ : FrameMem C Γ) → WordSpan μ.capacity → U256 →
  StorePermit μ → FrameMem C Γ
load32 : (μ : FrameMem C Γ) → WordSpan μ.capacity → U256
snapshot : (μ : FrameMem C Γ) → (s : ByteSpan μ.capacity) →
  { d : List UInt8 // d.length = nat s.length }

structure ReturnSlice (d : RevertData) where
  sourceOffset length : U256
  inBounds : nat sourceOffset + nat length ≤ d.length
copyReturnData : (μ : FrameMem C Γ) → (d : RevertData) → ReturnSlice d →
  DestinationSpan μ → StorePermit μ → FrameMem C Γ
```

store32 writes big-endian byte j at a+j for0≤j<32, including unaligned offsets;
all other cells and logical state unchanged. load32 is its inverse for exactly32
bytes. expandZero preserves old bytes and appends zeros; it rounds high-water
only for actual nonempty access, not capacity proof bookkeeping. Read/slice beyond
old high-water expands zero memory if feasible, not a read failure. No implicit
word alignment. copyReturnData copies **actual immutable return bytes**; invalid
source range is a target exceptional-outcome obligation, not zero padding.
CALLDATACOPY has a different zero-padding rule and is not conflated with it.
For an overlapping same-frame object copy, use a pre-copy snapshot (memmove law)
and prove same-alias versus fresh-copy identities; generic MCOPY support is not
claimed needed/implemented. A byte32 scratch write cannot silently overwrite an
owned typed object's header/value and leave ObjectBytes valid.

```text
structure AllocationWitness (μ : FrameMem C Γ) (n : U256) where
  allocatorReady : valid free-pointer and required zero-slot facts
  aligned : free pointer divisible by32
  checked : exact pinned solc overflow/uint64 guard succeeds
  endCapacity : rounded allocation fits a justified expansion
  freshRegion : disjoint from all frame-visible live objects

allocateBytes : (μ : FrameMem C Γ) → (n : U256) → AllocationWitness μ n →
  Σ ν : FrameMem C Γ,
    Σ e : μ.st.H <+: ν.st.H,
      Σ r : HRef ν.st.H bytesR, NewBytesObject μ ν e r n
```

NewBytesObject requires r.id=old heap length, exact default/payload contents,
unchanged old identities via HRef.wk, TEnv.wk agreement and actual physical base
from free pointer. `assignAlias` returns same HRef/base; deep copy allocates a new
identity/base and snapshot-equal bytes. A fresh allocated r need not yet be in Γ. Layout.pending must hold its typed HRef, physical base/footprint and object representation as an explicit allocation result root; a bindPending theorem promotes that root to FrameReach after State.push/TEnv binding. Unreachable old caller objects are never promoted by this mechanism. Separation covers pending regions too.

The current State.allocPush/Grown/Out
machinery is reused, not replaced by an untyped pointer heap.

The snapshot consumer is existing MObj bytes allocation and RevPart.mem:
`snapshotObj σ d : MObj σ.H bytesR`, with elements `d.map byteWord` and length
bound `d.length<2^256`. Proposed `snapshot_capture_exact` uses σ.allocPush of
that object, actual fresh ref/heap extension and existing RevPart.evalT_mem /
TRun.revertData_mem to derive **THalt.ofData d**, including empty d→.revert.
Its input d must be snapshot's computed output, not caller-supplied expected
bytes. The synthetic typed allocation is ghost/compiler-witness materialization;
it must NOT be charged as an extra allocation in the callee EVM execution or
claimed physically present there. The callee EVM returns a raw slice directly.
The separate real caller catch allocation does consume its own memory/gas.

## Source/producer/compiled-run interfaces

```text
structure ArtifactBundle where
  exactOriginalSourceHash compiledInputHash compilerBinaryHash outputHash ...
  pipeline evmVersion optimizer metadataSettings ...
  sourceUnit sourceId calleeDeclarationId callerDeclarationIds ...
  sameInvocation : exact AST/code/source-map/Yul provenance binding

structure StoreShapeCert (b : ArtifactBundle) (C : Contract) (Γ : Ctx) where
  size : Idx Γ (.val .uint)
  calleeSignature : exact f(uint), no returns, pure, exact declaration
  orderedOperations : exact typed operands/offsets/constants and terminal revert
  externalRefs : size identifier resolves to the actual callee parameter
  sourceAndCompilerSpans : exact whole declarations and generated boundaries
  noExtraEffects : checked complete body/entry/continuation shape, not substring

structure EntryWitness (b : ArtifactBundle) (σ : State C Γ)
    (μ : FrameMem C Γ) : Prop where
  logicalState : μ.st = σ
  frameIdentity : same actual invocation/callee/caller/self/value/code bundle
  freshMemory : actual external frame initialization relation
  dispatcher : actual selector/ABI/value checks succeeded before body
  prologue : actual compiled mstore(64,128), not assumed heap layout
  prefix : exact no-intervening-writes/allocator behavior for this shape
```

A concrete code theorem must CONSTRUCT EntryWitness from the actual compiled
entry path under explicit successful-entry conditions, not accept desired tail
bytes as its premise. Shape recognizer soundness must prove every accepted AST
node/operand and compiler boundary; changing source/compiler/settings/decl IDs
requires a new bundle. Hash equality alone is not compiler correctness.

```text
stores_exact : StoreShapeCert b C Γ → EntryWitness b σ μ →
  ∃ ν, TypedStoreSequence b μ ν ∧ ExactFootprintAndStateFrame μ ν
snapshot_exact : TypedStoreSequence b μ ν → ByteSpan ν.capacity →
  ExactSnapshot ν ... (snapshot ν ...)
producer_halt : (shape : StoreShapeCert b C Γ) → EntryWitness b σ μ →
  (n : U256) → TEnv.get shape.size σ.env = n →
  CertifiedFeasibleRange b μ n →
  ProducerTypedRun shape n σ = .error (THalt.ofData (producedSlice shape μ n))
```

ProducerTypedRun is to be a construction in existing intrinsic Prog/Stmt plus
materialization, not the current run of an already-admitted InlineAssembly
statement (there is no such current admission). No new source statement/rule
is smuggled in by naming it. stores_exact computes producedSlice from typed
store semantics; neither EntryWitness nor CertifiedFeasibleRange contains the
claimed equality/result as a field. Feasibility contains actual finite-range/
resource premises, never “it returns desired bytes”.

Compiled/source adequacy remains a separate, nonvacuous theorem:

```text
compiled_producer_correspondence : StoreShapeCert b C Γ →
  EntryWitness b σ μ → ByteExecOfSameBundle b μ outcome →
  ∃ typedOutcome,
    ProducerTypedRun ... σ = typedOutcome ∧
    OutcomeCorrespondence typedOutcome outcome
```

ByteExecOfSameBundle and the MSTORE/MLOAD/expansion/RETURN/REVERT primitive
simulation are NOT current word-machine theorems. Their precise missing owner is
published G46.02/R31 (see proof-plan); no abstract assumption with no possible
producer counts as a completed proof. Finite engine receipts are tests, not this
theorem. Source admission/CLI automation requires an additional reviewed
certificate consumer and policy decision; none is implemented or authorized now.

OutcomeCorrespondence must enumerate normal return, actual data revert, decoded
panic/error, argument/dispatch failure, target exceptional failure, divergence,
resource exhaustion and host stop/refusal separately. Current THalt conversion
for physical gas/OOG/invalid is NOT silently chosen here. Only the actual completed
revert case supplies a producer-halt candidate; reusable original-source hcall additionally requires BoundCalleeFrame transport below. No normal,
exhausted or diverged execution is recast as completed failure; unknown/refused
certificate construction is not an execution verdict or narrowed target.


## Separate actual-callee transport (required before original-source hcall)

ProducerTypedRun is NOT the body already carried by the original try statement.
The kernel call carries its scoped body explicitly; do not invent a runtime
body lookup that current semantics lacks. Source resolution/import closure must
supply its actual referencedDeclaration, native signature and body construction.

```text
BoundCalleeFrame b c sargs rets hs body : Prop
  -- exact resolved source f#7/signature and same bundle/callsite
  -- body : TStep C (rho ++ ps) GammaF, exact imported/captured body
  -- scalar Args evaluation, parameter position, CallRet/Ext/context agreement
  -- kernel-checked body CONSTRUCTION identity with certified producer lowering
  -- original receiver/self=true/caller/self/value/rollback boundary preserved

callee_halt_transport : BoundCalleeFrame b c sargs rets hs body →
  ActualEntryOfCall sigma sargs sigmaIn n →
  (ProducerTypedRun shape n sigmaIn).halt? = some (THalt.ofData d) →
  TRun.call sargs (.rets rets) hs body sigma = .error (THalt.ofData d)
```

All C/Gamma/ps/rho/GammaF are the existing intrinsic call indices, not erased
frames. ActualEntryOfCall is exact Args/CallRet.enterT entry with actual state/
heap/env transport. Body construction equality must be generated/checked against
the whole resolved source closure; it is NOT an assumed hcall or a field merely
asserting the desired run equation. Normal results require a separate frame-exit
relation, not equality between different Out-context types. The halt projection
above avoids such an ill-typed cross-context equality.

Neither byte target correspondence nor producer_halt constructs BoundCalleeFrame
for current refused source. P8's certified source consumer (or equivalent explicit
reviewed source-body representation) must construct it. M1 yields producer halt
and may test a manually constructed typed call/catch, labeled as such; it cannot
yield the original callee hcall, source validity or native source pass until this
transport exists. Wrong-body substitution with the same bytes must fail identity.

The producer preserves raw `THalt.ofData d` even when d decodes as Panic67. It must not normalize a256byte raw halt to `.panic67` and lose its suffix. Decoded Error/Panic are caller handler observations, not replacements for the raw producer halt.


## Specialized Error interior-copy capture (not ordinary allocateBytes)

Generic allocateBytes above is an ordinary length-header-at-free-base operation.
Pinned Error decoding instead returns msg=data+offset inside a larger copied
buffer. It needs its own witness, with no extra physical EVM allocation:

```text
structure DecodeCopyWitness (μ : FrameMem C Γ) (d : RevertData) where
  dataBase : U256          -- actual mload(64), e.g.128 after proved prefix
  copyRange : ReturnSlice d -- source4,count d.length-4, checks ordered exactly
  offset length : U256    -- actual mload values, here32/7
  msgBase : U256          -- exact dataBase+offset, no wrap under guards
  finalizeEnd : U256      -- dataBase+roundUp32(offset+32+length)
  auxiliaryAndObject : disjoint typed ownership within allocated buffer
  failedGuardEffects : exact scratch/copy/high-water effects if decoder returns0

captureReasonFromCopy : DecodeCopyWitness μ d → DecoderGuardSuccess ... →
  Σ ν : FrameMem C (.mem bytesR :: Γ),
    Σ e : μ.st.H <+: ν.st.H,
      Σ r : HRef ν.st.H bytesR, InteriorReasonRepr μ ν e r d
```

InteriorReasonRepr's object base is msgBase, not old free pointer; auxiliary
prefix and dead tail do not become logical heap objects. Physical copy/finalize
steps occur once in the target; logical State allocation is their ghost/source
representation. No second invocation/replay/extra charged allocation. Guard
failure produces no new HRef, yet must preserve target scratch effects and
allocator word if finalize wasn't reached. A result theorem must cover each
ordered guard exit. highWaterWords need not equal or be≤free pointer/32, and
freeTailZero is NOT a general protocol invariant. Scalar Panic code capture
has no heap allocation: selector/panic returndata copies modify caller scratch
0..32 while the actual return buffer remains immutable. Uncaught forwarding
copies exact d then reverts, never normalizes/re-encodes it.


## Default empty-string sentinel is not a fresh physical allocation

Pinned malformed_error viaIR zero_value_for_split_string returns96 (0x60).
Represent default-return HRef objects with a distinct read-only EmptySentinel
role: actual logical length0, physical word[96,128)=0, no payload, no charged
allocation. Multiple distinct logical empty default objects MAY share this
read-only sentinel without identifying their HRef IDs. Same-HRef alias implies
same base; reverse base equality is not universal logical identity. Mutable
Owned regions remain disjoint from each other and the sentinel. An allocated
new bytes(0) with a real own header is a different role, not automatically96.

Layout must therefore carry role-indexed representation witnesses
OwnedObject/EmptySentinel/PendingObject, not require every distinct source object
to own32disjoint bytes. bindDefaultReturn proves the source default slot's
actual HRef and sentinel role. Reads/encoding of length0 agree; indexed write
through empty bytes fails its original bounds check, rebinding changes the
logical reference and does not mutate sentinel. Any direct physical store into
a live sentinel needs proof of zero preservation or invalidates that view.
Callee Error raw stores do not mutate the CALLER's default sentinel: frame keys/
visibility isolate it even if the logical heap H still contains caller objects.
A layout theorem must not claim caller heap empty or share the two byte images.
