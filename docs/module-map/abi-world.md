<!-- Generated from docs/module-map/abi-world.d/ by scripts/coord-tools/fragments.sh; edit the fragments there, not this file. -->
# ABI packet consumers

These modules provide component observations; presence does not establish full ABI compilation.

| Module | Content |
|---|---|
| `Backend/AbiWorld/ErrorLayout.lean` | Existing Error codec layout/padding and plain List append identities. |
| `Backend/AbiWorld/ErrorRoundtrip.lean` | Existing Error decoder readback under explicit length bounds. |
| `Backend/AbiWorld/ErrorReadWindow.lean` | Complete unpadded Error reason and suffix readback. |
| `Backend/AbiWorld/ErrorReadWindowControls.lean` | Inhabited Error windows and malformed/boundary observations. |
| `Backend/AbiWorld/ErrorOffsetWindow.lean` | Existing Error decoder offset windows, including unaligned offsets. |
| `Backend/AbiWorld/ErrorOffsetWindowControls.lean` | Offset, overlap and ordered packet controls. |
| `Backend/AbiWorld/PanicReadWindow.lean` | Full-word Panic readback and constant terminal emission. |
| `Backend/AbiWorld/PanicCallFrame.lean` | Actual typed call/try-call Panic binding and local dropping. |
| `Backend/AbiWorld/PanicCallFrameControls.lean` | Populated Panic call frames and selector/truncation controls. |
| `Backend/AbiWorld/LibraryResultPacket.lean` | Existing uint/bytes heterogeneous result codec layout. |
| `Backend/AbiWorld/ReturnWordTransport.lean` | Indexed uint values, complete word readback and bounded known-packet emission. |
| `Backend/AbiWorld/ReturnWordTransportControls.lean` | Full-word, explicit-count, truncation and ordered-output controls. |
| `Backend/AbiWorld/PacketPrefix.lean` | Prefix execution of the existing constant-packet emitter. |
| `Backend/AbiWorld/PacketPrefixControls.lean` | Byte, push and terminal boundaries with populated stack controls. |
| `Backend/AbiWorld/CallerWordBytes.lean` | Explicit restored word-cell and physical byte-frame observations. |
| `Backend/AbiWorld/CallerWordBytesControls.lean` | Inhabited full-word caller-frame byte controls. |
| `Backend/AbiWorld/CheckedAddArtifact.lean` | Existing checked-add test, Panic emitter and success body assembled with explicit layout bounds and jump relocation. |
| `Backend/AbiWorld/CheckedAddArtifactControls.lean` | Kernel bounded-assembly witnesses and wrong-label controls; complete byte-layout observations, not branch execution. |

See [ABI packet consumers](../feature-work/abi-world-packets.md) for proof boundaries.

| `Backend/AbiWorld/NativeParentWord.lean` | Actual recovered native-parent counter connected to existing full-word ABI encoding and explicit-count byte readback. |
| `Backend/AbiWorld/NativeParentWordControls.lean` | Populated native-entry application and separately labeled caller-counter/word-boundary codec controls. |

| `Solidity.Backend.AbiWorld.MutatingEntryWords` | Ordered full-word codec observation of actual mutation and allocating child frame entry. |
| `Solidity.Backend.AbiWorld.MutatingEntryWordsControls` | Inhabited entry application, stale/order/heap-preservation negatives and complete codec vectors. |

| `Solidity.Backend.AbiWorld.MutatingWritePhysical` | Actual selected mutation prefix and P6 initial-frame physical byte-store consequence, with explicit scaled span. |
| `Solidity.Backend.AbiWorld.MutatingWritePhysicalControls` | Populated initial physical frame, actual write/neighbor application and scale/bound negatives. |
| `Correctness/Lowering/Loops/Family.lean` | Loop-lowering family: shapes, output association, endpoint and the `LowerLoopsCorrect` statement. |
| `Correctness/Lowering/Loops/WhileBreak.lean` | While/break leaf: generic flag-loop target run plus G19 Source half. |
| `Correctness/Lowering/Loops/Correct.lean` | `lowerLoops_correct` and kernel acceptance of actual producer outputs. |
| `Correctness/Lowering/Loops/ForBreak.lean` | For/break leaf: generic flag-loop target run with a never-run update, plus G19 Source half. |
| `Correctness/Lowering/Loops/Capture.lean` | Actual `lowerLoops` + `elabStmtsP` outputs for the loop-family samples, quoted. |
| `Correctness/Lowering/Loops/Horizon.lean` | Identity conversions in `while`/`do` conditions and bodies cost one Source horizon (monotonicity transport). |
| `Correctness/Lowering/Loops/WhileContinue.lean` | While/continue leaf: two-path flag-loop target run plus G19 Source half through the horizon transport. |
| `Correctness/Lowering/Loops/DoBreak.lean` | Do-while/break leaf: first-flag loop with short-circuited condition, plus G19 Source half. |
| `Correctness/Lowering/Loops/WhileReset.lean` | While leaf with a resetting body: two-path flag-loop target run plus G19 Source half. |
| `Correctness/Lowering/Loops/DoContinue.lean` | Do-while/continue leaf: one-turn first-flag loop plus G19 Source half. |
| `Correctness/Lowering/Loops/ReturnFamily.lean` | Function-level return family (H497): shapes, outputs, return-witness endpoint and statement. |
| `Correctness/Lowering/Loops/Returns.lean` | While/do-while return and if-return leaves at function level, plus G19 Source halves. |
| `Correctness/Lowering/Loops/Statement.lean` | `LowerLoopsCorrect`: the normal-outcome and return families together. |
| `Correctness/Lowering/Checker/Contract.lean` | P1 inventory and unfrozen candidate checker contract. |
| `Correctness/Lowering/Checker/IntrinsicProbe.lean` | Actual intrinsic elaboration capture for the bounded while/break probe. |
| `Correctness/Lowering/Checker/MeasuredPilot.lean` | Exact singleton soundness/completeness and measured contract-body refusal. |
| `Correctness/Lowering/Checker/RawProbe.lean` | Actual lowerLoops capture, total raw matcher and refusal controls. |
| `Correctness/Lowering/Checker/SourceAssociation.lean` | Resolved Source conversion and horizon transport for the bounded probe. |
| `Correctness/Lowering/Checker/WhileBreak.lean` | Actual-output mapped semantic leaf with explicit fixed-state boundary. |
| `Backend/AbiWorld/PublicCompilerTotal.lean` | H62/H69 compiler-success theorem: the public `Compiler.compile` accepts every program of a stated subset of the core fragment (H87/H96: signed bitwise, plain and array-indexed aliases with a per-alias kind judgement, storage `op=`) through its core branch, and `Compilation.Agrees` holds there. |
| `Backend/AbiWorld/PublicCompilerTotalControls.lean` | Inhabited alias/storage-`op=`/signed-`&`/loop/call program accepted by the theorem and by kernel evaluation; indexed-alias program with fresh-machine witness; self-balance, int-key, kind-change and unset-alias refusals. |
| `Backend/AbiWorld/P1RevertBridge.lean` | H68 P1-REVERT: `p1_revert_bridge`, a `BridgeGoal` over V12's `RuntimeFrameP1LangV2` for the public compiler's output on every assert-free statement of the totality domain; frame agreement and version-2 bare-revert transport. |
| `Backend/AbiWorld/P1RevertBridgeControls.lean` | Fresh-contract reverting entry and succeeding input through the bridge; `assert(false)` panic-data mismatch showing why `assert` is excluded. |
