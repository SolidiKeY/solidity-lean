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
