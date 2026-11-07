| `Evm/MemoryLoopHorizonObjectHeapGrowth.lean` | Actual allocating-body heap extension and exact initial-length-plus-count growth through scope exit. |
| `Evm/MemoryLoopHorizonObjectHeapControls.lean` | Existentially witnessed selected-loop execution with matched object count and cursor observations. |
| `Evm/MemoryLoopHorizonObjectHeapKeeps.lean` | Original typed objects survive actual empty-array allocation prefixes. |
| `Evm/MemoryLoopHorizonObjectHeapTypes.lean` | Exact typed source heap history for the empty-array allocating body. |
| `Evm/MemoryLoopHorizonObjectLiveCells.lean` | One actual reached machine preserves the explicit original typed live-cell footprint of the allocating loop. |
| `Evm/MemoryLoopHorizonObjectNewArrays.lean` | Initialization of newly appended uint arrays in the actual allocating loop. |
| `Evm/MemoryLoopHorizonObjectNewInventory.lean` | Inhabited inventory of the actual allocating loop's new uint arrays. |
| `Evm/MemoryLoopHorizonObjectNewSeparation.lean` | Pointer separation for actual finite allocating loop executions. |
| `Evm/MemoryLoopHorizonObjectNewSeparationControls.lean` | An inhabited two-turn control for distinct freshly allocated arrays. |
| `Evm/MemoryLoopHorizonObjectOldElements.lean` | Physical preservation of live payload cells in original dynamic or fixed arrays across the actual empty-array allocating loop. |
| `Evm/MemoryLoopHorizonObjectOldHeaders.lean` | Physical preservation of every original dynamic-array header by the actual allocating loop target. |
| `Evm/MemoryLoopHorizonObjectOldStructs.lean` | Actual allocating target execution preserves encoded primitive and reference fields in original typed struct objects. |
| `Evm/MemoryLoopHorizonObjectRetainedNew.lean` | Retention of arrays created before a finite allocating-loop pause. |
| `Evm/MemoryLoopHorizonObjectCheckedNested.lean` | Checked typed nested read selection after allocating-loop execution. |
| `Evm/MemoryLoopHorizonObjectCheckedReads.lean` | Checked typed read selection after actual allocating-loop execution. |
| `Evm/MemoryLoopHorizonObjectLocalAlias.lean` | Actual initialized memory locals survive the allocating loop. |
| `Evm/MemoryLoopHorizonObjectLocalAliasControls.lean` | Inhabited stored-local aliases across genuine allocating-loop execution. |
| `Evm/MemoryLoopHorizonObjectLocalBounds.lean` | Exact bounds reverts for loads through retained initialized array locals. |
| `Evm/MemoryLoopHorizonObjectLocalLoadControls.lean` | Inhabited success and bounds-revert observations after allocating loops. |
| `Evm/MemoryLoopHorizonObjectLocalLoads.lean` | Actual target loads through retained initialized array locals. |
| `Evm/MemoryLoopHorizonObjectLocalReads.lean` | Reads through actual initialized array locals after allocating loops. |
| `Evm/MemoryLoopHorizonObjectLocalRefLoads.lean` | Actual reference-valued loads through retained array locals. |
| `Evm/MemoryLoopHorizonObjectNestedBounds.lean` | Exact parent- or child-stage bounds reverts after allocating loops. |
| `Evm/MemoryLoopHorizonObjectNestedControls.lean` | Inhabited nested read success and two bounds-failure stages. |
| `Evm/MemoryLoopHorizonObjectNestedLoads.lean` | Actual nested loads through a retained parent local after loop allocation. |
| `Evm/MemoryLoopHorizonObjectRetainedRefs.lean` | Typed identities and pointer values retained across actual allocating loop resumption. |
