| `Backend/MemoryCopies/SnapshotRestoreInterface.lean` | Contract only for typed captured-array copy-back after an explicitly executed memory-preserving intervention, with reached-store cleanup and framing. |
| `Backend/MemoryCopies/SnapshotRestore.lean` | Proved typed captured-array restoration after an explicit memory-preserving intervention, with reached-old cleanup and reached-store framing. |
| `Backend/MemoryCopies/SnapshotRestoreControls.lean` | Executed length-changing storage intervention on empty, pair and 64-element captures; actual captured-memory write refutes preservation. |
