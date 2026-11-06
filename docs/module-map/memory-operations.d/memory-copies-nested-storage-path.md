| `Backend/MemoryCopies/NestedStoragePathInterface.lean` | Contract only for actual dynamic-outer storage path copying and intrinsic declaration/rebinding, full post-state/allocator and machine refusal. |
| `Backend/MemoryCopies/NestedStoragePath.lean` | Proved actual dynamic storage paths, exact live demand/growth, checked copy and intrinsic declaration/rebinding with full typed local transport. |
| `Backend/MemoryCopies/NestedStoragePathControls.lean` | Populated dynamic parent/child alias controls for copy growth, declaration, rebinding, empty/long children and machine capacity refusal. |
