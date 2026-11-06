| `Backend/MemoryCopies/FixedReferenceLiveInterface.lean` | Signature-only live normalization contract for all fixed primitive-array children, retaining original copy/representation despite storage shadows. |
| `Backend/MemoryCopies/FixedReferenceLive.lean` | Inhabited intrinsic live normalization preserving exact original storage copy, representation and stripped contents for arbitrary child shadows. |
| `Backend/MemoryCopies/FixedReferenceLiveControls.lean` | Arbitrary-shadow, zero/long/many controls and represented fixed-parent execution retaining original copied heap and stored shadows. |
