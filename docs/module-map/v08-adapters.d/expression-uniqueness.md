| `Backend/PrimitivePackets/SignedCheckedMul/Source.lean` | Checked int256 `*` Source evaluation on arbitrary locals: exact value or `Panic(0x11)`. |
| `Backend/PrimitivePackets/SignedCheckedMul/Selected.lean` | The public compiler selects `binaryCode .int .mul`, with the literal `sTail .mul` guard. |
| `Backend/PrimitivePackets/SignedCheckedMul/Target.lean` | Selected checked int256 `*` execution on any represented machine and saved stack: product or coarse revert. |
| `Backend/PrimitivePackets/SignedCheckedMul/Agreement.lean` | Source and selected target of checked int256 `*` from one local family. |
| `Backend/PrimitivePackets/SignedCheckedMul/Controls.lean` | Populated-frame, arbitrary-stack controls: both orders of `-2^255 * -1`, lower/upper overflow, regular products. |
