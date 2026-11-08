| `tests/h62/item4/generic-v08/IntrinsicWidthsV2.lean` | Explicit-mapFree fixed-bytes width consumers; isolated checker `scripts/h62/item4/generic-v08/check-width-v2.sh`. Frozen v1 headers remain unresolved; this test proves no historical correspondence or execution adequacy. |

The v2 checker uses the pinned toolchain and unchanged serial resource limits.
Its explicit `mapFree` consumers neither import nor certify the frozen original
module. Predicate independence compares two current-signature calls only.
The five original headers remain unresolved. Missing dirty work and unrecovered
historical validation remain UNVERIFIABLE under H151.
