# VY4 peer consumer compatibility

Existing owned PeerMemoryAgreement, PeerCreationAgreement and PeerWorldAgreement
are consumed unchanged from `0323f894c2d41a58aed940ee2caa97695dc09a0e`.
The actual published compilation memory harness is used. The single missing
producer, Backend.AbiWorld.WorldFrames, is read-only exact bytes from verified
V13 `66c08fdefbbb53c0eee111b09d1baa6277fedff5`; its bundle SHA256 is
`e5c3cc2ecaa093e32ad3a464eb10eaa4f65ff2d3154c8ec93a8762ba83bf2ee8`.
No Source or producer implementation is changed.

All eleven additional per-file checks pass. Generated signatures/axioms check
17declarations and12standard-only theorem reports. Actual target byte writes,
copy framing, unrelated persistent/transient account framing and heterogeneous
journal rollback are derived from the real imported exports. Initcode outcomes
remain explicitly scripted: creation-address/dataflow tests are not executable
initcode, reachable callbacks, Source/compiler or world adequacy.

Initial HEAD-ref fetch failed because the bundle exposes a named branch; the
exact named ref fetch succeeded. The initial per-command exit was not separately
captured by its surrounding shell; this is not relabeled success. All evidence
and the corrected successful command are retained. Independent read-only finder
and skeptic reviews report no findings. Full original lane/final gates remain
open; V08 P15 CTOR/SS-NEW plus VY5 H16 and G51 effect embedding are required.
