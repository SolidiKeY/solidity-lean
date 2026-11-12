
| `**/*Controls.lean` | Library membership (t2-controls-off-path): every `*Controls` module is in `Solidity`. `scripts/coord-tools/controls-classify.py` lists those no library module imports; `REGISTER_CONTROLS_SPLIT=1 register.sh` (off by default) would move them to a `SolidityControls` root once CI and the axiom audit cover it. |
