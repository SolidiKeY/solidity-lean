
| `**/*Controls.lean` | Library membership (t2-controls-off-path, H627): a `*Controls` module that no library module imports is in the default-target `SolidityControls` library (root `SolidityControls.lean`); the others stay in `Solidity`. `scripts/coord-tools/controls-classify.py` classifies them and `register.sh` writes both roots. |
