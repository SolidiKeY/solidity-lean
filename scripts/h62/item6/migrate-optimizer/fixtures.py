#!/usr/bin/env python3
"""Check canonical fixtures import real optimizer modules; never copy definitions."""
from pathlib import Path
import re
ROOT = Path(__file__).resolve().parents[4]
D = ROOT / "tests/h62/item6/migrate-optimizer"
for name in ["Acceptance.lean", "Interfaces.lean"]:
    text = (D / name).read_text()
    assert "import Solidity.Optimizer.Controls" in text.splitlines(), name
    assert not re.search(r"^(?:abbrev|def|structure|theorem) (?:Pass|Preserves|Validator)\b", text, re.M), name
for name in ["Generic.lean", "Isolated.lean"]:
    assert not (D / name).exists(), f"copied-definition fixture must remain archived: {name}"
print("Canonical fixtures import Solidity.Optimizer.Controls; no copied definitions or per-case copies.")
