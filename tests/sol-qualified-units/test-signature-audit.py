#!/usr/bin/env python3
"""Read-only negative controls for the explicitly scoped H27 evidence audit."""
if not __debug__:
    raise SystemExit("Run without Python optimization.")
import contextlib
import io
import json
from pathlib import Path
import runpy
from unittest.mock import patch
root = Path(__file__).resolve().parents[2]
audit = runpy.run_path(str(root / "scripts/check-sol-qualified-units.py"))["audit"]
original = Path.read_text
def remove_required_base(data):
    row = next(row for row in data["observed"] if row["id"] == "qualified-parameter-overload-gap")
    row["answer"]["symbols"].pop()

cases = [
    ("wrong G0 eliminator", "tests/sol-qualified-units/g0-kernel-helpers.json", lambda d: d["helpers"][0].update(eliminator="Syn.fake")),
    ("missing G0 twin link", "tests/sol-qualified-units/g0-kernel-helpers.json", lambda d: d["twins"][0].update(theorem="Missing.G0.link")),
    ("changed theorem header", "tests/sol-qualified-units/g0-kernel-helpers.json", lambda d: d["preserved_theorem_statements"][0].update(sha256="0"*64)),
    ("compiler expectation", "tests/sol-qualified-units/evidence/h27-location-probe.json", lambda d: d.update(compiler_fixtures_pass=False)),
    ("missing theorem row", "tests/sol-qualified-units/signature-normalization-matrix.json", lambda d: d["rows"].pop()),
    ("missing required base candidate", "tests/sol-qualified-units/evidence/query-report.json", remove_required_base),
    ("missing resolver query link", "tests/sol-qualified-units/resolution-query-links.json", lambda d: d.pop()),
    ("false getter rejection", "tests/sol-qualified-units/evidence/resolution-barrier-probe.json", lambda d: d["rows"][1].update(accepted=False)),
    ("failed scoped gate", "tests/sol-qualified-units/evidence/gate-build.json", lambda d: d.update(passed=False)),
]
for name, target, corrupt in cases:
    def intercepted(path, *args, **kwargs):
        value = original(path, *args, **kwargs)
        if path == root / target:
            data = json.loads(value)
            corrupt(data)
            return json.dumps(data)
        return value
    with patch.object(Path, "read_text", intercepted):
        try:
            with contextlib.redirect_stdout(io.StringIO()):
                audit(foundation_only=True)
        except AssertionError:
            print("REFUSED " + name)
        else:
            raise AssertionError("Accepted corrupted evidence: " + name)
print("SIGNATURE_AUDIT_NEGATIVE_CONTROLS_PASS 9; no files changed")
