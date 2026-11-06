#!/usr/bin/env python3
"""Regression checks for demonstrated census failures; no Lean/server needed."""
import importlib.util, json, sys
from pathlib import Path
sys.dont_write_bytecode = True
repo = Path(__file__).resolve().parents[4]
spec=importlib.util.spec_from_file_location("audit_census",repo/"scripts/h62/item2/audit-v08-adapters/census.py")
census=importlib.util.module_from_spec(spec);spec.loader.exec_module(census)

# A scanner which treats comments/strings as declarations is an omission hazard.
fixture = '''/- theorem fake : False := by /- theorem nested : False := by -/ -/
def quoted := "theorem fake2 : False := by"
def quoteChar := '\"'
namespace N
variable {P : Prop}
private theorem h (p : P) : P := p
section
 theorem «spaced name» : True := True.intro
end
end N
'''
rows=census.scan(fixture,"fixture.lean")
assert len(rows)==2 and rows[0]["name_candidate"]=="N.h"
assert rows[0]["visibility"]=="private" and rows[1]["name_candidate"]=="N.«spaced name»"
assert rows[0]["module_context_requires_elaboration"] is True

# Regression: equation theorem must not absorb proof clauses or next definition.
checked=repo/"Solidity/Lowering/P8/CheckedSyntax.lean"
row=next(r for r in census.scan(checked.read_text(),str(checked.relative_to(repo))) if r["name_candidate"].endswith(".checkUnits_sound"))
assert row["signature_source"] and "def check" not in row["signature_source"]
assert "|" not in row["signature_source"]

# Regression: a match in the theorem TYPE must not be cut at its first branch.
execution=repo/"Bridge/SolidityBridge/RoadmapV15/P10/Execution.lean"
row=next(r for r in census.scan(execution.read_text(),str(execution.relative_to(repo))) if r["name_candidate"].endswith(".dispatch_call"))
assert row["signature_source"] is None, "Ambiguous type match must fail conservatively"

# Map shorthand must resolve in the stated same-row directory.
assert census.resolve(repo,"RuntimeFrameNested.lean","Backend/InternalFlow")==["Solidity/Backend/InternalFlow/RuntimeFrameNested.lean"]
assert "Solidity/Source/Preservation/Controls.lean" in census.resolve(repo,"*Controls.lean","Source/Preservation")
assert census.expand("A/{B,C}D.lean")==["A/BD.lean","A/CD.lean"]

if len(sys.argv)>1:
    data=json.loads(Path(sys.argv[1]).read_text()); summary=data["summary"];rows=data["declarations"]
    assert summary["frozen_source_verified"] and summary["unresolved_references"]==[]
    assert summary["uncovered"]==len(rows) and summary["simultaneous_witnesses_verified"]==0
    assert len({r["id"] for r in rows})==len(rows)
    for r in rows:
        assert r["statement_fidelity"]=="UNELABORATED" and r["owner_status"]=="UNCONFIRMED"
        if r["signature_source"]:
            assert census.sha(r["signature_source"].encode())==r["signature_sha256"]
    # Null signatures are explicit unresolved obligations, never counted covered.
    assert len(summary["unterminated_signatures"])==sum(r["signature_source"] is None for r in rows)
print("CENSUS_REGRESSION_PASS (lexical tooling only; zero witness/fidelity claims)")
