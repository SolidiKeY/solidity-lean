#!/usr/bin/env python3
"""Regression checks for demonstrated census failures; no Lean/server needed."""
import importlib.util, json, sys
from pathlib import Path
sys.dont_write_bytecode = True
def require(condition, message):
    """Retain census refusals when Python optimization removes assertions."""
    if not condition:
        raise ValueError(message)


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
require(len(rows)==2 and rows[0]["name_candidate"]=="N.h", 'Census regression check failed at original line 23')
require(rows[0]["visibility"]=="private" and rows[1]["name_candidate"]=="N.«spaced name»", 'Census regression check failed at original line 24')
require(rows[0]["module_context_requires_elaboration"] is True, 'Census regression check failed at original line 25')

# Regression: equation theorem must not absorb proof clauses or next definition.
checked=repo/"Solidity/Lowering/P8/CheckedSyntax.lean"
row=next(r for r in census.scan(checked.read_text(),str(checked.relative_to(repo))) if r["name_candidate"].endswith(".checkUnits_sound"))
require(row["signature_source"] and "def check" not in row["signature_source"], 'Census regression check failed at original line 30')
require("|" not in row["signature_source"], 'Census regression check failed at original line 31')

# Regression: a match in the theorem TYPE must not be cut at its first branch.
execution=repo/"Bridge/SolidityBridge/RoadmapV15/P10/Execution.lean"
row=next(r for r in census.scan(execution.read_text(),str(execution.relative_to(repo))) if r["name_candidate"].endswith(".dispatch_call"))
require(row["signature_source"] is None, "Ambiguous type match must fail conservatively")

# Map shorthand must resolve in the stated same-row directory.
require(census.resolve(repo,"RuntimeFrameNested.lean","Backend/InternalFlow")==["Solidity/Backend/InternalFlow/RuntimeFrameNested.lean"], 'Census regression check failed at original line 39')
require("Solidity/Source/Preservation/Controls.lean" in census.resolve(repo,"*Controls.lean","Source/Preservation"), 'Census regression check failed at original line 40')
require(census.expand("A/{B,C}D.lean")==["A/BD.lean","A/CD.lean"], 'Census regression check failed at original line 41')

if len(sys.argv)>1:
    data=json.loads(Path(sys.argv[1]).read_text()); summary=data["summary"];rows=data["declarations"]
    require(summary["frozen_source_verified"] and summary["unresolved_references"]==[], 'Census regression check failed at original line 45')
    require(summary["complete_interface_inventory"] is False, 'Census regression check failed at original line 46')
    require(summary["uncovered"]==len(rows) and summary["simultaneous_witnesses_verified"]==0, 'Census regression check failed at original line 47')
    require(len({r["id"] for r in rows})==len(rows), 'Census regression check failed at original line 48')
    for r in rows:
        require(r["statement_fidelity"]=="UNELABORATED" and r["owner_status"]=="UNCONFIRMED", 'Census regression check failed at original line 50')
        if r["signature_source"]:
            require(census.sha(r["signature_source"].encode())==r["signature_sha256"], 'Census regression check failed at original line 52')
    # Null signatures are explicit unresolved obligations, never counted covered.
    require(len(summary["unterminated_signatures"])==sum(r["signature_source"] is None for r in rows), 'Census regression check failed at original line 54')
print("CENSUS_REGRESSION_PASS (lexical tooling only; zero witness/fidelity claims)")
