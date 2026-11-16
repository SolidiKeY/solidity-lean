#!/usr/bin/env python3
"""Reproduce the reviewed E3 citation checkpoint; never upgrade current statuses.

Only explicit source-reviewed mappings are entered. Lean environment checking is
separate and mandatory; this generator does not infer declarations from text.
"""
import json
from pathlib import Path
ROOT = Path(__file__).resolve().parents[1]

def cite(name, module, cls="d", premises=()):
    return dict(name=name, module=module, **{"class": cls}, premises=list(premises), direction="model")

BODY="Solidity.Frontend.SolcJson.Body"
GRAMMAR="Solidity.Syntax.Grammar"
NOTES={
"booleanLiterals":"Definition-only Boolean import branch; no general source/importer correspondence theorem. Downgraded present to partial under the non-d present gate (F8).",
"etherUnits":"Concrete typed one-ether derivation only; factor table is definitional. No theorem covers all denomination folding and range checks.",
"timeUnits":"Definition-only literal factor table; no unit-folding preservation theorem. Downgraded present to partial (F8).",
"boolType":"Boolean carrier is Bool by definition; no theorem of the full source typing requirement. Downgraded present to partial (F8).",
"parentheses":"Grouping macro branch only; no source evaluation-preservation theorem. Downgraded present to partial (F8).",
"ifStatement":"Rule soundness is against intrinsic repository semantics. Compiler theorem additionally requires fragment admission, state simulation and local-room bound; neither proves source lowering or solc agreement.",
"breakStatement":"Class c traces lowerLoops plus guard-message regressions in Solidity/Examples/Tactics/Loops.lean:60-106; transformed syntax tests do not prove general lowering correctness (F3).",
"erc7201Builtin":"Three concrete kernel namespace computations; no theorem relates runtime lowering to the ERC7201 root formula. General runtime formula agreement remains open.",
"msgSender":"Definition-only uint256 context field, not address160 bound or external-self-call transition proof. Downgraded present to partial (F8).",
"blockTimestamp":"Definition-only environment field; no clock guarantees asserted. Downgraded present to partial (F8).",
"typeName":"Importer definition tested by tests/solc/DeclarationMetadata.sol:26-29; compiler-supplied metadata, not an all-input source correspondence theorem.",
"interfaceId":"Concrete imported own-interface fixture only; selectors supplied by solc, not independently computed and proved equivalent.",
"errorEventSelector":"Concrete imported error/event selector fixtures only; no general signature-hash agreement theorem.",
"checkedArithmetic":"uint256/int256 admitted symbolic-machine compiler fragment only. compile_correct has hP/hm/hL premises and permits coarse revert/fault outcomes; guards do not establish all source intermediate widths, pipeline orders or exact panic bytes. F8 under-citation corrected without upgrading partial. F1/F10 payment-disjunction and oracle limits, F2 source composition, F3 lowering, F4 symbolic storage, F5 coarse failures and F6 fragment boundaries remain open.",
}
COMPILER_PREMISES=["hP: inFragP F P = some F' (fragment admission)","hm: Sim C L b F sigma m (initial simulation)","hL: L + Prog.pushes P <= Lmax (local room)"]
MAPPING={
"booleanLiterals":[cite("Solidity.Frontend.expr",BODY)],
"etherUnits":[cite("Solidity.Source.TypingExamples.w_litUnit","Solidity.Source.TypingExamples","c"),cite("Solidity.unitFactor?",GRAMMAR)],
"timeUnits":[cite("Solidity.unitFactor?",GRAMMAR)],
"boolType":[cite("Solidity.PrimTy.Denote","Solidity.Semantics")],
"parentheses":[cite("Solidity.expandExpr",GRAMMAR)],
"ifStatement":[cite("Solidity.iteStep_sound","Solidity.Calculus.SoundControl","a"),cite("Solidity.Evm.compile_correct","Solidity.Evm.Correct","b",COMPILER_PREMISES)],
"breakStatement":[cite("Solidity.lowerLoops","Solidity.Syntax.Elab.Lower","c")],
"erc7201Builtin":[cite("Solidity.Examples.Tactics.AbiFeatures."+n,"Solidity.Examples.Tactics.AbiFeatures","c") for n in ("erc20_namespace","empty_namespace","utf8_namespace")],
"msgSender":[cite("Solidity.TTx.msgSender","Solidity.Semantics.State")],
"blockTimestamp":[cite("Solidity.TTx.timestamp","Solidity.Semantics.State")],
"typeName":[cite("Solidity.Frontend.declarationMetadata",BODY,"c")],
"interfaceId":[cite("Solidity.Examples.Tactics.DeclarationMetadata.ownInterface","Solidity.Examples.Tactics.DeclarationMetadata","c")],
"errorEventSelector":[cite("Solidity.Examples.Tactics.DeclarationMetadata."+n,"Solidity.Examples.Tactics.DeclarationMetadata","c") for n in ("errorSelectors","eventSelector")],
"checkedArithmetic":[cite("Solidity.Evm.exp_tail","Solidity.Evm.Exp","a"),cite("Solidity.Evm.compile_correct","Solidity.Evm.Correct","b",COMPILER_PREMISES)]
 + [cite("Solidity.Evm."+n,"Solidity.Evm.SimLemmas","a") for n in ("add_tail","sub_tail","mul_tail","div_tail","mod_tail")]
 + [cite("Solidity.Evm."+n,"Solidity.Evm.Signed","a") for n in ("sadd_tail","ssub_tail","smul_tail","sdiv_tail","smod_tail","neg_run")]
 + [cite("Solidity.Evm.tail_simT","Solidity.Evm.SimLemmas","b",["hop: binInFrag op p = true","hand: op != and","hor: op != or","hacc: op.accepts p = true","ha: ReprV p a wa","hb: ReprV p b wb"]),
    cite("Solidity.Evm.compound_simT","Solidity.Evm.SimLemmas","b",["hop: op.hasCompoundAssign = true","hp: p.isNumeric = true","ha: ReprV p a wa","hb: ReprV p b wb"]),
    cite("Solidity.Evm.bump_simT","Solidity.Evm.SimLemmas","b",["hp: p.isNumeric = true","h: ReprV p a w"])],
}
# Additional audited partial mappings are explicit data, not inferred names.
partial_path = ROOT / "scripts/check-feature-citations-partials.json"
if partial_path.exists():
    for key, evidence in json.loads(partial_path.read_text()).items():
        assert key not in MAPPING
        MAPPING[key] = evidence["theorems"]
        NOTES[key] = evidence["citationNotes"]

DOWNGRADE={"booleanLiterals","timeUnits","boolType","parentheses","msgSender","blockTimestamp"}

def main():
    agreement = json.loads((ROOT / "scripts/check-feature-citations-agreement.json").read_text())
    path=ROOT/"docs/solidity-features.json"
    data=json.loads(path.read_text())
    assert data["schemaVersion"]==2
    found=set()
    for row in data["features"]:
        key=row["id"]
        if key in MAPPING:
            found.add(key)
            row["theorems"]=MAPPING[key]
            row["citationNotes"]=NOTES[key]
        if key in agreement:
            row["theorems"].extend(agreement[key]["theorems"])
            row["citationNotes"] += " " + agreement[key]["note"]
            row["modelToSolcGap"] = agreement[key]["gap"]
        else:
            row["modelToSolcGap"] = "No validated model-to-solc citation is established here; model declarations do not prove source/compiler agreement."
            if row["scope"] == "exclude":
                row["modelToSolcGap"] += " The legacy scope label is not an exclusion from the approved full compiler endpoint."
            elif row["scope"] == "upstream":
                row["modelToSolcGap"] += " Upstream/reserved inventory status is not an implementation proof."
        if key in DOWNGRADE:
            assert row["current"] in ("present","partial")
            row["current"]="partial"
    assert found==set(MAPPING)
    path.write_text(json.dumps(data,indent=2,ensure_ascii=False)+"\n")

if __name__=="__main__":
    main()
