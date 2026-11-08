#!/usr/bin/env python3
"""Frozen-source reference-class measurements. No elaboration or test execution.
Run from repository root: python3 -I docs/audits/direction-tools/statements/calibrate.py [--check|--refresh]
Public compiler endpoint declarations are compared as complete statement+proof
facades, not headers or transitive proof effort. Finite evaluator controls are
compared by relevant input/output vectors to the committed pinned solc snapshot.
An absent analogue remains null; no invented denominator or size judgement.
"""
import argparse,collections,hashlib,io,json,pathlib,re,runpy,subprocess,tarfile,urllib.request
HERE=pathlib.Path(__file__).resolve().parent
API=runpy.run_path(str(HERE/"scan.py"),run_name="frozen_statement_api")
ROOT=API["ROOT"];BASE=API["BASE"]

def facade(path,name):
    raw=API["frozen_text"](path);clean=API["mask"](raw)
    start=re.search(r"^theorem "+re.escape(name)+r"\b",clean,re.M).start()
    after=re.search(r"^(?:theorem|lemma|def|abbrev|open|end|namespace|#)\b",clean[start+1:],re.M)
    end=start+1+after.start() if after else len(clean)
    return sum(bool(line.strip()) for line in clean[start:end].splitlines())

def generate():
    refs=json.loads((HERE/"references.json").read_text());out=[]
    for name in ("compiler_correct","compiler_checked"):
        local=facade("Solidity/Theorems.lean",name)
        for ref in refs:
            remote=sum(bool(line.strip()) for line in ref["theorem_source"].splitlines())
            ratio=local/remote;outlier=ratio>3 or ratio<1/3
            out.append(dict(unit="Solidity/Theorems.lean#"+name,reference=ref["id"]+"#"+ref["theorem"],metric="nonblank public theorem declaration lines including proof, excluding contextual imports/open/shared definitions",local=local,reference_value=remote,ratio=round(ratio,6),outlier=outlier,verdict="justified" if outlier else None,reason="Public correctness facades. The small checked facade compresses premises/conclusion into Input/Agrees and calls the certificate correctness theorem; CakeML exposes a pass composition. Both delegate. This compares declaration source only, not transitive proof cost or language coverage."))
    manifest=json.loads(API["frozen_text"]("tests/upstream/snapshot.json"))
    archive=subprocess.check_output(["git","show",BASE+":tests/upstream/"+manifest["archive"]],cwd=ROOT)
    assert hashlib.sha256(archive).hexdigest()==manifest["archiveSha256"]
    fixtures=[("add_overflow_checked","viaYul/detect_add_overflow.sol","g(uint8,uint8)","Checked uint8 addition: local overflow input versus upstream same-width valid/boundary/overflow inputs."),("div_by_zero","arithmetics/unchecked_div_by_zero.sol","div(uint256,uint256)","Unchecked unsigned division: local zero-divisor input versus upstream nonzero and zero divisors; local uint8 versus reference uint256 does not change the zero-divisor rule."),("short_circuit","viaYul/short_circuit.sol","and(uint256)","Short-circuit conjunction with a state-changing right operand; local false-left input versus upstream true/false-left inputs.")]
    excerpts=[]
    with tarfile.open(fileobj=io.BytesIO(archive),mode="r:gz") as tar:
        entries={x["path"]:x for x in manifest["files"]}
        for name,suffix,selector,reason in fixtures:
            path="test/libsolidity/semanticTests/"+suffix;raw=tar.extractfile(path).read();text=raw.decode()
            assert hashlib.sha256(raw).hexdigest()==entries[path]["sha256"]
            vectors=[line for line in text.splitlines() if line.startswith("// "+selector) and "->" in line]
            source_path="Solidity/Source/SemanticsExamples.lean"
            source=API["frozen_text"](source_path)
            declaration=next(d for d in API["declarations"](source_path,source,API["mask"](source)) if d["name"]==name)
            assert not declaration["premises"], "Finite comparison requires a closed control"
            local=len(re.findall(r"\bevalE\b",declaration["conclusion"]))
            assert local==1, "Selected control must have one evaluator input; inspect new shapes"
            remote=len(vectors);assert remote
            ratio=local/remote;outlier=ratio>3 or ratio<1/3
            out.append(dict(unit="Solidity/Source/SemanticsExamples.lean#"+name,reference="solc#"+path,metric="distinct fixed input/output cases for matched operation",local=local,local_case_evidence="Closed theorem header with one explicit evalE invocation; counted and shape-checked by script",reference_value=remote,ratio=round(ratio,6),outlier=outlier,verdict="justified" if outlier else None,reason=reason+" This compares finite scenario coverage, not kernel proofs with runtime tests or whole suites. No solc run is claimed."))
            excerpts.append(dict(path=path,url="https://github.com/argotorg/solidity/blob/"+manifest["commit"]+"/"+path,sha256=hashlib.sha256(raw).hexdigest(),selector=selector,vectors=vectors,source=text))
    out += json.loads((HERE/"similarity-search.json").read_text())["comparisons"]
    return dict(base=BASE,scope="Similar external theorem declarations (with semantic differences stated), public compiler facades and matched finite operation scenarios. Nulls follow recorded nearest-theorem searches.",metric_boundary="No check-time or transitive lemma-count measurement. Facade LOC is statement plus proof code, unlike the superseded header-only ratios. Finite-case counts compare selected operation scenarios, not language coverage or proof strength.",comparisons=out,solc_snapshot=dict(commit=manifest["commit"],archiveSha256=manifest["archiveSha256"],manifest="tests/upstream/snapshot.json",excerpts=excerpts),counts=dict(comparisons=len(out),matched_units=len(set(x["unit"] for x in out)),outliers=sum(x["outlier"] for x in out)),conclusion="The small checked compiler facade is an outlier against the CakeML facade because compact Input/Agrees contracts hide detail that the reference facade exposes; both sides delegate. The other original compiler-facade and solc finite-case ratios are within 3x. Additional similar-theorem ratios include small fixed local computations and delegating calculus facades versus general external theorems. Their recorded outliers reflect different generality or proof packaging, not measured transitive proof effort. Semantic compiler weaknesses are assessed from permitted behaviours, not inferred from these sizes.")

def main():
    p=argparse.ArgumentParser();p.add_argument("--check",action="store_true");p.add_argument("--refresh",action="store_true");a=p.parse_args()
    if a.refresh:
        refs=json.loads((HERE/"references.json").read_text())
        for r in refs:
            raw=urllib.request.urlopen(r["url"],timeout=30).read();assert hashlib.sha256(raw).hexdigest()==r["source_sha256"]
            text=raw.decode();start=text.index(r["statement"]);ending="\nQed." if r["id"]=="compcert" else "\nQED"
            end=text.index(ending,start)+len(ending);r["theorem_source"]=text[start:end]
        (HERE/"references.json").write_text(json.dumps(refs,ensure_ascii=False,indent=2)+"\n")
    result=generate();body=json.dumps(result,ensure_ascii=False,indent=2)+"\n";target=HERE/"calibration.json"
    if a.check:assert target.read_text()==body,"STALE calibration.json"
    else:target.write_text(body)
    print("CALIBRATION_PASS",json.dumps(result["counts"],sort_keys=True))
if __name__=="__main__":main()
