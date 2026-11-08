#!/usr/bin/env python3
"""Reproduce: python3 docs/audits/direction-tools/mutation/audit.py [--scratch ABSOLUTE_WORKTREE].
No Lean is executed. Scratch must be an owned disposable worktree at the pinned base.
"""
import argparse, hashlib, json, re, subprocess, sys
sys.dont_write_bytecode=True
from static_refs import augment
from pathlib import Path
BASE="d4ad633a9624263a59b14fd2c520b9bc602f88f3"
ROOT=Path(__file__).resolve().parents[4]
OUT=Path(__file__).resolve().parent

def git(*args):
    return subprocess.check_output(["git",*args],cwd=ROOT,text=True).strip()
def write(name,obj):
    data=json.dumps(obj,indent=2,sort_keys=True)+"\n"
    assert len(data.encode())<1000000
    (OUT/name).write_text(data)
def generated(path):
    return path in ["Solidity.lean","SolidityExamples.lean","SolidityCorpus.lean","Bridge/SolidityBridge.lean"] or "/Corpus/" in path or "AxiomPins" in path or bool(re.search(r"(?i)generated|generator|agreement|chain",path))
def main():
    ap=argparse.ArgumentParser();ap.add_argument("--scratch",type=Path);a=ap.parse_args()
    assert git("merge-base",BASE,"HEAD")==BASE
    tracked=git("ls-tree","-r","--name-only",BASE).splitlines()
    lean={x:(ROOT/x).read_text() for x in tracked if x.endswith(".lean")}
    paths=["scripts/differential","scripts/bench","SolcValidation","docs/audits/architecture-tools/timing-sample.tsv","docs/audits/build-speed-tools","scripts/h62/item3/g52-differential","docs/feature-work/h62-3-g52-differential.md"]
    inventory={x:{"present":(ROOT/x).exists(),"tracked_files":sum(y==x or y.startswith(x+"/") for y in tracked)} for x in paths}
    counts={k:{"files":0,"lines":0} for k in ["generated_or_generator_named","other_unclassified"]}
    for path,s in lean.items():
        c=counts["generated_or_generator_named" if generated(path) else "other_unclassified"];c["files"]+=1;c["lines"]+=len(s.splitlines())
    inventory["lean_partition"]=counts
    inventory["partition_caveat"]="Path heuristic only, not a verified generated/handwritten split: Agreement and Chain names can be handwritten. Counts cannot support a generated-code-adjusted verdict. Both mutated source files are handwritten by inspection; broad inventory classification remains incomplete."
    inventory["corpus"]={"path":"tests/solkey/expected.tsv","data_rows":sum(bool(x.strip()) for x in (ROOT/"tests/solkey/expected.tsv").read_text().splitlines()),"boundary":"SolKey verdict parity, not solc execution agreement; check-corpus invokes prohibited project builds and was not run"}
    write("inventory.json",inventory)
    specs=[]
    def add(path,old,new,reason):
        src=lean[path];assert src.count(old)==1,(old,src.count(old))
        pos=src.index(old);prefix=src[:pos]
        decls=list(re.finditer(r"(?m)^(?:def|theorem) ([\w.]+)",prefix));symbol=decls[-1][1]
        specs.append(dict(id="M%02d"%(len(specs)+1),path=path,line=prefix.count("\n")+1,old=old,new=new,definition=symbol,expected_constraint=reason,generated=generated(path)))
    op="Solidity/Semantics/Ops.lean"
    for old,new in [("some (x + y)","some (x - y)"),("some (x - y)","some (x + y)"),("some (x * y)","some (x + y)"),("if y < 0 then none else some (x ^ y.toNat)","if y < 0 then none else some (x ^ (y.toNat + 1))"),("if y = 0 then none else some (Int.tdiv x y)","if y = 0 then some 0 else some (Int.tdiv x y)"),("if y = 0 then none else some (Int.tmod x y)","if y = 0 then some 0 else some (Int.tmod x y)"),("(· &&& ·)","(· ||| ·)"),("(· ||| ·)","(· &&& ·)"),("(· ^^^ ·)","(· ||| ·)"),("n < 256 then a *", "n < 255 then a *"),("n < 256 then a /", "n < 255 then a /"),("if a < 0 then -1 else 0", "if a < 0 then 0 else 0"),("some ((x + y) % Semantics.uintBound)","some ((x - y) % Semantics.uintBound)"),("some ((x - y) % Semantics.uintBound)","some ((x + y) % Semantics.uintBound)"),("some (x * y % Semantics.uintBound)","some ((x + y) % Semantics.uintBound)"),("x ^ y.toNat % Semantics.uintBound", "x ^ (y.toNat + 1) % Semantics.uintBound"),("decide (x < y)","decide (x ≤ y)"),("decide (y < x)","decide (y ≤ x)"),("decide (x ≤ y)","decide (x < y)"),("decide (y ≤ x)","decide (y < x)"),("some (a && b)","some (a || b)"),("some (a || b)","some (a && b)"),("| .addmod, x, y => x + y", "| .addmod, x, y => x - y"),("| .mulmod, x, y => x * y", "| .mulmod, x, y => x + y"),("if k.val = 0 then none", "if k.val = 0 then some (PrimTy.dflt .uint)"),("PrimTy.int.ofInt? (-a.1)","PrimTy.int.ofInt? (a.1)"),("some (!a)","some a"),("Semantics.uintBound - 1 - a.1", "Semantics.uintBound - 2 - a.1"),("a.1 < Semantics.intBound", "a.1 ≤ Semantics.intBound"),("(a.1 % Semantics.uintBound)","((a.1 + 1) % Semantics.uintBound)")]:
        add(op,old,new,"Operator boundary/example theorem mentioning enclosing definition; independent solc vectors alone do not execute this Lean definition")
    closer="Solidity/Calculus/Closers.lean"
    add(closer,"| .error .panic => true","| .error .panic => false","Modality.afterRunTR_not_panic may become vacuous; require boundary example, not merely successful elaboration")
    add(closer,"| .error .exhausted => false","| .error .exhausted => true","Modality.afterRunTR_diamond_fail expected to fail (exhaustion accepted)")
    # Candidate constraints selected by inspecting concrete example bodies; not measured kills.
    candidates=[("Values",60,"additionSimple"),("Values",63,"subtractionSimple"),("Values",66,"multiplicationSimple"),
      ("Values",288,"powerSimple"),
      ("Operators",113,"zero-divisor anonymous example"),("Operators",146,"signedRemainder: nonzero divisors, zero boundary not covered"),
      ("Operators",40,"bitwise"),("Operators",40,"bitwise"),("Operators",40,"bitwise"),
      ("Operators",56,"shifts"),("Operators",130,"signedBitwise: no unsigned shift-255 boundary"),("Operators",130,"signedBitwise"),
      ("Operators",95,"uncheckedAdd"),("Operators",103,"uncheckedWrap"),("SignedCasts",74,"uncheckedMul"),("SignedCasts",95,"uncheckedPow"),
      ("Operators",146,"signedRemainder: uses comparisons, equality boundary candidate"),("Operators",146,"signedRemainder: uses comparisons, equality boundary candidate"),
      ("Operators",146,"signedRemainder: uses comparisons, equality boundary candidate"),("Operators",146,"signedRemainder: uses comparisons, equality boundary candidate"),
      ("Operators",40,"bitwise: boolean conjunction in postcondition"),("ModularArithmetic",61,"short: short circuit boolean disjunction candidate"),
      ("ModularArithmetic",32,"basic modular result anonymous example"),("ModularArithmetic",32,"basic modular result anonymous example"),
      ("ModularArithmetic",50,"zeroAdd anonymous example"),("SignedCasts",113,"checkedNegReverts"),("Branch",135,"ifNegated"),
      ("Operators",47,"complement"),("SignedCasts",29,"downcast: uint-to-int conversion, but not the 256-bit threshold boundary"),("SignedCasts",46,"numberLiteral")]
    for m,(file,line,name) in zip(specs,candidates):
        path="Solidity/Examples/Tactics/"+file+".lean"
        assert 0<line<=len(lean[path].splitlines())
        m["expected_failing_candidate"]={"path":path,"line":line,"name":name,"status":"unvalidated candidate; may not kill this boundary"}
    specs[26]["expected_failing_candidate"]["status"]="non-discriminating: postcondition holds for either branch; no expected kill established"
    specs[28]["expected_failing_candidate"]=None
    specs[28]["constraint_search_result"]="No exact uint256-to-int threshold 2^255 constraint found in inspected cast examples; downcast is not a valid killer"
    for m in specs[len(candidates):]:
        name="afterRunTR_not_panic" if m["id"]=="M31" else "afterRunTR_diamond_fail"
        text=lean[closer];pos=text.index("theorem _root_.Solidity.Modality."+name)
        m["expected_failing_candidate"]={"path":closer,"line":text[:pos].count("\n")+1,"name":"Modality."+name,"status":"unvalidated; M31 may make premise vacuous rather than fail"}
    # Lexical references are candidates only: no claim of proof dependency or coverage.
    cache={}
    for m in specs:
        pat=re.compile(r"(?<![\w])"+re.escape(m["definition"])+r"(?![\w])")
        refs=cache.get(m["definition"])
        if refs is None:
            refs=[]
            for path,s in lean.items():
                if path==m["path"]:continue
                for line,text in enumerate(s.splitlines(),1):
                    if pat.search(text):refs.append(dict(path=path,line=line,generated=generated(path)))
            cache[m["definition"]]=refs
        m["static_mentions_first_30"]=refs[:30];m["static_mention_count"]=len(refs)
        m["static_boundary"]="Lexical names may collide across namespaces, occur in comments, or miss indirect dependencies; not theorem kills"
    constraint_summary=augment(lean,specs)
    write("constraints.json",constraint_summary)
    write("mutants.json",specs)
    if not a.scratch:return
    scratch=a.scratch.resolve();assert scratch!=ROOT and scratch.is_dir()
    assert subprocess.check_output(["git","rev-parse","HEAD"],cwd=scratch,text=True).strip()==BASE
    assert not subprocess.check_output(["git","status","--porcelain"],cwd=scratch,text=True).strip(),"scratch must be clean"
    for path in {m["path"] for m in specs}:
        expected=subprocess.check_output(["git","show",BASE+":"+path],cwd=scratch)
        assert (scratch/path).read_bytes()==expected,"scratch source differs from base"
    command=["node","scripts/check-backend-scalar.mjs"]
    def check():
        r=subprocess.run(command,cwd=scratch,text=True,capture_output=True,timeout=120)
        return dict(command=" ".join(command),returncode=r.returncode,output=(r.stdout+r.stderr)[-2000:])
    baseline=check();results=[]
    for m in specs:
        path=scratch/m["path"];original=path.read_text();assert original.count(m["old"])==1
        try:
            path.write_text(original.replace(m["old"],m["new"],1));r=check()
        finally:path.write_text(original)
        results.append(dict(id=m["id"],checker=r,status="cheap-check-survived; Lean-unassessed" if baseline["returncode"]==0 and r["returncode"]==0 else "checker-failed-unattributed",semantic_kill_established=False))
    write("checker-results.json",dict(baseline=baseline,mutants=results,boundary="Structural layer/source/trust/generation checker; no execution of changed Lean bodies. No semantic mutation score inferred."))
    source="docs/feature-work/h62-3-g52-differential.md";text=(ROOT/source).read_text()
    assert hashlib.sha256(text.encode()).hexdigest()=="4110f3923608d46d7955dd4fe0a555313ac59f6e168e3afa8f06c5753a607c18","cited snapshot changed; re-audit its denominators"
    assert "320 real comparisons produced zero mismatches" in text
    matched=int(re.search(r"(\d+) real primitive-fragment observations match",text)[1]);unsupported=int(re.search(r"(\d+) observations have reference execution only",text)[1])
    summary=dict(base=BASE,mutants=len(specs),cheap_checker_survivors=sum(r["status"].startswith("cheap-check-survived") for r in results),semantic_survivors=None,semantic_kills=None,lean_elaborations=0,axioms_added=0,sorry_added=0,mutation_selection=dict(handwritten=len(specs),generated=0,files=sorted({m["path"] for m in specs}),basis="Both selected source files inspected; broad inventory classification remains heuristic"),
      conclusion="Cheap structural checks do not constrain these operator/closer mutations. Whether existing proofs kill them remains unassessed; static references cannot establish coverage gaps.",
      differential=dict(source=source,source_sha256=hashlib.sha256(text.encode()).hexdigest(),pending_eest=int(re.search(r"All ([\d,]+) EEST rows are pending",text)[1].replace(",","")),provenance="cited committed report, not replayed",matched=matched,disagreed=0,matched_subset_agreement=matched/matched,reference_only_unsupported=unsupported,agreement_including_unsupported=None,disagreement_classes=[],disagreement_boundary="No mismatches reported for admitted primitive fragment; unsupported rows are not agreements",per_input_time_ratios=None,time_boundary="Matched per-input repository and solc compile/run timings unavailable; no ratio invented"),
      waits=[dict(id="W-TIMING",reason="Named va3/vu1 paths and matched raw timing outputs absent at pinned base; G52 private bulk results not present on VM"),dict(id="W-LEAN",reason="No Lean elaborations performed; systemd resource scope unavailable on this VM (no user bus); highest-value next checks are M32 afterRunTR_diamond_fail, M07 bitwise and M10 shifts. Structural survivors are not semantic survivors")],reproduce="python3 docs/audits/direction-tools/mutation/audit.py --scratch ABSOLUTE_BASE_WORKTREE")
    summary["static_constraints"]=constraint_summary
    captured=OUT/"captured-results.json"
    if captured.exists():
        summary["historical_capture"]=json.loads(captured.read_text())
        summary["waits"][0]={"id":"QDATA-TIMINGS","reason":"Historical archive verified and analyzed; matched per-input timings absent. Coordinator awaits existing matched archive or separate bounded-run authorization; no rerun authorized"}
        summary["waits"].append({"id":"W-REFERENCE-LOCK","reason":"Exact historical reference lock bytes not delivered; reference-environment reproduction UNVERIFIABLE under H151"})
    write("summary.json",summary)
if __name__=="__main__":main()
