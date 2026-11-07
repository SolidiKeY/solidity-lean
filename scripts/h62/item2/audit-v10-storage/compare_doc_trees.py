#!/usr/bin/env python3
"""Run one current strict checker against exact committed trees; never waive failures."""
import argparse, hashlib, io, json, os, re, subprocess, tarfile, tempfile
from pathlib import Path
FROZEN="fb379ae20f10e2c92113453ddd9d40d8f2efbe09"
CHECKER="scripts/check-doc-paths.sh"
def sha(data):return hashlib.sha256(data).hexdigest()
def runtime_checker(raw):
    line=b'cd "$(dirname "$0")/.."'
    if raw.count(line)!=1:raise ValueError("checker root line changed; review required")
    return raw.replace(line,b'cd "$DOC_COMPARE_ROOT"',1)
def extract_exact(archive,root):
    with tarfile.open(fileobj=io.BytesIO(archive)) as tree:
        for entry in tree:
            rel=Path(entry.name)
            if rel.is_absolute() or ".." in rel.parts:raise ValueError("unsafe archive path")
            target=root/rel
            if entry.isdir():target.mkdir(parents=True,exist_ok=True)
            elif entry.isfile():
                target.parent.mkdir(parents=True,exist_ok=True)
                target.write_bytes(tree.extractfile(entry).read());target.chmod(entry.mode&0o777)
            else:raise ValueError("unsupported archive member; no external paths accepted")
def findings(log):return sorted(set(x for x in log.splitlines() if x.startswith(("missing:","ambiguous:"))))
def validate_completion(status,log):
    lines=[x for x in log.splitlines() if x.strip()]
    missing=sum(x.startswith("missing:") for x in lines)
    ambiguous=sum(x.startswith("ambiguous:") for x in lines)
    if status==0 and not missing and not ambiguous:
        expected="OK: every backticked *.lean reference resolves."
    elif status==1 and missing:
        expected=f"FAIL: {missing} reference(s) name a file that does not exist."
    elif status==1 and ambiguous:
        expected=f"{ambiguous} ambiguous reference(s); all resolve, none is unique."
    else:raise ValueError("checker did not complete with a recognized strict result")
    if not lines or lines[-1]!=expected:
        raise ValueError("checker completion summary missing or inconsistent")
def compare(current,baseline):
    a,b=set(findings(current)),set(findings(baseline))
    new=sorted(a-b)
    return {"status":"fail" if new else "pass","new_findings":new,"removed_findings":sorted(b-a)}
def check_tree(repo,commit,checker,out,label):
    with tempfile.TemporaryDirectory(prefix="v10-doc-tree-") as temp:
        root=Path(temp)
        archive=subprocess.check_output(["git","archive",commit],cwd=repo)
        extract_exact(archive,root)
        subprocess.run(["git","init","-q",str(root)],check=True)
        subprocess.run(["git","add","--force","--all"],cwd=root,check=True)
        expected=set(subprocess.check_output(["git","ls-tree","-r","--name-only","-z",commit],cwd=repo).split(b"\0"))-{b""}
        actual=set(subprocess.check_output(["git","ls-files","-z"],cwd=root).split(b"\0"))-{b""}
        if actual!=expected:raise ValueError("snapshot tracked paths differ")
        env=dict(os.environ,DOC_COMPARE_ROOT=str(root))
        process=subprocess.run(["bash",str(checker),"--strict"],cwd=root,env=env,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
        raw=process.stdout; (out/(label+".log")).write_bytes(raw)
        text=raw.decode("utf-8")
        result={"commit":commit,"exit":process.returncode,"missing":sum(x.startswith("missing:") for x in text.splitlines()),"ambiguous":sum(x.startswith("ambiguous:") for x in text.splitlines()),"findings":findings(text),"log_sha256":sha(raw),"tracked_paths":len(expected)}
        try:validate_completion(process.returncode,text)
        except ValueError:
            (out/(label+"-infrastructure-failure.json")).write_text(json.dumps(result,indent=2)+"\n")
            raise
        result["completion_validated"]=True
        return result,text
def main():
    ap=argparse.ArgumentParser();ap.add_argument("--current",default="HEAD");ap.add_argument("--published",required=True);ap.add_argument("--frozen",default=FROZEN);ap.add_argument("--output",type=Path,required=True);args=ap.parse_args()
    repo=Path(subprocess.check_output(["git","rev-parse","--show-toplevel"],text=True).strip())
    out=args.output.resolve()
    if out.is_relative_to(repo):ap.error("bulk evidence must stay outside checkout")
    out.mkdir(parents=True,exist_ok=True)
    commits={name:subprocess.check_output(["git","rev-parse","--verify",rev+"^{commit}"],cwd=repo,text=True).strip() for name,rev in [("current",args.current),("published",args.published),("frozen",args.frozen)]}
    if any(not re.fullmatch("[0-9a-f]{40}",c) for c in commits.values()):raise ValueError("invalid commit")
    source=subprocess.check_output(["git","show",commits["current"]+":"+CHECKER],cwd=repo)
    runtime=runtime_checker(source);(out/"checker-original.sh").write_bytes(source);checker=out/"checker-runtime.sh";checker.write_bytes(runtime)
    rows={};logs={}
    for label,commit in commits.items():
        rows[label],logs[label]=check_tree(repo,commit,checker,out,label)
        print(json.dumps({"tree":label,"commit":commit,"exit":rows[label]["exit"],"missing":rows[label]["missing"],"ambiguous":rows[label]["ambiguous"]}),flush=True)
    comparisons={name:compare(logs["current"],logs[name]) for name in ("published","frozen")}
    report={"schema_version":1,"checker_source_sha256":sha(source),"checker_runtime_sha256":sha(runtime),"checker_change":"Only replace working-directory selection with DOC_COMPARE_ROOT; all checks, exclusions and strict mode unchanged.","boundary":"Exact committed trees without external caches. Raw strict failures and both baselines remain independent; no gate waiver.","trees":rows,"comparisons":comparisons}
    (out/"comparison.json").write_text(json.dumps(report,indent=2)+"\n")
    print(json.dumps({k:{"status":v["status"],"new":len(v["new_findings"]),"removed":len(v["removed_findings"])} for k,v in comparisons.items()}),flush=True)
    raise SystemExit(1 if any(x["status"]=="fail" for x in comparisons.values()) else 0)
if __name__=="__main__":main()
