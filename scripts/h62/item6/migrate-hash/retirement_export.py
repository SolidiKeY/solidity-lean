#!/usr/bin/env python3
"""H82 preservation only. No Lean, push, source application or goal mutation."""
import hashlib,json,pathlib,shutil,subprocess,tarfile
ROOT=pathlib.Path.cwd()
OUT=pathlib.Path("/workspace/migrate-hash-h82-handoff")
BASE="c6f550e281a7e5affa9a99bc2cdaed556dec00e4"
BRANCH="codex/solidity-h62-6-20261106/migrate-hash"
SOURCE="2a18afcdba00a85645b0b3079704f78ffcd78860"
RETIRE=ROOT/"tests/h62/item6/migrate-hash/retirement"
def git(*args):return subprocess.check_output(["git",*args])
def sha(path):return hashlib.file_digest(path.open("rb"),"sha256").hexdigest()
assert git("branch","--show-current").decode().strip()==BRANCH
assert not git("status","--porcelain"),"commit all preservation work first"
subprocess.run(["git","merge-base","--is-ancestor",BASE,"HEAD"],check=True)
assert not git("diff",SOURCE,"HEAD","--","Solidity/Hash","lean-toolchain","lakefile.toml")
HEAD=git("rev-parse","HEAD").decode().strip()
OUT.mkdir(exist_ok=False)
inputs=OUT/"inputs";inputs.mkdir()
for path in sorted(RETIRE.iterdir()):
    if path.is_file():shutil.copyfile(path,inputs/path.name)
coord=OUT/"coordinator-inputs";coord.mkdir()
for path in pathlib.Path("/workspace/h62-coordinator-inputs").iterdir():
    if path.is_file():shutil.copyfile(path,coord/path.name)
expected=json.loads((coord/"sha256.json").read_text())
for name,digest in expected.items():assert sha(coord/name)==digest
for name in ("AGENTS.md",".agents/skills/lean-verify/SKILL.md","docs/intrinsic.md","docs/contributing.md","docs/parallelism.md"):
    dest=OUT/"repository-instructions"/name;dest.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(ROOT/name,dest)
(OUT/"original.patch").write_bytes(git("diff","--binary",BASE,"HEAD"))
(OUT/"retirement-increment.patch").write_bytes(git("diff","--binary","a3f49ee0ec1829e63022c90194048d5a1ffe0d22","HEAD"))
(OUT/"commits.patch").write_bytes(git("format-patch","--stdout",BASE+"..HEAD"))
subprocess.run(["git","bundle","create",str(OUT/"migrate-hash.bundle"),BASE+"..HEAD"],check=True)
subprocess.run(["git","bundle","verify",str(OUT/"migrate-hash.bundle")],check=True)
legacy=pathlib.Path("/workspace/migrate-hash-evidence")
shutil.copyfile(legacy/"evidence.tar.gz",OUT/"prior-evidence.tar.gz")
shutil.copytree(legacy/"source-provenance-2a18afcdb",OUT/"source-provenance-2a18afcdb")
for name in ("producer-overlay.json","baseline-controller.json","reviews.md","provenance-review.json","performance.json","acceptance.json","owner-requests.json"):
    shutil.copyfile(legacy/name,OUT/name)
state=json.loads((RETIRE/"successor-state.json").read_text())
manifest={"schema":1,"batch":"solidity-h62-6-20261106","slug":"migrate-hash","status":"partial","retirement_state":"STOPPED_H82","handoff_to":"solidity-h62-6-20261106/migrate-root-gate","base":BASE,"head":HEAD,"branch":BRANCH,"repository":str(ROOT),"clean":True,"source_head":SOURCE,"worker_goal_pause":json.loads((RETIRE/"pause-report.json").read_text()),"push":state["push"],"scope_and_queues":{},"original_prompt_provenance":json.loads((RETIRE/"prompt-provenance.json").read_text()),"work_queue":state["work_queue_accounting"],"backfill_queue":state["backfill_accounting"],"waits":state["waits"],"public_api":state["public_api"],"supervisor":state["supervisor"],"proof_boundary":state["proof_boundary"],"known_limits":state["known_limits"],"no_automatic_implementation_continuation":True,"goal_marked_complete":False,"artifact_sha256":{}}
for name in ("original-user-assignment.txt","original-work-backfill-queue.md","scope-manifest.json","original-goal-objective.txt","original-environment-context.xml","prompt-provenance.json","successor-state.json","waits.json","pause-report.json","retirement-authority.md"):
    manifest["scope_and_queues"][name]={"committed_path":str(RETIRE/name),"handoff_path":str(inputs/name),"sha256":sha(inputs/name)}
(OUT/"HANDOFF.md").write_text(f"""# H82 final stopped acknowledgement

Handoff to: solidity-h62-6-20261106/migrate-root-gate
Base: {BASE}
Final head: {HEAD}
Branch: {BRANCH}
Repository: {ROOT}
Reviewed source head: {SOURCE}
Working tree: clean. No push/merge/master change. H71 permission was not supplied.

The worker stops after this preservation handoff. No automatic implementation
continuation is authorized. Existing goal PAUSED was requested by the user, but
no pause-capable goal tool exists: only complete/blocked outcomes are exposed.
Neither was substituted. Backend PAUSED is not claimed; no goal was completed,
created or reset. Coordinator must preserve the authorized pause externally.

Read all files in inputs/ before any successor work. They include the complete
original task user turn from the thread, the original work/backfill queue, exact
scope, original goal/environment, pause failure and every open item/schema-v1 wait.
The captured task text has its own SHA256; the separate advertised rendered-prompt
SHA256 ad33d9e4 was NOT reproduced. Its renderer/envelope was unavailable; do not
claim byte-identical rendering or digest equality. Scope and original content are
preserved in the cumulative patch and authenticated Git bundle.

H78 public/generated API coverage remains incomplete.121 named APIs/97 theorem
audits are not an exhaustive exported-declaration inventory. Exact old/new public
generated exports, visibility/binder/universe/kind fidelity and required shim
records are pending; no actual shim is implemented or guessed.

The source-provenance package binds exactly {SOURCE}; both Hash source files and
producer patch hashes are unchanged. Retained production checks pass; no new Lean
run occurred for retirement. The old full attempt is terminal after18/6389 with a
300s combined native command timeout. PID36556 is zombie; no active heavy jobs.
The new full probe fails in external Syntax.Raw. No complete clean full baseline,
matched full timing/RSS result, full affected/runtime gate or root acceptance.
All existing STOPs/trust/public-interface/resource obligations remain pending.
Do not rerun a known STOP unchanged or restart the baseline by implication.

prior-evidence.tar.gz contains the preserved previous proof/test/review evidence.
coordinator-inputs/ contains real copied VM inputs; coordinator-host paths in
records are provenance only. The original VM, private worktrees, toolchains and
bulk build products remain in place and were not deleted. Historical resources
are recorded; successor must obtain/obey current H81 policy before future checks.
Source retrieval is not permission to change another frozen interface/axiom set.

migrate-hash.bundle requires the exact pinned base and contains final commits;
original.patch is the cumulative base-to-final diff; commits.patch preserves
commit metadata. SHA256SUMS authenticates all exported files except itself.
Survivor integrates the final head after this stopped/head acknowledgement.
""")
archive=OUT/"evidence.tar.gz"
with tarfile.open(archive,"w:gz") as tar:
    for p in sorted(OUT.rglob("*")):
        if p.is_file() and p!=archive:tar.add(p,arcname=str(p.relative_to(OUT)),recursive=False)
for path in sorted(OUT.rglob("*")):
    if path.is_file():manifest["artifact_sha256"][str(path.relative_to(OUT))]=sha(path)
(OUT/"handoff-manifest.json").write_text(json.dumps(manifest,indent=2)+"\n")
(OUT/"SHA256SUMS").write_text("".join(sha(p)+"  "+str(p.relative_to(OUT))+"\n" for p in sorted(OUT.rglob("*")) if p.is_file() and p.name!="SHA256SUMS"))
print(json.dumps({"handoff_to":manifest["handoff_to"],"head":HEAD,"state":"STOPPED_H82;goal pause unavailable","directory":str(OUT),"manifest_sha256":sha(OUT/"handoff-manifest.json"),"checksums_sha256":sha(OUT/"SHA256SUMS"),"scope_and_queues":manifest["scope_and_queues"]},indent=2))
