"""Guard retained native closure classifications against hidden conditional transfers.

Historical binary/inventory pins come from the sealed ReadBounds6513 runtime
and complete-evidence archives, not current source or cached verdicts. Reuses
the reviewed tracked classifier, disassembles every reviewed origin body anew,
and retains failures. No native verifier, Lean, browser or benchmark is run.
This is an external static check, not current-source or semantic acceptance.
Caller must hold the repository writer lease and bound the invocation.
"""
import sys
sys.dont_write_bytecode=True
import ast
import hashlib
import importlib.util
from pathlib import Path
import re
import stat
import subprocess

AREA=Path(__file__).resolve().parent
POLICY=AREA/"scripts/closure-audit.py"
PINS={"binary":"86b6aa6b5e6adc7a88f356f8950935b239533ef3a8e92017f44083bb27e90dc9",
      "build":"46f28ca3d35c3a79eca80e3478979f19877bab03889ac3dfd4e5f37be3cb44b2",
      "inventory":"5dcb7d8fe9b6976f5ee6fd4b46bb35b5ffd296ecca1a4a28b0f556b3d3304ef8"}
TOOLS=("/usr/bin/nm","/usr/bin/objdump")
ENV={"PATH":"/usr/bin:/bin","LC_ALL":"C","HOME":"/nonexistent"}


def load(name,path):
    spec=importlib.util.spec_from_file_location(name,path)
    value=importlib.util.module_from_spec(spec);spec.loader.exec_module(value);return value

baseline=load("retained_baseline",AREA/"baseline-inputs.py")
reader=load("retained_reader",AREA.parent/"h109/input-copy.py")


def sha(path):
    digest=hashlib.sha256()
    with Path(path).open("rb") as stream:
        for block in iter(lambda:stream.read(262144),b""):digest.update(block)
    return digest.hexdigest()


def policy():
    # Execute only the trusted tracked function definition, never audit-file
    # top-level code or an expression supplied by an evidence file.
    raw=POLICY.read_bytes();tree=ast.parse(raw)
    functions=[n for n in tree.body if isinstance(n,ast.FunctionDef) and n.name=="machine_transfers"]
    assignments={n.targets[0].id:n.value for n in tree.body if isinstance(n,ast.Assign) and len(n.targets)==1 and isinstance(n.targets[0],ast.Name)}
    if len(functions)!=1:raise ValueError("reviewed transfer classifier unavailable")
    allowed=ast.literal_eval(assignments["machine_calls"])
    blocked_node=assignments["blocked"]
    if not isinstance(blocked_node,ast.Call) or ast.unparse(blocked_node.func)!="re.compile" or len(blocked_node.args)!=1 or blocked_node.keywords:
        raise ValueError("unknown reviewed origin policy")
    blocked=re.compile(ast.literal_eval(blocked_node.args[0]))
    namespace={"re":re}
    exec(compile(ast.Module(body=functions,type_ignores=[]),str(POLICY),"exec"),namespace)
    return namespace["machine_transfers"],allowed,blocked,hashlib.sha256(raw).hexdigest()


def classify(assembly,symbol,transfers,allowed):
    calls,branches,invalid=transfers(assembly,symbol)
    failures=[]
    if "<"+symbol+">:" not in assembly:failures.append("missing disassembly label")
    if (calls|branches)-allowed:failures.append("unreviewed machine transfer")
    if invalid:failures.append("unclassified or indirect transfer")
    return {"symbol":symbol,"calls":sorted(calls),"externalBranches":sorted(branches),
            "failures":failures,"disassembly":assembly}


def run(command):
    return subprocess.run(command,env=ENV,check=True,text=True,stdout=subprocess.PIPE,stderr=subprocess.PIPE,timeout=20).stdout


def audit(binary,build,inventory,baseline_dir):
    binary,build,inventory=Path(binary),Path(build),Path(inventory)
    if not binary.is_absolute() or binary!=binary.resolve(strict=True) or not stat.S_ISREG(binary.stat().st_mode):
        raise ValueError("canonical absolute regular binary required")
    if sha(binary)!=PINS["binary"]:raise ValueError("retained binary pin mismatch")
    manifest=reader.receipt(build,PINS["build"])
    selected=reader.receipt(inventory,PINS["inventory"])
    if manifest["executable"]!=PINS["binary"]:raise ValueError("build/binary identity mismatch")
    reference=baseline.load(baseline_dir)["native-stub-classification.json"]["data"]
    if reference.get("passed") is not True:raise ValueError("reviewed baseline not accepted")
    transfers,allowed,blocked,policy_pin=policy()
    tools={name:sha(name) for name in TOOLS}
    versions={name:run([name,"--version"]).splitlines()[0] for name in TOOLS}
    symbols=run([TOOLS[0],"-C","--defined-only","--",str(binary)])
    actual={line.split()[-1] for line in symbols.splitlines() if blocked.search(line)}
    expected={"initialize_"+r["module"].replace(".","_") for r in reference["records"]}
    failures=[];details=[]
    if actual!=expected:failures.append("origin symbol set changed")
    modules={row["module"]:row for row in selected}
    if len(modules)!=len(selected):raise ValueError("duplicate selected module")
    frontend={name for name in modules if name.startswith(("Lean.Meta","Lean.Elab","Lean.Kernel","Lean.Environment"))}
    if frontend!={r["module"] for r in reference["records"]}:failures.append("origin module set changed")
    for record in reference["records"]:
        row=modules.get(record["module"])
        if row is None or row["compiledCSha256"]!=record["compiledCSha256"]:
            raise ValueError("compiled origin body differs from reviewed baseline")
        for function in record["functions"]:
            symbol=function["symbol"]
            if not re.fullmatch("[A-Za-z_][A-Za-z0-9_]*",symbol) or symbol not in row["functions"]:
                raise ValueError("reviewed function absent from selected inventory")
            assembly=run([TOOLS[1],"-d","--disassemble="+symbol,"--",str(binary)])
            detail=classify(assembly,symbol,transfers,allowed)
            detail.update(module=record["module"],baselineCBodySha256=function["cBodySha256"])
            details.append(detail)
            failures.extend(symbol+": "+failure for failure in detail["failures"])
    if (sha(binary)!=PINS["binary"] or sha(build)!=PINS["build"] or sha(inventory)!=PINS["inventory"] or
            {name:sha(name) for name in TOOLS}!=tools or sha(POLICY)!=policy_pin):
        raise ValueError("retained artifact or audit tool changed during inspection")
    return {"passed":not failures,"status":"historical-static-transfers-only",
            "binarySha256":PINS["binary"],"buildSha256":PINS["build"],"selectedInventorySha256":PINS["inventory"],
            "policySha256":policy_pin,"tools":tools,"toolVersions":versions,"selectedModules":len(selected),
            "originModules":len(reference["records"]),"reviewedFunctions":len(details),
            "records":details,"failures":failures,"currentSourceQualified":False,
            "runtimeExecuted":False,"performanceStopReleased":False,
            "boundary":"Fresh external static disassembly of a retained historical binary. Not current-source freshness, executable closure beyond reviewed origin bodies, semantic/source/native correctness, runtime-load or performance acceptance."}
