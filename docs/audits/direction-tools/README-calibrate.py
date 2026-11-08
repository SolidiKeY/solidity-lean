#!/usr/bin/env python3
"""Whole-area audit, stdlib only. README prefix keeps this within the verdict lease.
Usage: python3 -B docs/audits/direction-tools/README-calibrate.py CACHE [--check]
Output is README-results.json; pinned source, no Lean or reference builds.
"""
import json, pathlib, runpy, subprocess, sys
HERE=pathlib.Path(__file__).resolve().parent
ROOT=HERE.parents[2]
BASE="dfdfa238b5bf63955048999fefd291d9d55dbd56"
def git(*args): return subprocess.check_output(["git","-C",str(ROOT),*args],text=True).strip()
def main():
 cache=pathlib.Path(sys.argv[1]).resolve()
 c=runpy.run_path(str(HERE/"census/metrics.py"))
 r=runpy.run_path(str(HERE/"references/measure.py"))
 r["count"].__globals__["EXT"].update({".sol",".vp"})
 paths=c["tree"](BASE); texts=c["blobs"]({p:b for p,b in paths.items() if p.endswith(".lean")})
 mods=[c["module"](p,t) for p,t in sorted(texts.items())]
 def local(prefix): return c["aggregate"]([m for m in mods if m["path"].startswith(prefix)])
 areas={a:local("Solidity/"+a+"/") for a in sorted({p.split("/")[1] for p in texts if p.startswith("Solidity/") and p.count("/")>1})}
 areas["Bridge"]=local("Bridge/SolidityBridge/")
 top=sorted(areas,key=lambda a:-(areas[a]["lines"]-areas[a]["generated_lines"]))[:10]
 pins=json.loads((HERE/"references/pins.json").read_text()); sources=json.loads((HERE/"references/sources.json").read_text())
 refs={}; subs={}
 specs={"backend":("CompCert",["backend/","x86/","x86_32/","x86_64/","aarch64/","arm/","riscV/","powerpc/"]),
 "backend-x86":("CompCert",["backend/","x86/","x86_64/"]),
 "cake-backend":("CakeML",["compiler/backend/"]),"yul":("EvmYul",["EvmYul/Yul/"]),
 "calculus":("SolKey",["keyext.solidity.core/src/main/resources/org/key_project/solidity/proof/rules/","key.core/src/main/resources/de/uka/ilkd/key/proof/rules/"]),
 "lowering":("CompCert",["cfrontend/Cshmgen","cfrontend/Cminorgen"]),
 "frontend":("CompCert",["cfrontend/"]),"source":("solc",["libsolidity/ast/","libsolidity/analysis/"]),
 "bridge":("Clear",[""]),"examples":("solc",["test/libsolidity/semanticTests/"]),
 "evm":("EvmYul",["EvmYul/EVM/"]),"semantics":("CompCert",["common/"])}
 for name,pin in pins.items():
  root=cache/name
  assert subprocess.check_output(["git","-C",str(root),"rev-parse","HEAD"],text=True).strip()==pin,name
  assert not subprocess.check_output(["git","-C",str(root),"status","--porcelain"],text=True).strip(),name+" dirty reference"
  tracked=r["tracked"](root)
  if name=="Isabelle-Solidity":tracked=[p for p in tracked if p.startswith("thys/Isabelle-Solidity/")]
  refs[name]={"pin":pin,"url":"https://github.com/"+sources[name]+"/tree/"+pin,"metrics":r["count"](root,tracked)}
 for key,(name,prefixes) in specs.items():
  root=cache/name; selected=[p for p in r["tracked"](root) if any(p.startswith(pre) for pre in prefixes)]
  subs[key]={"project":name,"prefixes":prefixes,"metrics":r["count"](root,selected)}
 drift=[p for p in git("diff","--name-only",c["BASE"],BASE,"--","*.lean").splitlines() if p]
 sizes=subprocess.check_output(["git","-C",str(ROOT),"cat-file","--batch-check=%(objectsize)"],input="".join(b+"\n" for p,b in paths.items() if p.startswith("docs/audits/direction-tools/")).encode()).decode().splitlines()
 data_paths=[p for p in paths if p.startswith("docs/audits/direction-tools/")]
 diet={"input_bytes":sum(map(int,sizes)),"split_bytes":sum(int(n) for p,n in zip(data_paths,sizes) if ("/census/modules-" in p or "/reachability/duplicates-" in p) and p.endswith(".json")),"split_files":sum(("/census/modules-" in p or "/reachability/duplicates-" in p) and p.endswith(".json") for p in data_paths)}
 mapping={"Backend":"backend-x86","Yul":"yul","Calculus":"calculus","Lowering":"lowering","Frontend":"frontend","Bridge":"bridge","Examples":"examples","Source":"source","Evm":"evm","Semantics":"semantics"}
 pairs={a:{"reference":mapping[a],"unmarked_over_reference":(areas[a]["lines"]-areas[a]["generated_lines"])/(subs[mapping[a]]["metrics"]["lines"]-subs[mapping[a]]["metrics"]["generated_lines"])} for a in top}
 root_imports={pre:sum(i.startswith(pre) for i in next(m for m in mods if m["path"]=="Solidity.lean")["imports"]) for pre in ["Solidity.Yul.Views.","Solidity.Backend.InternalFlow.","Solidity.SolcValidation.","Solidity.Frontend.SolcJson."]}
 out={"base":BASE,"input_base":c["BASE"],"lean_drift_paths":drift,"repository":c["aggregate"](mods),"solidity":local("Solidity/"),"top_areas":{a:areas[a] for a in top},"references":refs,"subsystems":subs,"data_diet":diet,"area_pairs":pairs,"root_imports":root_imports,"method":"Physical source lines; lexical declarations/theorems. Reference counters include supported source extensions, never Markdown prose. Generated flags are lower bounds, remaining source has untraced authorship. No elapsed-time or proof-strength inference from LOC."}
 encoded=json.dumps(out,indent=2,sort_keys=True)+"\n"
 target=HERE/"README-results.json"
 if "--check" in sys.argv: assert target.read_text()==encoded,"calibration drift"
 else: target.write_text(encoded)
 print("PASS whole-area calibration" if "--check" in sys.argv else encoded)
if __name__=="__main__":main()
