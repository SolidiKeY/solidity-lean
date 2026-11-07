#!/usr/bin/env python3
"""Deterministic source inventory; hashes freeze source, not elaborated types."""
from pathlib import Path
import hashlib, importlib.util, json, re, sys
root=Path(__file__).resolve().parents[4]
spec=importlib.util.spec_from_file_location("graph",root/"scripts/v08-build-graph.py")
g=importlib.util.module_from_spec(spec); sys.dont_write_bytecode=True; spec.loader.exec_module(g)
graph=g.SourceGraph(root)
targets=sorted("Solidity.Optimizer."+p.stem for p in (root/"Solidity/Optimizer").glob("*.lean"))
closure=graph.closure(["Solidity.KeySort"]+targets)
files={}
for m in closure:
 p=graph.source(m); text=p.read_text()
 files[m]={"path":str(p.relative_to(root)),"sha256":hashlib.sha256(p.read_bytes()).hexdigest(),"imports":graph.imports(m)}
 if m in targets:
  files[m]["declaration_headers"]=[{"line":i,"header":s} for i,s in enumerate(text.splitlines(),1) if re.match(r"(?:abbrev|def|structure|theorem) ",s)]
  files[m]["budgets"]=[s for s in text.splitlines() if "set_option" in s]
  files[m]["trust_tokens"]={k:len(re.findall(r"\b"+k+r"\b",text)) for k in ["sorry","axiom","native_decide"]}
print(json.dumps({"schema":1,"targets":targets,"ordered_closure":closure,"external_to_scope":[m for m in closure if m not in targets],"files":files},indent=2,ensure_ascii=False))
