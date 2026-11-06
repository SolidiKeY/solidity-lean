#!/usr/bin/env python3
"""Account for selected parser alternative labels in pinned declaration contexts.

These are syntax patterns, not typed Lean constructors or semantic exhaustiveness.
"""
import argparse
import hashlib
import json
import re
from pathlib import Path
import raw_census as base
import raw_context as context

MANIFEST=base.ROOT / "tests/h55/vectors-tables/master-raw-case-labels-manifest.json"
VALID=re.compile(r"[A-Za-z0-9_@.|+() \t\n]+")
TOKEN=re.compile(r"(?:@?\.?[A-Za-z_][A-Za-z0-9_]*(?:\+[0-9]+)?|[0-9]+|\(\))")
KINDS={"Lean.Parser.Term.matchAlt","Lean.Parser.Tactic.inductionAlt","Lean.Parser.Tactic.case"}
FIELDS={"kind","node_start","node_end","node_sha256","declaration_start","declaration_end","declaration_sha256","declaration_heading","pattern_index","pattern"}

def split_label(text,kind):
    at=text.find("=>")
    if at<0: raise ValueError("missing alternative arrow")
    label=text[:at].strip()
    if not VALID.fullmatch(label): raise ValueError("unsupported pattern schema")
    if kind=="Lean.Parser.Tactic.case":
        if not re.fullmatch(r"case\s+[A-Za-z_][A-Za-z0-9_]*",label): raise ValueError("case schema")
        return [label]
    if kind not in KINDS or not label.startswith("|"): raise ValueError("alternative schema")
    patterns=[x.strip() for x in label[1:].split("|")]
    if not patterns or any(not x for x in patterns): raise ValueError("empty pattern")
    if any(any(not TOKEN.fullmatch(token) for token in pattern.split()) for pattern in patterns): raise ValueError("unsupported pattern tokens")
    return patterns

def collect(root, context_log, reference):
    contexts=context.parse(root,context_log,reference)
    if context.summary(contexts)!=json.loads(context.MANIFEST.read_text()): raise ValueError("declaration context differs from manifest")
    result={}; alternative_nodes=0
    for name,decls in contexts["files"].items():
        source=(root / base.AREA / name).read_bytes(); rows=[]
        for decl in decls:
            for node in decl["nodes"]:
                if node["kind"] not in KINDS: continue
                alternative_nodes+=1
                raw=source[node["start"]:node["end"]]
                if hashlib.sha256(raw).hexdigest()!=node["source_sha256"]: raise ValueError("node hash")
                for index,pattern in enumerate(split_label(raw.decode("utf-8"),node["kind"])):
                    rows.append({"kind":node["kind"],"node_start":node["start"],"node_end":node["end"],"node_sha256":node["source_sha256"],"declaration_start":decl["start"],"declaration_end":decl["end"],"declaration_sha256":decl["source_sha256"],"declaration_heading":decl["heading"],"pattern_index":index,"pattern":pattern})
        result[name]=rows
    return {"master":contexts["master"],"alternative_nodes":alternative_nodes,"files":result}

def summary(data):
    if type(data) is not dict or set(data)!={"master","alternative_nodes","files"} or type(data["master"]) is not str or type(data["alternative_nodes"]) is not int or type(data["files"]) is not dict: raise ValueError("inventory schema")
    files={}
    for name,rows in data["files"].items():
        if type(rows) is not list or any(type(row) is not dict or set(row)!=FIELDS for row in rows): raise ValueError("row schema")
        for row in rows:
            if row["kind"] not in KINDS or any(type(row[k]) is not int or row[k]<0 for k in ("node_start","node_end","declaration_start","declaration_end","pattern_index")): raise ValueError("row type")
            if not row["declaration_start"]<=row["node_start"]<row["node_end"]<=row["declaration_end"]: raise ValueError("row span")
            if any(type(row[k]) is not str or not re.fullmatch(r"[0-9a-f]{64}",row[k]) for k in ("node_sha256","declaration_sha256")) or any(type(row[k]) is not str or not row[k] for k in ("declaration_heading","pattern")): raise ValueError("row value")
        encoded=json.dumps(rows,ensure_ascii=False,separators=(",", ":")).encode()
        files[name]={"arms":len(rows),"sha256":hashlib.sha256(encoded).hexdigest()}
    return {"master":data["master"],"alternative_nodes":data["alternative_nodes"],"files":files}

def main():
    p=argparse.ArgumentParser(); p.add_argument("mode",choices=("manifest","extract","check")); p.add_argument("snapshot",type=Path); p.add_argument("context_log",type=Path); p.add_argument("reference",type=Path); p.add_argument("data",nargs="?",type=Path); a=p.parse_args()
    result=collect(a.snapshot,a.context_log,a.reference)
    if a.mode=="manifest":
        if a.data is not None or MANIFEST.exists(): raise ValueError("manifest exists or unexpected data")
        MANIFEST.write_text(json.dumps(summary(result),indent=2)+"\n"); return
    if summary(result)!=json.loads(MANIFEST.read_text()): raise ValueError("case-label inventory differs")
    if a.data is None: raise ValueError("data required")
    if a.mode=="extract":
        out=a.data.resolve()
        if out.exists() or out.is_relative_to(base.ROOT): raise ValueError("new external data required")
        out.write_text(json.dumps(result,ensure_ascii=False,separators=(",", ":"))+"\n"); return
    if json.loads(a.data.read_text())!=result: raise ValueError("case-label data differs")
    print(f"PASS: {len(result['files'])} files, {result['alternative_nodes']} alternative nodes, {sum(map(len,result['files'].values()))} syntax patterns")

if __name__ == "__main__": main()
