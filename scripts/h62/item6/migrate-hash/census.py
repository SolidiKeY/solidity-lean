#!/usr/bin/env python3
"""Pinned-source census, exact textual signature comparison and reproduction.
This is a lexical check, not a replacement for kernel type/axiom validation.
Fail closed on unaccounted declaration forms. No proof body is hashed as a
signature; the whole-source hash separately binds bodies and comments.
"""
import hashlib, json, pathlib, re, subprocess
ROOT = pathlib.Path.cwd()
BASE = "c6f550e281a7e5affa9a99bc2cdaed556dec00e4"
OUT = ROOT/"tests/h62/item6/migrate-hash"
sha = lambda s: hashlib.sha256(s.encode()).hexdigest()

from lean_lex import strip_comments

pattern = re.compile(r"^(?:@\[[^\n]*\]\s*)?(def|theorem|instance)\b", re.M)
def parse(s):
    clean = strip_comments(s)
    assert not re.search(r"^\s*(?:private|protected|noncomputable|unsafe|partial|attribute)\b",clean,re.M), "unsupported declaration modifier/attribute"
    assert not re.search(r"^\s*@\[[^\n]*\]\s*$",clean,re.M), "standalone attribute"
    assert len(list(re.finditer(r"^\s*(?:@\[[^\n]*\]\s*)?(?:def|theorem|instance)\b",clean,re.M))) == len(list(pattern.finditer(clean))), "indented declaration"
    unsupported = re.findall(r"^(?:private |protected |noncomputable )?(?:opaque|abbrev|structure|inductive|class|axiom|constant|mutual)\b",clean,re.M)
    assert not unsupported, unsupported
    declarations = []
    starts = list(pattern.finditer(clean))
    for i, m in enumerate(starts):
        chunk = clean[m.start():starts[i+1].start() if i+1 < len(starts) else len(clean)]
        end = re.search(r":=|\n  \|",chunk)
        assert end, chunk[:100]
        header = " ".join(chunk[:end.start()].split())
        name = re.match(r"(?:@\[[^\n]*\]\s*)?(?:def|theorem|instance)\s+([^\s:{(\[]+)",header)
        declarations.append({"kind":m[1],"name":name[1].rstrip(".") if name else None,"line":clean[:m.start()].count("\n")+1,"header":header,"sha256":sha(header), "definition_body_sha256":sha(" ".join(chunk[end.end():].split())) if m[1] == "def" else None})
    return {"declarations":declarations,"imports":re.findall(r"^import (.+)$",clean,re.M),
            "contexts":re.findall(r"^(?:namespace|section|end|variable|universe|omit).*",clean,re.M),
            "proof_budget_options":re.findall(r"^set_option.*",clean,re.M),"source_sha256":sha(s)}

report = {"base":BASE,"modules":{},"direct_external_importers":{}}
checks = ["import tests.h62.item6.«migrate-hash».Adaptive", ""]
for name in ("CollisionBound","Adaptive"):
    path = f"Solidity/Hash/{name}.lean"
    old = subprocess.check_output(["git","show",f"{BASE}:{path}"],text=True)
    current = pathlib.Path(path).read_text()
    fixture = (OUT/f"{name}.lean").read_text().replace("import tests.h62.item6.«migrate-hash».CollisionBound", "import Solidity.Hash.CollisionBound")
    assert current in (old, fixture), "unexpected production source drift"
    original, candidate = parse(old), parse(fixture)
    for key in ("imports","contexts","proof_budget_options"):
        assert original[key] == candidate[key], (name,key)
    signatures = lambda d: [(x["kind"],x["name"],x["header"],x["definition_body_sha256"]) for x in d["declarations"]]
    assert signatures(original) == signatures(candidate), name
    for d in original["declarations"]:
        if d["name"]:
            checks.append(f"#check @Solidity.Hash.{d['name']}")
            if d["kind"] == "theorem": checks.append(f"#print axioms Solidity.Hash.{d['name']}")
    original["candidate_source_sha256"] = sha(fixture)
    original["production_source_sha256"] = sha(current)
    original["production_migration_applied"] = current == fixture
    report["modules"][path] = original
for rel in subprocess.check_output(["git","ls-files","*.lean"],text=True).splitlines():
    p = ROOT/rel
    if rel.startswith((".lake/","tests/","Solidity/Hash/")): continue
    text = p.read_text(errors="replace")
    if "import Solidity.Hash." not in text: continue
    imports = re.findall(r"^import (Solidity\.Hash\.[^\s]+)$", strip_comments(text),re.M)
    if imports: report["direct_external_importers"][rel] = imports
(OUT/"census.json").write_text(json.dumps(report,indent=2)+"\n")
checks += ["", "example : Decidable (Solidity.Hash.CollisionFree (fun x : Nat => x) [0,1]) := inferInstance", "example : Decidable (Solidity.Hash.Near 8 2 0 1) := inferInstance", "example : Decidable (Solidity.Hash.Covers 8 2 0 1) := inferInstance", "example : Decidable (Solidity.Hash.RegionsDisjoint 8 2 (fun x : Nat => x) [7] [0,3]) := inferInstance"]
(OUT/"Inventory.lean").write_text("\n".join(checks)+"\n")
(OUT/"ProductionInventory.lean").write_text(("\n".join(checks)+"\n").replace("import tests.h62.item6.«migrate-hash».Adaptive", "import Solidity.Hash.Adaptive"))
(OUT/"ProductionControls.lean").write_text((OUT/"Controls.lean").read_text().replace("import tests.h62.item6.«migrate-hash».Adaptive", "import Solidity.Hash.Adaptive"))
print(json.dumps({"declarations":{p:len(v["declarations"]) for p,v in report["modules"].items()},"external_importers":report["direct_external_importers"]},indent=2))
