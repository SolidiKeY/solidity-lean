#!/usr/bin/env python3
"""Reproduce isolated H78 type/value prototypes, NOT accepted API compatibility.
Known metadata/codegen/name-collision findings are recorded in the H78 receipt.
Never edit Source originals. Do not run Lean again while STOP is active.
Usage: h78-shims.py EVIDENCE OUTPUT_DIRECTORY
Old/new signatures are captured verbatim from checked API snapshots.
"""
import difflib
import hashlib
import json
from pathlib import Path
import subprocess
import sys
p=Path(sys.argv[1]);out=Path(sys.argv[2]);out.mkdir(parents=True,exist_ok=True)
a=json.loads((p/"api-partial-old.json").read_text());b=json.loads((p/"api-partial-new.json").read_text())
x={r["name"]:r for r in a["rows"]};y={r["name"]:r for r in b["rows"]}
names=sorted(n for n in x if n.endswith(".toCtorIdx") and n not in y)
assert len(names)==16
fixture=["import Lean", "import Solidity.Source.Syntax", "open Lean Elab Command", ""]
manifest=[];patchdefs=[]
for n in names:
    ty=n.rsplit(".",1)[0];target=ty+".ctorIdx";short=ty.rsplit(".",1)[1]
    assert x[n]["type_repr"]==y[target]["type_repr"] and x[n]["universes"]==y[target]["universes"]
    fixture += ["run_cmd do",f"  unless (← getEnv).contains `{n} do",f"    let declName := mkIdent `{n}",f"    elabCommand (← `(def $declName : {ty} → Nat := {target}))", "",
      f"theorem H78Compat.{short}_legacy_index (x : {ty}) :",f"    {n} x = {target} x := by", "  cases x <;> rfl",f"#print axioms H78Compat.{short}_legacy_index", ""]
    patchdefs += [f"def {short}.toCtorIdx : {short} → Nat := {short}.ctorIdx"]
    manifest.append({"name":n,"legacy_signature":ty+" → Nat","v435_original_signature":None,"v435_original_status":"name absent","replacement":target,"replacement_signature":ty+" → Nat","shim_signature":ty+" → Nat","old_type_repr":x[n]["type_repr"],"replacement_type_repr":y[target]["type_repr"],"old_universes":x[n]["universes"],"validation":"pending isolated old/new checks; original Source unchanged"})
(out/"EnumShims.lean").write_text("\n".join(fixture)+"\n")
old=subprocess.check_output(["git","show","c6f550e281a7e5affa9a99bc2cdaed556dec00e4:Solidity/Source/Syntax.lean"],text=True)
new=old+"\nnamespace Solidity.Source\n\n"+"\n".join(patchdefs)+"\n\nend Solidity.Source\n"
(out/"enum-shims.patch").write_text("".join(difflib.unified_diff(old.splitlines(True),new.splitlines(True),fromfile="a/Solidity/Source/Syntax.lean",tofile="b/Solidity/Source/Syntax.lean")))
for role in ("old","new"):
    typ="@Solidity.Source.Syn.noConfusionType c P x y" if role=="old" else "@Solidity.Source.Syn.noConfusionType P c x c y"
    val="@Solidity.Source.Syn.noConfusion c P x y h" if role=="old" else "@Solidity.Source.Syn.noConfusion P c x c y rfl (heq_of_eq h)"
    text="import Solidity.Source.Syntax\n\nnamespace H78Compat.Syn\n"
    text+="def noConfusionType.{u} {c : Solidity.Source.Cat} (P : Sort u) (x y : Solidity.Source.Syn c) : Sort u :=\n  "+typ+"\n"
    text+="def noConfusion.{u} {c : Solidity.Source.Cat} {P : Sort u} {x y : Solidity.Source.Syn c} (h : x = y) : noConfusionType P x y :=\n  "+val+"\nend H78Compat.Syn\n"
    text+="\nexample {c : Solidity.Source.Cat} (P : Sort u) (x y : Solidity.Source.Syn c) (h : x = y) : H78Compat.Syn.noConfusionType P x y :=\n  @H78Compat.Syn.noConfusion c P x y h\n"
    text+="\n#print axioms H78Compat.Syn.noConfusion\n"
    (out/("SynShape-"+role+".lean")).write_text(text)
manifest += [{"name":"H78Compat.Syn.noConfusionType","legacy_public_name":"Solidity.Source.Syn.noConfusionType","legacy_signature":"{c : Cat} → (P : Sort u) → Syn c → Syn c → Sort u","v435_original_signature":"(P : Sort u) → {c : Cat} → Syn c → {c' : Cat} → Syn c' → Sort u","shim_signature":"{c : Cat} → (P : Sort u) → Syn c → Syn c → Sort u","old_type_repr":x["Solidity.Source.Syn.noConfusionType"]["type_repr"],"new_type_repr":y["Solidity.Source.Syn.noConfusionType"]["type_repr"],"validation":"shape candidate only; does not restore old public name"},
{"name":"H78Compat.Syn.noConfusion","legacy_public_name":"Solidity.Source.Syn.noConfusion","legacy_signature":"{c : Cat} → {P : Sort u} → {x y : Syn c} → x = y → legacy noConfusionType P x y","v435_original_signature":"{P : Sort u} → {c : Cat} → {x : Syn c} → {c' : Cat} → {y : Syn c'} → c = c' → HEq x y → new noConfusionType P x y","shim_signature":"{c : Cat} → {P : Sort u} → {x y : Syn c} → x = y → H78Compat.Syn.noConfusionType P x y","old_type_repr":x["Solidity.Source.Syn.noConfusion"]["type_repr"],"new_type_repr":y["Solidity.Source.Syn.noConfusion"]["type_repr"],"validation":"shape candidate only; public-name compatibility unresolved"}]
(out/"shim-manifest.json").write_text(json.dumps({"policy":"H78 human correction supersedes Q-MS-API-01 answer","all_generated_public_api_frozen":True,"source_originals_changed":False,"shims":manifest,"boundary":"type/value prototypes only; protected/reducible/deprecation metadata not preserved by plain def; no accepted H78 compatibility or original-name noConfusion restoration claimed"},indent=2)+"\n")
print("Generated16 enum old-name shim candidates and2 differently named Syn shape candidates; no Source edits")
