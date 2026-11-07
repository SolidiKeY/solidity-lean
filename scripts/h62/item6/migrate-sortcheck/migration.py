#!/usr/bin/env python3
"""Exact H76 SortCheck overlay on the pinned base; no statement/budget edits."""
import hashlib, json, pathlib, subprocess
ROOT=pathlib.Path(__file__).resolve().parents[4]
BASE="c6f550e281a7e5affa9a99bc2cdaed556dec00e4"
def base_source(rel):
    return subprocess.check_output(["git","show",BASE+":"+rel],cwd=ROOT,text=True)
def alias_block():
    lines=["", "/-! Lean 4.24 compatibility for the frozen enum-tag API. -/"]
    descriptions={"ReadDomain":"Solidity storage, memory and net read domains", "ReadSite":"Solidity value, length, net and default read sites", "SortVarcond":"Solidity sort-variable conditions"}
    for name in ["ReadDomain","ReadSite","SortVarcond"]:
        lines.extend([f"/-- Retain the Lean 4.24 constructor-index API for {descriptions[name]}. -/",
          f'@[deprecated {name}.ctorIdx (since := "2025-08-25")]',
          f"protected abbrev {name}.toCtorIdx : type_of% {name}.ctorIdx := {name}.ctorIdx", ""])
    lines.extend(["-- The old generated aliases were hidden from completion as well.",
      "run_cmd Lean.modifyEnv fun env =>", "  [``Solidity.TacletAnnotations.ReadDomain.toCtorIdx,",
      "    ``Solidity.TacletAnnotations.ReadSite.toCtorIdx,",
      "    ``Solidity.TacletAnnotations.SortVarcond.toCtorIdx].foldl Lean.Meta.addToCompletionBlackList env", ""])
    return "\n".join(lines)+"\n"
def expected_sources():
    parser=base_source("Solidity/SortCheck/Parser.lean")
    assert parser.splitlines().count("  let t := l.trim")==1
    assert parser.splitlines().count("    let n := (t.dropRight 1).trim")==1
    parser=parser.replace("let t := l.trim", "let t := l.trimAscii.copy").replace("let n := (t.dropRight 1).trim", "let n := (t.dropEnd 1).trimAscii.copy")
    annotations=base_source("Solidity/SortCheck/Annotations.lean")
    closing="end TacletAnnotations\nend Solidity\n"
    assert annotations.count(closing)==1
    annotations=annotations.replace(closing,alias_block()+closing)
    return {"Solidity/SortCheck/Parser.lean":parser,"Solidity/SortCheck/Annotations.lean":annotations,
      "Solidity/SortCheck/Faithfulness.lean":base_source("Solidity/SortCheck/Faithfulness.lean")}
if __name__=="__main__":
    print(json.dumps({rel:{"expected_sha256":hashlib.sha256(text.encode()).hexdigest(),"matches":(ROOT/rel).read_text()==text} for rel,text in expected_sources().items()},indent=2))
