#!/usr/bin/env python3
"""Reproduce a proof-only candidate in an isolated generated fixture.
Never writes Source/Ctor.lean. Original definitions and theorem headers are unchanged.
"""
import difflib
from pathlib import Path
import subprocess
import sys
BASE="c6f550e281a7e5affa9a99bc2cdaed556dec00e4"
old=subprocess.check_output(["git","show",BASE+":Solidity/Source/Ctor.lean"],text=True)
s=old
before="cases s <;> simp only [Syn.nodes, Syn.children, List.flatMap_cons, List.flatMap_nil,\n    List.append_nil, List.append_assoc]"
after="cases s <;> apply congrArg (List.cons _) <;>\n    simp only [Syn.children, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.append_assoc]"
assert s.count(before)==1; s=s.replace(before,after)
start=s.index("theorem Syn.excl_ctor")
prefix=s[:start]; tail=s[start:]
tail=tail.replace("| pragma _ =>", "| pragma words =>")
contexts=[("  | assembly _ _ b =>", "isRethrow b", "Option.none", "Option.some Excl.inlineAssembly"),
          ("    | some b =>", "isLiteralBase b", "Option.none", "Option.some Excl.storageLayout"),
          ("  | pragma words =>", 'words == ["experimental", "solidity"]', "Option.some Excl.removedGenericSolidity", "Option.none"),
          ("    | some b =>", "b.placeholders == 0", "Option.some Excl.invalidModifierBody", "Option.none"),
          ("  | uncheckedItem b =>", "b.placeholders == 0", "Option.none", "Option.some Excl.invalidModifierBody")]
search=0
for marker, condition, yes, no in contexts:
    idx=tail.index(marker,search)
    a=tail.index("simp only [Syn.excl] at h",idx)
    b=tail.index("cases h",a)+len("cases h")
    indent=" "*(a-tail.rfind("\n",0,a)-1)
    replacement=("change (if "+condition+" then "+yes+" else "+no+") = Option.some f at h\n"+indent+"cases hb : ("+condition+") <;>\n"+indent+
      "  simp only [hb, Bool.false_eq_true,\n"+indent+
      "    ite_false, ite_true, Option.some.injEq, reduceCtorEq] at h\n"+indent+"subst h")
    tail=tail[:a]+replacement+tail[b:];search=a+len(replacement)
s=prefix+tail
s=s.replace("List.mem_cons, List.mem_singleton, true_or, or_true", "List.mem_cons, true_or, or_true")
out=Path(sys.argv[1]);out.parent.mkdir(parents=True,exist_ok=True)
out.write_text(s+"\n#print axioms Solidity.Source.Syn.nodes_eq\n#print axioms Solidity.Source.Syn.excl_ctor\n")
Path(sys.argv[2]).write_text("".join(difflib.unified_diff(old.splitlines(True),s.splitlines(True),fromfile="a/Solidity/Source/Ctor.lean",tofile="b/Solidity/Source/Ctor.lean")))
print("Generated fixture and proposed proof-only patch; original Source files unchanged")
