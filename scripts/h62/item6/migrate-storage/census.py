#!/usr/bin/env python3
"""Pinned lexical census; whole-source hashes freeze more than interfaces.
Declaration positions are navigation aids, not a Lean elaborator/API proof.
"""
import hashlib,io,json,pathlib,re,subprocess,sys,tarfile
BASE="c6f550e281a7e5affa9a99bc2cdaed556dec00e4"
ROOT=pathlib.Path(__file__).resolve().parents[4]
def git(*args):return subprocess.check_output(["git","-C",str(ROOT),*args])
def digest(data):return hashlib.sha256(data).hexdigest()
def frozen_matches(root,expected):
 return all((root/p).is_file() and digest((root/p).read_bytes())==h for p,h in expected.items())
def strip_comments(s):
 out=[];i=0;depth=0;string=False
 while i<len(s):
  if depth:
   if s[i:i+2]=="/-":depth+=1;out.extend("  ");i+=2
   elif s[i:i+2]=="-/":depth-=1;out.extend("  ");i+=2
   else:out.append("\n" if s[i]=="\n" else " ");i+=1
  elif string:
   out.append(s[i])
   if s[i]=="\\" and i+1<len(s):out.append(s[i+1]);i+=2;continue
   if s[i]=='"':string=False
   i+=1
  elif s[i:i+2]=="/-":depth=1;out.extend("  ");i+=2
  elif s[i:i+2]=="--":
   j=s.find("\n",i);j=len(s) if j<0 else j;out.extend(" "*(j-i));i=j
  else:
   if s[i]=='"':string=True
   out.append(s[i]);i+=1
 assert depth==0,"unterminated comment"
 return "".join(out)
def imports(s):
 return [m for line in strip_comments(s).splitlines() if re.match(r"^\s*(?:public\s+)?(?:meta\s+)?import\s+",line)
  for m in re.sub(r"^\s*(?:public\s+)?(?:meta\s+)?import\s+","",line).split()]
def closure(graph,targets):
 seen=set();active=set();out=[]
 def visit(m):
  if m in seen:return
  assert m not in active,"import cycle: "+m
  if m not in graph:return
  active.add(m)
  for d in graph[m]:visit(d)
  active.remove(m);seen.add(m);out.append(m)
 for m in targets:visit(m)
 return out
DECL=re.compile(r"^[ \t]*(?:@\[[^\n]*?\]\s*)?(?:(?:private|protected|noncomputable|unsafe|partial)\s+)*(def|abbrev|opaque|theorem|lemma|structure|inductive|class|instance|axiom)\s+([^\s:{(]+)",re.M)
def census():
 with tarfile.open(fileobj=io.BytesIO(git("archive",BASE,"Solidity"))) as archive:
  sources={m.name:archive.extractfile(m).read() for m in archive if m.isfile() and m.name.endswith(".lean")}
 graph={p[:-5].replace("/","."):imports(b.decode()) for p,b in sources.items()}
 owned=sorted(p for p in sources if p.startswith("Solidity/Storage/"));assert len(owned)==21
 targets=[p[:-5].replace("/",".") for p in owned]
 order=closure(graph,["Solidity.KeySort",*targets])
 rows=[]
 for p in owned:
  data=sources[p];text=strip_comments(data.decode());decls=[{"kind":m[1],"name":m[2],"line":text.count("\n",0,m.start(1))+1} for m in DECL.finditer(text)]
  rows.append({"path":p,"sha256":digest(data),"unchanged":(ROOT/p).read_bytes()==data,"imports":graph[p[:-5].replace("/",".")],"declarations":decls,"budgets":re.findall(r"set_option\s+(?:maxHeartbeats|maxRecDepth)\s+\S+",text),"trust_tokens":{k:len(re.findall(r"\b"+k+r"\b",text)) for k in ["sorry","axiom","native_decide"]}})
 rev={}
 for m,deps in graph.items():
  for d in deps:rev.setdefault(d,[]).append(m)
 affected=set(targets);pending=list(targets)
 while pending:
  for m in rev.get(pending.pop(),[]):
   if m not in affected:affected.add(m);pending.append(m)
 return {"base":BASE,"repository":str(ROOT),"scope_count":len(owned),"declaration_count":sum(len(r["declarations"]) for r in rows),"freeze_kind":"entire original source bytes (includes all statements, proofs, attributes, cases and budgets); not an elaborated ABI hash", "files":rows,"build_order":order,"closure_source_sha256":{m:digest(sources[m.replace(".","/")+".lean"]) for m in order},"closure_matches_checkout":frozen_matches(ROOT,{m.replace(".","/")+".lean":digest(sources[m.replace(".","/")+".lean"]) for m in order}),"external_dependencies":[m for m in order if m not in targets],"cross_directory_edges":[{"from":m,"to":d} for m in targets for d in graph[m] if d not in targets],"downstream_affected":sorted(affected-set(targets))}
if __name__=="__main__":
 result=census();assert result["closure_matches_checkout"],"external source drift";assert all(x["unchanged"] for x in result["files"]),"original source drift"
 print(json.dumps(result,indent=2,sort_keys=True))
