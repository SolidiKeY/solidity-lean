#!/usr/bin/env python3
"""Byte-compare original declaration headers, including anonymous examples/defaults."""
import argparse,hashlib,json,re
from pathlib import Path
from census import inventory,code_only
PATTERN=r"(?m)^\s*(?:@\[[^\n]*?\]\s*)*(?:(?:private|protected|noncomputable|partial|unsafe|local|scoped)\s+)*(def|theorem|lemma|inductive|structure|abbrev|class|instance|opaque|example)\b"
def headers(root):
 rows=[]
 for f in inventory(root)["files"]:
  text=(root/f["path"]).read_text();code=code_only(text);matches=list(re.finditer(PATTERN,code))
  for index,m in enumerate(matches):
   start=m.start();limit=matches[index+1].start() if index+1<len(matches) else len(code);depth=0;i=start
   if m[1]=="opaque":limit=code.find("\n",m.end())
   while i<limit:
    if depth==0 and (code[i:i+2]==":=" or re.match(r"where\b",code[i:]) or (code[i]=="|" and not code[code.rfind("\n",start,i)+1:i].strip())):break
    if code[i] in "([{":depth+=1
    if code[i] in ")]}":depth-=1
    i+=1
   header=text[start:i].strip()
   rows.append(dict(path=f["path"],ordinal=index,kind=m[1],header=header,sha256=hashlib.sha256(header.encode()).hexdigest()))
 return rows
if __name__=="__main__":
 p=argparse.ArgumentParser();p.add_argument("old",type=Path);p.add_argument("new",type=Path);p.add_argument("--output",type=Path,required=True);a=p.parse_args();old=headers(a.old);new=headers(a.new);changes=[dict(old=x,new=y) for x,y in zip(old,new) if x!=y];r=dict(status="pass" if old==new else "fail",headers=len(old),anonymous_examples=sum(x["kind"]=="example" for x in old),changes=changes,old_count=len(old),new_count=len(new),old=old,new=new);a.output.write_text(json.dumps(r,indent=2)+"\n");print(json.dumps({k:r[k] for k in ["status","headers","anonymous_examples","old_count","new_count"]}));raise SystemExit(0 if r["status"]=="pass" else 1)
