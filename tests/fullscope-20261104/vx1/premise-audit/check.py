from pathlib import Path
import hashlib, json, sys, copy
ROOT=Path(__file__).resolve().parents[4]
HERE=Path(__file__).resolve().parent
EXPECTED_IDS={f"{group}{n:02d}" for group in ("P","G","L") for n in range(1,11)}
FAMILIES={"P01","P02","P03","P04"}
def require(ok, reason):
 if not ok: raise ValueError(reason)
def validate(o):
 require(o.get("schemaVersion")==1,"schema")
 rows=o["items"]
 require(len(rows)==30 and {x["id"] for x in rows}==EXPECTED_IDS,"exact thirty unique IDs")
 expected=json.loads((HERE/"expected.json").read_text())
 require(set(expected)==EXPECTED_IDS,"expected IDs")
 refs=set()
 for x in rows:
  require(x["disposition"]==expected[x["id"]],"disposition changed")
  require((x["disposition"]=="approved-family")== (x["id"] in FAMILIES),"external premise whitelist")
  require(x["status"]=="open-production-linkage","unproved completion claim")
  require(bool(x["accounting"].strip()),"missing accounting")
  e=x["evidence"];path=e["path"];refs.add(path)
  require(path in o["sourceSha256"],"unbound source")
  content=(ROOT/path).read_bytes()
  require(hashlib.sha256(content).hexdigest()==o["sourceSha256"][path],"source drift")
  lines=content.decode().splitlines()
  hits=[n+1 for n,l in enumerate(lines) if e["anchor"] in l]
  require(0<=e["occurrence"]<len(hits) and hits[e["occurrence"]]==e["line"],"anchor/line drift")
 require(refs==set(o["sourceSha256"]),"unreferenced source")
 require(o["owners"]["source"]=="solidity-inline-assembly5-20261031/vy1-words (H125)","stale Source owner")
 require(o["owners"]["aggregateLifecycle"]=="V10 (H121b)","stale lifecycle owner")
def main():
 o=json.loads((HERE/"inventory.json").read_text());validate(o)
 mutations=[]
 x=copy.deepcopy(o);x["items"].pop();mutations.append(x)
 x=copy.deepcopy(o);x["items"][-1]=x["items"][0];mutations.append(x)
 x=copy.deepcopy(o);x["items"][10]["disposition"]="approved-family";mutations.append(x)
 x=copy.deepcopy(o);x["items"][0]["status"]="proved";mutations.append(x)
 x=copy.deepcopy(o);x["sourceSha256"][next(iter(x["sourceSha256"]))]="0"*64;mutations.append(x)
 x=copy.deepcopy(o);x["items"][0]["evidence"]["line"]+=1;mutations.append(x)
 x=copy.deepcopy(o);x["items"][0]["evidence"]["anchor"]="invented declaration";mutations.append(x)
 x=copy.deepcopy(o);x["owners"]["source"]="vy5-composition";mutations.append(x)
 x=copy.deepcopy(o);x["owners"]["aggregateLifecycle"]="vy5-composition";mutations.append(x)
 for n,x in enumerate(mutations):
  try:validate(x)
  except (ValueError,KeyError,IndexError):pass
  else:raise RuntimeError(f"mutation{n} accepted")
 print(f"PASS:{len(o['items'])} entries;{len(FAMILIES)} permitted premise-family entries;{len(o['sourceSha256'])} source pins;all production links open;{len(mutations)} mutations rejected")
if __name__=="__main__":main()
