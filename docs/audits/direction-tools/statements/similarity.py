#!/usr/bin/env python3
"""Bounded nearest-theorem search, reproducible offline or against pinned public sources.
Run: python3 -I docs/audits/direction-tools/statements/similarity.py --check
Remote replay: same command with --refresh --check (no files written).
--source-cache /tmp/da-search- reads initially fetched public text, never required for replay.
Catalog retains every parsed theorem header and full declarations for reviewed candidates.
This is lexical candidate discovery plus explicit human matching, not proof equivalence.
"""
import argparse,csv,hashlib,json,pathlib,re,runpy,urllib.request
HERE=pathlib.Path(__file__).resolve().parent
API=runpy.run_path(str(HERE/"scan.py"),run_name="statement_source_api")
def read(name):return json.loads((HERE/name).read_text())
def body(obj):return json.dumps(obj,ensure_ascii=False,indent=2)+"\n"
def comments(s):
    out=list(s);i=0;depth=0;string=False
    while i<len(s):
        if not depth and s[i]=='"':string=not string;i+=1;continue
        if not string and s[i:i+2]=="(*":depth+=1;out[i:i+2]="  ";i+=2;continue
        if depth and s[i:i+2]=="*)":depth-=1;out[i:i+2]="  ";i+=2;continue
        if depth and s[i]!="\n":out[i]=" "
        i+=1
    return "".join(out)
def parse(source,spec,reviewed):
    clean=comments(source);coq=spec["path"].endswith(".v")
    pattern=r"^(?:Lemma|Theorem|Remark|Corollary)\s+([A-Za-z_][\w']*)" if coq else r"^(?:lemma|theorem)\s+(?:\(in [^)]+\)\s*)?([A-Za-z_][\w'.]*)"
    result=[]
    for m in re.finditer(pattern,clean,re.M):
        if coq:
            end=re.search(r"^(?:Qed|Defined)\.",clean[m.end():],re.M)
            if end is None:continue
            end=m.end()+end.end()
        else:
            after=re.search(r"^(?:lemma|theorem|definition|fun|function|abbreviation|declare|locale|context|end|begin|section|subsection|subsubsection|text|method_setup|lemmas|datatype|primrec|interpretation)\b",clean[m.end():],re.M)
            end=m.end()+after.start() if after else len(clean)
        code=clean[m.start():end].strip()
        header=re.split(r"^Proof\b" if coq else r"^\s*(?:using|unfolding|apply|by|proof)\b",code,maxsplit=1,flags=re.M)[0].strip()
        key=spec["id"]+"#"+m[1]
        row=dict(id=key,source=spec["id"],name=m[1],line=source[:m.start()].count("\n")+1,statement=header)
        if key in reviewed:row["declaration_code"]=code
        result.append(row)
    return result
def catalog(specs,source_cache=None):
    reviewed={ref for s in specs.values() for ref in s["reviewed"]}
    out=[]
    for source in read("external-sources.json"):
        if source_cache:
            text=json.loads(pathlib.Path(source_cache+source["id"]+".json").read_text())["source"];raw=text.encode()
        else:raw=urllib.request.urlopen(source["url"],timeout=60).read();text=raw.decode()
        assert hashlib.sha256(raw).hexdigest()==source["sha256"],source["id"]
        out+=parse(text,source,reviewed)
    assert reviewed<={x["id"] for x in out},reviewed-{x["id"] for x in out}
    return out
def local_lines(path,name):
    source=API["frozen_text"](path);clean=API["mask"](source)
    start=re.search(r"^(?:@\[[^\]]*\]\s*)?(?:theorem|lemma)\s+"+re.escape(name)+r"(?=\s|:|\()",clean,re.M).start()
    after=re.search(r"^(?:@\[[^\]]*\]\s*)?(?:theorem|lemma|def|abbrev|open|end|namespace|#)\b",clean[start+1:],re.M)
    end=start+1+after.start() if after else len(clean)
    return sum(bool(x.strip()) for x in clean[start:end].splitlines())
def generate(cat,specs):
    sources={x["id"]:x for x in read("external-sources.json")}
    entries={x["id"]:x for x in cat};rows=[];comparisons=[]
    inventory=list(csv.DictReader((HERE/"statements.csv").open()))
    assert set(specs)=={x["path"]+"#"+x["name"] for x in inventory}
    for row in inventory:
        unit=row["path"]+"#"+row["name"];spec=specs[unit]
        queries=[]
        for query in spec["queries"]:
            hits=[x["id"] for x in cat if re.search(query,x["name"]+" "+x["statement"],re.I)]
            queries.append(dict(pattern=query,compiler_hits=[x for x in hits if x.startswith("cc-")],solidity_verification_hits=[x for x in hits if x.startswith("afp-")]))
        assert spec["reviewed"]
        candidates=[]
        for ref in spec["reviewed"]:
            entry=entries[ref];s=sources[entry["source"]]
            candidates.append(dict(reference=ref,url="https://github.com/"+s["repo"]+"/blob/"+s["ref"]+"/"+s["path"]+"#L"+str(entry["line"]),statement=entry["statement"],implicit_context=spec.get("context",{}).get(ref,"Consult pinned file for enclosing sections/locales; header is not an elaborated signature.")))
        selected=spec.get("selected")
        if selected:
            assert selected in spec["reviewed"]
            remote=sum(bool(x.strip()) for x in entries[selected]["declaration_code"].splitlines())
            local=local_lines(row["path"],row["name"]);ratio=local/remote;outlier=ratio>3 or ratio<1/3
            comparisons.append(dict(unit=unit,reference=selected,metric="nonblank public theorem declaration code lines including proof; comments and enclosing contexts excluded",local=local,reference_value=remote,ratio=round(ratio,6),outlier=outlier,verdict="justified" if outlier else None,reason=spec["shared"]+" Differences: "+spec["differences"]+" Declaration size only: local facade delegation or fixed-case computation and the reference proof's inversions/automation differ; this is not transitive proof effort, semantic coverage or correctness equivalence."))
        else:assert len(spec["reason"])>80
        rows.append(dict(unit=unit,queries=queries,reviewed_candidates=candidates,selected=selected,shared_property=spec.get("shared"),differences=spec.get("differences"),non_comparability_reason=None if selected else spec["reason"],existing_measurement=spec.get("existing_measurement")))
    return dict(base=API["BASE"],policy="Search compiler theorem headers first, then Solidity verification headers. Read the listed closest candidates. Similar propositions may differ in model, premises or generality; explain those differences. Null only after bounded search finds no similar proposition. This does not prove global absence.",search_scope=dict(sources=len(sources),theorem_headers=len(cat),rows=len(rows),similar_theorem_rows=sum(bool(x["selected"]) for x in rows),remaining_null_rows=sum(not x["selected"] and not x["existing_measurement"] for x in rows)),boundary="Pinned CompCert files: compiler endpoints, complements, C typing/execution/strategy, small-step determinacy, integers, memory data. Pinned Isabelle Solidity: WP, state monad and semantics. Existing CakeML compiler endpoint and solc finite vectors retained in calibration.json. No exhaustive claim about all external compiler or EVM libraries; no reference theorem rechecked.",rows=rows,comparisons=comparisons)
def main():
    p=argparse.ArgumentParser();p.add_argument("--check",action="store_true");p.add_argument("--refresh",action="store_true");p.add_argument("--source-cache");a=p.parse_args()
    specs=read("similarity-specs.json")
    cat=catalog(specs,a.source_cache) if a.refresh or a.source_cache else read("external-catalog.json")
    products={"external-catalog.json":cat,"similarity-search.json":generate(cat,specs)}
    for name,data in products.items():
        content=body(data)
        assert len(content.encode())<1000000,name
        if a.check:assert (HERE/name).read_text()==content,"STALE "+name
        else:(HERE/name).write_text(content)
    print("SIMILARITY_SEARCH_PASS",json.dumps(products["similarity-search.json"]["search_scope"],sort_keys=True))
if __name__=="__main__":main()
