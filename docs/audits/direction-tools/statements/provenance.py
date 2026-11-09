#!/usr/bin/env python3
"""Frozen source-generation provenance; no producer or Lean execution.
Run: python3 -I docs/audits/direction-tools/statements/provenance.py [--check]
Known generators/explicit exceptions are separated from untraced source, never
inferred from an Agreement/Chain filename. Expanded tactic terms are not LOC.
"""
import argparse,collections,hashlib,json,pathlib,re,runpy
HERE=pathlib.Path(__file__).resolve().parent
API=runpy.run_path(str(HERE/"scan.py"),run_name="provenance_api")

def generate():
    texts=API["frozen_lean"]();records=[];counts=collections.Counter()
    vector_manifest=json.loads(API["frozen_text"]("tests/h55/vectors-tables/vector-manifest.json"))
    vectors=vector_manifest["files"]
    corpus_gate=API["frozen_text"]("scripts/check-corpus.sh")
    assert "Basic.lean and Imported.lean" in corpus_gate and "hand-written" in corpus_gate
    selected={r["path"] for r in __import__("csv").DictReader((HERE/"statements.csv").open())}
    for path,raw in sorted(texts.items()):
        cat=API["generation"](path,raw);producer=None;reason=None
        if path in ("Solidity/Corpus/Basic.lean","Solidity/Corpus/Imported.lean"):
            cat="handwritten_explicit_exception";producer="scripts/check-corpus.sh";reason="Gate explicitly exempts these handwritten corpus source files."
        elif path in vectors:
            assert hashlib.sha256(raw.encode()).hexdigest()==vectors[path]["sha256"]
            cat="generated_vector_table";producer="scripts/h55/vectors-tables/vector_generator.py";reason="Frozen producer manifest authenticates complete generated vector module bytes."
        elif cat=="generated_corpus" or path=="SolidityCorpus.lean":
            cat="generated_corpus";producer="scripts/solkey-port.mjs";reason="Corpus producer output, excluding the two documented handwritten support files."
        elif cat=="generated_roots":producer="scripts/coord-tools/register.sh";reason="Registered generated import root."
        elif cat=="generated_axiom_pins":reason="Axiom-pin source kept separate from mathematical declarations; no claim of handwritten effort."
        elif cat=="unresolved_chain_agreement":reason="Filename alone is not producer evidence; source remains untraced, not assumed handwritten or generated."
        if producer:API["frozen_text"](producer)
        counts[cat+"_files"]+=1;counts[cat+"_lines"]+=len(raw.splitlines())
        clean=API["mask"](raw)
        uses=collections.Counter(re.findall(r"(?<![\w.])(?:#chain_rest|#chain|sol_chain)(?![\w])",clean))
        if uses or path in selected or "chain" in path.lower() or "agreement" in path.lower() or cat.startswith("generated_") or cat=="handwritten_explicit_exception":
            records.append(dict(path=path,category=cat,source_sha256=hashlib.sha256(raw.encode()).hexdigest(),producer=producer,reason=reason,explicit_theorem_lines=len(re.findall(r"^\s*(?:@\[[^]]*\]\s*)*(?:(?:private|protected)\s+)?(?:theorem|lemma)\s",clean,re.M)),chain_generator_lexical_uses=dict(uses),selected=path in selected))
    groups={"confirmed_generated_by_inventory":lambda c:c.startswith("generated_") and c!="generated_axiom_pins","explicitly_handwritten":lambda c:c=="handwritten_explicit_exception","untraced":lambda c:c in ("unmarked_other","unresolved_chain_agreement"),"axiom_pins_separate":lambda c:c=="generated_axiom_pins"}
    categories={name:{metric:sum(n for key,n in counts.items() if key.endswith("_"+metric) and predicate(key[:-(len(metric)+1)])) for metric in ("files","lines")} for name,predicate in groups.items()}
    assert sum(v["files"] for v in categories.values())==len(texts)
    assert sum(v["lines"] for v in categories.values())==sum(len(t.splitlines()) for t in texts.values())
    chain=API["frozen_text"]("Solidity/Calculus/ChainGen.lean")
    assert "elab_rules : command" in chain and "logInfo" in chain and "def generate" in chain
    return dict(base=API["BASE"],completion_authorization=API["COMPLETION_AUTHORIZATION"]["H244"],category_summary=categories,category_boundary="Confirmed-generated means identified by the frozen producer/marker inventory. Axiom-pin files are reported separately, not treated as mathematical handwriting. Untraced includes both unmarked source and unresolved Chain/Agreement filenames; no historical handwriting total is inferred.",method="Complete frozen Lean source inventory. Known file producers and documented handwritten exceptions override markers. Unknown provenance remains explicit; no historical authorship certificate inferred.",counts=dict(sorted(counts.items())),records=records,generator_boundary=dict(chain=dict(source="Solidity/Calculus/ChainGen.lean",mechanism="Chain.generate plus #chain/#chain_rest print suggested declarations; sol_chain constructs proof terms. Explicit source declarations are counted once; expanded proof terms are not source LOC.",selected_file_lexical_uses=sum(sum(r["chain_generator_lexical_uses"].values()) for r in records if r["selected"])),agreement="Agreement-named source modules are not automatically generated modules. No canonical file producer has been established for every such path; those records retain untraced provenance."),handwritten_boundary="Only explicit check-corpus.sh exceptions are positively labelled handwritten. Unmarked source and filename candidates are not combined with confirmed handwriting; overall historical handwriting count is unknown.")

def main():
    p=argparse.ArgumentParser();p.add_argument("--check",action="store_true");a=p.parse_args()
    data=generate();body=json.dumps(data,ensure_ascii=False,indent=2)+"\n";target=HERE/"provenance.json"
    if a.check:assert target.read_text()==body,"STALE provenance.json"
    else:target.write_text(body)
    print("PROVENANCE_PASS",len(data["records"]),"categorized records; selected generator uses",data["generator_boundary"]["chain"]["selected_file_lexical_uses"])
if __name__=="__main__":main()
