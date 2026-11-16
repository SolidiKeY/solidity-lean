#!/usr/bin/env python3
"""Reproduce the frozen-base statement inventory. Run at repo root with Python 3 -I.
No Lean elaboration. Import popularity means distinct direct importing modules,
not theorem use. Ties: path, then source line. All tracked Lean sources are
searched for goal attributes; public ranking is Solidity/ theorem/lemma only.
The parser masks nested comments and strings, retains offsets, and records raw
binders plus active variable/open/namespace commands (not elaborated types).
"""
import argparse,collections,csv,hashlib,json,pathlib,re,subprocess,tarfile,functools
BASE='d4ad633a9624263a59b14fd2c520b9bc602f88f3'
COMPLETION_AUTHORIZATION={
    'H243': {'question':'Q-STMT-REF-01','decision':'Find a theorem that looks similar. Before marking a row non-comparable, search for the nearest external compiler theorem. Use ratio=null with the exact reason only when none is similar.'},
    'H244': {'question':'Q-STMT-PROV-01','decision':'A: accept the frozen inventory; report confirmed-generated, explicitly-handwritten and untraced separately; no claim about historical handwriting totals.'}
}
HERE=pathlib.Path(__file__).resolve().parent
ROOT=HERE.parents[3]
def git(*args): return subprocess.check_output(['git',*args],cwd=ROOT,text=True).strip()
@functools.lru_cache(maxsize=None)
def frozen_text(path):
    return subprocess.check_output(['git','show',BASE+':'+path],cwd=ROOT).decode('utf-8')

def frozen_lean():
    # Git pathspec *.lean recursively selects tracked Lean blobs at BASE.
    proc=subprocess.Popen(['git','archive',BASE,'--','*.lean'],cwd=ROOT,stdout=subprocess.PIPE)
    texts={}
    with tarfile.open(fileobj=proc.stdout,mode='r|') as archive:
        for entry in archive:
            if entry.isfile():texts[entry.name]=archive.extractfile(entry).read().decode('utf-8')
    if proc.wait():raise RuntimeError('Cannot read frozen Lean archive')
    return texts

def mask(s):
    out=list(s); i=0; depth=0; string=False
    while i<len(s):
        if depth:
            if s[i:i+2]=='/-': depth+=1; out[i:i+2]='  '; i+=2; continue
            if s[i:i+2]=='-/': depth-=1; out[i:i+2]='  '; i+=2; continue
            if s[i]!='\n':out[i]=' '
            i+=1;continue
        if string:
            if s[i]=='\\':
                out[i]=' ';i+=1
                if i<len(s) and s[i]!='\n':out[i]=' '
            elif s[i]=='"':out[i]=' ';string=False
            elif s[i]!='\n':out[i]=' '
            i+=1;continue
        if s[i:i+2]=='/-':depth=1;out[i:i+2]='  ';i+=2;continue
        if s[i:i+2]=='--':
            j=s.find('\n',i);j=len(s) if j<0 else j
            out[i:j]=' '*(j-i);i=j;continue
        if s[i]=='"':out[i]=' ';string=True
        i+=1
    return ''.join(out)
DECL=re.compile(r'^[ \t]*(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable|unsafe)\s+)*(theorem|lemma|abbrev|def)\s+([^\s:({\[]+)',re.M)
def split_type(s):
    depth=0
    for i,c in enumerate(s):
        if c in '([{⦃':depth+=1
        elif c in ')]}⦄':depth-=1
        elif c==':' and depth==0:return s[:i].strip(),s[i+1:].strip()
    return s.strip(),''
def declarations(path,raw,clean):
    found=list(DECL.finditer(clean)); rows=[]
    for index,m in enumerate(found):
        end=found[index+1].start() if index+1<len(found) else len(clean)
        eq=-1;depth=0;equations=False
        for pos in range(m.end(),end):
            ch=clean[pos]
            if ch in '([{⦃':depth+=1
            elif ch in ')]}⦄':depth-=1
            elif depth==0 and clean[pos:pos+2]==':=':eq=pos;break
            elif depth==0 and ch=='|' and clean[clean.rfind('\n',m.end(),pos)+1:pos].strip()=='':eq=pos;equations=True;break
        if eq<0:continue
        header=raw[m.end():eq].strip();binders,conclusion=split_type(header)
        proof=clean[eq if equations else eq+2:end].strip()
        # Capture the first proof command for classification, not the whole file tail.
        ns=[]
        for a in re.finditer(r'^\s*(namespace|section|end)\b([^\n]*)',clean[:m.start()] if path in ('Solidity/Theorems.lean','Solidity/Calculus/Closers.lean','Solidity/Source/SemanticsExamples.lean') else '',re.M):
            if a[1]=='end':
                if ns:ns.pop()
            else:ns.append(a[2].strip())
        name=m[2];qualified=name.removeprefix('_root_.') if name.startswith('_root_.') else '.'.join([n for n in ns if n]+[name])
        context=[]
        for a in re.finditer(r'^(?:variable|open)\b[^\n]*(?:\n[ \t]+[^\n]+)*',clean[:m.start()] if path in ('Solidity/Theorems.lean','Solidity/Calculus/Closers.lean','Solidity/Source/SemanticsExamples.lean') else '',re.M):
            context.append(raw[a.start():a.end()])
        rows.append(dict(path=path,line=raw[:m.start()].count('\n')+1,name=name,qualified_name=qualified,kind=m[1],premises=binders,conclusion=conclusion,context='\n'.join(context),proof_first=proof.splitlines()[0] if proof else '',private=bool(re.search(r'\bprivate\b',m[0])),header=header,statement_lines=len(raw[m.start():eq].strip().splitlines())))
    return rows

def generation(path,raw):
    if path in ('Solidity.lean','SolidityExamples.lean','Bridge/SolidityBridge.lean'):return 'generated_roots'
    if path in ('Solidity/Corpus/Basic.lean','Solidity/Corpus/Imported.lean'):return 'handwritten_explicit_exception'
    if '/Corpus/' in path or path=='SolidityCorpus.lean':return 'generated_corpus'
    if path in ('Solidity/Yul/Checks/Bytes.lean','Solidity/Yul/Checks/Powers.lean') or re.fullmatch(r'Solidity/Yul/Checks/(?:Shifts/Part0[0-3]|Arithmetic/Part0[0-2])\.lean',path):return 'generated_vector_table'
    if 'AxiomPins' in path:return 'generated_axiom_pins'
    marked=bool(re.search(r'(?i)(?:auto[- ]?generated|generated by|do not edit)',raw[:1600]))
    candidate=bool(re.search(r'(?i)(agreement|chain)',path))
    if marked:return 'generated_chain_agreement' if candidate else 'generated_marked_other'
    return 'unresolved_chain_agreement' if candidate else 'unmarked_other'

def generate():
    texts=frozen_lean();paths=sorted(texts);clean={};decls=[];fan=collections.defaultdict(set);goals=[];inventory=collections.Counter()
    for path in paths:
        raw=texts[path];c=mask(raw);clean[path]=c
        cat=generation(path,raw)
        inventory[cat+'_files']+=1;inventory[cat+'_lines']+=len(raw.splitlines())
        for imp in set(re.findall(r'^\s*(?:public\s+|meta\s+)*import\s+(\S+)',c,re.M)):fan[imp].add(path)
        for a in re.finditer(r'@\[[^]]*\bgoal\b[^]]*\]',c):goals.append(dict(path=path,line=raw[:a.start()].count('\n')+1,attribute=raw[a.start():a.end()]))
        if path.startswith('Solidity/'):decls+=declarations(path,raw,c)
    public=[d for d in decls if d['kind'] in ('theorem','lemma') and not d['private']]
    for d in public:
        importers=fan[d['path'][:-5].replace('/','.')]
        d['direct_importers']=len(importers)
        d['unmarked_importers']=sum(not generation(p,texts[p]).startswith('generated_') for p in importers)
    top=sorted(public,key=lambda d:(-d['direct_importers'],d['path'],d['line']))[:30]
    selected={ (d['path'],d['line']):dict(d,selection='top30_imported_module') for d in top }
    for d in decls:
        if d['path']=='Solidity/Theorems.lean':
            key=d['path'],d['line'];selected[key]=dict(d,selection=selected.get(key,{}).get('selection','')+';Theorems.lean')
    for a in goals:
        following=[d for d in decls if d['path']==a['path'] and d['line']>=a['line']]
        if following:
            d=following[0];selected[d['path'],d['line']]=dict(d,selection='goal')
    notes=json.loads((HERE/'judgements.json').read_text()); rows=[]
    for d in sorted(selected.values(),key=lambda d:(d['path'],d['line'])):
        key=d['path']+'#'+d['name'];note=notes.get(key)
        if note is None:raise ValueError('Missing judgement '+key)
        d.update(note);d.pop('private');d.pop('header');d.setdefault('direct_importers',len(fan[d['path'][:-5].replace('/','.')]));d.setdefault('unmarked_importers','')
        d['reference_calibration']=json.dumps([x for x in json.loads((HERE/'calibration.json').read_text())['comparisons'] if x['unit']==key] or [dict(unit=key,ratio=None,reason=d['non_comparability_reason'],authorization='H243')])
        d['external_theorem_search']=json.dumps(next(x for x in json.loads((HERE/'similarity-search.json').read_text())['rows'] if x['unit']==key))
        d['generated_status']=generation(d['path'],texts[d['path']])
        d['importer_generation_breakdown']=json.dumps(dict(sorted(collections.Counter(generation(p,texts[p]) for p in fan[d['path'][:-5].replace('/','.')]).items())))
        d['known_generated_importers']=d['direct_importers']-d['unmarked_importers'] if isinstance(d['unmarked_importers'],int) else '';rows.append(d)
    sources=['docs/audits/architecture-tools','docs/audits/proof-coverage-tools','docs/audits/build-speed-tools','docs/audits/build-speed.md','scripts/build-measure.py','scripts/build-measure-report.py','scripts/differential','scripts/bench']
    base_paths=git('ls-tree','-r','--name-only',BASE).splitlines()
    inv=[dict(path=p,present=any(q==p or q.startswith(p+'/') for q in base_paths)) for p in sources]
    problems=json.loads((HERE/'problems.json').read_text())
    timing=frozen_text('docs/audits/architecture-tools/timing-sample.tsv').splitlines()
    summary=dict(base=BASE,completion_authorization=COMPLETION_AUTHORIZATION,method=dict(command='python3 -I docs/audits/direction-tools/statements/scan.py --check',source='All source blobs, paths, inventory availability and timing sample read from Git objects at BASE, independent of current checkout or merged HEAD.',selection='All @[goal] in tracked Lean; all theorem/lemma/abbrev/def in Solidity/Theorems.lean; top 30 public theorems by distinct direct importers of their defining module, ties path then line. This is module exposure, not declaration usage. Includes examples explicitly.',generated='Roots, Corpus, AxiomPins, marked chain/agreement and other marked generation separated. Chain/agreement without markers is an explicit unresolved bucket, never called handwritten. Selected declaration files have no generation marker; no theorem strength verdict depends on generated counts. provenance.py traces known root/corpus/vector producers, including the explicit handwritten Basic/Imported corpus exceptions, and distinguishes chain-generator source uses from expanded proof terms. Historical authorship of untraced files remains unknown; no scale/effort verdict uses that unknown bucket.',parsing='Source-level, not elaborated. Premises column is explicit binders; arrows remain in conclusion. Context preserves open/variable commands, including commands from earlier ended sections; consult source for exact scope. No proof rechecked.',ratios='calibrate.py compares complete public compiler endpoint declaration code (statement plus proof) and matched finite scenario input counts in the pinned solc snapshot; it never measures headers alone or treats source size as transitive proof effort. The user clarification to H243 requires a nearest external compiler theorem search before non-comparability. similarity.py searches 11 pinned compiler/verification files, records inspected candidates, pairs similar propositions while stating differences, and retains null only with a row-specific reason. Declaration size never measures transitive proof effort.'),counts=dict(inventory,tracked_lean_files=len(paths),goal_attributes=len(goals),public_theorems=len(public),top_imported= len(top),selected=len(rows),headline_theorems=sum(d['path']=='Solidity/Theorems.lean' and d['kind']=='theorem' for d in rows),classifications=dict(collections.Counter(d['strength'] for d in rows)),witnesses=dict(collections.Counter(d['witness_status'] for d in rows)),matched_units=sum(any(x.get('ratio') is not None for x in json.loads(d['reference_calibration'])) for d in rows),unmatched_units=sum(all(x.get('ratio') is None for x in json.loads(d['reference_calibration'])) for d in rows)),goals=goals,inventory_reuse=inv,timings=dict(path='docs/audits/architecture-tools/timing-sample.tsv',rows=len(timing),sha256=hashlib.sha256(('\n'.join(timing)+'\n').encode()).hexdigest(),use='Existing sample only; no per-selected-theorem timing inferred'),references=json.loads((HERE/'references.json').read_text()),reference_calibration=json.loads((HERE/'calibration.json').read_text()),external_theorem_search=json.loads((HERE/'similarity-search.json').read_text())['search_scope'],cross_lane_reuse=json.loads((HERE/'reuse.json').read_text()),generation_provenance=dict(report='provenance.json',counts=json.loads((HERE/'provenance.json').read_text())['counts'],boundary=json.loads((HERE/'provenance.json').read_text())['handwritten_boundary'],categories=json.loads((HERE/'provenance.json').read_text())['category_summary']),top_problems=problems,waits=[],limitations=['Source-level witness audit, not fresh Lean elaboration; no build or timing run performed.','scripts/differential and scripts/bench are absent at the pinned base; no results inferred.','Null ratios follow the recorded nearest-theorem search but do not prove global absence outside its pinned files. Similarity is a reviewed semantic judgement, not inferred from keyword hits.','H244 accepts the frozen generated/handwritten/untraced inventory without historical handwriting totals.'],axioms_added=0,sorry_added=0,conclusion='Headline calculus theorems match their stated intrinsic-model scope. Compiler statements retain payment/refusal and abstraction gaps against behavioural refinement. Source examples are useful fixed-case checks, not general semantic preservation. No evidence here justifies judging overall project size redundant.')
    return rows,summary

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--check',action='store_true');args=ap.parse_args()
    rows,summary=generate()
    import io
    buf=io.StringIO(newline='');writer=csv.DictWriter(buf,fieldnames=list(rows[0]),lineterminator='\n');writer.writeheader();writer.writerows(rows)
    outputs={'statements.csv':buf.getvalue(),'summary.json':json.dumps(summary,ensure_ascii=False,indent=2)+'\n'}
    for name,body in outputs.items():
        if args.check:
            if (HERE/name).read_text()!=body:raise SystemExit('STALE '+name)
        else:(HERE/name).write_text(body)
    print(json.dumps(dict(status='PASS',selected=len(rows),goal_attributes=summary['counts']['goal_attributes'],classifications=summary['counts']['classifications']),sort_keys=True))
if __name__=='__main__':main()
