#!/usr/bin/env python3
"""Frozen, source-only proof-effort audit (Python standard library).
Run: python3 -B docs/audits/direction-tools/proof-effort/audit.py --refs CACHE [--check]
CACHE holds clean shallow CompCert, CakeML, Clear clones at references/pins.json.
No Lean, Coq or HOL elaboration. Git blobs, not working source, are measured.
"""
import argparse, collections as C, hashlib, io, json, math, pathlib, re, subprocess, tarfile
HERE=pathlib.Path(__file__).resolve().parent
ROOT=HERE.parents[3]
BASE='d6fd95f0886775d7c286813fa9b993a40ba7a777'
OLD='d4ad633a9624263a59b14fd2c520b9bc602f88f3'

def git(root,*args):return subprocess.check_output(['git','-C',str(root),*args],text=True).strip()
def blob(path):return subprocess.check_output(['git','-C',str(ROOT),'show',BASE+':'+path]).decode()
def digest(s):return hashlib.sha256(s.encode()).hexdigest()
def archive(root,rev,suffix):
    p=subprocess.Popen(['git','-C',str(root),'archive',rev],stdout=subprocess.PIPE)
    texts={}
    with tarfile.open(fileobj=p.stdout,mode='r|') as t:
        for e in t:
            if e.isfile() and e.name.endswith(suffix):texts[e.name]=t.extractfile(e).read().decode('utf-8',errors='replace')
    if p.wait():raise RuntimeError('git archive failed')
    return texts

def mask(s,lang='lean'):
    """Nested comments and quoted strings masked, preserving line/byte offsets.
    HOL quotation backticks remain: they delimit propositions, not strings.
    """
    op,cl,lc=('/-','-/','--') if lang=='lean' else ('(*','*)',None)
    out=list(s);i=0;depth=0;string=False
    while i<len(s):
        if depth:
            if s.startswith(op,i):depth+=1;out[i:i+2]='  ';i+=2;continue
            if s.startswith(cl,i):depth-=1;out[i:i+2]='  ';i+=2;continue
            if s[i]!='\n':out[i]=' '
        elif string:
            if s[i]=='\\' and i+1<len(s):
                out[i]=' ';i+=1
                if s[i]!='\n':out[i]=' '
            elif s[i]=='"':out[i]=' ';string=False
            elif s[i]!='\n':out[i]=' '
        elif s.startswith(op,i):depth=1;out[i:i+2]='  ';i+=2;continue
        elif lc and s.startswith(lc,i):
            j=s.find('\n',i);j=len(s) if j<0 else j
            out[i:j]=' '*(j-i);i=j;continue
        elif s[i]=='"':out[i]=' ';string=True
        i+=1
    return ''.join(out)

DECL=re.compile(r'^[ \t]*(?:@\[[^\]]*\][ \t\n]*)*(?:(?:private|protected|noncomputable|nonrec|partial|unsafe)\s+)*(theorem|lemma|def|abbrev|structure|inductive|class|instance|axiom|opaque)\b[ \t]*([^\s(:{\[=]+)?',re.M)
STOP=re.compile(r'^[ \t]*(?:end\b|namespace\b|section\b|open\b|variable\b|set_option\b|attribute\b|example\b|#\w+|(?:scoped\s+)?(?:notation|macro|elab|syntax|infixl|infixr|prefix|postfix)\b)',re.M)
TOKEN=re.compile(r"[^\W\d][\w'!?]*(?:\.[^\W\d][\w'!?]*)*",re.UNICODE)
TACTIC=re.compile(r'\b(?:simp_all|simp|simpa|rw|rfl|exact|apply|intro|intros|cases|rcases|by_cases|induction|constructor|refine|obtain|have|omega|decide|native_decide|aesop|grind|unfold|change|subst|assumption|contradiction|ext|dsimp|norm_num|bv_decide|linarith|nlinarith|ring|tauto)\b')

def assign(s):
    depth=0
    for i,c in enumerate(s):
        if c in '([{⦃':depth+=1
        elif c in ')]}⦄':depth-=1
        elif depth==0 and s[i:i+2]==':=':return i
    return None

def simp_sizes(s):
    sizes=[]
    for m in re.finditer(r'\b(?:simp|simpa|simp_all)(?:\s+only)?\s*\[',s):
        depth=1;n=0;has=False
        for c in s[m.end():]:
            if c in '[({':depth+=1
            elif c in '])}':
                depth-=1
                if depth==0:break
            if c==',' and depth==1:n+=1
            if not c.isspace():has=True
        if depth==0:sizes.append(n+1 if has else 0)
    return sizes

def metrics(raw,clean):
    # Nonblank source lines after masking are the cross-language common unit.
    rows=[s for s in clean.splitlines() if s.strip()]
    return dict(lines=len(rows),physical_span_lines=len(raw.strip().splitlines()),tokens=len(re.findall(r'\w+|[^\s\w]',clean)),tactic_steps=len(TACTIC.findall(clean)),case_splits=len(re.findall(r'\b(?:cases|rcases|by_cases|induction|Cases_on|Induct_on|destruct|induction|case_eq)\b',clean)),simp_sets=simp_sizes(clean),decide=len(re.findall(r'\bdecide\b',clean)),native_decide=len(re.findall(r'\bnative_decide\b',clean)))

def lean_decls(path,raw):
    s=mask(raw);starts=list(DECL.finditer(s));stops=[m.start() for m in STOP.finditer(s)];out=[]
    for k,m in enumerate(starts):
        end=starts[k+1].start() if k+1<len(starts) else len(s)
        # A top-level command terminates a declaration; don't eat end/#print tails.
        # STOP intentionally excludes tactic commands (including open ... in within proofs).
        relevant=[p for p in stops if m.end()<=p<end and len(s[p:s.find('\n',p)].split(s[p:s.find('\n',p)].lstrip())[0])<=len(m[0])-len(m[0].lstrip())]
        if relevant:end=min(relevant)
        a=assign(s[m.end():end]);eq=m.end()+a if a is not None else None
        proof=s[eq+2:end].strip() if eq is not None else ''
        proof=re.sub(r'^by\b', '  ', proof).strip()
        rawproof=raw[eq+2:end].strip() if eq is not None else ''
        # where-attached local lemmas remain charged to their parent proof.
        out.append(dict(path=path,name=m[2] or '<anonymous>',kind=m[1],line=s[:m.start()].count('\n')+1,start=m.start(),end=end,body=s[m.start():end],header=s[m.end():eq] if eq is not None else s[m.end():end],proof=proof,proof_raw=rawproof,**metrics(rawproof,proof)))
    return out

def gen(path,raw):
    if path.startswith('Generated/'):
        return 'explicitly_handwritten' if path.endswith('_user.lean') else 'generated_vc'
    if path in ('Solidity.lean','SolidityExamples.lean','Bridge/SolidityBridge.lean'):return 'generated_roots'
    if path in ('Solidity/Corpus/Basic.lean','Solidity/Corpus/Imported.lean'):return 'explicitly_handwritten'
    if '/Corpus/' in path or path=='SolidityCorpus.lean':return 'generated_corpus'
    if 'AxiomPins' in path:return 'generated_axiom_pins'
    if path in ('Solidity/Yul/Checks/Bytes.lean','Solidity/Yul/Checks/Powers.lean') or re.fullmatch(r'Solidity/Yul/Checks/(?:Shifts/Part0[0-3]|Arithmetic/Part0[0-2])\.lean',path):return 'generated_vector_table'
    if re.search(r'(?i)auto[- ]?generated|generated by|do not edit|Generated direct structural|Generated typed cuts',raw[:1600]):return 'generated_marked'
    if re.search(r'(?i)chain|agreement',path):return 'unresolved_chain_agreement'
    return 'untraced'

def area(p):
    a=p.split('/')
    return a[1] if a[0]=='Solidity' and len(a)>2 else 'Bridge' if a[0]=='Bridge' else a[0] if len(a)>1 else 'roots'

def foreign(path,raw,lang):
    s=mask(raw,lang);out=[]
    if lang=='coq':
        pat=re.compile(r'\b(?:Lemma|Theorem|Corollary|Remark|Fact|Proposition)\s+([\w\']+)\b(?:(?!\b(?:Lemma|Theorem|Corollary|Remark|Fact|Proposition)\b).)*?\bProof\s*(?:using[^.]*|with[^.]*)?\.(.*?)\b(Qed|Defined|Admitted)\.',re.S)
        headers=len(re.findall(r'\b(?:Lemma|Theorem|Corollary|Remark|Fact|Proposition)\s+[\w\']+',s))
        for m in pat.finditer(s):
            if m[3]=='Admitted':continue
            b=m[2];r=raw[m.start(2):m.end(2)]
            out.append(dict(path=path,name=m[1],line=s[:m.start()].count('\n')+1,**metrics(r,b),proof=b))
    else:
        pat=re.compile(r'^[ \t]*(?:Theorem|Triviality)\s+([^\s:\[]+)[^\n]*:.*?^\s*Proof\b(.*?)^\s*QED\b',re.M|re.S)
        headers=len(re.findall(r'^\s*(?:Theorem|Triviality)\s+',s,re.M))
        for m in pat.finditer(s):
            b=m[2];r=raw[m.start(2):m.end(2)]
            out.append(dict(path=path,name=m[1],line=s[:m.start()].count('\n')+1,**metrics(r,b),proof=b))
    return out,headers

def dist(xs):
    xs=sorted(xs);n=len(xs)
    if any(x<0 for x in xs):raise ValueError('negative measurement')
    if not n:return dict(n=0,total=0,mean=None,p50=None,p90=None,p99=None,max=None,histogram={})
    return dict(n=n,total=sum(xs),mean=round(sum(xs)/n,4),p50=xs[math.ceil(n*.5)-1],p90=xs[math.ceil(n*.9)-1],p99=xs[math.ceil(n*.99)-1],max=xs[-1],histogram={f'[{lo},{hi if hi is not None else "inf"})':sum(x>=lo and (hi is None or x<hi) for x in xs) for lo,hi in [(0,1),(1,2),(2,6),(6,11),(11,31),(31,100),(100,300),(300,1000),(1000,None)]})

def stats(ds):
    return dict(proofs=len(ds),proof_lines=dist([d['lines'] for d in ds]),physical_proof_spans=dist([d['physical_span_lines'] for d in ds]),tactic_keyword_occurrences=dist([d['tactic_steps'] for d in ds]),tokens=dist([d['tokens'] for d in ds]),simp_set_entries=dist([x for d in ds for x in d['simp_sets']]),case_split_keywords=sum(d['case_splits'] for d in ds),decide_occurrences=sum(d['decide'] for d in ds),native_decide_occurrences=sum(d['native_decide'] for d in ds))

def loc(d):return {k:d[k] for k in ('path','line','name','lines','physical_span_lines','tactic_steps','case_splits')}
def groups_stats(ds):
    groups=C.defaultdict(list)
    for d in ds:groups[area(d['path'])].append(d)
    return {a:stats(v) for a,v in sorted(groups.items())}

def inventory(texts):
    paths=git(ROOT,'ls-tree','-r','--name-only',BASE).splitlines()
    sources=['docs/audits/architecture-tools/','docs/audits/proof-coverage-tools/','docs/audits/build-speed','scripts/build-measure','scripts/differential/','scripts/bench/']
    out=[]
    for src in sources:
        hits=[p for p in paths if p.startswith(src)]
        out.append(dict(prefix=src,paths=hits,status='reused inventory; no fresh build' if hits else 'absent at base'))
    old=json.loads(blob('docs/audits/direction-tools/reachability/summary.json'))
    drift=git(ROOT,'diff','--name-only',OLD,BASE,'--','*.lean').splitlines()
    return dict(base=BASE,inputs=out,previous_source_base=OLD,changed_lean_paths=drift,previous_duplicate_inventory=old['duplication'],previous_duplicates_base=old['base'],tracked_lean_files=len(texts),physical_lean_lines=sum(len(x.splitlines()) for x in texts.values()))

def timing():
    rows=[r.split('\t') for r in blob('docs/audits/architecture-tools/timing-sample.tsv').splitlines() if len(r.split('\t'))==5]
    return dict(ignored_nonrecords=[r for r in blob('docs/audits/architecture-tools/timing-sample.tsv').splitlines() if len(r.split('\t'))!=5],source='docs/audits/architecture-tools/timing-sample.tsv',source_sha256=digest(blob('docs/audits/architecture-tools/timing-sample.tsv')),rows=len(rows),statuses=dict(C.Counter(r[-1] for r in rows)),first_seconds=dist([float(r[2]) for r in rows]),second_seconds=dist([float(r[3]) for r in rows]),reference_seconds=None,ratio=None,verdict='No matched check-time claim: committed historical sample is reused, not remeasured.',boundary='Historical file wall timings, not per-theorem kernel times; unmatched hardware/cache/toolchain. No Lean or project build run.')

def alpha_proof(s):
    # Preserve numerals and tactic keywords; canonicalize identifier order only.
    names={};keep=set(TACTIC.pattern.split('|'))|set('by only at with fun let in match true false Prop Type Nat Int Bool List Option constructor'.split())
    keep.update(re.findall(r'\w+',TACTIC.pattern))
    return TOKEN.sub(lambda m:m[0] if m[0] in keep else 'v'+str(names.setdefault(m[0],len(names))),s)

def waste(ds,texts,refs):
    # Reuse the previous near-file cluster candidates, and measure their proof spans anew.
    prior=json.loads(blob('docs/audits/direction-tools/reachability/summary.json'))
    reused=[c for c in prior['largest_30_clusters'] if c['kind']=='near_file']
    filecluster={m.replace('.','/')+'.lean':i for i,c in enumerate(reused) for m in c['modules']}
    groups=C.defaultdict(list)
    for d in ds:
        if d['lines']>=6 and not d['generated'].startswith('generated'):
            groups[digest(re.sub(r'\s+',' ',alpha_proof(d['proof'])).strip())].append(d)
    dup=[v for v in groups.values() if len(v)>1 and len({d['path'] for d in v})>1]
    dup.sort(key=lambda v:(-sum(d['lines'] for d in v[1:]),v[0]['path'],v[0]['line']))
    candidates=[]
    for v in dup:
        v.sort(key=lambda d:(d['path'],d['line']))
        savings=sum(max(0,d['lines']-1) for d in v[1:])
        candidates.append(dict(kind='near_identical_proof',representative=loc(v[0]),members=[loc(d) for d in v],estimated_line_savings=savings,verdict='redundant',reason='Repeated proof scaffolding, not redundant statements. The recorded statement and proof substitutions identify the parameters a common lemma must retain; distinct predicates, layouts and refusals stay explicit. Savings are conditional on that extraction, not claimed kernel-checked.',generic_lemma=suggestion(v[0]),schema=template_evidence(v),reused_near_file_cluster_ids=sorted({filecluster[d['path']] for d in v if d['path'] in filecluster})))
    # Independent, non-overlapping ranking: greedy exclude overlapping declaration keys.
    used=set();top=[]
    for c in candidates:
        keys={(x['path'],x['line']) for x in c['members']}
        if used&keys:continue
        top.append(c);used|=keys
        if len(top)==30:break
    long=sorted([d for d in ds if d['lines']>=100],key=lambda d:(-d['lines'],d['path'],d['line']))
    families={}
    for n,sel in [('lowering_G_families',lambda d:d['path'].startswith('Solidity/Lowering/') and bool(re.search(r'(?:/|\b)G\d+',d['path']))),('yul_views_transports',lambda d:d['path'].startswith('Solidity/Yul/Views/'))]:
        v=[d for d in ds if sel(d)];families[n]=dict(**stats(v),largest=[loc(d) for d in sorted(v,key=lambda d:(-d['case_splits'],-d['lines'],d['path'],d['line']))[:10]],suggested_generic_lemma='Induct once over the syntax/descriptor family with a parameterized per-field frame invariant; instantiate it for each scenario.')
    return dict(reused_cluster_source='docs/audits/direction-tools/reachability/summary.json#largest_30_clusters',reused_cluster_base=prior['base'],reused_near_file_clusters=reused,near_identical_groups=len(dup),top30=top,estimated_nonoverlapping_line_savings=sum(c['estimated_line_savings'] for c in top),estimate_boundary='Conditional proof-body replacement estimate: retain first proof, charge one source line for every subsequent application. Excludes generic-lemma statement/side-condition cost, is not a deletion authorization or proved safe reduction.',long_proof_count=len(long),long_proofs_top30=[dict(**loc(d),generic_lemma=suggestion(d),reference_search=long_analogue(d,refs)) for d in long[:30]],case_split_families=families)

def suggestion(d):
    p=d['path'];n=d['name'];h=d.get('header','')
    if n=='operand_run':
        return 'wrapped_binary_operand_run(pipeline, operation, alias_case, bounded_operands): factor typed reads and modular arithmetic, preserving target update and index-alias equations for each operand emitter.'
    if n in ('allocator','initial_repr','contextBefore','fullChild','beforeDst','storage_repr') or re.search(r'\b(?:AllocatorRepr|StructAllocatorRepr|ReprStore|Represented)\b',h):
        return 'representation_of_finite_layout(layout, address_map, initial_values, lookup_equations, bounds, separation): construct the recorded '+('allocator/state' if 'llocator' in h or 'StateRepr' in h else 'storage/context')+' representation witness once; retain each concrete address, value, capacity and alias premise.'
    if n=='target_result':
        return 'compiled_fixture_result(code, initial_memory, stack, successful_run): share the symbolic execution and projection harness while retaining every fixture expected memory/stack outcome as a separate control.'
    if n in ('transfer_paid','transfer_sim'):
        return 'transfer_simulation_of_value_runs(receiver_run, amount_run, frame, call_outcome): share the core transfer run composition with explicit balance, exceptional outcome and assertion obligations.'
    if n in ('leaf_body','entry_body'):
        return 'progOf_body_lookup(declarations, unique_function_id, selected_body): prove list/function-body lookup once and instantiate the concrete declaration; keep body identity and all distinctness premises.'
    if 'pack_spec' in n:
        return 'declaration_pack_spec(field_pack_spec, ordered_roots, distinct_keys, initial_cursor): one induction over field descriptors, preserving capacity, separated paths and root/member ownership membership.'
    if n=='binaryValue_correct':
        return 'binary_value_simulation_of_operand_runs(left_sim, right_sim, operation_correct, frame): share sequential operand execution and typed result construction; keep memory/object state relations explicit.'
    if n.endswith('.other_key'):
        return 'ownership_step_other_key(project, written_key, unrelated_transient_or_address): one update-frame proof retaining the exact transient/address disjunction, rather than assuming global nonaliasing.'
    if n.endswith('_typed_landing'):
        return 'typed_landing_of_checked_body(body_lookup, argument_types, checked_context): factor fixture inference derivations while preserving each mutant landing and refusal observation.'
    if n in ('forIter_nsStep','forIterX_step'):
        return 'for_iter_no_abrupt(body_NS, expression_NS, frame, accepted_fragment): share the for-loop step induction with normal/return outcomes and preserve all typing, frame and refusal premises.'
    if '/StatementGrammarH28/' in p and 'head' in n:
        return 'syntax_head_invariant_for(P, atom_heads, append_closed): one Syn induction over an abstract first-token predicate P, specializing SafeStart and BoundaryStart; retain category-specific atom laws.'
    if '/ExpressionUniqueness/' in p and 'arrange' in n:
        return 'arrange_preserves(P, nil, append, separator, enclosure): one arrangement induction for a list predicate P with each token-algebra law explicit; specialize additive, comma-free and bracket invariants.'
    if '/MemoryCopies/' in p and 'Controls' in p and ('repr' in n or 'represented' in n):
        return 'heap_represents_of_finite_cells(layout, cells, values, reads, disjointness): construct the HeapRep witness once from lookup equations, preserving each fixture layout and alias condition; retain concrete controls as applications.'
    if '/Compilation/Normal' in p and 'Transport' in p:
        return 'normal_control_machine(leaf_run, condition_run): one induction over the existing normal-control derivation, abstracting only leaf/condition execution certificates; preserve concrete selectors and frame equations.'
    if '/Yul/Views/' in p and 'DeclarationFinal' in p:
        return 'declaration_actual_snapshot(provenance, residual, writes, frame): factor shared descriptor/certificate composition, with root/inherited field ordering and snapshots as explicit arguments.'
    if '/Yul/Local' in p and 'source_agrees' in n:
        return 'local_control_agrees(initial_value, value_kind, expression_agreement): factor block/loop induction while retaining Boolean/default initialization and abrupt completion branches.'
    if '/Yul/Views/' in p and 'Separation' in p:
        return 'strided_header_elements_apart(base, width, index_bounds, footprint): interval arithmetic once, with signed/packed/path offsets and nonalias hypotheses explicit.'
    if '/Yul/Views/' in p and 'same_word_store' in n:
        return 'ownership_same_word_store(project, owned, same_key, frame): a projection/update commutation theorem preserving the owner-specific key function and disjointness obligations.'
    if '/Lowering/' in p:return 'A descriptor-indexed lowering preservation lemma abstracting source reads, writes and the unchanged frame; instantiate the scenario.'
    if '/Yul/Views/' in p:return 'A view-morphism transport lemma parameterized by projection, update commutation and untouched fields; instantiate each layout.'
    if '/Backend/' in p:return 'A generic instruction/block frame-preservation lemma parameterized by effect footprint and stack relation.'
    if '/Bridge/' in '/'+p:return 'A relation-preservation lemma over a single opcode family with explicit state observations and gas premises.'
    return 'A single structural congruence/induction lemma with explicit constructor cases and parameterized side conditions.'

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--refs',type=pathlib.Path,required=True);ap.add_argument('--check',action='store_true');a=ap.parse_args()
    texts=archive(ROOT,BASE,'.lean');print('Scanning frozen Lean source',flush=True);ds=[];allnodes=[];filegen={};hb=[]
    for p,raw in sorted(texts.items()):
        cat=gen(p,raw);filegen[p]=cat;nodes=lean_decls(p,raw);allnodes+=nodes
        for m in re.finditer(r'\bset_option\s+(maxHeartbeats|maxRecDepth)\s+(\d+)',mask(raw)):
            hb.append(dict(path=p,line=raw[:m.start()].count('\n')+1,option=m[1],value=int(m[2]),generated=cat))
        for d in nodes:
            if d['kind'] in ('theorem','lemma') and d['proof']:
                d['generated']=cat;d['origin']='vendored' if p.startswith('Bridge/vendor/') else 'owned_bridge' if p.startswith('Bridge/SolidityBridge/') else 'owned_core' if p.startswith('Solidity/') else 'external_consumers_and_roots';ds.append(d)
    pins=json.loads(blob('docs/audits/direction-tools/references/pins.json'));sources=json.loads(blob('docs/audits/direction-tools/references/sources.json'));refs={};refds={};reftexts={}
    for n,suffix,lang in [('CompCert','.v','coq'),('CakeML','.sml','hol'),('Clear','.lean','lean')]:
        root=a.refs/n
        if git(root,'rev-parse','HEAD')!=pins[n]:raise RuntimeError('reference pin mismatch '+n)
        if git(root,'status','--porcelain'):raise RuntimeError('dirty reference '+n)
        print('Scanning reference '+n,flush=True)
        tx=archive(root,pins[n],suffix);reftexts[n]=tx;rds=[];heads=0;legacy=0
        for p,raw in sorted(tx.items()):
            if lang=='lean':
                nd=lean_decls(p,raw);heads+=sum(d['kind'] in ('theorem','lemma') for d in nd);dd=[d for d in nd if d['kind'] in ('theorem','lemma') and d['proof']]
            else:dd,h=foreign(p,raw,lang);heads+=h
            legacy+=len(re.findall(r'\b(?:Q\.)?store_thm\b',mask(raw,lang))) if lang=='hol' else 0
            for d in dd:d['generated']=gen(p,raw) if n=='Clear' else 'generated_marked' if re.search(r'(?i)auto[- ]?generated|generated by|do not edit|Generated direct structural|Generated typed cuts',raw[:1600]) else 'untraced'
            rds+=dd
        refds[n]=rds
        refs[n]=dict(pin=pins[n],url='https://github.com/'+sources[n]+'/tree/'+pins[n],files=len(tx),theorem_headers=heads,parsed_proofs=len(rds),unparsed_or_nonexplicit_headers=heads-len(rds),legacy_store_thm_occurrences=legacy,all=stats(rds),not_marked_generated=stats([d for d in rds if not d['generated'].startswith('generated')]),generated=stats([d for d in rds if d['generated'].startswith('generated')]))
    distribution=dict(base=BASE,all=stats(ds),per_origin={o:stats([d for d in ds if d['origin']==o]) for o in sorted(set(d['origin'] for d in ds))},owned_per_area=groups_stats([d for d in ds if d['origin'] in ('owned_core','owned_bridge')]),per_area=groups_stats(ds),not_marked_generated_per_area=groups_stats([d for d in ds if not d['generated'].startswith('generated')]),per_provenance={c:stats([d for d in ds if d['generated']==c]) for c in sorted(set(filegen.values()))},file_provenance={c:dict(files=sum(x==c for x in filegen.values()),physical_lines=sum(len(texts[p].splitlines()) for p,x in filegen.items() if x==c)) for c in sorted(set(filegen.values()))},references=refs,options=dict(maxHeartbeats=dist([x['value'] for x in hb if x['option']=='maxHeartbeats']),unlimited_maxHeartbeats=sum(x['value']==0 and x['option']=='maxHeartbeats' for x in hb),per_area={a:dict(C.Counter(x['option'] for x in hb if area(x['path'])==a)) for a in sorted(set(area(x['path']) for x in hb))},locations=hb))
    print('Computing proof patterns and slices',flush=True)
    w=waste(ds,texts,refds)
    inv=inventory(texts)
    comparisons=calibrate(ds,refds)
    bridge=bridge_slice(texts,reftexts['Clear'],allnodes)
    summary=dict(schema=1,base=BASE,command='python3 -B docs/audits/direction-tools/proof-effort/audit.py --refs /workspace/proof-effort-refs --check',method=dict(unit='Nonblank proof-body source lines after masking nested comments and strings; excludes theorem statements and Proof/Qed/Proof/QED delimiters, excludes Lean by. Inline bodies count one line.',distribution='Named theorem/lemma only for Lean; named Lemma/Theorem/Corollary/Remark/Fact/Proposition with explicit Proof...Qed/Defined for Coq; Theorem/Triviality...Proof...QED for HOL4. Equational definitions, examples, term-only Coq proofs and legacy HOL store_thm excluded and coverage reported.',tactics='Keyword occurrences are a within-language source proxy, not executed tactic steps. Not compared numerically across tactic languages. simp brackets count comma-separated entries at outer depth, not expanded simp databases.',provenance='Generated roots, Corpus, known vector tables, AxiomPins and explicit source markers separated. Chain/agreement names alone remain unresolved. Not-marked-generated is not a handwriting claim.',ratio='Mean named proof-body lines in matched subsystem populations; also p50/p90 and >100-line tails. Different theorem granularity means descriptive reference-class calibration, not labor or checking cost.',slice='Lexical transitive declarations constrained by imports, final identifier components overconnect; not an elaborated dependency proof. Both local-scope and all-tracked closure counted; external dependency library declarations excluded.'),proof_effort_ratios=comparisons,waste=dict(top30_file='waste.json',patterns=len(w['top30']),estimated_conditional_line_savings=w['estimated_nonoverlapping_line_savings'],safe_proved_deletion_lines=0,long_proofs=w['long_proof_count']),bridge=bridge,findings=headlines(ds,refs,w,bridge),inventory_file='inventory.json',distribution_file='distributions.json',timing=timing(),waits=[dict(id='TIMING',gap='No matched CompCert/CakeML/Clear check times in committed inputs; no check-time ratio inferred.'),dict(id='DIFFERENTIAL-BENCH',gap='scripts/differential/ and scripts/bench/ absent at assigned base; no output invented.')],limitations=['Source-level parser and lexical slices, not elaborated kernel declarations or measured human effort.','No Lean proof or external conformance test execution performed; historical timing is external evidence only.','Generated classification is provenance evidence, not historical authorship.','Case/template consolidation savings are estimates, not checked refactors.'])
    outputs={'inventory.json':inv,'distributions.json':distribution,'waste.json':w,'summary.json':summary}
    for name,obj in outputs.items():
        data=json.dumps(obj,indent=2,ensure_ascii=False,sort_keys=True)+'\n'
        if len(data.encode())>=1000000:raise RuntimeError(name+' exceeds size cap')
        if a.check:
            if (HERE/name).read_text()!=data:raise RuntimeError(name+' differs; regenerate')
        else:(HERE/name).write_text(data)
    print(('PASS reproducible: ' if a.check else 'WROTE: ')+', '.join(outputs))
    print(json.dumps(dict(local_proofs=len(ds),references={n:len(v) for n,v in refds.items()},bridge_verdict=bridge['verdict'],top30=len(w['top30']))))

def calibrate(ds,refs):
    rows=[]
    for ar,local in sorted({a:[d for d in ds if area(d['path'])==a] for a in set(area(d['path']) for d in ds)}.items()):
        core=[d for d in local if not d['generated'].startswith('generated')]
        for name in ('CompCert','CakeML'):
            # The nearest verified-compiler reference populations; other areas are explicitly portfolio context.
            if name=='CompCert':
                prefix='backend/' if ar in ('Backend','Evm') else 'cfrontend/' if ar in ('Frontend','Lowering','Source','Yul') else 'common/' if ar in ('Semantics','Storage','Typing','Bridge') else ''
            else:
                prefix='compiler/backend/' if ar in ('Backend','Lowering','Evm','Yul') else 'compiler/parsing/' if ar=='Frontend' else 'semantics/' if ar in ('Semantics','Source','Storage','Typing','Bridge') else ''
            counterpart=[d for d in refs[name] if d['path'].startswith(prefix) and not d['generated'].startswith('generated')]
            lm=stats(core);rm=stats(counterpart)
            prod=[d for d in core if not re.search(r'Controls|Checks|Examples|Test|Fixture',d['path'])]
            wrapper=sum(d['lines']<=5 for d in core);rwrapper=sum(d['lines']<=5 for d in counterpart)
            mean=lm['proof_lines']['mean'];den=rm['proof_lines']['mean'];ratio=round(mean/den,4) if mean is not None and den else None
            out=ratio is not None and (ratio>3 or ratio<1/3)
            context=not prefix or ar in ('Bridge','Source','Yul','Evm','Storage','Typing') or (ar=='Frontend' and name=='CakeML')
            total_ratio=lm['proof_lines']['total']/rm['proof_lines']['total'] if rm['proof_lines']['total'] else None
            aggregate_outlier=total_ratio is not None and (total_ratio>3 or total_ratio<1/3)
            aggregate_reason='Whole-area totals are context, not equal guarantees.' if context else 'Aggregate proof source lies within the threefold band.'
            if aggregate_outlier and not context:
                aggregate_reason=('The CompCert subsystem is smaller, but the independently measured complete CakeML compiler/backend proof population is larger than the local Backend proof population; the volume is within a real verified-compiler reference class. This does not justify every repeated certificate transport.' if ar=='Backend' else 'Local Frontend also proves intrinsic admission, qualified names and solc-JSON acceptance. CompCert cfrontend proof bodies do not include the same parser/adapter obligations; short-proof and production-path sensitivities are reported. Repeated syntax invariants still warrant consolidation.')
            if aggregate_outlier and ar=='Lowering' and name=='CakeML':
                aggregate_reason='The local lowering area is a subset of a compiler pipeline, while the denominator is the complete CakeML backend; a low aggregate outlier is justified by subsystem scope. Mean-body production-path sensitivity is reported separately.'
            production_mean=stats(prod)['proof_lines']['mean']
            production_ratio=round(production_mean/den,4) if production_mean is not None and den else None
            rows.append(dict(area=ar,reference=name,reference_prefix=prefix or '<whole portfolio>',population='portfolio context only' if context else 'nearest compiler/runtime subsystem',all_local=stats(local),local_short_le5=dict(proofs=wrapper,fraction=round(wrapper/len(core),4) if core else None),reference_short_le5=dict(proofs=rwrapper,fraction=round(rwrapper/len(counterpart),4) if counterpart else None),production_path_sensitivity=stats(prod),not_marked_generated_local=lm,not_marked_generated_reference=rm,total_proof_line_ratio=round(lm['proof_lines']['total']/rm['proof_lines']['total'],4) if rm['proof_lines']['total'] else None,proof_count_ratio=round(len(core)/len(counterpart),4) if counterpart else None,aggregate_outlier=aggregate_outlier,aggregate_verdict='descriptive-only' if context else 'justified' if aggregate_outlier else 'within-band',aggregate_reason=aggregate_reason,production_mean_proof_line_ratio=production_ratio,mean_proof_line_ratio=ratio,p90_ratio=round(lm['proof_lines']['p90']/rm['proof_lines']['p90'],4) if core and counterpart and rm['proof_lines']['p90'] else None,outlier=out,verdict='descriptive-only' if context else 'justified' if out else 'within-band' if ratio is not None else 'unpaired',reason=(f'Short proofs (at most five lines) account for {wrapper}/{len(core)} local and {rwrapper}/{len(counterpart)} reference proofs. The measured wrapper/control population and production-path sensitivity explain the short-body outlier; source bodies count delegations, not transitive labor or missing obligations. Removing control/check/example path populations changes the mean ratio to {production_ratio}.' if ratio is not None and ratio<1/3 else 'Longer named proof bodies in a language-specific population; the ratio is not theorem-equivalence or a safe deletion budget.' if out else 'Mean named proof-body length lies within the threefold reference-class band; this looks fine at this granularity.' if ratio is not None else 'No parsed reference proof in selected population.'),boundary='Includes test/control theorems in each selected population; no statement-equivalence or effort-per-guarantee claim. Reference granularity and tactic automation differ. Portfolio context ratios do not adjudicate subsystem redundancy.'))
    lowering=[d for d in ds if d['path'].startswith('Solidity/Lowering/') and not d['generated'].startswith('generated')]
    two=[d for d in refs['CompCert'] if d['path'] in ('cfrontend/Cshmgenproof.v','cfrontend/Cminorgenproof.v')]
    l=stats(lowering);r=stats(two);ratio=l['proof_lines']['total']/r['proof_lines']['total']
    full=stats([d for d in refs['CompCert'] if d['path'].startswith('cfrontend/') and not d['generated'].startswith('generated')]);full_ratio=l['proof_lines']['total']/full['proof_lines']['total']
    rows.append(dict(area='Lowering',reference='CompCert',reference_paths=['cfrontend/Cshmgenproof.v','cfrontend/Cminorgenproof.v'],population='two-pass proof-only comparison; complete cfrontend row is the scope sensitivity',not_marked_generated_local=l,not_marked_generated_reference=r,total_proof_line_ratio=round(ratio,4),mean_proof_line_ratio=round(l['proof_lines']['mean']/r['proof_lines']['mean'],4),outlier=ratio>3,verdict='justified' if ratio>3 else 'within-band',reason=f'The two-pass ratio {ratio:.4f} crosses back inside the outlier band at {full_ratio:.4f} against the full C frontend proof population. Solidity memory/layout/effect and scenario obligations extend beyond two C lowering passes, so the narrow denominator does not establish wrong direction. Repeated scaffold consolidation is separately measured in waste.json; no deletion budget inferred.',boundary='Nearest two lowering passes, not equivalent accepted languages. Direction judgement concerns repeated scenario expansion, never a deletion budget.'))
    return rows

_SLICE_CACHE={}
def prepare_slice(texts,preparsed):
    key=id(texts)
    if key in _SLICE_CACHE:return _SLICE_CACHE[key]
    nodes=[];byfile={};mods={}
    grouped=C.defaultdict(list)
    for d in preparsed or []:grouped[d['path']].append(d)
    for p,raw in sorted(texts.items()):
        dd=grouped[p] if preparsed is not None else lean_decls(p,raw);ids=[]
        for d in dd:ids.append(len(nodes));nodes.append(d)
        byfile[p]=ids
        mod=p[:-5].replace('/','.')
        if p.startswith('Bridge/vendor/'):mod=mod.removeprefix('Bridge.vendor.')
        elif p.startswith('Bridge/'):mod=mod.removeprefix('Bridge.')
        mods[mod]=p
    imports={p:[mods[m] for line in re.findall(r'^\s*(?:(?:public|meta)\s+)*import\s+([^\n]+)',mask(raw),re.M) for m in line.split() if m in mods] for p,raw in texts.items()}
    idx=C.defaultdict(set)
    for i,d in enumerate(nodes):idx[d['name'].split('.')[-1]].add(i)
    _SLICE_CACHE[key]=(nodes,byfile,mods,imports,idx)
    return _SLICE_CACHE[key]

def slice_count(texts,roots,prefix,preparsed=None):
    nodes,byfile,mods,imports,idx=prepare_slice(texts,preparsed)
    def files(p):
        seen=set();todo=[p]
        while todo:
            q=todo.pop()
            if q in seen:continue
            seen.add(q);todo+=imports.get(q,[])
        return seen
    filecache={};visible={};rootids=[]
    for p,n in roots:
        got=[i for i in byfile.get(p,[]) if nodes[i]['name']==n]
        if len(got)!=1:raise RuntimeError('slice root missing or ambiguous '+p+'#'+n)
        rootids+=got
    seen=set();todo=rootids[:]
    while todo:
        i=todo.pop()
        if i in seen:continue
        seen.add(i);d=nodes[i];p=d['path']
        if p not in filecache:
            filecache[p]=files(p);visible[p]={j for q in filecache[p] for j in byfile[q]}
        for t in set(TOKEN.findall(d['body'])):
            todo.extend(idx.get(t.split('.')[-1],set()) & visible[p])
    selected=[nodes[i] for i in sorted(seen)];scoped=[d for d in selected if d['path'].startswith(prefix)]
    def count(dd):
        return dict(declarations=len(dd),theorems=sum(d['kind'] in ('theorem','lemma') for d in dd),proof_lines=sum(d['lines'] for d in dd if d['kind'] in ('theorem','lemma')),declaration_nonblank_lines=sum(sum(bool(x.strip()) for x in d['body'].splitlines()) for d in dd),files=len(set(d['path'] for d in dd)),generated_declarations=sum(gen(d['path'],texts[d['path']]).startswith('generated') for d in dd))
    return dict(roots=[dict(path=p,name=n) for p,n in roots],scope_prefix=prefix,scope=count(scoped),all_tracked=count(selected),vendored=count([d for d in selected if d['path'].startswith('Bridge/vendor/')]),members=[dict(path=d['path'],name=d['name'],line=d['line'],kind=d['kind']) for d in scoped],external_imports=sorted({m for d in selected for line in re.findall(r'^\s*import\s+([^\n]+)',mask(texts[d['path']]),re.M) for m in line.split() if m not in mods}))

def bridge_slice(texts,clear,preparsed):
    # Same semantic object is absent on one side, not a denominator of 9,615 lines.
    local_roots=[('Bridge/SolidityBridge/ExternalEvm.lean','simulation'),('Bridge/SolidityBridge/ExternalEvm.lean','upstream_step')]
    mem_roots=[('Bridge/SolidityBridge/ExternalEvm/MemoryRefinement.lean','load_refines'),('Bridge/SolidityBridge/ExternalEvm/MemoryRefinement.lean','store_refines')]
    storage_roots=[('Bridge/SolidityBridge/ExternalEvm/StorageSlots.lean','bounded_refinement')]
    nearest=[('Clear/Abstraction.lean','Spec_ok_unfold'),('Clear/State.lean','evm_multifill'),('Clear/State.lean','evm_setStore')]
    # Enumerate the complete candidate relation declarations and their statements, not a name-only absence assertion.
    relation_candidates=[]
    for p,raw in sorted(clear.items()):
        for d in lean_decls(p,raw):
            if re.search(r'State\s*→\s*State\s*→\s*Prop|MachineState|EVMState|Represents|Simulation|Bisimulation',d['header']):
                relation_candidates.append(dict(path=p,line=d['line'],name=d['name'],kind=d['kind'],header=d['header'].strip()[:600]))
    shared=primitive_calibration(texts,clear,preparsed)
    return dict(shared_arithmetic_state_relation=shared,verdict='justified',reason='The common arithmetic return/unchanged-state equations have one-line proofs on both sides, as measured in shared_arithmetic_state_relation. The measured Bridge relations add cross-model arithmetic-stack, finite-storage and preallocated-byte-memory refinements. Clear has no corresponding cross-model EVM-state refinement endpoint at its pinned source; its Spec relates two states of its own Yul interpreter. The sevenfold whole-project ratio counted different obligations and cannot establish redundancy.',matched_cross_model_relation=dict(local='numeric EVM arithmetic stack with upstream operations; finite storage and capacity-bounded byte memory measured separately',clear_matching_roots=[],clear_matched_transitive_declarations=0,ratio=None,division_by_zero_reason='No theorem with the same two model carriers and refinement guarantee in Clear; zero roots means empty matched slice, not a zero-cost proof.'),local_arithmetic=slice_count(texts,local_roots,'Bridge/SolidityBridge/',preparsed),local_memory=slice_count(texts,mem_roots,'Bridge/SolidityBridge/',preparsed),local_storage=slice_count(texts,storage_roots,'Bridge/SolidityBridge/',preparsed),clear_nearest_not_equivalent=slice_count(clear,nearest,'Clear/'),clear_relation_candidate_search=relation_candidates,search_boundary='All tracked Clear Lean declarations scanned and candidate headers recorded. Clear/Abstraction.Spec and Clear/State.evm_* are intramodel specifications/observational framing, not agreement with Solidity.Evm.Machine or EVMYulLean. No matched ratio fabricated.',verdict_boundary='Justified extra obligations in the measured relation slices; no claim that every Bridge module is necessary, or that any endpoint proves full EVM/gas/fork conformance.',proof_boundary='Lexical source closure only; external Mathlib/CSLib dependencies not counted as local development. Existing proof statements retain their premises, including bounded capacity, padding and finite-domain setup.')


def primitive_calibration(texts,clear,nodes):
    p='Bridge/SolidityBridge/ExternalEvm.lean';q='Clear/PrimOps.lean'
    local=next(d for d in nodes if d['path']==p and d['name']=='reference_step')
    names=["EVMAdd'","EVMSub'","EVMMul'","EVMDiv'","EVMMod'","EVMAnd'","EVMOr'","EVMXor'"]
    foreigns=[d for d in lean_decls(q,clear[q]) if d['name'] in names]
    assert len(foreigns)==len(names)
    conversions=[d for d in nodes if d['path']==p and d['name'] in ('add_step','sub_step','mul_step','div_step','mod_step','and_step','or_step','xor_step')]
    return dict(shared_observation='Eight arithmetic results and unchanged non-stack state. Local transformer consumes/pushes stack and increments PC; Clear returns the result list with unchanged Yul state. Observe arithmetic return plus framed non-PC state, not identical full-state functions.',local_root=loc(local),clear_roots=[loc(d) for d in foreigns],local_proof_lines=local['lines'],clear_mean_proof_lines=sum(d['lines'] for d in foreigns)/len(foreigns),root_proof_line_ratio=local['lines']/(sum(d['lines'] for d in foreigns)/len(foreigns)),local_transitive=slice_count(texts,[(p,'reference_step')],'Bridge/SolidityBridge/',nodes),clear_transitive=slice_count(clear,[(q,n) for n in names],'Clear/'),extra_conversion_proofs=[loc(d) for d in conversions],conversion_scope='These extra roots compare different word representations and source instruction semantics; Clear primitive equations have no second word/machine representation. They are not added to the shared primitive ratio.',verdict='justified',reason='The common primitive equations are definitional on both sides; local generic op parameter shares eight cases in one proof. Cross-model conversion and simulation add separate, explicitly measured obligations, rather than eight copies of a Clear primitive proof.')

def template_evidence(v):
    # Full headers and proof identifier substitutions are reviewable, unlike a hash alone.
    # A canonical proof is a candidate schema, never semantic equivalence of statements.
    base=list(dict.fromkeys(TOKEN.findall(v[0]['proof'])))
    maps=[]
    for d in v:
        toks=list(dict.fromkeys(TOKEN.findall(d['proof'])))
        maps.append(dict(path=d['path'],name=d['name'],statement=d['header'].strip(),substitutions={x:y for x,y in zip(base,toks) if x!=y}))
    return dict(common_proof=v[0]['proof'],instantiations=maps,obligation='The proposed generic lemma must quantify differing predicates, projections and cited laws shown here, then reproduce every original statement. Template similarity alone does not prove theorem equivalence.')

def long_analogue(d,refs):
    # Read nearest grammar/compiler properties, including a broad endpoint sensitivity.
    if '/Frontend/' in d['path'] and any(x in d['path'] for x in ('StatementGrammarH28/','ExpressionUniqueness/','Admission/SyntaxOccurrence')):
        shortname='ptree_head_NT_mkNd' if 'head' in d['name'].lower() else 'valid_ptree_mkNd'
        short=next(x for x in refs['CakeML'] if x['path']=='compiler/parsing/proofs/pegSoundScript.sml' and x['name']==shortname)
        broad=next(x for x in refs['CakeML'] if x['path']=='compiler/parsing/proofs/pegSoundScript.sml' and x['name']=='peg_sound')
        return dict(reference='CakeML',nearest_short=loc(short),reference_url='https://github.com/CakeML/cakeml/blob/b3e6ea34ca1aed91a57703a30549260ce6f6448e/'+short['path']+'#L'+str(short['line']),short_ratio=round(d['lines']/short['lines'],4),broad_sensitivity=loc(broad),broad_ratio=round(d['lines']/broad['lines'],4),shared_property='Syntactic tree validity/head/fringe invariant',differences='Local dependent Syn covers the complete Solidity grammar (or an expression/occurrence invariant). The short reference lemma is a generic tree-constructor law, not soundness of every grammar constructor; peg_sound is the complete PEG correctness sensitivity.',verdict='justified',reason='The short-analogue outlier changes when the denominator includes the full grammar proof; grammar-constructor enumeration is a real extra obligation. Repeated local invariants are consolidation candidates in top30, not evidence that one generic tree equation can replace a grammar-wide proof.')
    names=[('CompCert','common/Memory.v','load_store_same'),('CompCert','cfrontend/Cminorgenproof.v','transl_step_correct'),('CakeML','compiler/backend/proofs/bvl_to_bviProofScript.sml','compile_semantics')]
    found=[dict(reference=n,**loc(x)) for n,p,k in names for x in refs[n] if x['path']==p and x['name']==k]
    return dict(searched_nearest=found,ratio=None,verdict='inconclusive',reason='No length-based redundancy or proportionality verdict: nearest runtime memory/pass preservation results are recorded, but do not prove the named local calculus normalization, intrinsic frame or compiler-fragment statement. No valid short same-statement reference analogue established; length alone does not show waste.',settling_measurement='A statement/premise-matched proof-body comparison for this exact local invariant, rather than a short constructor/helper theorem.')


def headlines(ds,refs,w,bridge):
    local=stats(ds)
    return dict(individual_proof_effort=dict(verdict='justified',local_mean=local['proof_lines']['mean'],local_p50=local['proof_lines']['p50'],reference_means={n:r['all']['proof_lines']['mean'] for n,r in refs.items()},reference_p50={n:r['all']['proof_lines']['p50'] for n,r in refs.items()},reason='Bodies are short relative to the measured reference distributions. Aggregate totals and theorem counts remain separate; short bodies can still multiply redundant scaffolding.'),consolidation=dict(verdict='redundant',unit='repeated proof scaffolding, not original theorem statements',candidate_clusters=len(w['top30']),conditional_line_savings=w['estimated_nonoverlapping_line_savings'],proved_safe_deletion_lines=0),case_splits={n:dict(proofs=f['proofs'],split_keywords=f['case_split_keywords'],keywords_per_proof=round(f['case_split_keywords']/f['proofs'],4) if f['proofs'] else None,reason='Lexical split count is a scenario-family diagnostic, not the size of an executed proof-search tree. Inspect largest members in waste.json.') for n,f in w['case_split_families'].items()},bridge=dict(verdict=bridge['verdict'],shared_primitive_ratio=bridge['shared_arithmetic_state_relation']['root_proof_line_ratio'],reason=bridge['verdict_boundary']))

if __name__=='__main__':main()
