#!/usr/bin/env python3
"""Analyze native environment edges plus Lean's source reference index.
No name-token matching is used to infer dependencies. Source spans come only
from .ilean definition records; auxiliary constants may have no source span.
Run: python3 -I .../analyze.py --graph GRAPH --view VIEW --out OUT
Negative results apply only to the explicitly recorded module universe.
"""
import argparse,collections,csv,hashlib,json,pathlib,re,runpy,sys
HERE=pathlib.Path(__file__).resolve().parent
API=runpy.run_path(str(HERE/'audit.py'))
ROOT=API['ROOT']; BASE=API['BASE']; FAMILIES=API['FAMILIES']
def closure(edges,seeds):
    seen=set(); todo=list(seeds)
    while todo:
        n=todo.pop()
        if n in seen:continue
        seen.add(n);todo.extend(edges.get(n,()))
    return seen
def testpath(p):
    return '/Examples/' in p or '/Corpus/' in p or '/TestSuite/' in p or bool(re.search(r'(?:Controls|Checks|Pins|Coverage)\.lean$',p))
def load_graph(graph,view,src):
    nodes={};edges={};spans={}; indexed={};commands=set();source_edges=0
    for line in graph.open():
        r=json.loads(line);n=r['name'];nodes[n]=r;edges[n]=set(r['refs'])
    for p in src:
        modpath=p.removeprefix('vendor/LeanTeX/').removeprefix('Bridge/')
        f=view/pathlib.Path(modpath).with_suffix('.ilean')
        if not f.exists():continue
        j=json.loads(f.read_text());module=j['module'];indexed[module]=p
        defs=[]; owner_ranges=collections.defaultdict(set)
        for k,v in j['references'].items():
            key=json.loads(k)
            n=key.get('c',{}).get('n');d=v.get('definition')
            if d and n in nodes and nodes[n]['module']==module:
                if len(d)>=9:
                    span=(int(d[5])+1,int(d[7])+(1 if int(d[8]) else 0))
                    owner_ranges[n].add(tuple(map(int,d[5:9])))
            for u in v.get('usages',[]):
                if len(u)>=9 and u[4] in nodes and nodes[u[4]]['module']==module:
                    owner_ranges[u[4]].add(tuple(map(int,u[5:9])))
        for n,rs in owner_ranges.items():
            if len(rs)!=1:continue
            a,b,c,d=next(iter(rs));spans[n]=(a+1,c+(1 if d else 0));defs.append((n,((a,b),(c,d))))
        for k,v in j['references'].items():
            key=json.loads(k)
            if 'c' not in key:continue
            target=key['c']['n']
            for u in v.get('usages',[]):
                if len(u)>=5 and u[4] in nodes:owners=[u[4]]
                else:
                    candidates=[n for n,(a,b) in defs if a<=tuple(map(int,u[:2])) and tuple(map(int,u[2:4]))<=b]
                    owners=candidates if len(candidates)==1 else []
                if not owners:
                    owner='@unowned-reference:'+module+':'+str(u[0])+':'+str(u[1]);owners=[owner];commands.add(owner)
                    nodes.setdefault(owner,dict(name=owner,module=module,kind='unowned_source_reference'))
                for owner in owners:
                    edges.setdefault(owner,set()).add(target);source_edges+=1
    # Follow only local declarations: external Lean/core constants are reported as
    # boundary nodes, not charged Solidity source lines.
    external=set().union(*edges.values())-nodes.keys()
    edges={n:{r for r in rs if r in nodes} for n,rs in edges.items()}
    return nodes,edges,spans,indexed,commands,source_edges,external

def run(graph,view,out,source_root=None):
    src=API['assert_sources'](source_root); source_provenance={p:API["provenance"](p,t) for p,t in src.items()}; mask=runpy.run_path(str(HERE.parent/'statements/scan.py'))['mask']; goals=[p for p,t in src.items() if re.search(r'@\[[^\]]*\bgoal\b',mask(t))];assert not goals,'Goal attributes need explicit root mapping: '+str(goals); nodes,edges,spans,indexed,commands,source_edges,external=load_graph(graph,view,src)
    facade={n for n,r in nodes.items() if r['module']=='Solidity.Theorems' and r['kind']=='theorem'}
    tests={n for n,r in nodes.items() if n not in commands and testpath(indexed.get(r['module'],''))}
    main_used=closure(edges,facade);test_used=closure(edges,tests)-main_used
    unused=nodes.keys()-main_used-test_used
    incoming=collections.Counter(r for n,rs in edges.items() for r in rs if n!=r)
    zero={n for n in unused if not incoming[n] and n not in commands}
    classes={n:('facade_used' if n in main_used else 'policy_check_only' if n in test_used else 'unreached') for n in nodes}
    prov=collections.defaultdict(collections.Counter)
    dirs=collections.defaultdict(lambda:collections.Counter()); areas=collections.defaultdict(lambda:collections.Counter())
    lines=collections.defaultdict(lambda:collections.defaultdict(set))
    declared=collections.Counter()
    for n,r in nodes.items():
        p=indexed.get(r['module'])
        if not p:continue
        c=classes[n];kind='unowned_reference_nodes' if n in commands else 'declarations'
        d=str(pathlib.PurePosixPath(p).parent);a='/'.join(p.split('/')[:2])
        for dst in (dirs[d],areas[a],prov[source_provenance[p]]):
            dst[c+'_'+kind]+=1
            if n in zero:dst['zero_incoming_declarations']+=1
            if n in spans:dst['source_spanned_native_constants']+=1
            if n in spans and n in unused:dst['unreached_source_spanned_native_constants']+=1
            if n not in commands and n not in spans:dst['declarations_without_source_span']+=1
        if n in spans:
            lo,hi=spans[n];lines[p][c].update(range(lo,hi+1));declared[p]+=1
    # Priority partitions overlapping declaration lines. No attribution of
    # imports/comments/unindexed commands to an allegedly dead declaration.
    for p in indexed.values():
        cs=lines[p]
        taken=set();d=str(pathlib.PurePosixPath(p).parent);a='/'.join(p.split('/')[:2])
        for c in ('facade_used','policy_check_only','unreached'):
            ls=cs[c]-taken;taken.update(cs[c])
            for dst in (dirs[d],areas[a],prov[source_provenance[p]]):dst[c+'_source_span_lines']+=len(ls)
        for dst in (dirs[d],areas[a],prov[source_provenance[p]]):dst['unattributed_physical_lines']+=len(src[p].splitlines())-len(taken)
    family={}
    out.mkdir(parents=True,exist_ok=True)
    for pre in FAMILIES:
        ns={n for n,r in nodes.items() if indexed.get(r['module'],'').startswith(pre) and n not in commands}
        ownroots={n for n in tests if indexed.get(nodes[n]['module'],'').startswith(pre)}
        otherused=closure(edges,tests-ownroots)|main_used
        onlyown=(closure(edges,ownroots)-otherused)&ns
        own_lines=collections.defaultdict(set);other_lines=collections.defaultdict(set)
        for group,dest in ((onlyown,own_lines),(otherused,other_lines)):
            for n in group:
                if n in spans:
                    p=indexed.get(nodes[n]['module'])
                    if p and p.startswith(pre):dest[p].update(range(spans[n][0],spans[n][1]+1))
        family_lines=collections.Counter()
        for p,cs in lines.items():
            if not p.startswith(pre):continue
            taken=set()
            for c in ('facade_used','policy_check_only','unreached'):
                family_lines[c]+=len(cs[c]-taken);taken.update(cs[c])
        family[pre]=dict(indexed_files=sum(p.startswith(pre) for p in indexed.values()),declarations=len(ns),source_spanned_native_constants=len(ns & spans.keys()),unreached_source_spanned_native_constants=len(ns & unused & spans.keys()),
            facade_used_declarations=len(ns&main_used),policy_check_only_declarations=len(ns&test_used),unreached_declarations=len(ns&unused),
            zero_incoming_declarations=len(ns&zero),used_only_by_own_policy_check_roots_declarations=len(onlyown),
            verdict='No deletion verified: native dependency graph is bounded by the indexed module universe; removal rebuilds not performed.',
            deletable_now_verified_lines=0,unused_but_planned_verified_lines=0,
            used_only_by_own_policy_check_roots_source_span_lines=sum(len(ls-other_lines[p]) for p,ls in own_lines.items()),
            source_span_lines=dict(family_lines))
        rows=[]
        for n in sorted(ns&unused):
            r=nodes[n];lo,hi=spans.get(n,('',''));rows.append([indexed[r['module']],n,r['kind'],lo,hi,int(n in zero)])
        # Regenerable full lists stay outside Git if large. Every individual
        # committed family shard must be less than 1 MB.
        name=pre.strip('/').replace('/','_')+'-unreached.tsv'
        with (out/name).open('w') as h:
            w=csv.writer(h,delimiter='\t',lineterminator='\n');w.writerow(['serialized_module_owner_path','name','kind','first_line','last_line','zero_incoming']);w.writerows(rows)
    for name,table in [('directories',dirs),('areas',areas)]:
        fields=sorted(set().union(*(r.keys() for r in table.values())))
        with (out/(name+'.csv')).open('w') as h:
            w=csv.writer(h,lineterminator="\n");w.writerow(['path']+fields)
            for k,r in sorted(table.items()):w.writerow([k]+[r[f] for f in fields])
    missing=[p for p in src if p not in indexed.values()]
    summary=dict(base=BASE,graph_sha256=hashlib.sha256(graph.read_bytes()).hexdigest(),status='partial',indexed_physical_lines=sum(len(src[p].splitlines()) for p in indexed.values()),module_universe=len(indexed),native_declarations=sum(n not in commands for n in nodes),
        unowned_source_reference_nodes=len(commands),native_and_source_edges=sum(map(len,edges.values())),source_reference_occurrences=source_edges,
        external_constant_boundary=len(external),provenance=dict(sorted(prov.items())),facade_theorem_roots=len(facade),goal_roots=0,
        missing_files=len(missing),missing_physical_lines=sum(len(src[p].splitlines()) for p in missing),
        missing_by_area=dict(sorted(collections.Counter('/'.join(p.split('/')[:2]) for p in missing).items())),families=family,
        deletable_now_verified_lines=0,unused_but_planned_verified_lines=0,
        semantic_certification='INVALID for semantic use: .ilean aliases can merge local binders and constants; earlier source-span and liveness fields are provisional index statistics pending native-range replay.',
        constant_identity='Global imported constant Name, not necessarily unique source declaration: cached modules can define the same fully qualified theorem name.',
        supplemental_measurements={'warm_check_recovery':'warm-check-summary.json','pinned_trust_audit':'trust-audit-summary.json','cached_ir_inventory':'ir-summary.json','module_compiler_overrides':'module-compiler-attributes.json','ci_and_plan_catalog':'root-plan-catalog.json','native_expression_graph':'native-summary.json','historical_candidates':'historical-summary.json','native_candidate_bindings':'candidate-summary.json','syntax_census':'syntax-census.json','compiler_overrides':'compiler-edges.json','effect_on_liveness':'Old fields are provisional index statistics. Native module expression measurements supersede their semantic/source-binding interpretation; full CI/test liveness is still unresolved.'},
        limitations=['No systemd scope on the cloud VM (H232).',
            'Unreached and zero-incoming are measured only inside the explicitly indexed universe; missing modules can be consumers.',
            'Unowned source references are preserved as incoming uses but are not rooted; exact CI/#eval/example root reconstruction remains outstanding.',
            'Native counts include generated auxiliary and realized constants. Module ownership is serialized emission ownership, not necessarily source declaration origin; unspanned constants have no charged source lines.',
            'Policy check roots use explicit testpath() filename categories, not an exact CI test-root reconstruction. No filename heuristic infers a dependency.',
            'No deletion rebuild was performed; no declaration is certified deletable.', 'Exporter loads constants without environment extensions; compiler-attribute, dynamic and reflective dependencies are unmeasured.',
            'No unused-but-planned declaration has been certified against a plan owner.'],
        reproduction=['python3 -I docs/audits/direction-tools/declgraph/audit.py inventory --check',
        'LEAN_NUM_THREADS=1 LAKE_CACHE_DIR=CACHE python3 -I docs/audits/direction-tools/declgraph/prepare.py --cache CACHE --view VIEW --modules MODULES',
        'LEAN_NUM_THREADS=1 LEAN_PATH=VIEW lean -j1 --run docs/audits/direction-tools/declgraph/Export.lean graph MODULES GRAPH',
        'python3 -I docs/audits/direction-tools/declgraph/analyze.py --graph GRAPH --view VIEW --out OUT'])
    (out/'summary.json').write_text(json.dumps(summary,sort_keys=True,indent=2)+'\n')
    print('GRAPH_ANALYSIS_PASS',len(nodes),'nodes',len(indexed),'modules')
def main():
    p=argparse.ArgumentParser();p.add_argument('--graph',type=pathlib.Path,required=True);p.add_argument('--view',type=pathlib.Path,required=True);p.add_argument('--out',type=pathlib.Path,required=True);p.add_argument('--source-root',type=pathlib.Path,help='Explicit frozen-source checkout; default verifies this checkout');a=p.parse_args();run(a.graph,a.view,a.out,a.source_root)
if __name__=='__main__':main()
