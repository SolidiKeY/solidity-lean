#!/usr/bin/env python3
"""H238: source-only compiler semantic-preservation calibration against CompCert.

python3 -B docs/audits/direction-tools/reachability/calibrate.py --reference /tmp/da-reachability-compcert [--check]
A missing reference directory is shallow-cloned, then pinned to REF_COMMIT.
Existing reference directories must already have the exact clean pinned HEAD.
No Coq/Lean elaboration, configuration, build, dependencies or source edits.
"""
import argparse
import bisect
import collections as C
import hashlib
import importlib.util
import json
from pathlib import Path
import re
import subprocess

HERE=Path(__file__).resolve().parent
REF_URL='https://github.com/AbsInt/CompCert.git'
REF_COMMIT='2685140bf72c959446981fb99b5e44a8975021bc'
spec=importlib.util.spec_from_file_location('reach',HERE/'reach.py')
r=importlib.util.module_from_spec(spec);spec.loader.exec_module(r)
COQ_DECL=re.compile(r'^[ \t]*(?:(?:Local|Global|Program|Polymorphic|Monomorphic)\s+)*(Theorem|Lemma|Definition|Fixpoint|CoFixpoint|Inductive|CoInductive|Record|Instance|Axiom|Parameter|Corollary|Remark|Fact|Proposition|Let|Ltac|Nondetfunction)\s+([\w\u0080-\uffff\']+)',re.M)
REQUIRE=re.compile(r'\b(?:From\s+([\w.]+)\s+)?Require\s+(?:(?:Import|Export)\s+)?(.*?)\.(?=\s|$)',re.S)
COQ_CONTEXT=re.compile(r'^[ \t]*(?:Variables?|Hypotheses?|Context|Existing\s+Instance|(?:Local\s+|Global\s+)?Hint)\b.*?\.(?=\s|$)',re.M|re.S)
# Makefile DIRS/VPATH precedence for the representative x86_64 target.
COQ_DIRS=['lib','common','x86_64','x86','backend','cfrontend','driver','cparser',
          'flocq/Core','flocq/Prop','flocq/Calc','flocq/IEEE754','MenhirLib']


def coq_clean(text):
    out=[];i=depth=0;string=False
    while i<len(text):
        pair=text[i:i+2];c=text[i]
        if depth:
            if pair=='(*':depth+=1;out.extend('  ');i+=2;continue
            if pair=='*)':depth-=1;out.extend('  ');i+=2;continue
            out.append('\n' if c=='\n' else ' ');i+=1;continue
        if string:
            if pair=='""':out.extend('  ');i+=2;continue
            if c=='"':string=False
            out.append('\n' if c=='\n' else ' ');i+=1;continue
        if pair=='(*':depth=1;out.extend('  ');i+=2;continue
        if c=='"':string=True;out.append(' ')
        else:out.append(c)
        i+=1
    return ''.join(out)


def coq_spans(text):
    """Keep proof-local Ltac/Let inside the enclosing proof, not disconnected."""
    matches=list(COQ_DECL.finditer(text))
    bounds=sorted(set([len(text)]+[x.start() for x in matches]+
               [x.start() for x in re.finditer(r'^[ \t]*(?:End|Section|Module|Variables?|Hypotheses?|Context|Require|Import|Export|From|Set|Unset|Notation|Infix|Hint)\b',text,re.M)]))
    spans=[];covered=0
    for match in matches:
        if match.start()<covered:continue
        end=bounds[bisect.bisect_right(bounds,match.start())]
        proof=re.search(r'\bProof\b[^.]*\.',text[match.end():end])
        if proof:
            after=match.end()+proof.end()
            terminal=re.search(r'\b(?:Qed|Defined|Admitted|Abort)\s*\.',text[after:])
            if not terminal:raise ValueError('unterminated Coq proof at '+str(match.start()))
            end=after+terminal.end()
            if end<len(text) and text[end]=='\n':end+=1
            covered=end
        spans.append((match,end))
    return spans


def coq_graph(root):
    tracked=set(subprocess.check_output(['git','-C',str(root),'ls-files'],text=True).splitlines())
    selected={};shadowed=[]
    for directory in COQ_DIRS:
        for p in sorted(tracked):
            if str(Path(p).parent)!=directory or not p.endswith(('.v','.vp')):continue
            name=Path(p).stem
            if name in selected:shadowed.append(dict(module=name,selected=selected[name],shadowed=p))
            else:selected[name]=p
    texts={m:(root/p).read_text() for m,p in selected.items()}
    graph={};external=set();nodes=[];byname=C.defaultdict(set);bymod=C.defaultdict(list)
    for m,p in selected.items():
        text=coq_clean(texts[m]);deps=set()
        for match in REQUIRE.finditer(text):
            prefix=match.group(1)
            for token in match.group(2).split():
                # Coq's standard library is outside the source universe even if
                # it has a same-basename module. Flocq is locally vendored.
                if prefix in ('Coq','Stdlib'):external.add(prefix+'.'+token);continue
                candidate=token.split('.')[-1]
                if candidate in selected:deps.add(candidate)
                else:external.add((prefix+'.' if prefix else '')+token)
        graph[m]=deps
        context='\n'.join(x.group() for x in COQ_CONTEXT.finditer(text))
        for match,end in coq_spans(text):
            raw=text[match.start():end];i=len(nodes)
            nodes.append(dict(module=m,name=match.group(2),kind=match.group(1),
                              start=text.count('\n',0,match.start())+1,lines=len(raw.splitlines()),
                              text=raw[:match.start(2)-match.start()]+raw[match.end(2)-match.start():]+'\n'+context))
            bymod[m].append(i);byname[match.group(2)].add(i)
    imports={m:r.closure(graph,[m]) for m in graph};dg={};ambiguous=0
    for i,n in enumerate(nodes):
        edges=set()
        for token in set(r.TOKEN.findall(n['text'])):
            candidates={j for j in byname.get(token.split('.')[-1],()) if nodes[j]['module'] in imports[n['module']]}
            ambiguous+=len(candidates)>1;edges.update(candidates)
        edges.discard(i);dg[i]=edges
    modules={m:dict(path=p,lines=len(texts[m].splitlines()),generated_reasons=(['tracked .vp generator input; emitted .v not measured'] if p.endswith('.vp') else r.generated(p,texts[m])),
                         provenance='vendored' if p.startswith(('flocq/','MenhirLib/')) else 'project') for m,p in selected.items()}
    return dict(nodes=nodes,modules=modules,graph=dg,imports=imports,external_imports=sorted(external),shadowed=shadowed,
                ambiguous_token_sites=ambiguous,selected_paths=selected)


def metrics(data,module,name):
    roots=[i for i,n in enumerate(data['nodes']) if n['module']==module and n['name']==name]
    if len(roots)!=1:raise ValueError('root not unique: '+module+'.'+name)
    reached=r.closure(data['graph'],roots);mods={data['nodes'][i]['module'] for i in reached}
    imported=data['imports'][module];modules=data['modules'];nodes=data['nodes']
    return dict(root=dict(module=module,name=name,path=modules[module]['path'],line=nodes[roots[0]]['start']),
                lexical=dict(declarations=len(reached),source_span_lines=sum(nodes[i]['lines'] for i in reached),
                             modules_with_reachable_declarations=len(mods),
                             marked_generated_declarations=sum(bool(modules[nodes[i]['module']]['generated_reasons']) for i in reached),
                             marked_generated_source_span_lines=sum(nodes[i]['lines'] for i in reached if modules[nodes[i]['module']]['generated_reasons']),
                             handwritten_or_unmarked_declarations=sum(not modules[nodes[i]['module']]['generated_reasons'] for i in reached)),
                import_slice=dict(modules=len(imported),physical_lines=sum(modules[m]['lines'] for m in imported),
                                  marked_generated_physical_lines=sum(modules[m]['lines'] for m in imported if modules[m]['generated_reasons']),
                                  handwritten_or_unmarked_physical_lines=sum(modules[m]['lines'] for m in imported if not modules[m]['generated_reasons']),
                                  vendored_physical_lines=sum(modules[m]['lines'] for m in imported if modules[m]['provenance']=='vendored'),
                                  own_physical_lines=sum(modules[m]['lines'] for m in imported if modules[m]['provenance']!='vendored'),
                                  paths=sorted(modules[m]['path'] for m in imported)),
                within_import_slice_declaration_share=len(reached)/sum(1 for n in nodes if n['module'] in imported))


def compare(lean,coq):
    rows=[]
    for section,metric in [('lexical','declarations'),('lexical','source_span_lines'),('lexical','modules_with_reachable_declarations'),('import_slice','modules'),('import_slice','physical_lines'),('import_slice','handwritten_or_unmarked_physical_lines'),('import_slice','own_physical_lines')]:
        a,b=lean[section][metric],coq[section][metric];ratio=a/b
        outlier=ratio>3 or ratio<1/3
        # A below-1/3 slice is justified by an explicitly smaller theorem scope:
        # intrinsic scoped core fragment -> abstract EVM vs full C -> target ASM
        # through the passes of Compiler.v. This is NOT an efficiency verdict.
        judgement=('justified' if ratio<1/3 else 'unresolved counting-method sensitivity' if ratio>3 else 'within 3x; this proxy looks fine')
        reason=('The Solidity root covers an intrinsic core fragment selected by inFragP; CompCert composes the C frontend and optimizing target pipeline. Smaller source slices do not establish better proof engineering.' if ratio<1/3 else
                'Lexical collisions, implicit elaboration, generated declarations and parser differences require an elaborated follow-up before assigning a direction verdict.' if ratio>3 else
                'No reference-class outlier at this source-proxy resolution; theorem coverage and language constructs still differ.')
        rows.append(dict(metric=section+'.'+metric,solidity=a,compcert=b,solidity_over_compcert=ratio,outlier_over_3x_either_way=outlier,judgement=judgement,reason=reason))
    return rows


def generate(reference):
    report,dead,nodes,modules,texts,generators,graph=r.build()
    # Same lexical model as reach.py, with a compiler-only root instead of the
    # entire headline theorem suite. Counts include named declarations only:
    # Lean #commands do not have Coq declaration counterparts.
    named={i for i,n in enumerate(nodes) if n['kind']!='command'}
    mg={k:set(v['imports'])&modules.keys() for k,v in modules.items()}
    lean=dict(nodes=nodes,modules=modules,graph={i:graph[i]&named for i in named},
              imports={m:r.closure(mg,[m]) for m in modules})
    # Metric denominators exclude commands in both systems.
    def lean_metrics(module,name):
        result=metrics(lean,module,name)
        imported=set(result['import_slice']['paths'])
        result['within_import_slice_declaration_share']=result['lexical']['declarations']/sum(n['kind']!='command' and modules[n['module']]['path'] in imported for n in nodes)
        return result
    coq=coq_graph(reference)
    a=lean_metrics('Solidity.Evm.Correct','compile_correct')
    b=metrics(coq,'Compiler','transf_c_program_correct')
    companion=metrics(coq,'Compiler','c_semantic_preservation')
    headline=lean_metrics('Solidity.Theorems','compiler_correct')
    return dict(schema=1,authorization='H238; coordinator answer DAREACH-REF: CompCert semantic-preservation roots, compiler-proof dependency slices',
                solidity_base=r.BASE,reference=dict(repository=REF_URL,commit=REF_COMMIT,version=(reference/'VERSION').read_text().strip(),
                   target='representative x86_64 source selection; no configure/build run',source_directories=COQ_DIRS,
                   source_modules=len(coq['modules']),physical_lines=sum(v['lines'] for v in coq['modules'].values()),declarations=len(coq['nodes']),
                   provenance={role:dict(modules=sum(v['provenance']==role for v in coq['modules'].values()),physical_lines=sum(v['lines'] for v in coq['modules'].values() if v['provenance']==role)) for role in ('project','vendored')},
                   template_inputs=[p for p in sorted(coq['selected_paths'].values()) if p.endswith('.vp')],
                   template_generator=dict(path='tools/ndfun.ml',make_rule='%.v: %.vp tools/ndfun',
                                          build_prerequisite_link_verified='%.v: %.vp tools/ndfun' in (reference/'Makefile').read_text(),
                                          meaning='build-time generator input/output link, not a Coq proof declaration dependency'),
                   external_imports=coq['external_imports'],shadowed_target_modules=coq['shadowed'],
                   tracked_source_hashes={p:hashlib.sha256((reference/p).read_bytes()).hexdigest() for p in sorted(coq['selected_paths'].values())}),
                scope_mapping=dict(solidity='Solidity.Evm.Correct.compile_correct: intrinsic Prog core fragment selected by inFragP with state-representation/length premises, outcomes include payment refusal/divergence; not full Solidity/solc.',
                                   compcert='Compiler.transf_c_program_correct: successful Csyntax-to-Asm translation implies backward simulation; c_semantic_preservation is its semantic companion.',
                                   why_nearest='Both relate source-program semantics to compiled machine semantics; compare dependency-slice source proxies, not equivalent language coverage or compiler cost.'),
                solidity_core=a,compcert_program=b,solidity_headline_sensitivity=headline,compcert_semantic_companion=companion,
                ratios=compare(a,b),headline_sensitivity_ratios=compare(headline,b),
                limitations=['No kernel dependency dump, Coq build, Lean build or check-time comparison. These are measured source proxies, not cited global LOC figures.',
                    'Lexical graphs keep all visible matching final name components and overconnect locals/overloads; constructors/projections, implicit instances/typeclasses, notation, Ltac and Lean tactics can hide edges.',
                    'Coq declaration spans and Lean declaration spans count different syntactic units. Top-level Let/Ltac are counted; proof-local Ltac/Let remain inside their theorem span; Lean commands are excluded from paired declaration counts. Ratios of declarations are low-confidence sensitivity data.',
                    'Module import slices include everything in imported files, not only semantic dependencies. Solidity direct core root avoids unrelated Main theorem imports; the headline slice is shown separately.',
                    'No cross-project ratio of whole-repository goal reachability shares: their repository universes and test suites differ. Within-import-slice shares are descriptive only.',
                    'Marked/rule-generated code is separated from handwritten/unmarked code; unmarked generation and parser-generated declarations can remain. CompCert Flocq/MenhirLib are separately labeled vendored.',
                    'Tracked .vp compiler-module templates are counted as generation inputs, not missing external libraries; Nondetfunction forms are counted as input declarations; emitted .v preprocessor output and additional generated helpers are not measured or built.',
                    'Source strings/comments and imports are normalized differently for Lean and Coq; qualified import resolution follows basename/VPATH precedence and reports shadowed target modules and unresolved external imports.',
                    'Below-1/3 counts are justified only by the smaller core-fragment theorem scope; no automatic redundant/wrong-direction or compiler-efficiency conclusion. Above-3x values remain unresolved rather than being justified by assumption.'],
                citations=[dict(path='driver/Compiler.v',url=REF_URL.removesuffix('.git')+'/blob/'+REF_COMMIT+'/driver/Compiler.v',roots=['transf_c_program_correct','c_semantic_preservation']),
                           dict(path='Makefile',url=REF_URL.removesuffix('.git')+'/blob/'+REF_COMMIT+'/Makefile',purpose='DIRS/ARCHDIRS/VPATH source precedence'),
                           dict(path='Solidity/Evm/Correct.lean',commit=r.BASE),dict(path='Solidity/Theorems.lean',commit=r.BASE)],
                command='python3 -B docs/audits/direction-tools/reachability/calibrate.py --reference /tmp/da-reachability-compcert --check')


def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--reference',type=Path,required=True);ap.add_argument('--check',action='store_true');args=ap.parse_args()
    if not args.reference.exists():
        subprocess.run(['git','clone','--depth','1',REF_URL,str(args.reference)],check=True)
        head=subprocess.check_output(['git','-C',str(args.reference),'rev-parse','HEAD'],text=True).strip()
        if head!=REF_COMMIT:
            subprocess.run(['git','-C',str(args.reference),'fetch','--depth','1','origin',REF_COMMIT],check=True)
            subprocess.run(['git','-C',str(args.reference),'checkout','--detach',REF_COMMIT],check=True)
    head=subprocess.check_output(['git','-C',str(args.reference),'rev-parse','HEAD'],text=True).strip()
    if head!=REF_COMMIT or subprocess.check_output(['git','-C',str(args.reference),'status','--porcelain'],text=True).strip():raise SystemExit('reference must be clean at exact pinned commit')
    text=json.dumps(generate(args.reference),indent=2)+'\n'
    if len(text.encode())>=1_000_000:raise SystemExit('calibration exceeds small-data limit')
    path=HERE/'calibration.json'
    if args.check:
        if path.read_text()!=text:raise SystemExit('stale calibration.json')
    else:path.write_text(text)
    print('PASS reproducible CompCert source calibration' if args.check else 'WROTE calibration.json')

if __name__=='__main__':main()
