#!/usr/bin/env python3
"""Conservative source census; never treats lexical screening as a Lean witness.
Bulk deterministic JSON stays outside Git (H44). Run from repository root.
"""
import argparse, collections, glob, hashlib, json, pathlib, re, subprocess
BASE = 'c6f550e281a7e5affa9a99bc2cdaed556dec00e4'
MAP = pathlib.Path('docs/module-map/yul.md')

def sha(s): return hashlib.sha256(s.encode()).hexdigest()

def mask(s):
    """Preserve offsets/newlines while hiding nested comments and strings."""
    a=list(s); i=0; depth=0; string=False
    while i<len(s):
        if depth:
            if s.startswith('/-',i): a[i:i+2]='  ';depth+=1;i+=2
            elif s.startswith('-/',i): a[i:i+2]='  ';depth-=1;i+=2
            else:
                if s[i]!='\n': a[i]=' '
                i+=1
        elif string:
            if s[i]=='\\':
                a[i]=' ';i+=1
                if i<len(s): a[i]=' ';i+=1
            else:
                if s[i]=='"':string=False
                if s[i]!='\n':a[i]=' '
                i+=1
        elif s.startswith('/-',i):a[i:i+2]='  ';depth=1;i+=2
        elif s.startswith('--',i):
            j=s.find('\n',i)
            if j<0:j=len(s)
            a[i:j]=' '*(j-i);i=j
        elif s[i]=='"':a[i]=' ';string=True;i+=1
        else:i+=1
    if depth or string: raise ValueError('unterminated comment/string')
    return ''.join(a)

def expand(token):
    m=re.search(r'\{([^{}]*)\}',token)
    if m:
        return [t for x in m[1].split(',') for t in expand(token[:m.start()]+x+token[m.end():])]
    if not token.endswith('.lean') and not token.endswith('**'):token+='.lean'
    prefix='' if token.startswith('Bridge/') else 'Solidity/'
    return sorted(glob.glob(prefix+token,recursive=True))

def files():
    selected={}; unmatched=[]
    for line_no,line in enumerate(MAP.read_text().splitlines(),1):
        if not line.startswith('| `'):continue
        cell=line.split('|')[1]
        for token in re.findall(r'`([^`]+)`',cell):
            if token == 'Controls' and '(+`Controls`)' in cell: continue
            matches=[p for p in expand(token) if p.endswith('.lean')]
            if not matches:unmatched.append({'line':line_no,'pattern':token})
            if '(+`Controls`)' in cell:
                matches += [p[:-5]+'Controls.lean' for p in matches if pathlib.Path(p[:-5]+'Controls.lean').exists()]
            for p in matches:selected.setdefault(p,[]).append({'map_line':line_no,'pattern':token})
    # The area root is an interface: its local Yul import closure is part of scope.
    queue=list(selected)
    for p in queue:
        for imp in re.findall(r'^import\s+(\S+)',mask(pathlib.Path(p).read_text()),re.M):
            child=imp.replace('.','/')+'.lean'
            if child.startswith(('Solidity/Yul/','Bridge/SolidityBridge/Yul/')) and child not in selected:
                if not pathlib.Path(child).is_file():raise ValueError('missing local import '+child)
                selected[child]=[{'imported_by':p}];queue.append(child)
    return selected,unmatched

def owner(p):
    if '/Compilation/' in p or p.startswith('Bridge/'):return 'VY3'
    if '/Views/' in p or '/Adapters/' in p or p.startswith('Solidity/Evm/'):return 'VY2'
    if '/World/' in p:return 'VY4'
    if '/Composition/' in p or '/Lowering/P8/' in p:return 'VY5'
    return 'VY1'

# Extract commands at line starts. Signatures use balanced binder delimiters;
# a theorem ending in `where` is retained without its proof body.
COMMAND=re.compile(r'(?m)^[ \t]*(?:(?:private|protected|noncomputable|unsafe)\s+)*(namespace|section|mutual|end|variable|theorem|lemma|example|structure|class)\b')

def declarations(path):
    s=pathlib.Path(path).read_text();m=mask(s); stack=[]; result=[]
    commands=list(COMMAND.finditer(m))
    for index,c in enumerate(commands):
        kind=c[1];start=c.start();tail=m[c.end():];line=m.count('\n',0,start)+1
        if kind in ('namespace','section','mutual'):
            name=tail.split('\n',1)[0].strip();stack.append((kind,name,[]));continue
        if kind=='end':
            if stack:stack.pop()
            continue
        if kind=='variable':
            end=commands[index+1].start() if index+1<len(commands) else len(s)
            # Keep exact command up to next top-level command (including non-census commands).
            other=re.search(r'(?m)^\S',m[c.end():end])
            if other:end=c.end()+other.start()
            if stack:stack[-1][2].append(s[start:end].rstrip())
            continue
        if kind not in ('theorem','lemma','example','structure','class'):continue
        name_match=re.match(r'\s*([^\s({:]+)',tail)
        name=name_match[1] if name_match and kind!='example' else '<example@'+str(line)+'>'
        nesting=[];end=c.end();found=False
        while end<len(m):
            ch=m[end]
            if not nesting and (m.startswith(':=',end) or re.match(r'where\b',m[end:])):
                found=True;break
            if ch in '({[':nesting.append(ch)
            elif ch in ')}]' and nesting:nesting.pop()
            end+=1
        if not found:raise ValueError(f'unterminated signature {path}:{line}')
        ns='.'.join(x[1] for x in stack if x[0]=='namespace')
        fq=name[len('_root_.'):] if name.startswith('_root_.') else '.'.join(filter(None,[ns,name]))
        private=bool(re.search(r'\bprivate\b',m[start:c.end()]))
        result.append(dict(id=f'{path}:{line}:{name}',file=path,line=line,kind=kind,
            source_name=fq,visibility='private' if private else 'public',signature=s[start:end].rstrip(),
            signature_sha256=sha(s[start:end].rstrip()),section_variables=[v for frame in stack for v in frame[2]],
            owner=owner(path),owner_basis='area convention; pending exact-file producer confirmation',
            witness_status='uncovered',hypothesis_classification='requires elaborated type; not inferred from lexical binders'))
    return result

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--output',type=pathlib.Path,required=True);ap.add_argument('--parsed',type=pathlib.Path);ap.add_argument('--witnesses',type=pathlib.Path);ap.add_argument('--kernel',type=pathlib.Path);args=ap.parse_args()
    selected,unmatched=files();rows=[]
    frozen=dict((p,(mode,kind,oid)) for mode,kind,oid,p in (line.split(None,3) for line in subprocess.check_output(['git','ls-tree','-r',BASE],text=True).splitlines()))
    paths=sorted(set(selected)|{str(MAP)})
    hashes=subprocess.check_output(['git','hash-object','--stdin-paths'],input=''.join(p+'\n' for p in paths),text=True).splitlines()
    for p,oid in zip(paths,hashes):
        if p not in frozen or frozen[p][2]!=oid:raise ValueError('frozen source mismatch: '+p)
    parsed={}
    if args.parsed:
        for line in args.parsed.read_text().splitlines():
            rec=json.loads(line)
            if rec.get('source_text') != pathlib.Path(rec['file']).read_text():raise ValueError('parser source mismatch: '+rec['file'])
            if rec['file'] in parsed:raise ValueError('duplicate parser file: '+rec['file'])
            parsed[rec['file']]=rec
    if args.parsed and set(parsed)!=set(selected):raise ValueError('parser file census mismatch')
    for p in sorted(selected):rows.extend(declarations(p))
    parsed_spans={}
    for file,rec in parsed.items():
        data=pathlib.Path(file).read_bytes()
        for sig in rec['signatures']:
            parsed_spans[(file,data[:sig['start_byte']].count(b'\n')+1)]=(data,sig)
    for row in rows:
        row['signature_status']='lexical_candidate_only'
        if row['kind'] not in ('theorem','lemma','example'):continue
        candidate=parsed_spans.get((row['file'],row['line']))
        if candidate:
            data,sig=candidate
            if not sig['signature_missing']:
                row['signature']=data[sig['start_byte']:sig['end_byte']].decode().rstrip()
                row['signature_sha256']=sha(row['signature'])
                row['signature_status']='lean_parser_confirmed_source_span'
                row['file_parse_errors']=parsed[row['file']]['parse_errors']
    if args.witnesses:
        manifest=json.loads(args.witnesses.read_text())
        for evidence in manifest['statements']:
            matches=[row for row in rows if row['source_name']==evidence['theorem'] and row['kind']=='theorem']
            if len(matches)!=1:raise ValueError('non-unique statement: '+evidence['theorem'])
            row=matches[0]
            if row['signature_sha256']!=evidence['frozen_signature_sha256']:raise ValueError('witness signature mismatch: '+evidence['theorem'])
            row['witness_status']=evidence['status'];row['audit_evidence']=evidence
    kernel_rows=[];kernel_index=collections.defaultdict(list)
    if args.kernel:
        for line in args.kernel.read_text().splitlines():
            rec=json.loads(line);kernel_rows.append(rec)
            if rec['status']=='typed':kernel_index[(rec['module'],rec['source_name'])].append(rec)
        for row in rows:
            module=row['file'].removesuffix('.lean').removeprefix('Bridge/').replace('/','.')
            matches=[r for r in kernel_index[(module,row['source_name'])] if r['kind']==('structure' if row['kind']=='class' else row['kind'])]
            row['kernel_status']='matched' if len(matches)==1 else ('ambiguous' if matches else 'not_yet_matched')
            if len(matches)!=1:continue
            rec=matches[0]
            row['kernel']={key:rec[key] for key in ['kernel_name','module','level_parameters','pretty_type','binders','result_pretty','result_is_false','axioms','source_range']}
            row['kernel']['type_sha256']=sha(rec['type_repr'])
            row['kernel']['fields']=[dict(name=f['name'],type_sha256=sha(f['type_repr']),pretty_type=f['pretty_type']) for f in rec['fields']]
            row['hypothesis_classification']='Fully exposed elaborated telescope recorded; global structure versus per-input roles require case evidence.'
            if row['kind']=='theorem' and row['witness_status']=='uncovered' and not rec['binders'] and set(rec['axioms'])<={'propext','Classical.choice','Quot.sound'}:
                row['witness_status']='closed_statement_verified'
            if row.get('audit_evidence',{}).get('frozen_type_sha256') and row['audit_evidence']['frozen_type_sha256']!=sha(rec['type_repr']):raise ValueError('kernel witness statement drift: '+row['source_name'])
    accepted={'joint_witness_proved','intentional_refutation_proved','closed_statement_verified'}
    ids=[r['id'] for r in rows];assert len(ids)==len(set(ids))
    output=dict(base=BASE,module_map_sha256=sha(MAP.read_text()),scope='module-map explicit patterns plus local Yul import closure',
        limitations=['Source census is conservative, not an elaborated hypothesis census.',
        'Source names for private/protected declarations require kernel-name reconciliation.',
        'No witness or feasibility conclusion is inferred from a source signature.'],
        kernel_metadata_file=str(args.kernel) if args.kernel else None,kernel_metadata_sha256=hashlib.sha256(args.kernel.read_bytes()).hexdigest() if args.kernel else None,kernel_records=len(kernel_rows),kernel_errors=sum(r['status']=='error' for r in kernel_rows),frozen_blobs_verified=True,parser_files=len(parsed),unmatched_patterns=unmatched,files=[dict(path=p,sha256=sha(pathlib.Path(p).read_text()),reasons=selected[p]) for p in sorted(selected)],declarations=rows)
    args.output.mkdir(parents=True,exist_ok=True)
    text=json.dumps(output,ensure_ascii=False,sort_keys=True,indent=2)+'\n'
    (args.output/'census.json').write_text(text)
    summary=dict(files=len(selected),declarations=len(rows),kinds=dict(collections.Counter(r['kind'] for r in rows)),owners=dict(collections.Counter(r['owner'] for r in rows)),unmatched_patterns=unmatched,census_sha256=sha(text),joint_witnesses=sum(r['witness_status']=='joint_witness_proved' for r in rows),intentional_refutations=sum(r['witness_status']=='intentional_refutation_proved' for r in rows),closed_theorems=sum(r['kind']=='theorem' and r['witness_status']=='closed_statement_verified' for r in rows),typed_source_declarations=sum(r.get('kernel_status')=='matched' for r in rows),typed_source_structures=sum(r['kind']=='structure' and r.get('kernel_status')=='matched' for r in rows),pending_negative_classifications=sum(r['kind']=='theorem' and r.get('kernel',{}).get('result_is_false',False) and r['witness_status'] not in accepted for r in rows),uncovered_named_theorems=sum(r['kind']=='theorem' and r['witness_status'] not in accepted for r in rows),uncovered=sum(r['witness_status'] not in accepted for r in rows),refutation_candidates=sum(r['witness_status']=='refutation_candidate_requires_check' for r in rows),signature_status=dict(collections.Counter(r['signature_status'] for r in rows)))
    (args.output/'summary.json').write_text(json.dumps(summary,indent=2,sort_keys=True)+'\n');print(json.dumps(summary,sort_keys=True))
if __name__=='__main__':main()
