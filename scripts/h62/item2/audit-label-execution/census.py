#!/usr/bin/env python3
"""Frozen source census, not a substitute for elaborated premise/witness checking.

Output is off git. Every named theorem/lemma is retained, including controls,
private helpers and statements that may have no Prop premises. Classification
of elaborated premises requires a Lean environment; source routing hints below
do not establish types, inhabitance or simultaneous feasibility.
"""
import argparse
from collections import Counter
import fnmatch
import hashlib
import json
from pathlib import Path
import re
import subprocess

BASE = 'c6f550e281a7e5affa9a99bc2cdaed556dec00e4'
MAP = 'docs/module-map/label-execution.md'

def digest(data):
    return hashlib.sha256(data).hexdigest()

def mask(text):
    """Blank nested comments and string literals without changing offsets."""
    out = list(text)
    i = 0
    depth = 0
    string = False
    line = False
    while i < len(text):
        pair = text[i:i+2]
        if line:
            if text[i] == '\n': line = False
            else: out[i] = ' '
        elif depth:
            if pair == '/-':
                out[i:i+2] = '  '; depth += 1; i += 1
            elif pair == '-/':
                out[i:i+2] = '  '; depth -= 1; i += 1
            elif text[i] != '\n': out[i] = ' '
        elif string:
            if text[i] == '\\' and i+1 < len(text):
                out[i:i+2] = '  '; i += 1
            elif text[i] == '"': out[i] = ' '; string = False
            elif text[i] != '\n': out[i] = ' '
        elif pair in ('/-', '--'):
            out[i:i+2] = '  '
            depth = int(pair == '/-'); line = pair == '--'; i += 1
        elif text[i] == '"': out[i] = ' '; string = True
        i += 1
    if depth or string: raise ValueError('unterminated comment/string')
    return ''.join(out)

def expand_braces(s):
    m = re.search(r'\{([^{}]*)\}', s)
    if not m: return [s]
    return [v for choice in m[1].split(',')
            for v in expand_braces(s[:m.start()] + choice + s[m.end():])]

def frozen_bytes(root, path):
    data = subprocess.check_output(['git','show',f'{BASE}:{path}'],cwd=root)
    if (root/path).read_bytes() != data:
        raise ValueError(f'frozen source differs from worktree: {path}')
    return data

def modules(root):
    text = frozen_bytes(root, MAP).decode()
    pattern = r'(?:Bridge/SolidityBridge|Frontend/Yul|Backend|Lowering|Yul|HashBridge|ExternalEvm)/[A-Za-z0-9_/{},.]*[A-Za-z0-9_}]'
    paths = set()
    for m in re.finditer(pattern, text):
        for name in expand_braces(m[0]):
            if not name.endswith('.lean'): name += '.lean'
            if name.startswith(('HashBridge/', 'ExternalEvm/')):
                name = 'Bridge/SolidityBridge/' + name
            elif not name.startswith('Bridge/'):
                name = 'Solidity/' + name
            paths.add(name)
    missing = [p for p in sorted(paths) if not (root / p).is_file()]
    if missing: raise ValueError('unresolved map paths: ' + ', '.join(missing))
    return sorted(paths)

DECL = re.compile(r'(?m)^[ \t]*(?:(?:private|protected|noncomputable)\s+)*(theorem|lemma)\s+([^\s({\[:]+)')
SCOPE = re.compile(r'(?m)^(namespace|section|end)\b[^\n]*')

def balanced_end(clean, start):
    pairs = {'(': ')', '{': '}', '[': ']'}
    stack = []
    for i in range(start, len(clean)):
        c = clean[i]
        if c in pairs: stack.append(pairs[c])
        elif c in pairs.values():
            if not stack or stack.pop() != c:
                raise ValueError('unbalanced source binder')
            if not stack: return i + 1
    raise ValueError('unterminated source binder')

def top_colon(clean):
    stack = []
    for i, c in enumerate(clean):
        if c in '({[': stack.append(c)
        elif c in ')}]': stack.pop()
        elif c == ':' and not stack and clean[i:i+2] != ':=': return i
    return None

def top_assignment(clean):
    depth = 0
    for i, c in enumerate(clean):
        if c in '({[': depth += 1
        elif c in ')}]': depth -= 1
        elif depth == 0 and clean[i:i+2] == ':=': return i
    return None

def source_role(type_source):
    """Source routing hint only: no elaborated Prop/type or inhabitance claim."""
    t = ' '.join(mask(type_source).split())
    if re.search(r'(?:^|[. ])Glob(?: |$)', t):
        return 'global-environment-carrier', 'Glob parameter; source/global data, not an inhabited-laws proof'
    if t.endswith('Prop') or t.endswith('Prop)'):
        return 'predicate-or-relation-parameter', 'Prop-valued type expression; truth of this relation is not assumed by supplying the parameter'
    if re.search(r'(?:∀|→)', t):
        return 'quantified-or-function-bundle', 'must retain the entire function/forall field; whether a law or data function needs elaboration'
    if re.search(r'(?:BoolSlot|StateRepr|@?Parsed|@?Prepared|AssemblyParse|Assembly|Represents|Related|Agreement|Certificate|Premises|Producer|InstrShape|BlockShape|CodeShape|\bSim\b|\.Sim\b|Frame|Capacity|CollisionFree)', t):
        return 'indexed-or-structured-bundle', 'inspect the original definition and all dependent fields jointly; Type-valued certificates can contain proof obligations'
    if re.search(r'(?:(?<!:)=|≠|≤|≥|<|>|∧|∨|¬|∈|∉)', t):
        return 'per-input-condition', 'source relation/equality/bound; exact proposition and dependence await elaboration'
    return 'argument-or-unresolved-bundle', 'data/index/type parameter or opaque premise bundle; no premise exclusion inferred'

def leading_result_foralls(result):
    """Partition written leading quantifiers; do not turn conclusions into premises."""
    clean = mask(result)
    records = []
    offset = 0
    while offset < len(clean):
        while offset < len(clean) and clean[offset].isspace(): offset += 1
        if offset == len(clean) or clean[offset] != '∀': break
        start = offset
        offset += 1
        depth = 0
        comma = None
        for i in range(offset, len(clean)):
            if clean[i] in '({[': depth += 1
            elif clean[i] in ')}]': depth -= 1
            elif clean[i] == ',' and depth == 0: comma = i; break
        if comma is None: raise ValueError('leading forall has no source delimiter')
        prefix = result[offset:comma].strip()
        prefix_clean = mask(prefix)
        plain = prefix_clean.strip()
        binders = []
        status = 'source-partitioned'
        if any(op in plain for op in ['∈','∉']):
            status = 'bounded-notation-retained-for-elaboration'
        elif plain and plain[0] in '({[':
            try:
                # The wrapper is parser input only, never a saved/checked Lean declaration.
                binders = source_bundle('theorem __source_quantifier ' + prefix + ' : True')['header_binders']
            except ValueError: status = 'opaque-source-prefix-retained'
        else:
            colon = top_colon(prefix_clean)
            names_source = prefix_clean[:colon].strip() if colon is not None else plain
            names = names_source.split()
            if not names or any(not re.fullmatch(r"[^\W\d][\w']*|_",n) for n in names):
                status = 'opaque-source-prefix-retained'
            else:
                ty = prefix[colon+1:].strip() if colon is not None else None
                role, reason = source_role(ty) if ty is not None else ('inferred-parameter-group','source has no written binder type')
                binders = [dict(source=prefix,names=names,type_source=ty,binder_syntax='result-quantified-unbracketed',
                                role_hint=role,role_evidence=reason,type_kind='pending-elaboration',inhabitance='not-checked')]
        records.append(dict(start=start,end=comma+1,source=result[start:comma+1],binder_source=prefix,
                            source_binders=binders,parse_status=status,
                            interpretation='result-level quantifier; not promoted to a header assumption'))
        offset = comma + 1
    return dict(groups=records,remaining_source=result[offset:],remaining_offset=offset,
                has_remaining_quantifier='∀' in clean[offset:],
                status='source-only; bounded, inferred and nested obligations require elaboration')

def source_bundle(signature):
    clean = mask(signature)
    match = DECL.match(clean)
    if not match: raise ValueError('not a source theorem signature')
    i = match.end()
    binders = []
    while i < len(clean):
        if clean[i].isspace(): i += 1; continue
        if clean[i] == ':':
            result = signature[i+1:].strip()
            break
        if clean[i] not in '({[':
            raise ValueError('unhandled theorem header near: ' + signature[i:i+40])
        end = balanced_end(clean, i)
        body = signature[i+1:end-1]
        colon = top_colon(mask(body))
        if colon is None and clean[i] != '[':
            names, ty = body.strip().split(), None
            role, reason = 'inferred-parameter-group', 'source has no written binder type; infer nothing before elaboration'
        else:
            names = body[:colon].strip().split() if colon is not None else []
            ty = body[colon+1:].strip() if colon is not None else body.strip()
            default = top_assignment(mask(ty))
            role, reason = source_role(ty[:default].strip() if default is not None else ty)
        binders.append(dict(source=signature[i:end], names=names, type_source=ty,
                            binder_syntax={'(': 'explicit', '{': 'implicit', '[': 'instance'}[clean[i]],
                            role_hint=role, role_evidence=reason,
                            type_kind='pending-elaboration', inhabitance='not-checked'))
        i = end
    else: raise ValueError('missing result colon')
    return dict(classification_level='source-routing-only',
                header_binders=binders, result_source=result,
                leading_result_quantifiers=leading_result_foralls(result),
                result_contains_forall='∀' in mask(result),
                result_begins_forall=mask(result).lstrip().startswith('∀'),
                result_boundary='conclusion as written, not promoted to additional header premises',
                result_contains_arrow='→' in mask(result),
                result_premise_review='pending: retain all forall/arrow domains and local lets; do not equate the header with the elaborated telescope',
                simultaneous_bundle='all parameters, certificates, global fields and per-input facts from the unchanged statement together',
                simultaneous_witness='pending', global_structure_inhabitance='not-checked',
                per_input_feasibility='not-checked')

def declarations(text, path):
    clean = mask(text)
    scopes = []
    events = sorted([(m.start(), 'scope', m) for m in SCOPE.finditer(clean)] +
                    [(m.start(), 'decl', m) for m in DECL.finditer(clean)])
    rows = []
    for pos, kind, m in events:
        if kind == 'scope':
            words = m[0].split()
            if words[0] == 'end':
                if scopes: scopes.pop()
            else: scopes.append((words[0], words[1] if len(words)>1 else ''))
            continue
        start = m.start()
        # Defaults inside binders contain :=; only depth-zero := ends a signature.
        depth = 0
        pending_lets = 0
        end = None
        for i in range(m.end(), len(clean)):
            c = clean[i]
            if c in '({[': depth += 1
            elif c in ')}]': depth -= 1
            if depth == 0 and clean[i:i+3] == 'let' and (i == 0 or not (clean[i-1].isalnum() or clean[i-1] == '_')) and (i+3 == len(clean) or not (clean[i+3].isalnum() or clean[i+3] == '_')):
                pending_lets += 1
            if depth == 0 and clean[i:i+2] == ':=':
                if pending_lets: pending_lets -= 1
                else:
                    end = i; break
        if end is None: raise ValueError(f'{path}:{m[2]}: unsupported theorem syntax')
        ns = '.'.join(n for k,n in scopes if k == 'namespace')
        name = m[2]
        full = name[len('_root_.'):] if name.startswith('_root_.') else '.'.join(filter(None,[ns,name]))
        raw = text[start:end].strip()
        rows.append(dict(name=full, source_name=name, path=path,
                         line=text.count('\n',0,start)+1,
                         signature=raw, signature_sha256=digest(raw.encode()),
                         source_premise_bundle=source_bundle(raw),
                         visibility='private' if re.search(r'\bprivate\b', clean[start:m.end()]) else 'public',
                         context_sha256=digest(text[:start].encode()),
                         preceding_variable_commands=[v[0] for v in re.finditer(r'(?m)^variable\b[^\n]*(?:\n[ \t]+[^\n]*)*', text[:start])],
                         premise_classification='pending-elaborated-type',
                         simultaneous_witness='pending', statement_fidelity='pending'))
    return rows

def owners(path, registry):
    matches = []
    for item in registry['items']:
        if item.get('group') != 'h30-file-ownership': continue
        for glob in item.get('writeScope','').split(';'):
            if fnmatch.fnmatchcase(path, glob.strip()):
                matches.append(dict(owner=item.get('owner'), reservation=item['id'], pattern=glob.strip()))
    return matches

def reconcile_owners(root, registry, files, rows, reconciliation):
    if reconciliation.get('base') != BASE: raise ValueError('owner reconciliation base mismatch')
    indexed = {r['path']: r for r in reconciliation['files']}
    if len(indexed) != len(reconciliation['files']): raise ValueError('duplicate owner reconciliation path')
    missing = {f['path'] for f in files if not f['owner_evidence']}
    if set(indexed) != missing: raise ValueError('reconciliation must cover exactly the missing-reservation files')
    for path, entry in indexed.items():
        f = next(f for f in files if f['path'] == path)
        if entry['frozen_sha256'] != f['sha256'] or entry['declarations'] != f['declarations']:
            raise ValueError('owner source/count mismatch: ' + path)
        producer = next(r for r in registry['items'] if r['id'] == entry['producer_mapping_id'])
        if producer.get('owner') != entry['live_producer']:
            raise ValueError('live producer mapping mismatch: ' + path)
        migration = next(r for r in registry['items'] if r['id'] == entry['migration_reservation'])
        if migration['owner'] != entry['migration_overlay_owner'] or not any(fnmatch.fnmatchcase(path, g.strip()) for g in migration['writeScope'].split(';')):
            raise ValueError('migration reservation mismatch: ' + path)
        lineage_path_seen = False
        for evidence in entry['source_evidence']:
            if evidence['kind'] == 'frozen-document':
                if digest(frozen_bytes(root, evidence['path'])) != evidence['sha256']:
                    raise ValueError('owner document mismatch')
            elif evidence['kind'] == 'integration-commit':
                subprocess.run(['git','merge-base','--is-ancestor',evidence['commit'],BASE],cwd=root,check=True)
                changed = subprocess.check_output(['git','diff-tree','--no-commit-id','--name-only','-r',evidence['commit']],cwd=root,text=True).splitlines()
                lineage_path_seen = lineage_path_seen or path in changed
            else: raise ValueError('unsupported owner evidence')
        if not lineage_path_seen: raise ValueError('no exact-file integration evidence: ' + path)
    for item in files + rows:
        evidence = item['owner_evidence']
        if item['path'] in indexed:
            entry = indexed[item['path']]
            item['producer_attribution'] = dict(owner=entry['live_producer'],
                basis='frozen source lineage plus explicit existing producer mapping',
                evidence=entry['source_evidence'], migration_overlay_owner=entry['migration_overlay_owner'],
                exact_file_h30_reservation_present=False,
                write_authorization='none granted; task scope keeps original files read-only')
        elif len(evidence) == 1:
            item['producer_attribution'] = dict(owner=evidence[0]['owner'],basis='existing H30 snapshot',
                exact_file_h30_reservation_present=True,
                write_authorization='none granted; task scope keeps original files read-only')
        else:
            item['producer_attribution'] = dict(owner=None,basis='unresolved or ambiguous',
                write_authorization='none granted')

def apply_source_reviews(root, rows, review):
    if review['base'] != BASE: raise ValueError('source review base mismatch')
    indexed = {(r['path'], r['name']): r for r in rows}
    seen = set()
    for definition in review['definitions']:
        data = frozen_bytes(root, definition['path'])
        if digest(data) != definition['source_sha256'] or definition['excerpt'] not in data.decode() or digest(definition['excerpt'].encode()) != definition['excerpt_sha256']:
            raise ValueError('source definition excerpt mismatch')
    for entry in review['declarations']:
        key = (entry['path'], entry['name'])
        if key in seen: raise ValueError('duplicate source review')
        seen.add(key)
        if entry['status'] != 'source-inspection-only' or entry['simultaneous_witness'] != 'pending':
            raise ValueError('source review cannot certify a witness')
        row = indexed[key]
        if row['signature_sha256'] != entry['signature_sha256']: raise ValueError('source review signature mismatch')
        row['source_review'] = entry

def module_source_summaries(files, rows):
    areas = ['Bridge/SolidityBridge/ExternalEvm/','Bridge/SolidityBridge/HashBridge/',
             'Solidity/Backend/LabelExec/','Solidity/Backend/Transient/',
             'Solidity/Backend/PrimitivePackets/UnsignedDiv/','Solidity/Backend/StructuredFlow/',
             'Solidity/Frontend/Yul/','Solidity/Lowering/G19/','Solidity/Yul/Adapters/',
             'Solidity/Yul/Checks/','Solidity/Yul/']
    for f in files:
        members = [r for r in rows if r['path'] == f['path']]
        if len(members) != f['declarations']: raise ValueError('module declaration total mismatch')
        headers = [b for r in members for b in r['source_premise_bundle']['header_binders']]
        quantifiers = [g for r in members for g in r['source_premise_bundle']['leading_result_quantifiers']['groups']]
        quantified_binders = [b for g in quantifiers for b in g['source_binders']]
        area = next((a for a in areas if f['path'].startswith(a)),None)
        if area is None: raise ValueError('unclassified mapped source area: ' + f['path'])
        f['source_summary'] = dict(area=area,classification='source-only; not module proof validation',
            declared_theorems=len(members),public_theorems=sum(r['visibility']=='public' for r in members),
            private_helpers=sum(r['visibility']=='private' for r in members),
            declared_statement_identities=[dict(name=r['name'],line=r['line'],signature_sha256=r['signature_sha256']) for r in members],
            zero_direct_declarations=not members,
            zero_declaration_boundary='no direct named theorem; may contain definitions or only imports; not an inhabitance or imported-interface claim' if not members else None,
            header_binder_groups=len(headers),header_role_hints=dict(Counter(b['role_hint'] for b in headers)),
            leading_result_quantifier_groups=len(quantifiers),result_binder_groups=len(quantified_binders),
            result_role_hints=dict(Counter(b['role_hint'] for b in quantified_binders)),
            retained_unparsed_or_bounded_prefixes=sum(g['parse_status']!='source-partitioned' for g in quantifiers),
            retained_nested_quantifier_statements=[r['name'] for r in members if r['source_premise_bundle']['leading_result_quantifiers']['has_remaining_quantifier']],
            manually_source_reviewed=sum('source_review' in r for r in members),
            elaborated_signatures=0,simultaneous_witnesses=0,
            pending=['exact implicit/inherited binder closure','bundled certificate fields and global laws',
                     'joint per-input feasibility','success/totality and observable boundaries','Lean verification'])
    identities=[(f['path'],r['name']) for f in files for r in f['source_summary']['declared_statement_identities']]
    if len(identities)!=len(rows) or len(set(identities))!=len(rows):
        raise ValueError('module source census does not account for every statement exactly once')

def run(root, registry, reconciliation=None, source_reviews=None):
    files = []
    rows = []
    for path in modules(root):
        data = frozen_bytes(root,path)
        ds = declarations(data.decode(),path)
        own = owners(path,registry)
        for row in ds: row['owner_evidence'] = own
        files.append(dict(path=path, sha256=digest(data), declarations=len(ds), owner_evidence=own))
        rows.extend(ds)
    for item in files + rows:
        own = item['owner_evidence']
        item['producer_attribution'] = dict(owner=own[0]['owner'] if len(own) == 1 else None,
            basis='existing H30 snapshot' if len(own) == 1 else 'unresolved or ambiguous',
            exact_file_h30_reservation_present=len(own) == 1,
            write_authorization='none granted; task scope keeps original files read-only')
    if reconciliation is not None: reconcile_owners(root,registry,files,rows,reconciliation)
    if source_reviews is not None: apply_source_reviews(root,rows,source_reviews)
    module_source_summaries(files,rows)
    keys = [(r['path'],r['name']) for r in rows]
    if len(keys) != len(set(keys)): raise ValueError('duplicate declaration identity')
    return dict(schema=3, base=BASE, map=MAP, map_sha256=digest(frozen_bytes(root,MAP)),
                source_fidelity='all mapped worktree bytes equal pinned git blobs',
                limitations=['Source signatures retain defaults and full-prefix hashes; elaboration must recover section/implicit binders.',
                             'All named source theorems are candidates; no theorem is excluded by a textual hypothesis heuristic.',
                             'Owner reservations are evidence from the supplied snapshot; absent/overlapping claims require coordinator resolution.'],
                files=files, declarations=rows,
                counts=dict(files=len(files), declarations=len(rows), witnessed=0,
                            uncovered=len(rows), owner_unresolved=sum(len(r['owner_evidence']) != 1 for r in rows),
                            producer_attribution_unresolved=sum(not r.get('producer_attribution', {}).get('owner') for r in rows),
                            source_partitioned=len(rows), source_reviewed=sum('source_review' in r for r in rows), source_modules_partitioned=len(files), elaborated=0))

if __name__ == '__main__':
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--root',type=Path,default=Path(__file__).resolve().parents[4])
    p.add_argument('--ownership',type=Path,required=True)
    p.add_argument('--output',type=Path,required=True)
    p.add_argument('--owner-reconciliation',type=Path)
    p.add_argument('--source-reviews',type=Path)
    args=p.parse_args()
    result=run(args.root,json.loads(args.ownership.read_text()),
               json.loads(args.owner_reconciliation.read_text()) if args.owner_reconciliation else None,
               json.loads(args.source_reviews.read_text()) if args.source_reviews else None)
    args.output.write_text(json.dumps(result,indent=2,ensure_ascii=False)+'\n')
    print(json.dumps(result['counts'],sort_keys=True))
