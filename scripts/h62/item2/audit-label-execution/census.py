#!/usr/bin/env python3
"""Frozen source census, not a substitute for elaborated premise/witness checking.

Output is off git. Every named theorem/lemma is retained, including controls,
private helpers and statements that may have no Prop premises. Classification
of elaborated premises requires a Lean environment; source routing hints below
do not establish types, inhabitance or simultaneous feasibility.
"""
import argparse
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
    keys = [(r['path'],r['name']) for r in rows]
    if len(keys) != len(set(keys)): raise ValueError('duplicate declaration identity')
    return dict(schema=2, base=BASE, map=MAP, map_sha256=digest(frozen_bytes(root,MAP)),
                source_fidelity='all mapped worktree bytes equal pinned git blobs',
                limitations=['Source signatures retain defaults and full-prefix hashes; elaboration must recover section/implicit binders.',
                             'All named source theorems are candidates; no theorem is excluded by a textual hypothesis heuristic.',
                             'Owner reservations are evidence from the supplied snapshot; absent/overlapping claims require coordinator resolution.'],
                files=files, declarations=rows,
                counts=dict(files=len(files), declarations=len(rows), witnessed=0,
                            uncovered=len(rows), owner_unresolved=sum(len(r['owner_evidence']) != 1 for r in rows),
                            producer_attribution_unresolved=sum(not r.get('producer_attribution', {}).get('owner') for r in rows),
                            source_partitioned=len(rows), source_reviewed=sum('source_review' in r for r in rows), elaborated=0))

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
