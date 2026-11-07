#!/usr/bin/env python3
"""Source-only premise and additional-declaration census for H70.

No Lean process or elaboration is used. Lexical binders and result telescopes
are distinguished from potential section context and nested result propositions.
Every category carries source evidence; unresolved types stay in the ledger.
No category excludes an original declaration or adds checked witness coverage.
"""
import argparse
import collections
import hashlib
import json
import pathlib
import re
import subprocess
from census import BASE, EVENT, mask, signature_end

ROOT = pathlib.Path(__file__).resolve().parents[4]
RULES_PATH = ROOT/'tests/h62/item2/audit-roadmap/source-classification-rules.json'
PAIRS = {'(':')', '{':'}', '[':']', '⦃':'⦄'}


def sha(data):
    return hashlib.sha256(data).hexdigest()


def top_positions(text):
    """Source character offsets outside (), {}, [] and strict implicit binders."""
    stack = []
    for i, ch in enumerate(text):
        if not stack:
            yield i
        if ch in PAIRS:
            stack.append(PAIRS[ch])
        elif ch in PAIRS.values():
            if not stack or stack.pop() != ch:
                raise ValueError('unbalanced source delimiters')
    if stack:
        raise ValueError('unbalanced source delimiters')


def top_find(text, token):
    clean = mask(text)
    for i in top_positions(clean):
        if clean.startswith(token, i):
            return i
    return -1


def group_end(text, start):
    stack = []
    for i in range(start, len(text)):
        ch = text[i]
        if ch in PAIRS:
            stack.append(PAIRS[ch])
        elif ch in PAIRS.values():
            if not stack or stack.pop() != ch:
                raise ValueError('unbalanced binder')
            if not stack:
                return i+1
    raise ValueError('unterminated binder')


def default_assignment(text):
    clean = mask(text)
    pending = 0
    for i in top_positions(clean):
        if re.match(r'(?:let|have)\b',clean[i:]) and (i == 0 or not (clean[i-1].isalnum() or clean[i-1] in '_.')):
            pending += 1
        if clean.startswith(':=',i):
            if pending:
                pending -= 1
            else:
                return i
    return -1


def binder_groups(raw):
    """Parse only consecutive source binder groups, never groups inside types."""
    text = mask(raw)
    i = 0
    groups = []
    while True:
        while i < len(text) and text[i].isspace():
            i += 1
        if i == len(text) or text[i] not in PAIRS:
            return groups, i
        end = group_end(text, i)
        content = text[i+1:end-1]
        raw_content = raw[i+1:end-1]
        colon = top_find(content, ':')
        if text[i] == '[':
            before = content[:colon] if colon >= 0 else ''
            typ = raw_content[colon+1:] if colon >= 0 else raw_content
            names = before.strip().split()
            style = 'instance'
        else:
            before = content[:colon] if colon >= 0 else content
            typ = raw_content[colon+1:] if colon >= 0 else None
            names = before.strip().split()
            style = {'(':'explicit','{':'implicit','⦃':'strict-implicit'}[text[i]]
        default = None
        if typ is not None:
            pos = default_assignment(typ)
            if pos >= 0:
                default, typ = typ[pos+2:].strip(), typ[:pos]
            typ = typ.strip()
        groups.append(dict(raw=raw[i:end], names=names, type_source=typ,
            default_source=default, binder_style=style,
            source_start=i, source_end=end))
        i = end


def strip_outer(text):
    text = text.strip()
    while text.startswith('(') and group_end(mask(text),0) == len(text):
        text = text[1:-1].strip()
    return text


def peel_result(raw):
    """Only leading forall/arrow domains; never flatten Not, exists or a let."""
    text = raw.strip()
    nodes = []
    while text:
        if text.startswith('∀') or re.match(r'forall\b',text):
            prefix = 1 if text.startswith('∀') else 6
            comma = top_find(text[prefix:], ',')
            if comma < 0:
                return nodes, text, 'leading-forall-unparsed'
            binder = text[prefix:prefix+comma].strip()
            groups, consumed = binder_groups(binder)
            if groups and not binder[consumed:].strip():
                for g in groups:
                    nodes.append(dict(kind='leading-forall-binder', **g))
            else:
                colon = top_find(binder, ':')
                nodes.append(dict(kind='leading-forall-binder',raw=binder,
                    names=(binder[:colon] if colon >= 0 else binder).split(),
                    type_source=binder[colon+1:].strip() if colon >= 0 else None,
                    binder_style='inferred-source-forall'))
            text = text[prefix+comma+1:].strip()
            continue
        if re.match(r'(let|have|match|if|fun|do|by|calc|exists|Exists)\b',text) or text.startswith(('∃','Σ')):
            return nodes, text, 'scoped-expression-retained-without-promoting-inner-arrows'
        if top_find(text,'↔') >= 0:
            return nodes, text, 'outer-iff-retained-without-promoting-inner-arrows'
        arrow = top_find(text,'→')
        ascii_arrow = top_find(text,'->')
        choices = [(arrow,1),(ascii_arrow,2)]
        choices = [(i,n) for i,n in choices if i >= 0]
        if not choices:
            return nodes, text, 'result-preserved-without-flattening-nested-propositions'
        i,n = min(choices)
        domain = text[:i].strip()
        groups, consumed = binder_groups(domain)
        if groups and not domain[consumed:].strip() and all(g['type_source'] is not None and all(re.fullmatch(r"[\w'.?]+",name) for name in g['names']) for g in groups):
            for g in groups:
                nodes.append(dict(kind='leading-dependent-arrow-binder', **g))
        else:
            nodes.append(dict(kind='leading-arrow-domain',raw=domain,names=[],
                type_source=domain,binder_style='anonymous-domain'))
        text = text[i+n:].strip()
    return nodes, text, 'empty-result-source'


def type_head(text):
    text = strip_outer(text)
    match = re.match(r'[@]?([^\s({\[]+)', text)
    return match[1] if match else ''


def source_shape(typ, predicates, records):
    if typ is None:
        return 'inferred-or-unresolved-type'
    _, tail, stop = peel_result(typ)
    tail = strip_outer(tail)
    if stop.startswith('scoped-expression'):
        return 'scoped-result-needs-semantic-review'
    if re.fullmatch(r'Prop',tail):
        return 'predicate-or-proposition-sort'
    if re.match(r'(Type|Sort)(\s|$)',tail):
        return 'type-sort'
    if any(top_find(tail, op) >= 0 for op in ['↔','∧','∨','≠',' = ',' ≤ ',' < ',' ∈ ']) or tail.startswith(('¬','∃')) or tail in ('True','False'):
        return 'proposition-expression-source'
    head = type_head(tail).lstrip('@')
    if head in predicates or any(head.endswith('.'+n) for n in predicates):
        return 'named-proposition-application-source'
    if head in records:
        return 'named-proof-bearing-record-source'
    if head in {'Bool','String','Expr','Lean.Expr','MetaM','Lean.MetaM','CoreM','Lean.CoreM',
                'IO','EIO','CommandElab','Tactic','TacticM','TermElabM','StateRefT','ReaderT',
                'Nat','Int','UInt8','UInt64','Unit','List','Option','Array','Vector','Repr',
                'ToExpr','Lean.ToExpr','LE','Append','Name','Lean.Name','Format','Doc'}:
        return 'operational-or-data-type-annotation'
    return 'named-or-dependent-type-needs-semantic-review'


def role_for(group, predicates, records):
    typ = group['type_source']
    shape = source_shape(typ,predicates,records)
    if group.get('binder_style') == 'instance':
        role = 'typeclass-input; laws-and-instances-not-elaborated'
    elif shape == 'named-proof-bearing-record-source':
        role = 'global-certificate-or-proof-bearing-interface-input'
    elif shape == 'predicate-or-proposition-sort':
        role = 'predicate-data-input; not-proof-of-that-predicate'
    elif shape == 'type-sort':
        role = 'type-or-sort-input'
    elif shape in ('proposition-expression-source','named-proposition-application-source'):
        head = type_head(typ).rsplit('.',1)[-1] if typ else ''
        if head in {'PublicCorrectness','NonVacuous','AllSettings','SettingsRespected','Refines','RefinesUnder','Approved','Sane','Keccak','AllPipelines'}:
            role = 'global-contract-or-relation-law-source-pattern; joint-world-required'
        elif head in {'Admitted','WellFormed','InProfile','Allowed','Admissible','Matches','Forward','Guard','NoCollision','NoOverlap','Exec'}:
            role = 'per-input-or-per-run-feasibility-proof-source-pattern; joint-world-required'
        else:
            role = 'law-or-per-input-feasibility-proof-source; semantic-scope-unresolved; joint-world-required'
    else:
        role = 'value-or-unresolved-dependent-input; proof-bearing-status-not-excluded'
    return dict(**group, source_type_shape=shape, premise_role=role,
        elaborated_parameter_status='not asserted')


def declaration_header(src, clean, match, limit):
    prefix = clean[match.start():match.start(1)]
    if 'deriving' in prefix.split():
        end = src.find('\n',match.start())
        if end < 0: end = len(src)
        return src[match.start():end], end, 'generated-instance-command'
    end = signature_end(clean,match.end(1))
    if end > limit:
        raise ValueError('header crosses next source declaration')
    return src[match.start():end].strip(), end, 'source-header'


def header_parts(raw,kind):
    clean = mask(raw)
    m = re.search(r'\b'+kind+r'\b',clean)
    pos = m.end()
    while pos < len(clean) and clean[pos].isspace():
        pos += 1
    rest = clean[pos:]
    anonymous = kind == 'instance' and (not rest or rest[0] in ':({[')
    if not anonymous:
        name = re.match(r'\S+',rest)
        pos += name.end()
    raw_rest = raw[pos:]
    groups, consumed = binder_groups(raw_rest)
    result = raw_rest[consumed:].strip()
    return groups, result[1:].strip() if result.startswith(':') else None


def structure_fields(src, clean, begin, end):
    body = clean[begin:end]
    boundary = re.search(r'^(?:\S|[ \t]*deriving\b)', body, re.M)
    if boundary:
        end = begin + boundary.start()
        body = clean[begin:end]
    matches = []
    for m in re.finditer(r'^([ \t]+)([^\s:(){}\[\]|]+)([^\n]*)',body,re.M):
        content = m[2]+m[3]
        try:
            colon = top_find(content,':')
        except ValueError:
            continue  # Continuation/body line, not a complete field prefix.
        if colon >= 0 and not content[colon:].startswith(':='):
            matches.append((len(m[1]),m,colon))
    if not matches:
        return []
    indent = min(d for d,_,_ in matches)
    matches = [(m,c) for d,m,c in matches if d == indent]
    fields = []
    for index,(m,colon) in enumerate(matches):
        start = begin+m.start()+len(m[1])
        stop = begin+matches[index+1][0].start() if index+1 < len(matches) else end
        raw = src[start:stop].strip()
        clean_field = mask(raw)
        split = top_find(clean_field,':')
        tail = raw[split+1:].strip()
        default = default_assignment(tail)
        if default >= 0: tail = tail[:default].strip()
        tail = tail[:len(mask(tail).rstrip())].strip()
        fields.append(dict(field_index=index,source_field_label=m[2],
            line=src[:start].count('\n')+1,source_char_offset=start,
            type_source=tail,type_sha256=sha(tail.encode()),
            default_present=default >= 0,
            identity_boundary='source-location and index; no generated projection name asserted'))
    return fields


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--census',required=True,type=pathlib.Path)
    ap.add_argument('--audit',required=True,type=pathlib.Path)
    ap.add_argument('--output',required=True,type=pathlib.Path)
    args = ap.parse_args()
    out = args.output.resolve()
    if out.is_relative_to(ROOT): raise ValueError('H44: output must be off git')
    census = json.loads(args.census.read_text())
    audit = json.loads(args.audit.read_text())
    assert census['base'] == audit['base'] == BASE
    checked = {r['source_qualified_name']:r for r in audit['statements']}
    overrides = json.loads(RULES_PATH.read_text())['rules']
    inputs = {(r['module'],r['line']):r for r in census['statements']}
    candidates = {(r['module'],r['line']):r for r in census['other_declaration_candidates']}
    assert len(inputs) == 351 and len(candidates) == 649
    records = []
    for module in census['modules']:
        path = module['path']
        data = subprocess.check_output(['git','show',BASE+':'+path],cwd=ROOT)
        assert sha(data) == module['sha256']
        src = data.decode(); clean = mask(src); events = list(EVENT.finditer(clean))
        for i,m in enumerate(events):
            line = src[:m.start()].count('\n')+1
            key = (path,line)
            if key not in inputs and key not in candidates: continue
            original = inputs.get(key) or candidates[key]
            limit = events[i+1].start() if i+1 < len(events) else len(src)
            header,end,form = declaration_header(src,clean,m,limit)
            params,result = ([],None) if form == 'generated-instance-command' else header_parts(header,m[1])
            inherited = []
            for context in original.get('section_variable_context',[]):
                raw = re.sub(r'^variable\s*','',context)
                groups,_ = binder_groups(raw)
                inherited.extend(groups)
            fields = structure_fields(src,clean,end+len('where'),limit) if m[1] == 'structure' else []
            record = dict(source_id=f'{path}:{line}',module=path,line=line,
                source_qualified_name=original.get('source_qualified_name'),kind=m[1],
                source_form=form,source_char_offset=m.start(),
                source_byte_offset=len(src[:m.start()].encode()),
                header=header,header_sha256=sha(header.encode()),
                parameter_groups=params,result_type_source=result,
                potential_inherited_context=inherited,structure_fields=fields,
                checked_proof_claim_added=False,
                proof_boundary='source syntax and authored review only; no elaboration or new witness')
            records.append(record)
    assert len(records) == len(inputs)+len(candidates)
    names = {r['source_qualified_name'] for r in records}
    assert set(overrides) <= names
    predicates = set()
    proof_records = {part for name,rule in overrides.items() for part in (name,name.rsplit('.',1)[-1])
        if rule['category'] in ('proof-bearing-record-type','proposition-record-type')}
    for r in records:
        typ = r['result_type_source']
        if typ and source_shape(typ,set(),set()) == 'predicate-or-proposition-sort':
            predicates.add(r['source_qualified_name'].rsplit('.',1)[-1])
        for f in r['structure_fields']:
            if source_shape(f['type_source'],set(),set()) == 'predicate-or-proposition-sort':
                predicates.add(f['source_field_label'])
    for r in records:
        r['parameter_groups'] = [role_for(g,predicates,proof_records) for g in r['parameter_groups']]
        r['potential_inherited_context'] = [dict(**role_for(g,predicates,proof_records),
            usage_status='potential lexical context only; actual inheritance/usage not established')
            for g in r['potential_inherited_context']]
        for f in r['structure_fields']:
            f['source_type_shape'] = source_shape(f['type_source'],predicates,proof_records)
        r['result_type_shape'] = source_shape(r['result_type_source'],predicates,proof_records)
        nodes,remaining,stop = peel_result(r['result_type_source']) if r['result_type_source'] else ([],None,'inferred-result-type')
        r['leading_result_telescope'] = [role_for(n,predicates,proof_records) for n in nodes]
        r['remaining_result_source'] = remaining
        r['result_scope_boundary'] = stop
        r['joint_world_requirement'] = 'All actual declaration/leading inputs and premises must hold together; potential lexical context needs elaborated filtering. Nested conclusion propositions are not silently promoted to assumptions.'
        r['live_owner_status'] = 'unconfirmed; H70 routing conveys no original-file edit permission'
        name = r['source_qualified_name']
        if r['kind'] in ('theorem','lemma'):
            prior = checked[name]
            r['classification'] = prior['classification']
            r['existing_witness_status'] = prior['witness_status']
            r['source_only_work_item'] = prior['witness_status'] == 'uncovered'
            r['dependency_blockers'] = prior['dependency_blockers']
        elif name in overrides:
            r['classification'] = overrides[name]['category']
            r['classification_reason'] = overrides[name]['reason']
        elif r['source_form'] == 'generated-instance-command':
            r['classification'] = 'generated-instance-command; elaborated names unknown'
        elif r['kind'] in ('structure','inductive'):
            r['classification'] = 'proposition-type-declaration' if r['result_type_shape'] == 'predicate-or-proposition-sort' else 'record-or-inductive-type-with-source-field-ledger'
        elif r['kind'] == 'instance':
            r['classification'] = 'operational-or-unresolved-instance; laws not inferred from class name'
        elif r['result_type_shape'] == 'predicate-or-proposition-sort':
            r['classification'] = 'predicate-definition; not a proof inhabitant'
        elif r['result_type_shape'] in ('proposition-expression-source','named-proposition-application-source'):
            r['classification'] = 'proposition-valued-term-source; kernel proof check pending'
        elif r['result_type_shape'] == 'named-proof-bearing-record-source':
            r['classification'] = 'proof-carrying-constructor-source; whole record check pending'
        elif r['result_type_shape'] == 'operational-or-data-type-annotation':
            r['classification'] = 'operational-or-data-result-source; no proof exclusion implied'
        elif r['kind'] == 'abbrev':
            r['classification'] = 'alias-with-inferred-target; semantic expansion pending'
        else:
            r['classification'] = 'dependent-or-inferred-result; semantic classification pending'
    theorem_rows = [r for r in records if r['kind'] in ('theorem','lemma')]
    candidate_rows = [r for r in records if r['kind'] not in ('theorem','lemma')]
    summary = dict(mapped_modules=len(census['modules']),theorems=len(theorem_rows),
        uncovered_source_rows=sum(r['source_only_work_item'] for r in theorem_rows),
        existing_checked_originals=sum(not r['source_only_work_item'] for r in theorem_rows),
        original_additional_candidates=642,omitted_source_commands_recovered=7,
        additional_candidates=len(candidate_rows),
        source_parameter_groups=sum(len(r['parameter_groups']) for r in theorem_rows),
        leading_result_input_groups=sum(len(r['leading_result_telescope']) for r in theorem_rows),
        potential_inherited_groups=sum(len(r['potential_inherited_context']) for r in theorem_rows),
        structure_fields=sum(len(r['structure_fields']) for r in candidate_rows),
        candidate_categories=dict(collections.Counter(r['classification'] for r in candidate_rows)),
        new_checked_witnesses=0,elaborated_telescope_claim=False)
    result = dict(base=BASE,
        h70_wait_plan=dict(contacts=['solidity-h62-6-20261106/'+lane for lane in ['migrate-backend','migrate-hash','migrate-sortcheck','migrate-source','migrate-syntax']],
            boundary='Plan-wide requester routing only; not per-row dependency edges, live ownership or edit permission; relay.sh is host-only'),
        structure_field_scope='Direct source fields only; inherited/generated projections are not elaborated or expanded',
        h70_boundary='source census only; routed owners do not grant edits',
        inputs=dict(census=str(args.census.resolve()),census_sha256=sha(args.census.read_bytes()),
            audit=str(args.audit.resolve()),audit_sha256=sha(args.audit.read_bytes()),
            authored_rules_sha256=sha(RULES_PATH.read_bytes())),summary=summary,
        theorem_premise_census=theorem_rows,additional_declaration_census=candidate_rows)
    out.mkdir(parents=True,exist_ok=True)
    data = (json.dumps(result,ensure_ascii=False,indent=2)+'\n').encode()
    (out/'source-premises.json').write_bytes(data)
    (out/'SHA256SUMS').write_text(sha(data)+'  source-premises.json\n')
    lines = ['# H70 source-only census', '',
        'No new checked witness or elaborated telescope is asserted.', '',
        f"Theorems: {len(theorem_rows)}; previously checked: {summary['existing_checked_originals']}; uncovered: {summary['uncovered_source_rows']}.",
        f"Additional source candidates: {len(candidate_rows)} (642 previously inventoried plus seven recovered commands).", '',
        '| Module | Theorems | Uncovered | Other source candidates | Direct structure fields |',
        '|---|---:|---:|---:|---:|']
    for module in census['modules']:
        path = module['path']
        ts = [r for r in theorem_rows if r['module'] == path]
        cs = [r for r in candidate_rows if r['module'] == path]
        lines.append(f"| {path} | {len(ts)} | {sum(r['source_only_work_item'] for r in ts)} | {len(cs)} | {sum(len(r['structure_fields']) for r in cs)} |")
    lines += ['', 'Categories describe source evidence only. Predicate definitions are not proofs;',
        'Bool/Expr/checker data are not semantic certificates. Type-valued certificates may carry laws.',
        'Potential inherited context is not a list of elaborated parameters.',
        'Unresolved dependent results and aliases remain obligations, never exclusions.',
        'Migration contacts are plan-wide routing metadata; no original-file edit permission follows.', '']
    (out/'source-summary.md').write_text('\n'.join(lines))
    print(json.dumps(summary,sort_keys=True))

if __name__ == '__main__':
    main()
