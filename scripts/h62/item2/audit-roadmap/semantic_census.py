#!/usr/bin/env python3
"""Source semantic refinement of the 246 H70 pending results.
Family descriptions never establish type equality, proof exclusion or witnesses.
"""
import argparse
import collections
import hashlib
import json
import pathlib
import re
import subprocess
from census import BASE, EVENT, mask, signature_end
from source_census import peel_result, type_head

ROOT = pathlib.Path(__file__).resolve().parents[4]
RULES = ROOT/'tests/h62/item2/audit-roadmap'
PENDING = ('dependent-or-inferred-result','alias-with-inferred-target')
SENSITIVE = {'Word','Address','State','Heap','Options','Context','Machine','Env','Program','Artifact','Pass'}

def sha(data):
    return hashlib.sha256(data).hexdigest()

def body_first_line(src,line):
    """Frozen targeted aliases and string RHS use one physical source line.
    Fail for unsupported layout instead of inventing an expansion.
    """
    clean = mask(src)
    matches = list(EVENT.finditer(clean))
    found = [(i,m) for i,m in enumerate(matches) if src[:m.start()].count('\n')+1 == line]
    assert len(found) == 1
    i,m = found[0]
    stop = matches[i+1].start() if i+1 < len(matches) else len(src)
    end = signature_end(clean,m.end(1))
    assert clean[end:end+2] == ':=', 'expansion requires explicit := declaration'
    raw = src[end+2:stop]
    assert raw and raw.splitlines()[0].strip(), 'multiline expansion unsupported'
    return raw.splitlines()[0].strip()

def family_index(families):
    index = {}
    for f in families:
        for head in f['heads']:
            if head in index:
                raise ValueError('ambiguous authored family head: '+head)
            index[head] = f
    return index

def classify_record(record,families,aliases,folds,src,identities=None):
    name = record['source_qualified_name']
    result = dict(prior_classification=record['classification'],
        evidence_level='source-directed family/alias review only',
        checked_witness_added=False,elaborated_identity_claim=False,
        excludes_from_audit=False,
        residual_obligations=[
            'Exact elaborated types, intrinsic proof fields and semantic laws remain subject to checking.',
            'This classification does not witness a conjunction of interface hypotheses.'])
    if record['kind'] == 'abbrev':
        if name not in aliases:
            raise ValueError('unreviewed alias: '+str(name))
        rule = aliases[name]
        rhs = body_first_line(src,record['line'])
        assert rhs == rule['expected_rhs'], (name,rhs,rule['expected_rhs'])
        result.update(family=rule['category'],evidence_references=rule.get('target_evidence',[]),source_expansion=rhs,
            source_expansion_sha256=sha(rhs.encode()),
            identity_policy='Exact frozen RHS recorded; no kernel definitional-equality claim.')
        result['residual_obligations'].append(rule['remaining'])
        return result
    if record['result_type_source'] is None:
        rhs = body_first_line(src,record['line'])
        allowed = {'Solidity.Tools.Upstream.ABI.'+n for n in ['dataName','outputName','argName','retName']}
        assert name in allowed and rhs.startswith(('"','s!"')), (name,rhs)
        result.update(family='inferred-string-or-interpolated-string-function',
            source_expansion=rhs,source_expansion_sha256=sha(rhs.encode()),
            identity_policy='Literal/interpolation source classification; private elaborated name unknown.')
        result['residual_obligations'].append('Naming text is not replay/admission correctness.')
        return result
    _,tail,scope = peel_result(record['result_type_source'])
    head = type_head(tail)
    if head not in families:
        raise ValueError('unreviewed result-family head: '+head+' at '+str(name))
    f = families[head]
    result.update(family=f['id'],declared_result_source=record['result_type_source'],
        ultimate_result_source=tail,ultimate_head_source=head,
        description=f['description'],evidence_references=f['evidence'],
        source_scope_boundary=scope,
        identity_policy='Namespace/open-sensitive spelling retained; family tags never unify types or exclude proof obligations.')
    result['residual_obligations'].append(f['remaining'])
    result['namespace_sensitive_short_head'] = head in SENSITIVE
    if head in SENSITIVE:
        identities = identities or {}
        assert name in identities and identities[name]['expected_head'] == head, 'unreviewed namespace-sensitive result'
        result['source_identity_review'] = identities[name]
    result['syntactic_parametric_marker_present'] = bool(re.search(r'(?<![\w])(?:α|β|p\.Denote)(?![\w])',record['result_type_source']))
    result['external_target_definition_not_expanded'] = head == 'EVM.State'
    if head == 'Fold':
        assert name in folds, 'concrete Fold codomains need source review'
        result['concrete_fold_codomains'] = folds[name]
        result['residual_obligations'].append('Concrete codomains do not discharge fold equations, invariants or semantic consumer obligations.')
    return result

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--source-census',required=True,type=pathlib.Path)
    ap.add_argument('--output',required=True,type=pathlib.Path)
    args = ap.parse_args()
    out = args.output.resolve()
    if out.is_relative_to(ROOT):
        raise ValueError('H44: bulk evidence stays off git')
    source = json.loads(args.source_census.read_text())
    assert source['base'] == BASE
    catalog_path = RULES/'result-family-rules.json'
    alias_path = RULES/'alias-semantic-rules.json'
    catalog = json.loads(catalog_path.read_text())
    aliases = json.loads(alias_path.read_text())['aliases']
    families = family_index(catalog['families'])
    cache = {}
    def frozen(path):
        if path not in cache:
            cache[path] = subprocess.check_output(['git','show',BASE+':'+path],cwd=ROOT)
        return cache[path]
    evidence = []
    references = {}
    for subject,refs in (
            [(f['id'],f['evidence']) for f in catalog['families']] +
            [(n,a['target_evidence']) for n,a in aliases.items()] +
            [(n,a['evidence']) for n,a in catalog['reviewed_source_identities'].items()]):
        for ref in refs:
            references.setdefault((ref['path'],ref['line']),[]).append(subject)
    for (path,line),subjects in sorted(references.items()):
            ref = dict(path=path,line=line)
            data = frozen(path)
            lines = data.decode().splitlines()
            line = ref['line']
            assert 1 <= line <= len(lines)
            excerpt = '\n'.join(lines[max(0,line-2):min(len(lines),line+8)])
            evidence.append(dict(subjects=subjects,**ref,base=BASE,
                file_sha256=sha(data),excerpt=excerpt,excerpt_sha256=sha(excerpt.encode())))
    targeted = [r for r in source['additional_declaration_census'] if r['classification'].startswith(PENDING)]
    assert len(targeted) == 246
    assert sum(r['kind']=='abbrev' for r in targeted) == len(aliases) == 20
    for row in targeted:
        src = frozen(row['module']).decode()
        assert row['header'] in src and sha(row['header'].encode()) == row['header_sha256']
        row['source_semantic_refinement'] = classify_record(row,families,aliases,catalog['concrete_folds'],src,catalog['reviewed_source_identities'])
    assert len({r['source_id'] for r in targeted}) == 246
    summary = dict(targeted_records=246,source_families_reviewed=246,
        alias_rhs_expansions=20,inferred_string_definitions=4,
        declared_result_families=222,concrete_folds=7,
        family_counts=dict(collections.Counter(r['source_semantic_refinement']['family'] for r in targeted)),
        namespace_sensitive_short_heads=sum(r['source_semantic_refinement'].get('namespace_sensitive_short_head',False) for r in targeted),
        source_identity_reviews=15,
        nonexhaustive_syntactic_parametric_markers=sum(r['source_semantic_refinement'].get('syntactic_parametric_marker_present',False) for r in targeted),
        external_target_expansions_pending=sum(r['source_semantic_refinement'].get('external_target_definition_not_expanded',False) for r in targeted),
        historical_checked_originals=source['summary']['existing_checked_originals'],
        historical_uncovered_originals=source['summary']['uncovered_source_rows'],
        coverage_boundary='Historical source-census reference only; no checked status revalidation by this tool.',
        marker_boundary='Alpha/beta/p.Denote regex markers are nonexhaustive, not a census of all dependent payloads.',
        new_checked_witnesses=0,
        elaborated_identity_claim=False,proof_exclusions=0)
    output = dict(base=BASE,source_census_path=str(args.source_census.resolve()),
        source_census_sha256=sha(args.source_census.read_bytes()),
        authored_catalog_sha256=sha(catalog_path.read_bytes()),
        authored_alias_rules_sha256=sha(alias_path.read_bytes()),summary=summary,
        inherited_witness_status='Historical snapshot only; use the separate hash-bound audit_report gate for current checked status.',
        status='Source family review added; elaborated identities, intrinsic constraints and semantic obligations remain open.',
        theorem_premise_census=source['theorem_premise_census'],
        additional_declaration_census=source['additional_declaration_census'],
        source_evidence=evidence)
    out.mkdir(parents=True,exist_ok=True)
    data=(json.dumps(output,ensure_ascii=False,indent=2)+'\n').encode()
    (out/'semantic-results.json').write_bytes(data)
    (out/'SHA256SUMS').write_text(sha(data)+'  semantic-results.json\n')
    lines=['# H70 source result-family review','',
        f"Historical source snapshot: {summary['historical_checked_originals']} checked originals; {summary['historical_uncovered_originals']} uncovered. This tool revalidates neither count.",
        'Zero new checked witnesses; all residual obligations retained.',
        'All246 previous dependent/inferred/alias candidates receive source evidence. No proof exclusion or elaborated identity follows.','',
        '| Source declaration | Family | Residual boundary |','|---|---|---|']
    for row in targeted:
        ref=row['source_semantic_refinement']
        lines.append('| '+str(row['source_qualified_name'])+' | '+ref['family']+' | '+ref['residual_obligations'][-1].replace('|','/')+' |')
    (out/'semantic-summary.md').write_text('\n'.join(lines)+'\n')
    print(json.dumps(summary,sort_keys=True))

if __name__ == '__main__':
    main()
