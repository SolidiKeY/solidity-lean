#!/usr/bin/env python3
"""Lossless static triage of every frozen census row. Never verifies a premise.
Grouped binders and leading-forall source text are retained with offsets; unusual
syntax stays unresolved rather than being discarded. Output is off Git only.
"""
import argparse
import collections
import json
import pathlib
import re
import subprocess
import census

OPEN = {'(': ')', '{': '}', '[': ']'}
CLOSE = set(OPEN.values())
MARKERS = ['FiniteRun', 'Transport', 'Represented', 'PathSupported',
           'PathEndpoint', 'StateEndpoint', 'ReachedEndpoint']

def top_positions(code, wanted):
    stack=[]
    for pos, char in enumerate(code):
        if not stack and char in wanted: yield pos
        if char in OPEN: stack.append(OPEN[char])
        elif char in CLOSE:
            if not stack or stack.pop()!=char: raise ValueError('unbalanced delimiters')
    if stack: raise ValueError('unclosed delimiter')

def groups(raw, code):
    result=[]; pos=0
    while pos<len(code):
        if code[pos].isspace(): pos+=1; continue
        if code[pos] not in OPEN:
            return result, raw[pos:]
        start=pos; stack=[OPEN[code[pos]]]; pos+=1
        while stack and pos<len(code):
            c=code[pos]
            if c in OPEN: stack.append(OPEN[c])
            elif c in CLOSE:
                if stack.pop()!=c: raise ValueError('binder delimiter mismatch')
            pos+=1
        if stack: raise ValueError('unclosed binder')
        body=code[start+1:pos-1]
        colon=next(top_positions(body, ':'), None)
        result.append(dict(raw=raw[start:pos], start=start, end=pos,
                           delimiter=code[start],
                           names=(body[:colon].split() if colon is not None else []),
                           type_source=(raw[start+1+colon+1:pos-1].strip() if colon is not None else None)))
    return result, ''

def classify(signature):
    code=census.mask(signature)
    m=census.COMMAND.search(code)
    if m is None: raise ValueError('missing theorem command')
    tail=code[m.end():]; raw_tail=signature[m.end():]
    col=next(top_positions(tail, ':'), None)
    if col is None: raise ValueError('missing declaration type colon')
    binders, unresolved=groups(raw_tail[:col],tail[:col])
    result_source=raw_tail[col+1:]
    result_code=tail[col+1:]
    stripped=result_code.lstrip(); leading_forall=None
    if stripped.startswith('∀'):
        offset=len(result_code)-len(stripped)
        after=offset+1
        comma=next(top_positions(result_code[after:], ','),None)
        if comma is not None:
            leading_forall=result_source[after:after+comma]
    syntax_class=('declaration-binders' if binders else 'no-declaration-binders')
    if leading_forall is not None: syntax_class += '+leading-forall'
    if unresolved: syntax_class='unresolved-header'
    return dict(syntax_class=syntax_class, declaration_binders=binders,
                binder_offset_reference='signature suffix immediately after theorem/lemma name',
                unresolved_header=unresolved, leading_forall_source=leading_forall,
                result_source=result_source,
                arrow_count_in_result=result_code.count('→'),
                quantifier_count_in_result=result_code.count('∀'),
                surface_markers=[w for w in MARKERS if re.search(r'(?<![\w])'+w+r'(?![\w])', code)],
                marker_boundary='Occurrences anywhere in signature; not a premise/global/per-input classification')

def collect(root):
    inventory=census.collect(root)
    manual=json.loads((root/'tests/h62/item2/audit-v10-storage/candidate-bundles.json').read_text())
    manual_index={(r['path'],r['theorem'].rsplit('.',1)[1]):r for r in manual['bundles']}
    assert len(manual_index)==len(manual['bundles'])
    rows=[]; classes=collections.Counter(); markers=collections.Counter(); covered_manual=set()
    for d in inventory['declarations']:
        try: features=classify(d['signature'])
        except ValueError as error: features=dict(syntax_class='unresolved-syntax',error=str(error))
        classes[features['syntax_class']]+=1
        markers.update(features.get('surface_markers',[]))
        selected=manual_index.get((d['path'],d['source_name']))
        if selected: covered_manual.add((d['path'],d['source_name']))
        rows.append(dict(id=d['id'],path=d['path'],line=d['line'],source_name=d['source_name'],
                         owner=d['owner'],private=d['private'],signature=d['signature'],
                         signature_sha256=d['signature_sha256'],context_sha256=d['context_sha256'],
                         features=features,manual_classification=selected,
                         section_dependencies='unresolved; inspect frozen source context before semantic classification',
                         semantic_status='manual-source-analysis; Lean pending' if selected else 'unresolved',
                         witness_status='uncovered',counts_as_verified_witness=False))
    assert covered_manual==set(manual_index)
    assert len(rows)==len({r['id'] for r in rows})==inventory['counts']['declarations']
    return dict(schema=1,base=inventory['base'],
                boundary='Static syntax/markers for routing only. No semantic premise inference, interface exclusion, satisfiability, or proof coverage.',
                manual_plan_definitions=manual.get('planned_definitions',{}),
                counts=dict(rows=len(rows),syntax_classes=dict(sorted(classes.items())),
                            surface_marker_rows=dict(sorted(markers.items())),
                            manual_source_classifications=len(covered_manual),
                            verified_witnesses=0,uncovered=len(rows)),rows=rows)

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--output',type=pathlib.Path,required=True); a=ap.parse_args()
    root=pathlib.Path(subprocess.check_output(['git','rev-parse','--show-toplevel'],text=True).strip())
    output=a.output.resolve()
    if output==root or root in output.parents: ap.error('bulk output must be outside checkout')
    result=collect(root); output.mkdir(parents=True,exist_ok=True)
    (output/'surface-classification.json').write_text(json.dumps(result,ensure_ascii=False,indent=2)+'\n')
    print(json.dumps(result['counts'],sort_keys=True))

if __name__=='__main__': main()
