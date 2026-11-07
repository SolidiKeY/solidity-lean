#!/usr/bin/env python3
"""Static review of coordinator-relayed numbers and the inline Hash diff.

Never invokes Lean, applies a patch, changes source, or disposes a STOP.
The external input is an explicitly labelled projection of the user payload.
Canonical patch reconstruction is checked against supplied blob prefixes;
this is not a producer-commit ancestry or elaboration certificate.
"""
import argparse
import difflib
import hashlib
import json
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parents[4]
BASE = 'c6f550e281a7e5affa9a99bc2cdaed556dec00e4'


def require(condition, message):
    if not condition:
        raise ValueError(message)


def pct(old, new):
    require(old > 0, 'nonpositive comparison denominator')
    return (new / old - 1) * 100


def blob(data):
    return hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()


def replace_once(text, old, new):
    require(text.count(old) == 1, 'inline patch anchor is not unique: '+old)
    return text.replace(old, new, 1)


def hash_overlay():
    specs = [
        ('Solidity/Hash/Adaptive.lean', 'cb5d5a1c6', '20087c3f9'),
        ('Solidity/Hash/CollisionBound.lean', 'b54c93a5b', '092971eda'),
    ]
    files = []
    patch = ''
    for name, old_prefix, new_prefix in specs:
        original = subprocess.check_output(['git', 'show', BASE+':'+name], cwd=ROOT)
        require(blob(original).startswith(old_prefix), 'frozen base blob mismatch')
        require((ROOT/name).read_bytes() == original, 'unexpected live owner source difference')
        text = original.decode()
        migrated = text.replace('if_pos', 'ite_eq_left').replace('if_neg', 'ite_eq_right')
        if name.endswith('Adaptive.lean'):
            for predicate, witness in [('eagerCollides, eagerQueries', 'CollisionFree.nil'),
                                       ('eagerRegionsFail, eagerQueries', 'RegionsDisjoint.nil')]:
                migrated = replace_once(migrated,
                    '      simp only ['+predicate+', decide_eq_true_eq, Classical.not_not]\n'
                    '      exact '+witness,
                    '      simp only ['+predicate+']\n'
                    '      exact fun h => (of_decide_eq_true h) '+witness)
        else:
            migrated = migrated.replace('if_true', 'ite_true')
            migrated = replace_once(migrated,
                '      congr 1\n    rw [hsplit, List.length_cons]',
                '      simp only [List.contains_cons]\n    rw [hsplit, List.length_cons]')
            for predicate, variable in [('Near', 'b'), ('Covers', 'r')]:
                migrated = replace_once(migrated,
                    '    simp only [decide_eq_true_eq, '+predicate+'] at hn',
                    "    have hn' : "+predicate+' N L a '+variable+" := of_decide_eq_true hn\n"
                    "    unfold "+predicate+" at hn'")
        after = migrated.encode()
        require(blob(after).startswith(new_prefix), 'reconstruction differs from supplied postimage '+name)
        headers = lambda source: re.findall(r'^[ \t]*(?:@\[[^\n]*?\]\s*)*(?:(?:private|protected|noncomputable)[ \t]+)*theorem\s+[^\s(]+[\s\S]*?:=', source, re.MULTILINE)
        require(headers(text) == headers(migrated), 'lexical theorem header changed')
        require((ROOT/name).read_bytes() == original, 'live source changed during static review')
        patch += 'diff --git a/'+name+' b/'+name+'\nindex '+blob(original)+'..'+blob(after)+' 100644\n'
        patch += ''.join(difflib.unified_diff(text.splitlines(True), migrated.splitlines(True),
                                             fromfile='a/'+name, tofile='b/'+name))
        files.append(dict(path=name, base_blob=blob(original), reconstructed_blob=blob(after),
                          source_sha256=hashlib.sha256(original).hexdigest(),
                          reconstructed_sha256=hashlib.sha256(after).hexdigest(),
                          lexical_theorem_headers_unchanged=len(headers(text))))
    check = subprocess.run(['git', 'apply', '--check', '--whitespace=error-all', '-'],
                           cwd=ROOT, input=patch.encode(), capture_output=True)
    require(check.returncode == 0, 'read-only patch applicability failed: '+check.stderr.decode())
    return files, patch


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('input', type=Path)
    parser.add_argument('output', type=Path)
    args = parser.parse_args()
    incoming = json.loads(args.input.read_text())
    require(incoming['base'] == BASE, 'wrong assignment base')
    generic = incoming['optimizer']['generic']
    old, new = generic['old'], generic['new']
    require(old['exit'] == new['exit'] == 0, 'failed fixture runs are not comparable')
    changes = {key: pct(old[key], new[key]) for key in
               ['wall_seconds', 'kernel_wall_seconds', 'sampled_group_rss_bytes', 'maximum_child_rss_kib']}
    for key, expected in generic['reported_percent'].items():
        require(abs(changes[key]-expected) < 1e-8, 'reported arithmetic differs: '+key)
    prefix = []
    for item in incoming['theory']['modules']:
        prefix.append(dict(module=item['module'],
                           wall_percent=pct(item['old_wall_s'], item['new_wall_s']),
                           sampled_rss_percent=pct(item['old_rss_bytes_sampled'], item['new_rss_bytes_sampled'])))
    closure = incoming['optimizer']['reviewed_closure']
    closure_ok = closure['old']['exit'] == closure['new']['exit'] == 0
    old_axioms = set(incoming['context_axiom_excerpts']['old'])
    new_axioms = set(incoming['context_axiom_excerpts']['new'])
    files, patch = hash_overlay()
    result = dict(
        status='static-review-only; PERFORMANCE-HOLD retained', base=BASE,
        input_sha256=hashlib.sha256(args.input.read_bytes()).hexdigest(),
        provenance=incoming['provenance'],
        optimizer=dict(generic_percent=changes,
                       outer_minus_kernel_seconds=dict(old=old['wall_seconds']-old['kernel_wall_seconds'],
                                                        new=new['wall_seconds']-new['kernel_wall_seconds']),
                       closure_comparison=dict(comparable=closure_ok, old_exit=closure['old']['exit'],
                                               new_exit=closure['new']['exit']),
                       reported_resource_profile=incoming['optimizer']['resource_profile'],
                       reported_image=incoming['optimizer']['image'],
                       reported_archive_sha256=incoming['optimizer']['archive_sha256'],
                       full_migration_timing_delta=None,
                       boundary='one short successful generic fixture pair; fixture/driver bytes and commands absent'),
        theory=dict(prefix=prefix, boundary=incoming['theory']['boundary']),
        context_axioms=dict(declarations=incoming['context_axiom_excerpts']['declarations'],
                            added=sorted(new_axioms-old_axioms), removed=sorted(old_axioms-new_axioms),
                            boundary='inline axiom lines only; full new staged log and exact leaf pending'),
        hash_overlay=dict(producer_head='2a18afcdba00a85645b0b3079704f78ffcd78860', files=files,
                          git_apply_check_exit=0, canonical_patch_sha256=hashlib.sha256(patch.encode()).hexdigest(),
                          original_files_changed=False, producer_commit_binding='pending bundle/head manifest',
                          proof_boundary='lexical headers/base/postimage prefixes only; no Lean or semantic equivalence proof'),
        accounting_boundary='kernel_usage is the producer field label, not an established kernel-only or CPU-time measurement; outer minus kernel is arithmetic, not causal attribution',
        validation_restarted=False, patches_applied=False, trust_or_pin_changed=False)
    args.output.mkdir()
    (args.output/'hash-inline-reconstructed.patch').write_text(patch)
    (args.output/'review.json').write_text(json.dumps(result, indent=2, sort_keys=True)+'\n')
    print(args.output/'review.json')


if __name__ == '__main__':
    main()
