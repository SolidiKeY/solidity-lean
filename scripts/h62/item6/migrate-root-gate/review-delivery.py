#!/usr/bin/env python3
"""H76 receipt/content review only. No Lean, patch application or STOP waiver.

The fullpatch+manifest alternative proves delivered content against declared
source hashes/base/head. It cannot prove the missing bundle's Git ancestry.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[4]
BASE = 'c6f550e281a7e5affa9a99bc2cdaed556dec00e4'
HEAD = '2a18afcdba00a85645b0b3079704f78ffcd78860'
RECEIPTS = {
 '8590f8229c-HANDOFF.md': ('82212df8f602f036266bf4b2eb0343eac0209432352e9104a5c353f6efe62e7b',13297),
 'a939d5a056-HANDOFF.md': ('3113ce744565374b686b6565bafb902edfdce3b2b5246e4f3169884e57ef0914',26051),
 'ce4e8a1b04-HANDOFF.json': ('7e41dd8cd41cde5523c5b82549e1e3d3cf030a505324139f1a88d472d86ff729',13590),
 'fc3898d847-HANDOFF.md': ('d341d3f3eff0cc013fa1fb5710ee08b764f018d2740b098c3d61edddc2062cf3',10997),
 'bdda07e705-dependency-report.json': ('6c43de081d3cac929b99871271acd94c4563014db30645e80a33f8448b38b006',13298),
 '0852bca66d-output.log': ('fa10c29170e4bd3abf0910da51d0e935ea82198dcb111bda8e5de1e7ba81a55c',11536),
 '28038e1c7a73-dependency-report.json': ('31db3233b95a905ab0e32eab72e1a84478bf7784684ef9c4edd54e65cddd3fba',16907),
 '300764ecfb-producer-overlay.json': ('2ae88b9e70a54731ec61bc454abdd9b5204895c95b9ea5e25018d9b12bd4a910',3488),
 '079ced0d71-result.json': ('241cef35fa4215a961d29a4948c73284f3075854df29178ffcd053a049c4be22',11638),
 '3f6f954038-hash-owner-overlay.patch': ('b07f36b08faf0244fd350a54c9d72e3f5c333a566726b1e7f420aa21b727ffec',9298),
}


def require(value, message):
    if not value:
        raise ValueError(message)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def apply_in_memory(patch, originals):
    """Strictly consume unified hunk contexts/counts; never write sources."""
    lines = patch.splitlines(keepends=True)
    i = 0
    images = {}
    while i < len(lines):
        match = re.fullmatch(r'diff --git a/(\S+) b/(\S+)\n', lines[i])
        require(match is not None and match[1] == match[2], 'unsupported file header')
        name = match[1]
        require(name in originals and name not in images, 'unexpected/duplicate patch path')
        original = originals[name].decode().splitlines(keepends=True)
        output, cursor = [], 0
        i += 1
        while i < len(lines) and not lines[i].startswith('@@ '):
            require(lines[i].startswith(('index ', '--- a/', '+++ b/')), 'unsupported patch metadata')
            i += 1
        require(i < len(lines), 'missing hunk')
        while i < len(lines) and lines[i].startswith('@@ '):
            hunk = re.match(r'@@ -(\d+)(?:,(\d+))? \+(\d+)(?:,(\d+))? @@', lines[i])
            require(hunk is not None, 'bad hunk header')
            old_start, old_count, new_start, new_count = [int(v) if v is not None else 1 for v in hunk.groups()]
            require(cursor <= old_start-1 <= len(original), 'overlap/out-of-bounds hunk')
            output.extend(original[cursor:old_start-1]);cursor = old_start-1
            require(len(output) == new_start-1, 'new hunk offset mismatch')
            used_old = used_new = 0
            i += 1
            while used_old < old_count or used_new < new_count:
                require(i < len(lines), 'truncated hunk')
                line = lines[i];i += 1
                require(line[:1] in [' ', '+', '-'], 'unsupported hunk line')
                if line[0] in ' -':
                    require(cursor < len(original) and original[cursor] == line[1:], 'base context mismatch')
                    cursor += 1;used_old += 1
                if line[0] in ' +':
                    output.append(line[1:]);used_new += 1
                require(used_old <= old_count and used_new <= new_count, 'hunk count overflow')
        output.extend(original[cursor:]);images[name] = ''.join(output).encode()
    require(set(images) == set(originals), 'missing patch file')
    return images


def check_patch_at_base(patch):
    """Check applicability against BASE using a disposable index, never the real index."""
    with tempfile.TemporaryDirectory(prefix='h62-root-patch-review-') as directory:
        env = dict(os.environ, GIT_INDEX_FILE=str(Path(directory)/'index'))
        subprocess.run(['git', 'read-tree', BASE], cwd=ROOT, env=env, check=True,
                       capture_output=True)
        return subprocess.run(['git', 'apply', '--cached', '--check', '--whitespace=error', '-'],
                              cwd=ROOT, env=env, input=patch, capture_output=True)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('inputs', type=Path)
    parser.add_argument('output', type=Path)
    args = parser.parse_args()
    args.inputs = args.inputs.resolve(strict=True)
    data, receipts = {}, {}
    for name, (expected, size) in RECEIPTS.items():
        raw = (args.inputs/name).read_bytes()
        require(len(raw) == size and sha(raw) == expected, 'receipt mismatch: '+name)
        data[name] = raw
        receipts[name] = dict(sha256=expected, bytes=size, verified=True)
    manifest = json.loads(data['300764ecfb-producer-overlay.json'])
    result = json.loads(data['079ced0d71-result.json'])
    require(manifest['base'] == result['base'] == BASE, 'Hash base mismatch')
    require(manifest['head'] == result['head'] == HEAD, 'Hash declared head mismatch')
    patch_sha = sha(data['3f6f954038-hash-owner-overlay.patch'])
    require(manifest['patches']['hash-owner-overlay.patch']['sha256'] == patch_sha, 'manifest patch binding')
    require(result['artifact_sha256']['hash-owner-overlay.patch'] == patch_sha, 'result patch binding')
    require(result['artifact_sha256']['producer-overlay.json'] == sha(data['300764ecfb-producer-overlay.json']), 'result manifest binding')
    specs = {entry['path']: entry for entry in manifest['files']}
    require(set(specs) == {'Solidity/Hash/Adaptive.lean','Solidity/Hash/CollisionBound.lean'}, 'Hash scope differs')
    originals = {name: subprocess.check_output(['git','show',BASE+':'+name],cwd=ROOT) for name in specs}
    current = {name: (ROOT/name).read_bytes() for name in specs}
    for name, raw in originals.items():
        require(sha(raw) == specs[name]['base_sha256'], 'Hash base source hash')
    images = apply_in_memory(data['3f6f954038-hash-owner-overlay.patch'].decode(), originals)
    for name, raw in images.items():
        require(sha(raw) == specs[name]['head_sha256'], 'Hash head source hash')
    for name in specs:
        require(current[name] in (originals[name], images[name]), 'current Hash differs from pinned or reviewed bytes')
    check = check_patch_at_base(data['3f6f954038-hash-owner-overlay.patch'])
    require(check.returncode == 0, 'Hash read-only git check failed')
    context = data['0852bca66d-output.log'].decode()
    axioms = {name: [v.strip() for v in values.split(',')] for name, values in
              re.findall(r"^'([^']+)' depends on axioms: \[([^\]]*)\]", context, re.MULTILINE)}
    require(len(axioms) == 5 and all('Classical.choice' in values for values in axioms.values()), 'Context log unexpected')
    storage = json.loads(data['bdda07e705-dependency-report.json'])
    root_hashes = {}
    for entry in storage['external_dependencies']:
        if 'solidity-h62-6-20261106/migrate-root-gate' in entry['owner']:
            name = entry['module'].replace('.','/')+'.lean'
            actual = sha((ROOT/name).read_bytes())
            require(actual == entry['sha256'], 'Storage root source binding mismatch')
            root_hashes[name] = actual
    roadmap = json.loads(data['ce4e8a1b04-HANDOFF.json'])
    precomp = json.loads(re.search(r'```json\s*\n(.*?)\n```',data['a939d5a056-HANDOFF.md'].decode(),re.S).group(1))
    require(roadmap['report']['base'] == precomp['base'] == BASE, 'producer base mismatch')
    counter = json.loads(data['28038e1c7a73-dependency-report.json'])
    require(counter['base'] == BASE, 'Counterexamples base mismatch')
    for name, raw in originals.items():
        require((ROOT/name).read_bytes() == current[name], 'Hash source changed during static review')
    report = dict(status='static-review-only; holds retained', receipts=receipts,
        delivery_request='Q-H70-STAGED resolved: all seven plus Hash fullpatch/manifest/result delivered',
        hash_overlay=dict(base=BASE,declared_head=HEAD,files=specs,computed_postimage_sha256={n:sha(v) for n,v in images.items()},
                          fullpatch_manifest_result_bindings=True,git_apply_check_exit=0,
                          applicability_base=BASE,applicability_uses_disposable_index=True,
                          current_source_sha256={n:sha(v) for n,v in current.items()},
                          bundle='not delivered; coordinator searched receipts; fullpatch+manifest alternative satisfied',
                          reported_bundle_sha256=result['artifact_sha256']['migration.bundle'],git_ancestry_verified=False,
                          elaboration_replayed=False,patch_applied=False),
        context=dict(axioms=axioms,expr_type_blocks=re.findall(r'^FROZEN_TYPE (\S+)',context,re.MULTILINE),
                     Context_Cold_mentions=context.count('Lean.Core.Context.Cold'),exact_leaf='unresolved'),
        roadmap_owned_api_request=roadmap['owned_api_request'],storage_root_source_bindings=root_hashes,
        counterexamples_assigned=counter['assigned_modules'],precompiles_changed_modules=precomp['modules_changed'],
        holds_waived=False,Lean_started=False,production_source_changed=False,
        boundary='Delivered handoffs/logs and content bindings reviewed; underlying referenced traces/driver provenance not thereby delivered; no ancestry/proof/performance acceptance.')
    args.output.mkdir()
    (args.output/'review.json').write_text(json.dumps(report,indent=2,sort_keys=True)+'\n')
    print(args.output/'review.json')


if __name__ == '__main__':
    main()
