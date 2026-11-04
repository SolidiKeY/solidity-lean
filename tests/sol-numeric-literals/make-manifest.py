#!/usr/bin/env python3
"""Explicit pin-recording step. Acceptance never calls this script."""
import difflib,json,pathlib
from packetlib import ROOT,FOLDER,BASE,PREFIX,CONSTRUCTOR_CONTROLS,REQUIRED_THEOREMS,case_families,controls,normalized_inventory,sha,source_snapshot
modules=source_snapshot()
actual=normalized_inventory(json.loads((FOLDER/'evidence/kernel-inventory.actual.json').read_text()))
(FOLDER/'kernel-inventory.json').write_text(json.dumps(actual,indent=2)+'\n')
pins=json.loads((FOLDER/'source-pins.json').read_text())
for path in ['Solidity/Frontend/Checked/Tables.lean','Solidity/Keccak.lean']:pins['sha256'][path]=sha(ROOT/path)
(FOLDER/'source-pins.json').write_text(json.dumps(pins,indent=2)+'\n')
root=ROOT/'Solidity.lean';old=root.read_text();lines=old.splitlines()
header=[]
for line in lines:
 if line.startswith('import '):break
 header.append(line)
imports={line.split()[1] for line in lines if line.startswith('import ')}|{m['name'] for m in modules}
new='\n'.join(header+[f'import {name}' for name in sorted(imports)])+'\n'
patch=''.join(difflib.unified_diff(old.splitlines(True),new.splitlines(True),fromfile='a/Solidity.lean',tofile='b/Solidity.lean'))
(FOLDER/'registration.patch').write_text(patch)
rows=[f"| `{m['path'][len('Solidity/'):]}` | Numeric literal proof lane: {m['name'].split('.')[-1]}; source, declarations and trust inventory pinned in tests/sol-numeric-literals. |" for m in modules]
map_path=ROOT/'docs/module-map/frontend.md';map_old=map_path.read_text();map_new=map_old.rstrip()+'\n'+'\n'.join(row for row in rows if row not in map_old)+'\n'
map_patch=''.join(difflib.unified_diff(map_old.splitlines(True),map_new.splitlines(True),fromfile='a/docs/module-map/frontend.md',tofile='b/docs/module-map/frontend.md'))
(FOLDER/'registration.module-map.patch').write_text(map_patch)
registration=dict(desired_module_map_sha256=__import__('hashlib').sha256(map_new.encode()).hexdigest(),module_map_patch_sha256=sha(FOLDER/'registration.module-map.patch'),base=BASE,owner='coordinator at integration (H21 freeze)',modules=[m['name'] for m in modules],generated_root='Solidity.lean',current_root_sha256=sha(root),desired_root_sha256=__import__('hashlib').sha256(new.encode()).hexdigest(),root_patch_sha256=sha(FOLDER/'registration.patch'),module_map_file='docs/module-map/frontend.md',module_map_rows=rows,status='pending coordinator registration; no shared root or module map edited')
(FOLDER/'registration.json').write_text(json.dumps(registration,indent=2)+'\n')
scripts=['scripts/check-sol-numeric-literals.py']+['tests/sol-numeric-literals/'+p for p in ['packetlib.py','make-manifest.py','generate-wordtable.py','generate-fixtures.py','run-fixtures.mjs','differential.py','runtime/check.py','runtime/timed.py','runtime/bin/lake','runtime/lakefile.toml']]
manifest=dict(base=BASE,modules=modules,scanner_controls=controls(),case_families=case_families(),constructor_controls={PREFIX+k:PREFIX+v for k,v in CONSTRUCTOR_CONTROLS.items()},required_theorems=[PREFIX+n for n in REQUIRED_THEOREMS],kernel_inventory_sha256=sha(FOLDER/'kernel-inventory.json'),gate_scripts={p:sha(ROOT/p) for p in scripts},audit_boundary='Every imported declaration in owned proof modules, including compiler-generated helpers; Audit has no persistent declarations (run_cmd uses withoutModifyingEnv).',generated_partial_boundary='underscoreOk._unsafe_rec is a Lean-generated partial implementation helper, isUnsafe=false and no axioms; the kernel definition and proofs remain safe.')
(FOLDER/'acceptance.json').write_text(json.dumps(manifest,indent=2)+'\n')
print(f'pinned {len(modules)} modules, {len(actual)} kernel declarations, {len(CONSTRUCTOR_CONTROLS)} constructor controls, {len(controls())} scanner controls')
