#!/usr/bin/env python3
"""Explicit pin-recording step. Acceptance never calls this script."""
import difflib,json,pathlib,runpy
from packetlib import ROOT,FOLDER,BASE,ADOPTED_MASTER,PREFIX,CONSTRUCTOR_CONTROLS,REQUIRED_THEOREMS,case_families,controls,normalized_inventory,sha,source_snapshot
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
map_path=ROOT/'docs/module-map/frontend.md';map_old=map_path.read_text()
# The shared file must match the exact joint proposal:33 numeric rows plus
# the separately authorized Constants.Controls row. Existing rows are retained.
proposal,_=runpy.run_path(str(ROOT/'tests/primitive-packets-1105/Constants/registration-plan.py'))['collect']()
missing_rows=[r['row'] for r in proposal['missing_rows']]
map_new=map_old.rstrip()+'\n'+'\n'.join(missing_rows)+'\n' if missing_rows else map_old
map_patch=''.join(difflib.unified_diff(map_old.splitlines(True),map_new.splitlines(True),fromfile='a/docs/module-map/frontend.md',tofile='b/docs/module-map/frontend.md'))
(FOLDER/'registration.module-map.patch').write_text(map_patch)
registration=dict(adopted_master=ADOPTED_MASTER,missing_root_imports=[m['name'] for m in modules if 'import '+m['name']+'\n' not in old],module_map_rows_to_add=missing_rows,desired_module_map_sha256=__import__('hashlib').sha256(map_new.encode()).hexdigest(),module_map_patch_sha256=sha(FOLDER/'registration.module-map.patch'),base=BASE,owner='coordinator at integration (H21 freeze)',modules=[m['name'] for m in modules],generated_root='Solidity.lean',current_root_sha256=sha(root),desired_root_sha256=__import__('hashlib').sha256(new.encode()).hexdigest(),root_patch_sha256=sha(FOLDER/'registration.patch'),module_map_file='docs/module-map/frontend.md',module_map_rows=rows,status='pending coordinator registration; no shared root or module map edited')
(FOLDER/'registration.json').write_text(json.dumps(registration,indent=2)+'\n')
scripts=['scripts/check-sol-numeric-literals.py','tests/primitive-packets-1105/Constants/registration-plan.py','tests/primitive-packets-1105/Constants/validate-fresh.py','tests/primitive-packets-1105/Constants/check.py','tests/primitive-packets-1105/Constants/manifest.json']+['tests/sol-numeric-literals/'+p for p in ['packetlib.py','make-manifest.py','adoption.json','test-adoption.py','generate-wordtable.py','generate-fixtures.py','run-fixtures.mjs','differential.py','runtime/check.py','runtime/test-check.py','runtime/timed.py','runtime/bin/lake','runtime/lakefile.toml','h35/validate-axioms.py','h35/prepare-owned-cache.py','h35/PrintAxioms.lean','h35/PrintAllAxioms.lean','h35/expected.json','h35/test-h41.py']]
manifest=dict(base=BASE,adopted_master=ADOPTED_MASTER,modules=modules,scanner_controls=controls(),case_families=case_families(),constructor_controls={PREFIX+k:PREFIX+v for k,v in CONSTRUCTOR_CONTROLS.items()},required_theorems=[PREFIX+n for n in REQUIRED_THEOREMS],kernel_inventory_sha256=sha(FOLDER/'kernel-inventory.json'),gate_scripts={p:sha(ROOT/p) for p in scripts},audit_boundary='Every imported declaration in owned proof modules, including compiler-generated helpers; Audit has no persistent declarations (run_cmd uses withoutModifyingEnv).',generated_partial_boundary='underscoreOk._unsafe_rec is a Lean-generated partial implementation helper, isUnsafe=false and no axioms; the kernel definition and proofs remain safe.')
(FOLDER/'acceptance.json').write_text(json.dumps(manifest,indent=2)+'\n')
print(f'pinned {len(modules)} modules, {len(actual)} kernel declarations, {len(CONSTRUCTOR_CONTROLS)} constructor controls, {len(controls())} scanner controls')
