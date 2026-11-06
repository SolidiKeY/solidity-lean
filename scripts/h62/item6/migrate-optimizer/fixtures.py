#!/usr/bin/env python3
"""Generate isolated backfill from exact original blocks, never a migration substitute.
Three Scoped-dependent declarations remain untested by this isolated fixture.
"""
from pathlib import Path
import hashlib, json, sys
root=Path(__file__).resolve().parents[4]
d=root/'tests/h62/item6/migrate-optimizer'
def emit(name, text):
 p=d/name
 if '--check' in sys.argv: assert p.read_text()==text, 'stale generated fixture '+name
 else: p.write_text(text)
base=root/'Solidity/Optimizer'
source={p.name:p.read_text() for p in sorted(base.glob('*.lean'))}
pass_body=source['Pass.lean'].split('namespace Solidity.Optimizer',1)[1]
start=pass_body.index('namespace Lowering'); end=pass_body.index('namespace Yul',start)
pass_body='namespace Solidity.Optimizer'+pass_body[:start]+pass_body[end:]
laws=source['Laws.lean'].split('\n',1)[1]
roadmap='\n'.join(source['RoadmapComposition.lean'].splitlines()[2:])
controls='\n'.join(source['Controls.lean'].splitlines()[2:])
start=controls.index('/-- An inhabited intrinsic lowering context')
end=controls.index('/-- Composition with two guarded proposals',start)
controls=controls[:start]+controls[end:]
interfaces=(d/'Interfaces.lean').read_text().split('open Lean Elab Command in',1)[1]
acceptance=(d/'Acceptance.lean').read_text().split('\n',1)[1]
text='import Lean\nimport Solidity.Yul.Syntax\nimport Solidity.Roadmap.Contracts\n\n'+pass_body+'\n'+laws+'\n'+roadmap+'\n'+controls+'\n'+acceptance+'\nopen Lean Elab Command in'+interfaces
emit('Isolated.lean',text)
manifest={'kind':'exact-source isolated backfill, not full module validation','covered_explicit_declarations':32,'pending_scoped_declarations':['Solidity.Optimizer.Lowering.Pass','Solidity.Optimizer.Controls.loweringWitness','Solidity.Optimizer.Controls.lowering_identity'],'sources':{k:hashlib.sha256(v.encode()).hexdigest() for k,v in source.items()},'generated_sha256':hashlib.sha256(text.encode()).hexdigest()}
emit('isolated-manifest.json',json.dumps(manifest,indent=2)+'\n')

# Dependency-free fallback: preserve the exact 27 generic declarations.
# Intrinsic aliases/witnesses and Roadmap adapters remain pending owner imports.
generic_pass=source['Pass.lean'].split('namespace Solidity.Optimizer',1)[1]
generic_pass='namespace Solidity.Optimizer'+generic_pass.split('namespace Lowering',1)[0]+'end Solidity.Optimizer\n'
generic_controls='\n'.join(source['Controls.lean'].splitlines()[2:])
a=generic_controls.index('/-- Nonempty intrinsic Yul syntax')
b=generic_controls.index('/-- Composition with two guarded proposals',a)
generic_controls=generic_controls[:a]+generic_controls[b:]
generic_controls=generic_controls.replace('#print axioms asRoadmapPass\n','').replace('#print axioms beforeCompilation\n','')
a=acceptance.index('-- Intrinsic control')
b=acceptance.index('-- The pipeline proof',a)
generic_acceptance=acceptance[:a]+acceptance[b:]
generic_interfaces=interfaces.replace('#print axioms Solidity.Optimizer.beforeCompilation\n','')
generic='import Lean\n'+generic_pass+'\n'+laws+'\n'+generic_controls+'\n'+generic_acceptance+'\nopen Lean Elab Command in'+generic_interfaces
emit('Generic.lean',generic)
emit('generic-manifest.json',json.dumps({'kind':'dependency-free exact-source backfill only','covered_explicit_declarations':27,'pending_explicit_declarations':8,'sources':manifest['sources'],'generated_sha256':hashlib.sha256(generic.encode()).hexdigest()},indent=2)+'\n')
