"""Generate development theorem statements from the exact fixture source bodies."""
import json,pathlib,re
root=pathlib.Path(__file__).resolve().parent
rows=[r for r in json.loads((root/'manifest.json').read_text())['cases'] if not r['viaIR']]
s='''import KernelControls
/-! Exact fixture bodies in the existing intrinsic calculus. These kernel
controls are development validation, not native/browser source acceptance. -/
namespace Solidity.Frontend.ExecutableAst.Memory.KernelMatrix
def StoredContract : Contract := { vars := [("stored", .array (.prim .int))] }
def MappingContract : Contract := { vars := [("unused", .mapping .uint (.prim .int))] }
'''
for r in rows:
    source=(root/r['source']).read_text()
    body=re.search(r'function identity\(\) public .*?\{ (.*) \} \}',source,re.S).group(1)
    contract='StoredContract' if r['id'] in ['storageCopy','storageAlias','copyAfterPush'] else 'MappingContract' if r['id']=='mappingRoot' else 'KernelControls.EmptyContract'
    name=r['id']+'_'+r['modality']
    modal=f'[ {body} ]' if r['modality']=='box' else f'⟨ {body} ⟩'
    s+=f'\nnamespace {name}\nlocal instance : InContract := ⟨{contract}⟩\ntheorem checked : '+('' if r['requiredProven'] else '¬ (')+f'⊨ᶠ dl!{{ {modal} true }}'+('' if r['requiredProven'] else ')')+' := '
    if r['requiredProven']:
        s+='by\n  apply Proves.fmlValid (R := .all)\n  sol_prove\n'
    else:
        law='afterRunTR_not_panic' if r['modelHalt']=='panic' else 'afterRunTR_diamond_fail'
        s+=f'\n  fun h => Modality.{law} (h (State.init _)) (by decide +kernel)\n'
    s+=f'#print axioms checked\nend {name}\n'
s+='end Solidity.Frontend.ExecutableAst.Memory.KernelMatrix\n'
s='\n'.join(line.rstrip() for line in s.splitlines())+'\n'
(root/'KernelMatrix.lean').write_text(s)
