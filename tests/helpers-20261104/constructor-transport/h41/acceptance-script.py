import hashlib, json, pathlib, re, subprocess
root = pathlib.Path('/workspace/solidity-lean')
owned = root/'tests/helpers-20261104/constructor-transport'
packet = root/'Solidity/Lowering/V08/HelperPackets/ConstructorTransport'
ns = 'Solidity.Lowering.V08.HelperPackets.ConstructorTransport.'
modules = []
theorems = set()
diags = {'Source':'source-mcp-attempt5.log','Target':'target-mcp-attempt2.log','Producer':'producer-mcp-attempt3.log','Controls':'final-gates/controls-mcp.log'}
for p in sorted(packet.glob('*.lean')):
 text = p.read_text()
 code = re.sub(r'/\-.*?\-/', '', text, flags=re.S)
 assert not re.search(r'\b(sorry|admit|axiom|unsafe|opaque|maxHeartbeats)\b', code)
 declarations = [{'kind':k,'name':n} for k,n in re.findall(r'^(def|abbrev|structure|theorem) (\w+)', code, re.M)]
 theorems.update(ns+x['name'] for x in declarations if x['kind']=='theorem')
 assert 'diag: 0 errors' in (owned/diags[p.stem]).read_text()
 modules.append({'module':str(p.relative_to(root)),'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),
 'declarations':declarations,'kernel_command':'lake -f tests/helpers-20261104/constructor-transport/serial.toml build Solidity.Lowering.V08.HelperPackets.ConstructorTransport.Controls',
 'kernel_log':'final-gates/packet-build.log','mcp_log':diags[p.stem], 'status':'pass'})
pins = set(re.findall(r'^#print axioms (\S+)', (owned/'AxiomPins.lean').read_text(), re.M))
assert pins == theorems, (pins-theorems,theorems-pins)
assert len(theorems)==28
assert 'Build completed successfully' in (owned/'final-gates/packet-build.log').read_text()
assert 'error:' not in (owned/'final-gates/axiom-pins.log').read_text()
assert 'RUNTIME_GATE_PASS' in (owned/'final-gates/runtime.log').read_text()
assert 'c8649f8d57f81b3244c7d2dd662efc0620d1ae296f623b347a2c616a6cfd11d8' in (owned/'final-gates/compiler.log').read_text()
allowed=('Solidity/Lowering/V08/HelperPackets/ConstructorTransport/', 'tests/helpers-20261104/constructor-transport/', 'docs/feature-work/helper-constructor-transport-20261104.md')
changed = set(subprocess.check_output(['git','diff','--name-only','6f3eedf0788ee1f8a3bcf230558c712ecdca04d5'],text=True,cwd=root).splitlines())
changed.update(subprocess.check_output(['git','ls-files','--others','--exclude-standard'],text=True,cwd=root).splitlines())
assert all(x.startswith(allowed) for x in changed), changed
result={'packet_checks':'pass','assignment_completion':'pending_coordinator_merge_validation',
 'delivery_status':'coordinator-pending',
 'decision_receipt':'h41/coordinator-receipt.json',
 'theorem_count':len(theorems),'modules':modules,'axiom_pins':'AxiomPins.lean',
 'coverage': {'positive':'source_actual,target_body_actual,creation_actual,complete_transport; arbitrary admitted uint256 and bytes, both pipelines',
 'producer':'concrete_ssNew_body arbitrary after; creation_from_inputs conditional on unchanged published external inputs',
 'static':'source_static,target_static','timeout':'source_timeout horizon0',
 'wrong_order':'wrong_order_actual both pipelines + wrong_order_counterexample n!=7; boundary_seven equality',
 'boundaries':'boundary_zero,boundary_max,boundary_seven,nondefault_actual,nondefault_capture'},
 'external_boundary':'Pinned solc compilation and slots only. No EVM execution, compiler-correctness theorem, automatic Source default initialization or general new/try-new claim.',
 'full_gate':'Historical worker run-lean attempt failed at four unregistered helper imports; H41/QREG decision assigns full validation to coordinator merge, pending and not passed. Shared roots remain read-only.'}
(owned/'acceptance.json').write_text(json.dumps(result,indent=2)+'\n')
print('PACKET_ACCEPTANCE_PASS: 4 modules, 28 theorems, exact axiom pins, all declarations inventoried; full validation pending coordinator merge per H41/QREG; delivery coordinator-pending')
