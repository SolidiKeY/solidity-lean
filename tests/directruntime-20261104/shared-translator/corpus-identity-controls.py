"""Fail-closed census classifier controls, not translator or semantic proofs."""
import importlib.util,json,sys
sys.dont_write_bytecode=True
from pathlib import Path
path=Path(__file__).with_name('corpus-inventory.py')
spec=importlib.util.spec_from_file_location('census',path);module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module)
def row(pointer,content='same',unit='/ast'):return {'pointer':pointer,'nodeSha256':content,'unitRoot':unit}
cases=[
 (None,{},'null'),(True,{1:[row('/one')]},'malformed'),('1',{},'malformed'),
 ([],{},'malformed'),(-18,{},'negative-reference-candidate'),(2**32-18,{},'unsigned-negative-candidate'),
 (7,{},'missing-id'),(7,{7:[row('/decl')]},'unique-node-id'),
 (7,{7:[row('/one'),row('/two','different')]},'ambiguous-id'),
 (7,{7:[row('/one'),row('/two')]},'ambiguous-id'),
 (7,{7:[row('/one',unit='/left'),row('/two',unit='/right')]},'equivalent-cross-root-candidates')]
for target,index,expected in cases:
 status,targets=module.resolve(target,index);assert status==expected
 assert targets==[r['pointer'] for r in index.get(target,[])] if type(target) is int else targets==[]
# Equal numeric IDs in separate compilation worlds never resolve across worlds.
assert module.resolve(7,{})[0]=='missing-id' and module.resolve(7,{7:[row('/other-world')]})[0]=='unique-node-id'
print(json.dumps({'status':'pass','classifierCases':len(cases),'worldIsolation':'indexes supplied per document; no cross-document lookup','boundary':'Structural census classification controls only;no source/name/type/overload correctness proof.'}))

case={'nodeType':'Literal','route':'expression','caseId':'literal-a'}
module.check_observation_identity(case,dict(case))
for key,bad in [('nodeType','Identifier'),('route','typeName'),('caseId','literal-b')]:
 mutated=dict(case);mutated[key]=bad
 try:module.check_observation_identity(case,mutated)
 except AssertionError:pass
 else:raise AssertionError('misattached observation accepted: '+key)
print(json.dumps({'observationIdentityControls':'three altered kind/route/case identities refused'}))
