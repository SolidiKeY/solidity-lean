"""Observe compiler fixture subvariants, without inferring support or proofs."""
from pathlib import Path
import json,hashlib,collections
root=Path(__file__).resolve().parents[3];owned=Path(__file__).resolve().parent
bulk=owned/'artifacts/h68-bulk'
variants={}
def tstr(n):return n.get('typeDescriptions',{}).get('typeString') if isinstance(n,dict) else None
def subtype(n,parent,key):
 k=n.get('nodeType');out=None
 if k=='Literal':out={'kind':n.get('kind'),'type':tstr(n),'unit':n.get('subdenomination')}
 elif k=='UnaryOperation':out={'operator':n.get('operator'),'prefix':n.get('prefix'),'resolvedFunctionPresent':'function' in n}
 elif k=='BinaryOperation':out={'operator':n.get('operator'),'commonType':n.get('commonType',{}).get('typeString') if isinstance(n.get('commonType'),dict) else None,'resolvedFunctionPresent':'function' in n}
 elif k=='FunctionCall':
  c=n.get('expression',{});ref=c.get('referencedDeclaration') if isinstance(c,dict) else None
  out={'callKind':n.get('kind'),'calleeKind':c.get('nodeType') if isinstance(c,dict) else None,'calleeName':c.get('name',c.get('memberName')) if isinstance(c,dict) else None,'referenceSign':'builtin-negative' if isinstance(ref,int) and ref<0 else 'declaration-nonnegative' if isinstance(ref,int) else 'missing','namedArguments':bool(n.get('names'))}
 elif k=='TupleExpression':out={'inlineArray':n.get('isInlineArray'),'arity':len(n.get('components',[])),'holes':any(x is None for x in n.get('components',[])),'parentKind':parent,'parentKey':key}
 elif k=='VariableDeclaration':out={'location':n.get('storageLocation'),'state':n.get('stateVariable'),'mutability':n.get('mutability'),'typeNode':n.get('typeName',{}).get('nodeType') if isinstance(n.get('typeName'),dict) else None,'type':tstr(n)}
 elif k=='ElementaryTypeName':out={'name':n.get('name'),'stateMutability':n.get('stateMutability')}
 elif k=='FunctionTypeName':out={'visibility':n.get('visibility'),'stateMutability':n.get('stateMutability')}
 if out is not None:return {'nodeType':k,'fields':out}
for path in sorted((root/'tests/solc').rglob('*.ast.json')):
 try:data=json.loads(path.read_text())
 except (ValueError,OSError):continue
 h=data.get('header',{});fixtureSha=hashlib.sha256(path.read_bytes()).hexdigest()
 def walk(n,pointer='',parent=None,key=None,fun=None,unit=None):
  if isinstance(n,dict):
   kind=n.get('nodeType')
   if 'ast' in n and isinstance(n.get('name'),str):unit={'name':n['name'],'id':n.get('id'),'sourceSha256':n.get('sourceSha256')}
   if kind=='FunctionDefinition':fun={'id':n.get('id'),'name':n.get('name')}
   form=subtype(n,parent,key)
   if form:
    tag=json.dumps(form,sort_keys=True);entry=variants.setdefault(tag,{'variant':form,'occurrences':0,'witnesses':[]});entry['occurrences']+=1
    if len(entry['witnesses'])<2:entry['witnesses'].append({'fixture':str(path.relative_to(root)),'fixtureSha256':fixtureSha,'compilerVersion':h.get('solcVersion'),'compilerSha256':h.get('compilerSha256'),'sourceSha256':h.get('sourceSha256'),'unit':unit,'function':fun,'nodeId':n.get('id'),'src':n.get('src'),'line':n.get('line'),'pointer':pointer})
   for field,child in n.items():walk(child,pointer+'/'+field.replace('~','~0').replace('/','~1'),kind,field,fun,unit)
  elif isinstance(n,list):
   for i,child in enumerate(n):walk(child,pointer+'/'+str(i),parent,key,fun,unit)
 walk(data)
result={'schemaVersion':1,'basis':'4095d848297d87e374b4f069692511cfe4a36cf7','variantCount':len(variants),'byKind':dict(collections.Counter(v['variant']['nodeType'] for v in variants.values())),'variants':list(variants.values()),'boundary':'Observed variants in existing fixtures, including possible intentional mutations. No support, compiler authenticity, admission, intrinsic or backend proof is inferred.'}
(bulk/'fixture-variants.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({'variants':result['variantCount'],'byKind':result['byKind']},sort_keys=True))
