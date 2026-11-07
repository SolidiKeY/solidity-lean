"""Syntactic elaboration-arm index, not translation-preservation certification."""
from pathlib import Path
import json,hashlib,re,subprocess
owned=Path(__file__).resolve().parent
root=owned.parents[2]
raw=json.loads((owned/'coverage-inventory.json').read_text())['rawConstructors']
paths=['Solidity/Syntax/Elab/'+name+'.lean' for name in ['Values','Arms','Stmt','Lower']]
rows=[]
for family in ['RawExpr','RawStmt']:
 for constructor in raw[family]:
  hits=[]
  for path in paths:
   for line,text in enumerate((root/path).read_text().splitlines(),1):
    if re.search(r'^\s*\|[^\n]*\.'+re.escape(constructor)+r'\b',text):
     hits.append({'path':path,'line':line,'arm':text.strip()})
  rows.append({'family':family,'constructor':constructor,'syntacticArmReferences':hits,
    'proofClosure':'No AST/Raw lowering-preservation theorem established by this inventory; intrinsic target soundness is separate.'})
proofPaths=['Solidity/Calculus/StmtSound.lean','Solidity/Calculus/SoundStep.lean','Solidity/Theory/Bridge/Denote.lean']
proofs=[]
for path in proofPaths:
 for line,text in enumerate((root/path).read_text().splitlines(),1):
  if re.search(r'^theorem (?:Stmt\.(?:stepSound_arms|stepSound|sound|runs)|Op[0-3]\.denote_eval)\b',text):
   proofs.append({'path':path,'line':line,'declarationStart':text})
result={'schemaVersion':1,'basis':subprocess.check_output(['git','rev-parse','HEAD'],cwd=root,text=True).strip(),
 'boundary':'Syntactic search plus independent read-only finder review. Arm hits can include helper matches. Neither per-constructor elaboration correctness nor exact axiom signatures are certified.',
 'sourceSha256':{path:hashlib.sha256((root/path).read_bytes()).hexdigest() for path in paths+proofPaths},
 'counts':{'RawExpr':len(raw['RawExpr']),'RawStmt':len(raw['RawStmt'])},'constructors':rows,'typedTargetTheorems':proofs}
(owned/'raw-elaboration-ledger.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({'constructors':len(rows),'withoutSyntacticArmHit':[(r['family'],r['constructor']) for r in rows if not r['syntacticArmReferences']],'typedTargetTheoremStarts':len(proofs)}))
