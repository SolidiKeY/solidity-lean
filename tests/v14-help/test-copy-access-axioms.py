import subprocess,tempfile,sys,re
from pathlib import Path
root=Path(__file__).parent
queries=(root/'CopyAccessAxioms.lean').read_text()
names=re.findall(r"^#print axioms (\S+)$",queries,re.M)
valid="\n".join("'%s' does not depend on any axioms"%n for n in names)
cases=[('valid',queries,valid,True),('empty-query','', '',False),
 ('empty-output',queries,'',False),('missing',queries,valid.split('\n',1)[1],False),
 ('duplicate-query',queries.replace(names[0],names[1]),valid,False),
 ('duplicate-report',queries,"'%s' depends on axioms: [sorryAx]\n"%names[0]+valid,False),
 ('duplicate-standard',queries,valid+"\n'%s' depends on axioms: [propext]"%names[0],False),
 ('nonstandard',queries,valid.replace("'%s' does not depend on any axioms"%names[0],"'%s' depends on axioms: [oracle]"%names[0]),False)]
with tempfile.TemporaryDirectory(prefix='v14-byte-axiom-controls-') as directory:
 d=Path(directory);(d/'check-copy-access-axioms.py').write_text((root/'check-copy-access-axioms.py').read_text())
 for label,q,log,passed in cases:
  (d/'CopyAccessAxioms.lean').write_text(q);(d/'output.log').write_text(log)
  result=subprocess.run([sys.executable,'-O',str(d/'check-copy-access-axioms.py'),str(d/'output.log')],capture_output=True,text=True)
  if (result.returncode==0)!=passed: raise SystemExit(label+': wrong verdict '+result.stdout+result.stderr)
  print(label+': pass')
print('8/8 axiom audit controls pass (including optimized Python)')
