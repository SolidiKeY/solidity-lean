#!/usr/bin/env python3
"""Full frozen Bridge type fidelity, including actual private kernel constants."""
from census import census,ROOT
from inventory import split_declaration

def generate():
 out=["import SolidityBridge.PrecompileAgreement.Controls", "import Lean", "", "/-! Whole frozen types only; not a joint-premise witness or compiler-success theorem. Private terms below resolve one actual imported kernel constant and pass ordinary example type checking. No axiom or interface declaration is substituted. -/", "open Solidity Solidity.Precompiles Solidity.Roadmap.Evm EvmYul", "", "open Lean Elab Term in", 'elab "audit_private%" id:ident : term => do', "  let env ← getEnv", '  let suffix := "." ++ id.getId.toString', "  let found := env.constants.toList.filter fun (n, _) =>", '    n.toString.startsWith "_private.SolidityBridge.PrecompileAgreement." && n.toString.endsWith suffix', '  unless found.length = 1 do throwError "expected one actual frozen private constant: {id}"', "  let (name, info) := found.head!", '  unless info.levelParams.isEmpty do throwError "unexpected universe parameters: {name}"', '  logInfo m!"PRIVATE_CONSTANT {id.getId}: {name}"', "  return mkConst name", ""]
 total=private=closed=0
 for f in census()['files']:
  if not f['path'].startswith('Bridge/'):continue
  for row in f['declarations']:
   bs,goal=split_declaration(row);full=('∀ '+bs+', '+goal) if bs else goal
   ns=row['name'].rsplit('.',1)[0];value=('@'+row['name']) if row['visibility']=='public' else ('audit_private% '+row['name']);private+=row['visibility']=='private';closed+=not bool(bs)
   out+=['namespace '+ns,'-- Frozen source: '+row['name'],'set_option linter.unusedVariables false in','example : '+full+' := '+value,'end '+ns,''];total+=1
 assert (total,private,closed)==(73,4,25)
 out+=['run_cmd Lean.logInfo "BRIDGE_FULL_TYPE_FIDELITY_PASS total=73 private=4 closed=25"']
 return '\n'.join(out)+'\n'
if __name__=='__main__':
 import argparse
 p=argparse.ArgumentParser();p.add_argument('--check',action='store_true');a=p.parse_args();dst=ROOT/'tests/h62/item2/audit-precompiles/BridgeFidelity.lean';s=generate()
 if a.check:assert dst.read_text()==s
 else:dst.write_text(s)
 print('Generated73 unchanged full types; 4 private actual constants,25 closed statements; no witness promotion')
