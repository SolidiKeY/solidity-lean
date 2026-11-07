#!/usr/bin/env python3
"""Generate structural exclusion proofs from the frozen word table, not numeric grammar."""
import ast,hashlib,pathlib,sys
root=pathlib.Path(__file__).resolve().parents[2]
source=root/'Solidity/Frontend/Checked/Tables.lean'
text=source.read_text().split('def solWordTable : Bytes → WordClass\n')[1].split('/-- The fixed words of Yul')[0]
words={tuple(ast.literal_eval(line.strip()[2:].split('=>')[0])):line.split('=>')[1].strip() for line in text.splitlines() if line.startswith('  | [')}
assert len(words)==98
prefixes=sorted({w[:i] for w in words for i in range(len(w)+1)},key=lambda p:(-len(p),p))
assert len(prefixes)==439
def fmt(p):return '['+', '.join(map(str,p))+']'
def nm(p):return 'table_prefix_'+('_'.join(map(str,p)) if p else 'root')
blocks=[]
for prefix in prefixes:
 children=list(dict.fromkeys(w[len(prefix)] for w in words if len(w)>len(prefix) and w[:len(prefix)]==prefix))
 block=[f'theorem {nm(prefix)} (r : Bytes) (n : NumLit) :',f'    solWordTable ({fmt(prefix)} ++ r) ≠ .tok (.num n) := by','  intro h','  cases r with','  | nil =>',f'    with_unfolding_all change ({words.get(prefix,".other")} : WordClass) = .tok (.num n) at h','    cases h','  | cons b r =>']
 indent=4; guards=[]
 for child in children:
  sp=' '*indent; hn=f'h{child}';guards.append(hn)
  block += [sp+f'by_cases {hn} : b = {child}',sp+'· subst b',sp+f'  exact {nm(prefix+(child,))} r n h',sp+'·'];indent+=2
 sp=' '*indent
 if guards:
  expr='(.other : WordClass)'
  for child in reversed(children):expr=f'(dite (b = {child}) (fun _ => _) (fun _ => {expr}))'
  block += [sp+'delta solWordTable solWordTable.match_1 at h',sp+f'change {expr} = .tok (.num n) at h',sp+'rw ['+', '.join('dif_neg '+g for g in guards)+'] at h']
 else:block += [sp+'with_unfolding_all change (.other : WordClass) = .tok (.num n) at h']
 block += [sp+'cases h',''];blocks.append(block)
folder=root/'Solidity/Frontend/NumericLiteralProofs/WordTable'
expected={}
chunks=[blocks[i:i+15] for i in range(0,len(blocks),15)]
for i,chunk in enumerate(chunks):
 dep='Solidity.Frontend.Checked.Lexer' if i==0 else f'Solidity.Frontend.NumericLiteralProofs.WordTable.Part{i-1:02}'
 lines=[f'import {dep}','','/-! # Generated direct structural word-table proof.','No scanner changes, equation generation, or raised budgets. -/','namespace Solidity.Frontend.NumericLiteralProofs','open Solidity.Frontend.Checked Solidity.Source','']
 for block in chunk:lines+=block
 lines+=['end Solidity.Frontend.NumericLiteralProofs','']
 expected[folder/f'Part{i:02}.lean']='\n'.join(lines)
expected[folder.parent/'WordTable.lean']=f"""import Solidity.Frontend.NumericLiteralProofs.WordTable.Part{len(chunks)-1:02}

/-! # Every fixed word is disjoint from numeric tokens -/
namespace Solidity.Frontend.NumericLiteralProofs
open Solidity.Frontend.Checked Solidity.Source

theorem solWordTable_no_num (raw : Bytes) (n : NumLit) :
    solWordTable raw ≠ .tok (.num n) := table_prefix_root raw n

end Solidity.Frontend.NumericLiteralProofs
"""
if '--check' in sys.argv:
 assert set(folder.glob('Part*.lean'))=={p for p in expected if p.parent==folder}
 for path,text in expected.items():assert path.read_text()==text,path
else:
 folder.mkdir(exist_ok=True)
 for path in folder.glob('Part*.lean'):
  if path not in expected:path.unlink()
 for path,text in expected.items():path.write_text(text)
print(f'word table: {len(words)} fixed words, {len(prefixes)} prefix proofs, {len(chunks)} serial modules')
