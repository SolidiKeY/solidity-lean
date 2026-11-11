#!/usr/bin/env python3
"""Regression checks for the earlier cleaner's physical-newline drift."""
import pathlib,runpy,subprocess,unittest
HERE=pathlib.Path(__file__).resolve().parent
API=runpy.run_path(str(HERE/'historical.py'));ns,_=API['backend']()
class Coordinates(unittest.TestCase):
 def test_continuation_preserves_characters_but_changes_masked_lines(self):
  raw='def a := "x'+chr(92)+'\n'+'y"\ndef z := 0\n'
  masked=ns['clean'](raw);self.assertEqual(len(masked),len(raw))
  a=masked.index('def z');self.assertEqual(masked.count('\n',0,a)+1,2)
  self.assertEqual(API['raw_span'](raw,a,len(raw)),(3,3,1))
 def test_exclusive_end_at_lf_boundary(self):
  self.assertEqual(API['raw_span']('a\nb\nc',0,4),(1,2,2))
 def test_pinned_counterexamples(self):
  for path,name,reported,physical in [('Solidity/Frontend/SolcJson/Body.lean','boolKey',1139,1144),('Solidity/Frontend/SolcJson/Contract.lean','readContractWithNormalizationV1_forget',2249,2258)]:
   raw=subprocess.check_output(['git','show',API['BASE']+':'+path],cwd=API['ROOT'],text=True);masked=ns['clean'](raw)
   match=next(m for m in ns['DECL'].finditer(masked) if m.group(2)==name)
   self.assertEqual(masked.count('\n',0,match.start())+1,reported)
   self.assertEqual(API['raw_span'](raw,match.start(),match.end())[0],physical)
if __name__=='__main__':unittest.main()
