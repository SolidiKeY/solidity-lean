#!/usr/bin/env python3
"""Regression for startup headroom: no heavy launch below the fixed reserve."""
import tempfile,unittest
from pathlib import Path
from unittest.mock import patch,MagicMock
import final_gate

class StartupGuard(unittest.TestCase):
 def exercise(self,headroom):
  with tempfile.TemporaryDirectory() as tmp:
   root=Path(tmp); tool=root/'tool'; (tool/'bin').mkdir(parents=True)
   for name in ['lean','lake']: (tool/'bin'/name).write_text('unused fake test binary')
   def version(cmd,**kwargs):
    return 'Lean (version 4.24.0, test)\n' if Path(cmd[0]).name=='lean' else 'Lake version test\n'
   proc=MagicMock(); proc.poll.return_value=0; proc.returncode=0
   with patch('sys.argv',['final_gate.py','--toolchain',str(tool),'--artifacts',str(root),'--probe']), \
        patch.object(final_gate.bounded_lean,'available',return_value=headroom), \
        patch.object(final_gate.subprocess,'check_output',side_effect=version), \
        patch.object(final_gate.subprocess,'Popen',return_value=proc) as launch:
    if headroom<4*1024**3:
     with self.assertRaisesRegex(RuntimeError,'startup headroom'): final_gate.main()
     launch.assert_not_called()
    else:
     final_gate.main(); self.assertEqual(launch.call_count,2)
   self.assertFalse((root/'evidence/runtime-gate.json').exists())
 def test_below_reserve_never_launches(self): self.exercise(4*1024**3-1)
 def test_exact_reserve_allows_probe(self): self.exercise(4*1024**3)

if __name__=='__main__': unittest.main()
