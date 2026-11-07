"""Regression: conditional machine transfers must not evade the closure audit."""
import ast,pathlib,re,unittest
source=pathlib.Path(__file__).parent/'scripts/closure-audit.py'
node=next(n for n in ast.parse(source.read_text()).body if isinstance(n,ast.FunctionDef) and n.name=='machine_transfers')
namespace={'re':re}
exec(compile(ast.Module(body=[node],type_ignores=[]),str(source),'exec'),namespace)
transfers=namespace['machine_transfers']
class MachineTransfers(unittest.TestCase):
 def test_external_conditional_transfer_is_audited(self):
  calls,branches,invalid=transfers('  100: 75 05 jne 107 <unreviewed_function>','reviewed')
  self.assertEqual((calls,branches,invalid),(set(),{'unreviewed_function'},False))
  self.assertFalse((calls|branches)<={'lean_dec_ref_cold'})
 def test_local_conditionals_and_approved_calls(self):
  self.assertEqual(transfers(' 100: 75 05 jne 107 <reviewed+0x7>\n 102: e8 00 callq 200 <lean_dec_ref_cold>','reviewed'),({'lean_dec_ref_cold'},set(),False))
 def test_all_jump_families_are_audited(self):
  for op in ['jmp','jmpq','je','jne','jrcxz','loop','loope','loopne']:
   self.assertEqual(transfers('100: 00 '+op+' 200 <unreviewed>','reviewed'),(set(),{'unreviewed'},False))
 def test_indirect_and_unlabelled_transfers_fail_closed(self):
  for instruction in ['call *%rax','jmpq *%r11','jne 200','loop 200']:
   self.assertTrue(transfers('100: 00 '+instruction,'reviewed')[2])
if __name__=='__main__':unittest.main()
