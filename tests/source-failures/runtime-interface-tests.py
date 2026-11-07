import importlib.util,unittest
from pathlib import Path
root=Path(__file__).resolve().parents[2]
spec=importlib.util.spec_from_file_location('source_runtime_interface',root/'scripts/source-runtime-interface.py');tool=importlib.util.module_from_spec(spec);spec.loader.exec_module(tool)
source=(root/'Solidity/Source/Eval.lean').read_text()
class ForwardingTests(unittest.TestCase):
 def test_actual_inventory(self):
  result=tool.audit_forwarding(source);self.assertEqual(len(result),18);self.assertEqual(result['emitEvent'],5)
 def test_missing_argument_rejected(self):
  with self.assertRaises(ValueError):tool.audit_forwarding(source.replace('evalE (plan := plan)','evalE',1))
 def test_disabled_nested_call_rejected(self):
  with self.assertRaises(ValueError):tool.audit_forwarding(source.replace('evalE (plan := plan)','evalE (plan := none)',1))
 def test_disabled_event_rejected(self):
  with self.assertRaises(ValueError):tool.audit_forwarding(source.replace('emitEvent (plan := plan)','emitEvent (plan := none)',1))
 def test_missing_parameter_rejected(self):
  at=source.index('def evalE');changed=source[:at]+source[at:].replace('(plan : FailureExecution.RuntimePlan := none)','',1)
  with self.assertRaises(ValueError):tool.audit_forwarding(changed)
 def test_changed_default_rejected(self):
  # The first parameter is emitEvent outside the mutual block; mutate evalE's own header.
  at=source.index('def evalE');changed=source[:at]+source[at:].replace('(plan : FailureExecution.RuntimePlan := none)','(plan : FailureExecution.RuntimePlan := some points)',1)
  with self.assertRaises(ValueError):tool.audit_forwarding(changed)
 def test_nested_comments_ignored(self):
  changed=source.replace('\nmutual\n','\nmutual\n/- evalE missing /- dispatch missing -/ emitEvent missing -/\n',1)
  self.assertEqual(tool.audit_forwarding(changed),tool.audit_forwarding(source))
 def test_strings_ignored(self):
  changed=source.replace('"signature"','"evalE dispatch emitEvent"',1)
  self.assertEqual(tool.audit_forwarding(changed),tool.audit_forwarding(source))
 def test_unterminated_comment_rejected(self):
  with self.assertRaises(ValueError):tool.audit_forwarding(source+'\n/- broken')
 def test_qualified_missing_argument_rejected(self):
  with self.assertRaises(ValueError):tool.audit_forwarding(source.replace('evalE (plan := plan)','Source.evalE',1))
 def test_qualified_same_plan_accepted(self):
  self.assertEqual(tool.audit_forwarding(source.replace('evalE (plan := plan)','Solidity.Source.evalE (plan := plan)',1)),tool.audit_forwarding(source))
 def test_unterminated_string_rejected(self):
  with self.assertRaises(ValueError):tool.audit_forwarding(source+'\n"broken')
 def test_root_missing_argument_rejected(self):
  with self.assertRaises(ValueError):tool.audit_forwarding(source.replace('evalE (plan := plan)','_root_.Solidity.Source.evalE',1))
 def test_root_disabled_argument_rejected(self):
  with self.assertRaises(ValueError):tool.audit_forwarding(source.replace('evalE (plan := plan)','_root_.Solidity.Source.evalE (plan := none)',1))
 def test_root_same_plan_accepted(self):
  self.assertEqual(tool.audit_forwarding(source.replace('evalE (plan := plan)','_root_.Solidity.Source.evalE (plan := plan)',1)),tool.audit_forwarding(source))
 def test_unknown_qualification_rejected(self):
  with self.assertRaises(ValueError):tool.audit_forwarding(source.replace('evalE (plan := plan)','Alias.evalE (plan := plan)',1))
 def test_quoted_identifier_rejected(self):
  with self.assertRaises(ValueError):tool.audit_forwarding(source.replace('evalE (plan := plan)','«evalE»',1))
if __name__=='__main__':unittest.main()
