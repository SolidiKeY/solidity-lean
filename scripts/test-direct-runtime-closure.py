import importlib.util,pathlib,tempfile,unittest
spec=importlib.util.spec_from_file_location('closure',pathlib.Path(__file__).with_name('direct-runtime-closure.py'))
closure=importlib.util.module_from_spec(spec);spec.loader.exec_module(closure)
class ClosureTests(unittest.TestCase):
 def source(self,root,module,text):
  p=pathlib.Path(root)/'.lake/build/ir'/(module.replace('.','/')+'.c');p.parent.mkdir(parents=True,exist_ok=True);p.write_text(text)
 def test_closure_references_and_initializer_order(self):
  with tempfile.TemporaryDirectory() as root:
   self.source(root,'Solidity.Support','''// Module: Solidity.Support
// Imports:
static lean_object* l_value;
static lean_object* _init_l_value(void) { return lean_mk_string("}"); }
LEAN_EXPORT lean_object* l_support(void) { lean_object* res; return l_value; }
LEAN_EXPORT lean_object* initialize_Solidity_Support(uint8_t builtin, lean_object* w) {
l_value = _init_l_value();
lean_mark_persistent(l_value);
return lean_io_result_mk_ok(lean_box(0));
}
''')
   self.source(root,'Solidity.Tools.DirectRuntime','''// Module: Solidity.Tools.DirectRuntime
// Imports: Solidity.Support
LEAN_EXPORT lean_object* l_dead(void) { return lean_box(0); }
LEAN_EXPORT lean_object* solidity_direct_check(lean_object* x) { lean_object* res; return l_support(); }
LEAN_EXPORT lean_object* initialize_Solidity_Tools_DirectRuntime(uint8_t builtin, lean_object* w) {
res = registerFrontend();
return lean_io_result_mk_ok(lean_box(0));
}
''')
   output,stats=closure.extract(pathlib.Path(root),pathlib.Path(root))
   self.assertEqual([x[0] for x in output],['Solidity.Support','Solidity.Tools.DirectRuntime'])
   self.assertIn('l_value = _init_l_value();',output[0][1]);self.assertIn('lean_mk_string("}")',output[0][1])
   self.assertNotIn('registerFrontend()',output[1][1]);self.assertNotIn('l_dead(void)',output[1][1]);self.assertEqual(stats['closedValues'],1)
 def test_unrecognized_live_initializer_fails_closed(self):
  with tempfile.TemporaryDirectory() as root:
   self.source(root,'Solidity.Tools.DirectRuntime','''// Module: Solidity.Tools.DirectRuntime
// Imports:
static lean_object* l_value;
LEAN_EXPORT lean_object* solidity_direct_check(lean_object* x) { return l_value; }
LEAN_EXPORT lean_object* initialize_Solidity_Tools_DirectRuntime(uint8_t builtin, lean_object* w) {
l_value = makeEffectfulValue(w);
return lean_io_result_mk_ok(lean_box(0));
}
''')
   with self.assertRaisesRegex(ValueError,'unsupported initialization'):closure.extract(pathlib.Path(root),pathlib.Path(root))
if __name__=='__main__':unittest.main()
