"""Synthetic closure regressions; these are not semantic/runtime proofs."""
import importlib.util
import pathlib
import tempfile
import unittest

ROOT = pathlib.Path(__file__).resolve().parents[3]
spec = importlib.util.spec_from_file_location("closure", ROOT / "scripts/direct-runtime-closure.py")
closure = importlib.util.module_from_spec(spec)
spec.loader.exec_module(closure)

class ClosureRegressions(unittest.TestCase):
    def write(self, root, module, body, imports=""):
        path = root / ".lake/build/ir" / (module.replace(".", "/") + ".c")
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(f"// Module: {module}\n// Imports: {imports}\n" + body)

    def unit(self, body, initialization=""):
        return body + """
LEAN_EXPORT lean_object* initialize_Solidity_Tools_DirectRuntime(uint8_t builtin, lean_object* w) {
""" + initialization + """
return lean_io_result_mk_ok(lean_box(0));
}
"""

    def extract(self, body, initialization="", native_roots=()):
        with tempfile.TemporaryDirectory() as directory:
            root = pathlib.Path(directory)
            self.write(root, "Solidity.Tools.DirectRuntime", self.unit(body, initialization))
            return closure.extract(root, root, native_roots=native_roots)

    def test_closure_capture_retains_callback(self):
        outputs, stats = self.extract("""
static lean_object* l_value;
LEAN_EXPORT lean_object* l_callback(lean_object* x) { return x; }
static lean_object* _init_l_value(void) { return lean_alloc_closure((void*)l_callback, 1, 0); }
LEAN_EXPORT lean_object* solidity_direct_check(lean_object* x) { return l_value; }
""", "l_value = _init_l_value();\nlean_mark_persistent(l_value);\n")
        self.assertIn("l_callback(lean_object* x)", outputs[0][1])
        self.assertEqual(stats["closedValues"], 1)

    def test_native_abi_callback_retained_without_api_edge(self):
        outputs, stats = self.extract("""
LEAN_EXPORT lean_object* l_callback(lean_object* x) { return x; }
LEAN_EXPORT lean_object* solidity_direct_check(lean_object* x) { return x; }
""", native_roots={"l_callback"})
        self.assertIn("l_callback(lean_object* x)", outputs[0][1])
        self.assertEqual(stats["nativeRoots"], ["l_callback"])

    def test_iterator_native_callback_roots_retained(self):
        outputs, stats = self.extract("""
LEAN_EXPORT lean_object* l_callback(lean_object* x) { return x; }
LEAN_EXPORT lean_object* solidity_direct_check(lean_object* x) { return x; }
""", native_roots=iter(["l_callback"]))
        self.assertEqual(stats["nativeRoots"], ["l_callback"])
        self.assertIn("l_callback(lean_object* x)", outputs[0][1])

    def test_missing_generated_native_roots_fail_closed(self):
        for symbol in ("l_missing_callback", "_init_l_missing_value"):
            with self.subTest(symbol=symbol):
                with self.assertRaisesRegex(ValueError, "Unresolved generated native roots: " + symbol):
                    self.extract("LEAN_EXPORT lean_object* solidity_direct_check(lean_object* x) { return x; }\n",
                                 native_roots={symbol})

    def test_platform_native_roots_remain_linker_resolved(self):
        _, stats = self.extract("LEAN_EXPORT lean_object* solidity_direct_check(lean_object* x) { return x; }\n",
                                native_roots={"malloc", "memcpy"})
        self.assertEqual(stats["nativeRoots"], [])

    def test_unresolved_generated_reference_fails_closed(self):
        with self.assertRaisesRegex(ValueError, "Unresolved generated Lean symbol: l_missing"):
            self.extract("LEAN_EXPORT lean_object* solidity_direct_check(lean_object* x) { return l_missing(x); }\n")

    def test_pure_api_cannot_call_initializer(self):
        with self.assertRaisesRegex(ValueError, "Initializer called from pure API"):
            self.extract("LEAN_EXPORT lean_object* solidity_direct_check(lean_object* x) { return initialize_Solidity_Tools_DirectRuntime(1, x); }\n")

    def test_closed_dependency_initialization_order(self):
        outputs, stats = self.extract("""
static lean_object* l_first;
static lean_object* l_second;
static lean_object* _init_l_first(void) { return lean_box(1); }
static lean_object* _init_l_second(void) { return l_first; }
LEAN_EXPORT lean_object* solidity_direct_check(lean_object* x) { return l_second; }
""", "l_first = _init_l_first();\nlean_mark_persistent(l_first);\nl_second = _init_l_second();\nlean_mark_persistent(l_second);\n")
        text = outputs[0][1]
        self.assertLess(text.index("l_first = _init_l_first();"), text.index("l_second = _init_l_second();"))
        self.assertEqual(stats["closedValues"], 2)

if __name__ == "__main__":
    unittest.main()
