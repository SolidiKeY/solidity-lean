"""Fail-closed build controls, not runtime semantic proofs."""
import importlib.util, os, pathlib, subprocess, sys, tempfile, unittest
ROOT=pathlib.Path(__file__).resolve().parents[3]
spec=importlib.util.spec_from_file_location('closure',ROOT/'scripts/direct-runtime-closure.py')
helper=importlib.util.module_from_spec(spec);spec.loader.exec_module(helper)
class ProvenanceTests(unittest.TestCase):
    def test_changed_header_rejected(self):
        with tempfile.TemporaryDirectory() as d:
            p=pathlib.Path(d)/'lean.h';p.write_bytes(b'old')
            initial=helper.snapshot_files([p]);p.write_bytes(b'new')
            with self.assertRaisesRegex(ValueError,'Build inputs changed'):
                helper.verify_snapshot(initial,[p])
    def test_new_header_rejected(self):
        with tempfile.TemporaryDirectory() as d:
            d=pathlib.Path(d);p=d/'one.h';p.write_bytes(b'one')
            initial=helper.snapshot_files(d.glob('*.h'));(d/'two.h').write_bytes(b'two')
            with self.assertRaisesRegex(ValueError,'two.h'):
                helper.verify_snapshot(initial,d.glob('*.h'))
    def test_removed_header_rejected(self):
        with tempfile.TemporaryDirectory() as d:
            d=pathlib.Path(d);p=d/'one.h';p.write_bytes(b'one')
            initial=helper.snapshot_files(d.glob('*.h'));p.unlink()
            with self.assertRaisesRegex(ValueError,'one.h'):
                helper.verify_snapshot(initial,d.glob('*.h'))
    def test_unchanged_duplicate_iterable(self):
        with tempfile.TemporaryDirectory() as d:
            p=pathlib.Path(d)/'one.h';p.write_bytes(b'one')
            initial=helper.snapshot_files(iter([p,p]))
            helper.verify_snapshot(initial,iter([p]))
    def rejection(self,script,variable,value,message):
        env=dict(os.environ)
        for key in ['LEAN_CC','LEAN_SYSROOT','CPATH','C_INCLUDE_PATH','CPLUS_INCLUDE_PATH','LIBRARY_PATH','COMPILER_PATH','DIRECT_RUNTIME_FULL','EMCC_CFLAGS','EM_COMPILER_WRAPPER','EM_LLVM_ROOT','EM_BINARYEN_ROOT']:env.pop(key,None)
        env[variable]=value
        # No valid argv/toolchain: the boundary must reject before any Lean call.
        result=subprocess.run([sys.executable,str(ROOT/'scripts'/script)],env=env,text=True,capture_output=True)
        self.assertNotEqual(result.returncode,0)
        self.assertIn(message,result.stderr)
    def test_full_runtime_refused_before_toolchain(self):
        self.rejection('build-direct-runtime.py','DIRECT_RUNTIME_FULL','1','not an ordinary verifier')
    def test_implicit_emscripten_config_refused(self):
        self.rejection('build-direct-runtime.py','EM_CONFIG','','require an explicit EM_CONFIG')
    def test_native_overrides_refused_before_toolchain(self):
        for name in ['LEAN_CC','LEAN_SYSROOT','CPATH']:
            with self.subTest(name=name):self.rejection('build-direct-native.py',name,'/different','Unpinned compiler override: '+name)
    def test_wasm_overrides_refused_before_toolchain(self):
        for name in ['LEAN_CC','LEAN_SYSROOT','EMCC_CFLAGS','EM_COMPILER_WRAPPER']:
            with self.subTest(name=name):self.rejection('build-direct-runtime.py',name,'/different','Unpinned compiler override: '+name)
if __name__=='__main__':unittest.main()
