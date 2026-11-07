"""Batch plan controls prevent duplicated or unbound enumeration targets."""
import importlib.util,json,pathlib,sys,tempfile,unittest
sys.dont_write_bytecode=True
scripts=pathlib.Path(__file__).resolve().parents[4]/'scripts/h62/item6/migrate-yul'
sys.path.insert(0,str(scripts))
spec=importlib.util.spec_from_file_location('compiler_batches',scripts/'compiler-signatures-batch.py')
batch=importlib.util.module_from_spec(spec);spec.loader.exec_module(batch)
class CompilerBatches(unittest.TestCase):
    def test_job_binding_controls(self):
        with tempfile.TemporaryDirectory() as tmp:
            root=pathlib.Path(tmp);plan=root/'jobs.json'
            one=dict(module='Example',output=str(root/'one.jsonl'))
            plan.write_text(json.dumps([one]));self.assertEqual(batch.jobs(plan),[one])
            cases=[[one,dict(module='Other',output=one['output'])],
                [one,dict(module='Example',output=str(root/'two.jsonl'))],
                [dict(module='Example',output='relative.jsonl')],
                [dict(module='Example',output=one['output'],extra=True)]]
            for rows in cases:
                plan.write_text(json.dumps(rows))
                with self.assertRaises(ValueError):batch.jobs(plan)
if __name__=='__main__':unittest.main()
