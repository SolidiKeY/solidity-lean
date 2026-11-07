"""Completion/count/identity controls for the reused Lean inspection protocol."""
import json
import unittest
from read_elaborated_subset import decode


class InspectorProtocol(unittest.TestCase):
    def setUp(self):
        self.pins = dict(manifest_sha256='fingerprint', modules=['Example.Module'])
        self.row = dict(name='Example.Module.theorem', module='Example.Module',
                        manifest_sha256='fingerprint')
        self.done = dict(counts={'Example.Module':1}, manifest_sha256='fingerprint')

    def log(self, rows=None, done=None):
        rows = [self.row] if rows is None else rows
        done = [self.done] if done is None else done
        return '\n'.join(['H62_CENSUS_JSON '+json.dumps(r) for r in rows]+
                         ['H62_CENSUS_DONE '+json.dumps(r) for r in done])

    def test_complete(self):
        self.assertEqual(decode(self.log(), self.pins), [self.row])

    def test_missing_or_duplicate_completion(self):
        for records in [[], [self.done,self.done]]:
            with self.assertRaisesRegex(ValueError, 'completion marker'):
                decode(self.log(done=records), self.pins)

    def test_duplicate_identity(self):
        with self.assertRaisesRegex(ValueError, 'duplicate constant'):
            decode(self.log(rows=[self.row,self.row]), self.pins)

    def test_changed_fingerprint(self):
        for field in ['row','done']:
            row = dict(self.row)
            done = dict(self.done)
            (row if field=='row' else done)['manifest_sha256']='wrong'
            with self.assertRaisesRegex(ValueError, 'fingerprint mismatch'):
                decode(self.log([row],[done]), self.pins)

    def test_wrong_completion_count(self):
        with self.assertRaisesRegex(ValueError, 'count mismatch'):
            decode(self.log(done=[dict(self.done,counts={'Example.Module':2})]), self.pins)

    def test_unselected_module(self):
        row = dict(self.row,module='Other.Module')
        done = dict(self.done,counts={'Other.Module':1})
        with self.assertRaisesRegex(ValueError, 'count mismatch'):
            decode(self.log([row],[done]), self.pins)

    def test_loaded_module_with_zero_constants(self):
        done = dict(self.done, counts={'Example.Module':0})
        self.assertEqual(decode(self.log(rows=[], done=[done]), self.pins), [])
        with self.assertRaisesRegex(ValueError, 'count mismatch'):
            decode(self.log(rows=[], done=[dict(done, counts={})]), self.pins)



class ExecutionBinding(unittest.TestCase):
    def test_receipt_and_binding_controls(self):
        from read_elaborated_subset import validate_execution
        binding = dict(inspection_sha256='probe', source_sha256={'Example/Module.lean':'source'})
        command = ['python3','runner']
        gate = dict(exit=0,process_exit=0,resource_stop=False,command=command,
                    limits=dict(memory_max=12*1024**3,memory_swap_max=0,lean_num_threads=1),
                    minimum_parent_headroom_bytes=4*1024**3)
        lines = ['H62_SOURCE_BINDING '+json.dumps(dict(stage=s,**binding)) for s in ['before','after']]
        validate_execution('\n'.join(lines), gate, command, binding)
        for key,value in [('exit',1),('process_exit',1),('resource_stop',True),('command',['wrong']),('limits',{}),('minimum_parent_headroom_bytes',4*1024**3-1)]:
            with self.subTest(key=key), self.assertRaises(ValueError):
                validate_execution('\n'.join(lines), dict(gate,**{key:value}), command, binding)
        for bad in [lines[:1], list(reversed(lines)), [lines[0],lines[1].replace('source"','changed"')]]:
            with self.assertRaises(ValueError):
                validate_execution('\n'.join(bad), gate, command, binding)

    def test_changed_pin_probe_and_source(self):
        import hashlib
        from pathlib import Path
        import tempfile
        from read_elaborated_subset import check_pins
        sha = lambda b:hashlib.sha256(b).hexdigest()
        with tempfile.TemporaryDirectory() as tmp:
            repo=Path(tmp)/'repo';folder=Path(tmp)/'probe'
            (repo/'Example').mkdir(parents=True);folder.mkdir()
            source=repo/'Example/Module.lean';source.write_bytes(b'fixture source, not executable Lean')
            template='MODULES FINGERPRINT'
            provider=repo/'provider.py';provider.write_text('TEMPLATE = '+repr(template)+'\n')
            core=dict(base='base',modules=['Example.Module'],source_sha256={'Example/Module.lean':sha(source.read_bytes())},inspection_template_sha256=sha(template.encode()))
            fingerprint=sha(json.dumps(core,sort_keys=True,separators=(',', ':'),ensure_ascii=False).encode())
            probe=('import Lean\nimport Example.Module\n'+template.replace('MODULES','`Example.Module').replace('FINGERPRINT',fingerprint)).encode()
            pins=dict(core,manifest_sha256=fingerprint,inspection_sha256=sha(probe),template_provider='provider.py',template_provider_sha256=sha(provider.read_bytes()))
            p=folder/'pins.json';p.write_text(json.dumps(pins));(folder/'Probe.lean').write_bytes(probe)
            check_pins(repo,folder)
            p.write_text(json.dumps(dict(pins,base='changed')))
            with self.assertRaisesRegex(ValueError,'fingerprint mismatch'):check_pins(repo,folder)
            p.write_text(json.dumps(pins));(folder/'Probe.lean').write_bytes(b'changed')
            with self.assertRaisesRegex(ValueError,'inspection source changed'):check_pins(repo,folder)
            (folder/'Probe.lean').write_bytes(probe);source.write_bytes(b'changed')
            with self.assertRaisesRegex(ValueError,'producer changed'):check_pins(repo,folder)


if __name__ == '__main__':
    unittest.main()
