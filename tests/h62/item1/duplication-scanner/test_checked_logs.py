"""Guard parsed probe metadata detached from successful process output bytes."""
import copy
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import sys
import tempfile
import unittest
from unittest import mock

ROOT=Path(__file__).resolve().parents[4];SCRIPTS=ROOT/"scripts/h62/item1/duplication-scanner"
sys.path.insert(0,str(SCRIPTS))
try:
    import bind_signature_fixture as binder
    import bind_project_leaf as leaf
    import bind_project_closure as closure
    import bind_source_locations as source
    import census_fixture_kernel as kernel
finally:sys.path.pop(0)
observer=binder.observer


class CheckedLogControls(unittest.TestCase):
    def setUp(self):
        self.tmp=tempfile.TemporaryDirectory();self.addCleanup(self.tmp.cleanup);self.root=Path(self.tmp.name)
        self.log=self.root/"probe.log";self.raw=b'H62_ENVIRONMENT {}\n';self.log.write_bytes(self.raw)
        self.digest=hashlib.sha256(self.raw).hexdigest()
        self.step={"log":str(self.log),"log_sha256":self.digest,"exit":0,"timed_out":False,"stop_reason":None}

    def test_exact_bytes_are_parsed_and_unbound_offline_behavior_remains(self):
        self.assertEqual(observer.read_log_bytes(self.log,self.digest),self.raw)
        self.assertEqual(observer.read_log(self.log,self.digest),observer.read_log(self.log))
        self.log.write_bytes(b'H62_ENVIRONMENT {"fabricated":true}\n')
        self.assertEqual(observer.read_log(self.log)[0],{"fabricated":True})
        with self.assertRaisesRegex(ValueError,"checked process output"):observer.read_log(self.log,self.digest)

    def test_reader_checks_exact_buffer_not_a_second_file_read(self):
        with mock.patch.object(Path,"read_bytes",side_effect=AssertionError("must parse bounded buffer")):
            self.assertEqual(observer.read_log(self.log,self.digest)[0],{})

    def test_size_limit_and_invalid_expected_hash_refuse(self):
        with self.assertRaisesRegex(ValueError,"byte limit"):observer.read_log_bytes(self.log,self.digest,max_bytes=2)
        for digest in ("wrong",True,"A"*64):
            with self.assertRaisesRegex(ValueError,"expected log SHA256"):observer.read_log_bytes(self.log,digest)

    def test_live_symlink_and_fifo_refuse_before_open(self):
        link=self.root/"alias";link.symlink_to(self.log)
        with self.assertRaisesRegex(ValueError,"nonregular"):observer.read_log_bytes(link,self.digest)
        fifo=self.root/"pipe";os.mkfifo(fifo)
        with self.assertRaisesRegex(ValueError,"nonregular"):observer.read_log_bytes(fifo,self.digest)
        self.assertEqual(observer.read_log(link),observer.read_log(self.log))

    def test_successful_unique_in_memory_step_required(self):
        self.assertEqual(binder.expected_log_hash([self.step],self.log),self.digest)
        for steps in ([],[self.step,self.step],None,[None]):
            with self.assertRaises(ValueError):binder.expected_log_hash(steps,self.log)
        for field,value in (("exit",1),("exit",False),("timed_out",True),("stop_reason","memory"),("log_sha256","wrong")):
            row=dict(self.step);row[field]=value
            with self.assertRaises(ValueError):binder.expected_log_hash([row],self.log)

    def test_persistent_post_parse_log_change_refused(self):
        observer.read_log(self.log,binder.expected_log_hash([self.step],self.log))
        binder.verify_process_logs([self.step]);self.log.write_bytes(self.raw+b' ')
        with self.assertRaisesRegex(ValueError,"changed after execution"):binder.verify_process_logs([self.step])

    def test_source_parent_rejects_log_replaced_after_kernel_return(self):
        def encoded(part):return ["str",["anonymous"],part]
        def write_json(path,value):
            raw=(json.dumps(value,indent=2)+'\n').encode();path.write_bytes(raw)
            return hashlib.sha256(raw).hexdigest()
        def step(path):
            return {"log":str(path),"log_sha256":hashlib.sha256(path.read_bytes()).hexdigest(),"exit":0,"timed_out":False,"stop_reason":None}
        for mutate in (False,True):
            output=self.root/('bad' if mutate else 'good')
            def child(directory):
                (directory/'rebuild/logs').mkdir(parents=True)
                consumer=directory/'rebuild/logs/consumer.log'
                consumer.write_text(observer.PREFIX+json.dumps({"main_module":encoded("SignatureObservedConsumer")})+'\n')
                rebuild={"steps":[step(consumer)],"compiled_artifacts":[]}
                rebuild_hash=write_json(directory/'rebuild/receipt.json',rebuild)
                census_log=directory/'census.log';census_log.write_text('original kernel output\n')
                census_hash=write_json(directory/'census.json',{})
                live={"steps":[step(census_log)],"census_sha256":census_hash,"rebuild_receipt_sha256":rebuild_hash}
                write_json(directory/'receipt.json',live);return live
            def process(command,env,log,steps):
                log.write_text(observer.PREFIX+json.dumps({"main_module":encoded("SignatureSourceLocations")})+'\n'+source.PREFIX+'{}\n')
                steps.append(step(log))
            def join(*args):
                if mutate:(output/'kernel/census.log').write_text('replaced after child return\n')
                raw=(binder.FIXTURES/'SignatureFingerprint.lean').read_bytes()
                return {"lexical_total":20,"linked":0,"unresolved":20,"source_sha256":hashlib.sha256(raw).hexdigest()}
            with mock.patch.object(source.kernel,'run',side_effect=child),mock.patch.object(source.binder,'check_inputs',return_value=Path('/fake/lean')),mock.patch.object(source.binder.observer,'capture_environment',return_value={"artifacts":[]}),mock.patch.object(source.binder,'companion_artifacts',return_value=[]),mock.patch.object(source.binder,'runtime_files',return_value=[]),mock.patch.object(source.binder,'checked_process',side_effect=process),mock.patch.object(source,'join_locations',side_effect=join):
                if mutate:
                    with self.assertRaisesRegex(ValueError,'changed after execution'):source.run(output)
                    self.assertEqual(json.loads((output/'receipt.json').read_text())['status'],'failed')
                else:self.assertEqual(source.run(output)['status'],'pass')

    def test_all_metadata_readers_bind_before_parsing(self):
        census={"format":1,"module":kernel.MODULE,"total":1,"rows":[{"declaration":["str",["anonymous"],"t"],"kind":"theorem","status":"serialized","signature":[]}]}
        cases=[(leaf.read_log,leaf.PREFIX,{"census":{},"locations":{}}),
               (source.read_log,source.PREFIX,{}),(kernel.read_log,kernel.PREFIX,census),
               (closure.checked_probe,leaf.PREFIX,{"census":{},"locations":{}})]
        for reader,prefix,record in cases:
            raw=self.raw+(prefix+json.dumps(record)+'\n').encode();self.log.write_bytes(raw)
            digest=hashlib.sha256(raw).hexdigest();reader(self.log,digest)
            self.log.write_bytes(raw.replace(b'H62_ENVIRONMENT {}',b'H62_ENVIRONMENT {"changed":true}'))
            with self.assertRaisesRegex(ValueError,"checked process output"):reader(self.log,digest)


if __name__=="__main__":unittest.main()
