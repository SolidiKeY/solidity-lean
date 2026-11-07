"""Guard lost metadata refusals, domain confusion and saved-observation promotion."""
import copy
import importlib.util
import json
from pathlib import Path
import sys
import tempfile
import unittest
from unittest import mock

ROOT=Path(__file__).resolve().parents[4];SCRIPTS=ROOT/"scripts/h62/item1/duplication-scanner"
sys.path.insert(0,str(SCRIPTS))
try:
    import observe_metadata_types as observe
finally:sys.path.pop(0)


class MetadataObservationControls(unittest.TestCase):
    def setUp(self):
        name=["str",["anonymous"],"t"];module=observe.closure.encoded(["Solidity","Scope"])
        original={"declaration":name,"kind":"theorem","status":"unsupported","reason":"expression metadata"}
        self.legacy={"census":{"format":1,"module":module,"total":1,"rows":[original]},"locations":{}}
        self.value={"census":{"format":2,"module":module,"total":1,"rows":[{"declaration":name,"kind":"theorem","legacy":{"status":"unsupported","reason":"expression metadata"},"metadata_v2":{"status":"serialized","signature":["declaration-type-with-metadata-v2",0,["mdata",["metadata-entries"],["sort",["zero"]]]]}}]},"locations":{}}

    def test_separate_observation_retains_legacy_refusal(self):
        result=observe.validate(self.value,self.legacy)
        self.assertEqual(result['legacy_statuses'],{'unsupported':1});self.assertEqual(result['metadata_v2_statuses'],{'serialized':1})
        self.assertEqual(self.value['census']['rows'][0]['legacy']['reason'],'expression metadata')

    def test_row_omission_duplication_and_module_confusion_refuse(self):
        for change in (lambda v:v['census']['rows'].clear(),lambda v:v['census']['rows'].append(copy.deepcopy(v['census']['rows'][0])),lambda v:v['census'].update(module=['anonymous'])):
            value=copy.deepcopy(self.value);change(value)
            with self.assertRaises(ValueError):observe.validate(value,self.legacy)

    def test_legacy_promotion_or_range_drift_refuses(self):
        value=copy.deepcopy(self.value);value['census']['rows'][0]['legacy']={'status':'serialized','signature':[]}
        with self.assertRaisesRegex(ValueError,'legacy declaration result changed'):observe.validate(value,self.legacy)
        value=copy.deepcopy(self.value);value['locations']={'changed':True}
        with self.assertRaisesRegex(ValueError,'range coverage drift'):observe.validate(value,self.legacy)

    def test_old_domain_cannot_be_claimed_as_v2(self):
        value=copy.deepcopy(self.value);value['census']['rows'][0]['metadata_v2']['signature'][0]='declaration-type'
        with self.assertRaisesRegex(ValueError,'domain mismatch'):observe.validate(value,self.legacy)
        self.value['census']['rows'][0]['metadata_v2']={'status':'unsupported','reason':'metadata syntax payload'}
        self.assertEqual(observe.validate(self.value,self.legacy)['metadata_v2_statuses'],{'unsupported':1})

    def test_metadata_free_results_and_other_refusals_cannot_change(self):
        original=self.legacy['census']['rows'][0];original.pop('reason');original.update(status='serialized',signature=['declaration-type',0,['sort',['zero']]])
        row=self.value['census']['rows'][0];row['legacy']={k:v for k,v in original.items() if k not in ('declaration','kind')}
        row['metadata_v2']={'status':'serialized','signature':['declaration-type-with-metadata-v2',0,['sort',['zero']]]}
        observe.validate(self.value,self.legacy)
        row['metadata_v2']['signature'][2]=['sort',['succ',['zero']]]
        with self.assertRaisesRegex(ValueError,'metadata-free legacy type changed'):observe.validate(self.value,self.legacy)
        original.pop('signature');original.update(status='unsupported',reason='type is not closed');row['legacy']={'status':'unsupported','reason':'type is not closed'}
        with self.assertRaisesRegex(ValueError,'nonmetadata legacy refusal changed'):observe.validate(self.value,self.legacy)

    def test_saved_success_never_triggers_scope_build(self):
        with tempfile.TemporaryDirectory() as tmp:
            output=Path(tmp);(output/'receipt.json').write_text('{"status":"pass"}')
            with mock.patch.object(observe.closure,'run') as build:
                with self.assertRaises(FileExistsError):observe.run(output)
            build.assert_not_called()

    def test_helper_marker_bytes_bound_to_completed_process(self):
        with tempfile.TemporaryDirectory() as tmp:
            log=Path(tmp)/'helper.log';log.write_text('METADATA_V2_CONTROLS_PASS 14\n')
            step={'log':str(log),'log_sha256':observe.binder.sha(log),'exit':0,'timed_out':False,'stop_reason':None}
            observe.verify_controls_log(log,[step])
            log.write_text('METADATA_V2_CONTROLS_PASS 14\nextra invented text\n')
            with self.assertRaisesRegex(ValueError,'checked process output'):observe.verify_controls_log(log,[step])

    def test_child_metadata_replacement_after_read_refuses_final_seal(self):
        with tempfile.TemporaryDirectory() as tmp:
            directory=Path(tmp)
            for name in ('receipt.json','metadata.json','source-bindings.json'):(directory/name).write_text('{}')
            live={'metadata_sha256':observe.binder.sha(directory/'metadata.json'),'bindings_sha256':observe.binder.sha(directory/'source-bindings.json')}
            receipt_hash=observe.binder.sha(directory/'receipt.json')
            observe.verify_scope_artifacts(directory,live,receipt_hash)
            (directory/'metadata.json').write_text('{"changed_after_read":true}')
            with self.assertRaisesRegex(ValueError,'child artifact hash mismatch'):observe.verify_scope_artifacts(directory,live,receipt_hash)

    def test_updated_pin_does_not_admit_new_imports(self):
        pins=json.loads(observe.PINS.read_text());observe.admitted(pins)
        with tempfile.TemporaryDirectory() as tmp:
            helper=Path(tmp)/'MetadataFingerprintV2.lean';helper.write_text('import Solidity.Backend.WorldCalls.Premises\n')
            pins['helper_sha256']=observe.binder.sha(helper)
            with mock.patch.object(observe,'HELPER',helper),self.assertRaisesRegex(ValueError,'unadmitted observation imports'):observe.admitted(pins)


if __name__=='__main__':unittest.main()
