"""Guarded regression: consumed input bytes, including an unread tail, must match
an independently pinned digest. These are synthetic read controls, not fixtures.
"""
import gzip
import copy
import hashlib
import importlib.util
import json
from pathlib import Path
import sys
import tempfile
import unittest

REPO=Path(__file__).resolve().parents[4]
SOURCE=REPO/'scripts/h62/item3/g52-differential/engine_rejection_qualification.py'
sys.path.insert(0,str(SOURCE.parent));spec=importlib.util.spec_from_file_location('qualification',SOURCE);m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)

class ConsumedInput(unittest.TestCase):
    def test_exact_compressed_input_and_tail_are_hashed(self):
        rows=[dict(index=0,path='p',case='c')]
        records=[dict(index=0,path='p',case='c',fixture={'value':'original'}),dict(index=1,path='tail',case='tail',fixture={'value':'x'*100000})]
        raw=gzip.compress(('\n'.join(json.dumps(x) for x in records)+'\n').encode())
        with tempfile.TemporaryDirectory() as root:
            path=Path(root)/'inputs.gz';path.write_bytes(raw)
            out=m.original_items(path,rows,hashlib.sha256(raw).hexdigest());self.assertEqual(out,[dict(record=records[0],row=rows[0])])
            changed=gzip.compress((json.dumps(records[0])+'\n'+json.dumps({**records[1],'case':'mutated'})+'\n').encode());path.write_bytes(changed)
            with self.assertRaisesRegex(ValueError,'consumed input bytes'):m.original_items(path,rows,hashlib.sha256(raw).hexdigest())

    def test_wrong_identity_order_and_missing_selection_refuse(self):
        with tempfile.TemporaryDirectory() as root:
            path=Path(root)/'inputs.gz';raw=gzip.compress((json.dumps(dict(index=0,path='p',case='c'))+'\n').encode());path.write_bytes(raw);sha=hashlib.sha256(raw).hexdigest()
            for rows in [[dict(index=0,path='bad',case='c')],[dict(index=1,path='p',case='c')]]:
                with self.assertRaises(ValueError):m.original_items(path,rows,sha)
            path.write_bytes(gzip.compress((json.dumps(dict(index=1,path='p',case='c'))+'\n').encode()))
            with self.assertRaisesRegex(ValueError,'index'):m.original_items(path,[dict(index=0,path='p',case='c')],hashlib.sha256(path.read_bytes()).hexdigest())

class ObservationIntegerTypes(unittest.TestCase):
    def test_json_floats_and_booleans_do_not_normalize_through_javascript(self):
        row=dict(native=dict(steps=3,blocks=[dict(number='1',gas_used='20',transactions=[dict(index=0,type=0,receipt_status=1,gas_limit='100',receipt_cumulative_gas_used='20',total_gas_spent='20',execution_gas_used='10',native_gas_refund_counter='0')])]))
        row.update(binding=dict(payload_versions=4,forkchoice_version=3),expected=[dict(block_index=0)])
        row['native'].update(max_rlp_block_size=8388608,rejections=[dict(block_index=0,validation_facts=dict(transactionType=0))])
        m.validate_observed_integer_types([row])
        for mutate in [lambda x:x['native'].update(steps=3.0),lambda x:x['native']['blocks'][0].update(number=1.0),lambda x:x['native']['blocks'][0]['transactions'][0].update(total_gas_spent=20.5),lambda x:x['native']['blocks'][0]['transactions'][0].update(index=0.0),lambda x:x['native']['blocks'][0]['transactions'][0].update(receipt_status=True),lambda x:x['native'].update(max_rlp_block_size=8388608.0),lambda x:x['native']['rejections'][0].update(block_index=0.0),lambda x:x['native']['rejections'][0]['validation_facts'].update(transactionType=0.0),lambda x:x['expected'][0].update(block_index=0.0),lambda x:x['binding'].update(payload_versions=4.0),lambda x:x['binding'].update(forkchoice_version=3.0)]:
            bad=copy.deepcopy(row);mutate(bad)
            with self.assertRaises(ValueError):m.validate_observed_integer_types([bad])

class EvidenceMetrics(unittest.TestCase):
    def test_metrics_are_derived_from_original_inputs_and_captured_observations(self):
        selected=[dict(record=dict(index=7,fixture=dict(engineNewPayloads=[dict(params=[dict(transactions=['0x01'])]),dict(validationError='X')])),row=dict(native=dict(blocks=[dict(transactions=[dict(logs=[])])],steps=3)))]
        item=dict(index=7,qualified_rejections=1,accepted_prefix_blocks=1,transaction_observations=1,raw_log_entries=0,steps=3)
        m.validate_metrics([item],selected)
        for key in item:
            bad={**item,key:item[key]+1}
            with self.subTest(key=key),self.assertRaises(ValueError):m.validate_metrics([bad],selected)
        for bad in [[],[item,item],[{**item,'steps':3.5}],[{**item,'index':True}]]:
            with self.assertRaises(ValueError):m.validate_metrics(bad,selected)

if __name__=='__main__':unittest.main()
