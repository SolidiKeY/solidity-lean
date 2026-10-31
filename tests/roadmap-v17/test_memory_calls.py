"""New published-component controls; synthetic parser cases are not kernel proof."""
import copy
import importlib.util
import json
from pathlib import Path
import unittest
ROOT=Path(__file__).resolve().parents[2]
spec=importlib.util.spec_from_file_location('m',ROOT/'scripts/roadmap-v17-memory-calls.py');m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
class MemoryCallsControls(unittest.TestCase):
    def row(self):return dict(schema=1,isMemoryCalls=True,usesMemory=True,requiredFrame=12,callerFrame=4,allocationCost=5,sourceAliases=[2,7,88,0],targetWords=[77,261,99,42,8,1,7,2,88,0],emptyCodeWords=[77,256],intrinsicCode='actual fixture code bytes',semanticPremisesDischarged=False,releaseClosed=False)
    def raw(self,r):return ('V17_MEMORY_CALLS_BEGIN\n'+json.dumps(r)+'\nV17_MEMORY_CALLS_END\n').encode()
    def test_positive_and_mutations(self):
        r=self.row();self.assertEqual(m.observation(self.raw(r)),r);self.assertFalse(m.exact_replay(r,copy.deepcopy(r))['releaseClosed'])
        for key,value in [('intrinsicCode','changed call code bytes'),('requiredFrame',4),('allocationCost',0),('sourceAliases',[2,0,88,0]),('targetWords',[77,0]),('isMemoryCalls',False),('requiredFrame',True),('semanticPremisesDischarged',True)]:
            bad=copy.deepcopy(r);bad[key]=value
            with self.subTest(key=key),self.assertRaises(ValueError):m.exact_replay(r,bad)
            if key!='intrinsicCode':
                with self.assertRaises(ValueError):m.observation(self.raw(bad))
    def test_frames_missing_duplicate_truncated(self):
        raw=self.raw(self.row())
        for bad in [b'',raw+raw,raw[:-8],raw.replace(b'"schema": 1',b'"schema": 1, "schema": 1')]:
            with self.subTest(bad=bad[:20]),self.assertRaises(ValueError):m.observation(bad)
    def test_publication_and_query_scope(self):
        identity=m.publication_identity();self.assertEqual(identity['publication'],m.PUBLICATION)
        self.assertEqual(len(m.PUBLIC_REQUESTS)+len(m.PRIVATE),16)
        raw=m.query_bytes();self.assertIn(m.name_term('Solidity.Evm.Compiler.Compilation.memoryCalls').encode(),raw);self.assertIn(b'wrong_code_rejected',raw);self.assertIn(b'private_frame_rejected',raw)
        self.assertIn(b'KernelQuery.extract requests',raw)
if __name__=='__main__':unittest.main()
