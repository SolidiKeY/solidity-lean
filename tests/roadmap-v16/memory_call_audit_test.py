#!/usr/bin/env python3
"""Negative controls against the actual revision-bound memory-call observations."""
import copy,importlib.util,json,pathlib,sys,unittest
sys.dont_write_bytecode=True
ROOT=pathlib.Path(__file__).resolve().parents[2]
spec=importlib.util.spec_from_file_location('memory_call_audit',ROOT/'scripts/roadmap-v16-memory-call-audit.py')
m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
DATA=None;LOG=None;REPORT=None
class AuditTests(unittest.TestCase):
    def setUp(self):self.r=copy.deepcopy(REPORT)
    def rejected(self):
        with self.assertRaises(m.core.Invalid):m.validate_report(self.r,DATA,LOG)
    def test_live(self):m.validate_report(self.r,DATA,LOG)
    def test_wrong_revision(self):self.r['producerRevision']='0'*40;self.rejected()
    def test_wrong_head(self):self.r['head']=m.PRODUCER;self.rejected()
    def test_wrong_producer_bytes(self):self.r['producerHashes'][m.FILES[0]]='0'*64;self.rejected()
    def test_constructor_absent(self):self.r['constructor']='absent';self.rejected()
    def test_constructor_closed(self):self.r['constructorStatus']='closed';self.rejected()
    def test_lane_closed(self):self.r['laneComplete']=True;self.rejected()
    def test_stage_closed(self):self.r['stageStatus']['G49.01']='closed';self.rejected()
    def test_erased_input(self):self.r['openPremises'].pop(0);self.rejected()
    def test_fabricated_events(self):self.r['eventBoundary']='full G01 events';self.rejected()
    def test_absent_actual_statement(self):self.r['controls']['theorems'].pop();self.rejected()
    def test_changed_actual_statement(self):self.r['controls']['theorems'][0]['type']='PublicCorrectness';self.rejected()
    def test_assumed_public_correctness(self):self.r['controls']['theorems'][0]['typeConstants'].append('Solidity.Roadmap.PublicCorrectness');self.rejected()
    def test_undesired_axiom(self):self.r['controls']['theorems'][0]['axioms'].append('sorryAx');self.rejected()
    def test_missing_emitter(self):self.r['controls']['definitions']=[];self.rejected()
    def test_changed_scope_boundary(self):self.r['boundary']='all compiler correctness proved';self.rejected()
    def test_stale_script(self):self.r['auditScriptSha256']='0'*64;self.rejected()
if __name__=='__main__':
    DATA=json.loads(pathlib.Path(sys.argv[1]).read_text());LOG=pathlib.Path(sys.argv[2]);REPORT=json.loads(pathlib.Path(sys.argv[3]).read_text())
    unittest.main(argv=[sys.argv[0]],verbosity=2)
