"""Guard percentile denominators, overlap policy and unavailable timing/RSS data."""
import importlib.util,json,pathlib,tempfile,unittest
spec=importlib.util.spec_from_file_location('report',pathlib.Path(__file__).with_name('partial-report.py'))
m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
class ReportTests(unittest.TestCase):
 def test_nearest_rank_and_constant_size(self):
  self.assertIsNone(m.stats([]));self.assertEqual(m.stats([0,10,30,20]),{'count':4,'p50':10,'p95':30,'max':30})
  self.assertIsNone(m.correlation([{'statements':2,'wallMs':x} for x in [0,1,2]])['pearsonR'])
 def test_failed_attempts_unknown_rss_overlap_and_placeholder_timers(self):
  with tempfile.TemporaryDirectory() as d:
   p=pathlib.Path(d)
   identity={'source':'/a.sol','sourceHash':'hash','contract':'C','sourceId':1,'signature':'f()'}
   def save(name,value):
    path=p/name;path.write_text(json.dumps(value));return str(path)
   sizes=save('sizes.json',{'results':[dict(identity,staticSize={'statements':3})]})
   def report(wall,state,rss):
    return {'rows':[{'input':identity,'state':state,'attempts':[{'wallMs':wall,'maxIndividualProcessRssKiB':rss,'attemptFinished':True,'results':[dict(identity,status='proved')],'errors':[]}]}, {'input':dict(identity,sourceId=2),'state':'pending','attempts':[]}],'attemptFinished':False}
   a=save('a.json',report(10,'passed',None));b=save('b.json',report(20,'failed',123))
   rows=[{'input':dict(identity,sourceId=i),'observations':[dict(identity,sourceId=i,status=status,elapsedMs=value)],'functionReportedElapsedMs':value} for i,(status,value) in enumerate([('notRun',0),('excluded',0),('pending',0),('proved',5),('future',1)])]
   batch=save('batch.json',{'rows':rows,'attemptFinished':False,'timerScope':'check only','apiWallMs':None})
   x=m.summarize([('a',a,sizes),('b',b,sizes)],batch,sizes)
   self.assertFalse(x['sourceToVerdictBaseline']);self.assertFalse(x['suiteComplete'])
   self.assertEqual(len(x['groups']),2);self.assertEqual(x['groups'][0]['states']['pending'],1)
   self.assertIsNone(x['groups'][0]['maxIndividualProcessRssKiB'])
   self.assertEqual(x['groups'][1]['wallMsFailedFunctionTotals']['count'],1)
   self.assertEqual(len(x['top10IsolatedFunctions']),1);self.assertEqual(x['top10IsolatedFunctions'][0]['wallMs'],20)
   self.assertEqual(x['batchChecks']['reportedCheckElapsedMs']['count'],2)
   self.assertEqual(x['batchChecks']['reportedCheckElapsedMs']['p50'],0)
   self.assertIsNone(x['batchChecks']['perFunctionSourceToVerdictWallMs'])
   raw=json.loads(pathlib.Path(batch).read_text())
   proved=raw['rows'][3]
   for rows in [[proved,proved], [dict(proved,observations=[dict(proved['observations'][0],sourceHash='wrong')])], [dict(proved,functionReportedElapsedMs=6)]]:
    bad=save('bad.json',dict(raw,rows=rows))
    self.assertIsNone(m.summarize([],bad)['batchChecks']['reportedCheckElapsedMs'])
   bad=save('drift.json',dict(raw,errors=[{'stage':'identity','reason':'HEAD changed'}]))
   check=m.summarize([],bad)['batchChecks']
   self.assertFalse(check['provenance']['statisticsAllowed']);self.assertIsNone(check['reportedCheckElapsedMs'])
   invalid=save('invalid.json',dict(report(10,'passed',100),errors=[{'stage':'runner','reason':'compiler changed'}]))
   group=m.summarize([('bad',invalid,sizes)])['groups'][0]
   self.assertIsNone(group['wallMsAllCompletedFunctionTotals'])
   invalid_sizes=save('bad-sizes.json',{'results':[dict(identity,staticSize={'statements':3})], 'errors':[{'stage':'identity'}]})
   point=m.summarize([('bad-size',a,invalid_sizes)])['groups'][0]
   self.assertEqual(point['wallMsAllCompletedFunctionTotals']['max'],10)
   self.assertEqual(point['costVsStaticStatements']['count'],0)
   self.assertFalse(point['sizesProvenance']['statisticsAllowed'])
   ambiguous=save('ambiguous.json',{'results':[dict(identity,staticSize={'statements':3})]*2})
   with self.assertRaises(ValueError):m.summarize([('bad',a,ambiguous)])

 # Guard landing review: failed wrong-identity attempts must never enter statistics.
 def test_attempt_identity_errors_and_returned_mismatches_are_excluded(self):
  with tempfile.TemporaryDirectory() as d:
   p=pathlib.Path(d);expected={'source':'/a.sol','sourceHash':'hash','contract':'C','sourceId':1,'signature':'f()'}
   sizes=p/'sizes.json';sizes.write_text(json.dumps({'results':[dict(expected,staticSize={'statements':3})]}))
   valid={'wallMs':10,'maxIndividualProcessRssKiB':20,'attemptFinished':True,'results':[dict(expected,status='proved')],'errors':[]}
   bads=[dict(valid,errors=[{'stage':stage,'reason':'sourceHash mismatch'}]) for stage in ['identity','source-identity','selection','setup','report','verification']]
   bads += [dict(valid,results=[dict(expected,status='proved',**change)]) for change in [{'sourceHash':'wrong'},{'sourceId':2},{'contract':'Other'},{'source':'/other.sol'},{'sourceId':True},{'verification':'direct'}]]
   bads += [dict(valid,results=[]),dict(valid,results=[dict(expected,status='proved'),dict(expected,status='proved')]),dict(valid,attemptFinished=False)]
   for bad in bads:
    bad=dict(bad,wallMs=123,maxIndividualProcessRssKiB=456)
    for attempts in [[bad],[valid,bad]]:
     receipt={'rows':[{'input':expected,'state':'failed','attempts':attempts}], 'attemptFinished':True,'errors':[]}
     report=p/'report.json';report.write_text(json.dumps(receipt))
     x=m.summarize([('bad',str(report),str(sizes))]);g=x['groups'][0]
     self.assertFalse(g['provenance']['statisticsAllowed']);self.assertEqual(g['provenance']['excludedComparableRows'],1)
     self.assertEqual(g['states'],{'failed':1});self.assertIsNone(g['wallMsAllCompletedFunctionTotals'])
     self.assertIsNone(g['maxIndividualProcessRssKiB']);self.assertEqual(g['costVsStaticStatements']['count'],0)
     self.assertEqual(x['top10IsolatedFunctions'],[])
     self.assertEqual(g['rowProvenance'][0]['attempts'][-1]['errors'],bad['errors'])
 def test_valid_failed_attempts_and_valid_rows_survive_invalid_neighbor(self):
  with tempfile.TemporaryDirectory() as d:
   p=pathlib.Path(d);expected={'source':'/a.sol','sourceHash':'hash','contract':'C','sourceId':1,'signature':'f()'}
   other=dict(expected,sourceId=2,signature='g()')
   bad={'wallMs':123,'maxIndividualProcessRssKiB':456,'attemptFinished':True,'results':[expected],'errors':[{'stage':'identity','reason':'sourceHash mismatch'}]}
   good={'wallMs':7,'maxIndividualProcessRssKiB':8,'attemptFinished':True,'results':[dict(other,status='pending')],'errors':[{'stage':'process','reason':'CLI exited 1'},{'stage':'verification','reason':'pending'}]}
   rows=[{'input':expected,'state':'failed','attempts':[bad]}, {'input':other,'state':'failed','attempts':[good,good]}]
   report=p/'report.json';report.write_text(json.dumps({'rows':rows,'attemptFinished':True,'errors':[]}))
   sizes=p/'sizes.json';sizes.write_text(json.dumps({'results':[dict(r,staticSize={'statements':3}) for r in [expected,other]]}))
   x=m.summarize([('mixed',str(report),str(sizes))]);g=x['groups'][0]
   self.assertEqual(g['states'],{'failed':2});self.assertEqual(g['provenance']['comparableRowsIncluded'],1)
   self.assertEqual(g['provenance']['excludedComparableRows'],1)
   self.assertEqual(g['wallMsAllCompletedFunctionTotals'],{'count':1,'p50':14,'p95':14,'max':14})
   self.assertEqual(g['maxIndividualProcessRssKiB']['max'],8)
   self.assertEqual(len(x['top10IsolatedFunctions']),1);self.assertEqual(x['top10IsolatedFunctions'][0]['function'],'g()')

 def test_malformed_matching_ids_and_unfinished_row_evidence(self):
  with tempfile.TemporaryDirectory() as d:
   p=pathlib.Path(d)
   for value in [None,True,False,'','1',1.5,-1]:
    expected={'source':'/a.sol','sourceHash':'hash','contract':'C','sourceId':value,'signature':'f()'}
    attempt={'wallMs':123,'maxIndividualProcessRssKiB':456,'attemptFinished':True,'results':[dict(expected,status='proved')],'errors':[]}
    sizes=p/'sizes.json';sizes.write_text(json.dumps({'results':[dict(expected,staticSize={'statements':3})]}))
    report=p/'report.json';report.write_text(json.dumps({'rows':[{'input':expected,'state':'passed','attempts':[attempt]}],'attemptFinished':True,'errors':[]}))
    g=m.summarize([('domain',str(report),str(sizes))])['groups'][0]
    self.assertEqual(g['provenance']['statisticsAllowed'],type(value) is int)
   expected=dict(expected,sourceId=1)
   attempt=dict(attempt,errors=[{'stage':'identity','reason':'sourceHash mismatch'}],results=[dict(expected,status='proved')])
   report.write_text(json.dumps({'rows':[{'input':expected,'state':'pending','attempts':[attempt]}],'attemptFinished':False,'errors':[]}))
   g=m.summarize([('unfinished',str(report),str(sizes))])['groups'][0]
   self.assertEqual(g['states'],{'pending':1});self.assertIsNone(g['wallMsAllCompletedFunctionTotals'])
   self.assertEqual(g['provenance']['rowsNotCompleted'],1)
   self.assertEqual(g['rowProvenance'][0]['attempts'][0]['errors'],attempt['errors'])
   self.assertEqual(g['rowProvenance'][0]['attempts'][0]['returnedIdentities'][0]['sourceId'],1)

if __name__=='__main__':unittest.main()
