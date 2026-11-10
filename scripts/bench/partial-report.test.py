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
    return {'rows':[{'input':identity,'state':state,'attempts':[{'wallMs':wall,'maxIndividualProcessRssKiB':rss}]}, {'input':dict(identity,sourceId=2),'state':'pending','attempts':[]}],'attemptFinished':False}
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

if __name__=='__main__':unittest.main()
