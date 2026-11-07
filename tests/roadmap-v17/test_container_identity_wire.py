#!/usr/bin/env python3
"""Bounded host-only wire controls; no container or native proof execution."""
import copy
import json
from pathlib import Path
import types
import unittest
path=Path(__file__).with_name('test_container_identity.py')
f=types.ModuleType('transport_fixtures');f.__file__=str(path)
exec(compile(path.read_bytes(),str(path),'exec'),f.__dict__)
t=f.t

def args():
    request,reply,*rest=f.fixture()
    a=t.canonical(request);b=t.canonical(reply)
    return [f.m,a,t.digest(a),b,t.digest(b),*rest]
class WireTests(unittest.TestCase):
 def test_positive_synthetic_byte_consistency_only(self):
    result=t.consume_reply(*args())
    self.assertTrue(result['bytePinsConsistent']);self.assertTrue(result['consistencyOnly'])
    for key in ['liveTransportAuthenticated','kernelValidated','semanticPremisesDischarged','releaseClosed','selectorsAuthenticated','replayVerified','toolExecutionAuthenticated']:self.assertIs(result[key],False)
 def test_corrupt_and_wrong_pins(self):
    for index,value in [(1,b'{}'),(2,'0'*64),(3,b'{}'),(4,'0'*64)]:
     a=args();a[index]=value
     with self.subTest(index=index),self.assertRaises(ValueError):t.consume_reply(*a)
 def test_truncated_and_duplicate_json(self):
    for raw in [b'{',b'{"schema":1,"schema":1}',b'{"a":NaN}',b'null',b'[]']:
     a=args();a[3]=raw;a[4]=t.digest(raw)
     with self.subTest(raw=raw),self.assertRaises((ValueError,KeyError,TypeError)):t.consume_reply(*a)
 def test_size_and_shape_bounds(self):
    for raw,limit in [(b'',16),(b' '*17,16)]:
     with self.assertRaises(ValueError):t.decode_pinned(raw,t.digest(raw),limit)
    with self.assertRaises(ValueError):t.decode_pinned('not bytes','0'*64,16)
 def test_nonfinite_exponent_even_in_unused_nested_field(self):
    for number in [b'1e999',b'-1e999']:
     a=args();a[3]=a[3][:-1]+b',"extra":{"nested":['+number+b']}}';a[4]=t.digest(a[3])
     with self.subTest(number=number),self.assertRaises(ValueError):t.consume_reply(*a)
    for limit in [True,-1,0,t.MAX_MESSAGE+1]:
     with self.subTest(limit=limit),self.assertRaises(ValueError):t.decode_pinned(b'{}',t.digest(b'{}'),limit)
 def test_wrong_request_source_and_revision(self):
    for key,value in [('nonce','0'*32),('observerSha256','0'*64),('transportSha256','0'*64),('binding',dict(consumerHead='0'*40,sourceToolchainKey='0'*64))]:
     a=args();request=json.loads(a[1]);request[key]=value;a[1]=t.canonical(request);a[2]=t.digest(a[1])
     with self.subTest(key=key),self.assertRaises(ValueError):t.consume_reply(*a)
 def test_contradictory_success_flags(self):
    for key in ['liveTransportAuthenticated','selectorsAuthenticated','replayVerified','runtimeAuthenticated','toolExecutionAuthenticated','kernelValidated','releaseClosed']:
     a=args();reply=json.loads(a[3]);reply[key]=True;a[3]=t.canonical(reply);a[4]=t.digest(a[3])
     with self.subTest(key=key),self.assertRaises(ValueError):t.consume_reply(*a)
 def test_changed_cap_still_fails_even_with_matching_wire_pins(self):
    a=args();reply=json.loads(a[3]);reply['observedCaps']['memory.max']='max';a[3]=t.canonical(reply);a[4]=t.digest(a[3])
    with self.assertRaises(ValueError):t.consume_reply(*a)
 def test_actual_failed_capture_cannot_be_a_reply(self):
    source=Path(__file__).with_name('container-identity-refusal.json');raw=source.read_bytes()
    self.assertEqual(t.digest(raw),'c0fad5ad8d4876240b66474d8f78ba81ef016f3325f00f7a74d947786bda1478')
    self.assertEqual(json.loads(raw)['outcome'],'NONPASS')
    a=args();a[3]=raw;a[4]=t.digest(raw)
    with self.assertRaises(ValueError):t.consume_reply(*a)
 def test_missing_phase_and_observation(self):
    for key in ['initAfter','rows','requestSha256','observedCaps']:
     a=args();reply=json.loads(a[3]);del reply[key];a[3]=t.canonical(reply);a[4]=t.digest(a[3])
     with self.subTest(key=key),self.assertRaises((ValueError,KeyError)):t.consume_reply(*a)
if __name__=='__main__':unittest.main()
