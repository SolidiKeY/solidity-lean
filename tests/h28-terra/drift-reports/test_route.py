"""Guard lexical routing false positives, lost file rows and truncated corpus coverage.

These controls do not settle conflicting duplicate ownership IDs: that contract
choice is Q-H152-ROUTE-CONFLICT. Fixture owner records never assign real ownership.
"""
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import unittest

ROOT = Path(__file__).resolve().parents[3]
TOOL = ROOT / 'scripts/h28-terra/drift-reports/route.py'
BASE = '6f3eedf0788ee1f8a3bcf230558c712ecdca04d5'
OWNERS = [{'id':'P1','owner':'fixture-p1','metadata':{'candidate':True}},
          {'id':'G49.01','owner':'fixture-g49'},
          {'id':'A+B','owner':'fixture-literal'},
          {'id':'V07','owner':'fixture-v07'}]
BY_ID = {r['id']:r for r in OWNERS}


def expected(path, ids):
    return {'path':path,'ownerHints':[BY_ID[i] for i in sorted(ids)],
            'verdict':'lexical-hint-owner-review-required' if ids else 'unassigned-owner-review-required'}


def literal_token(text, token):
    # Independent literal-position oracle, not the producer's regular expression.
    def boundary(char): return char.isalnum() or char in '_-.'
    start = 0
    while True:
        index = text.find(token,start)
        if index < 0: return False
        end = index + len(token)
        if (index == 0 or not boundary(text[index-1])) and (end == len(text) or not boundary(text[end])):
            return True
        start = index + 1


class Routing(unittest.TestCase):
    def invoke(self, files, owners=OWNERS):
        data = {'files':files,'ownership':owners}
        proc = subprocess.run([sys.executable,'-B',str(TOOL)],input=json.dumps(data),
                              capture_output=True,text=True,timeout=30)
        self.assertEqual(proc.returncode,0,proc.stderr)
        self.assertEqual(proc.stderr,'')
        return json.loads(proc.stdout)

    def test_empty_and_unassigned_coverage(self):
        self.assertEqual(self.invoke([]),[])
        self.assertEqual(self.invoke([{'path':'Unknown.lean','text':'nothing linked'}]),
                         [expected('Unknown.lean',[])])
        self.assertEqual(self.invoke([{'path':'P1/Unknown.lean','text':'P1'}], owners=[]),
                         [expected('P1/Unknown.lean',[])])

    def test_path_and_raw_comment_or_string_tokens_are_lexical_only(self):
        files = [{'path':'V07/A.lean','text':'-- P1\nexample := "G49.01"'},
                 {'path':'G49.01.lean','text':'not a whole owner token'}]
        self.assertEqual(self.invoke(files),[expected('G49.01.lean',[]),expected('V07/A.lean',['G49.01','P1','V07'])])

    def test_nonlean_and_uppercase_suffixes_are_not_routed(self):
        files = [{'path':'a.sol','text':'P1'}, {'path':'b.md','text':'P1'},
                 {'path':'c.LEAN','text':'P1'}, {'path':'d.lean','text':'P1'}]
        self.assertEqual(self.invoke(files),[expected('d.lean',['P1'])])

    def test_exact_boundaries_prefixes_unicode_and_regex_metacharacters(self):
        negative = 'P10 xP1 _P1 P1_ P1.2 P1-suffix αP1 P1β G49X01 G49.010 G49.01-tail AAAB AAB'
        self.assertEqual(self.invoke([{'path':'A.lean','text':negative}]),[expected('A.lean',[])])
        positive = '(P1), [G49.01]; "A+B" /V07/'
        self.assertEqual(self.invoke([{'path':'A.lean','text':positive}]),[expected('A.lean',list(BY_ID))])

    def test_repeated_tokens_make_one_hint_per_identifier(self):
        self.assertEqual(self.invoke([{'path':'A.lean','text':'P1 P1 G49.01 G49.01'}]),
                         [expected('A.lean',['P1','G49.01'])])

    def test_duplicate_file_occurrences_are_not_discarded(self):
        files=[{'path':'A.lean','text':'P1'},{'path':'A.lean','text':'V07'}]
        self.assertEqual(self.invoke(files),[expected('A.lean',['P1']),expected('A.lean',['V07'])])

    def test_complete_payloads_and_deterministic_sort_order(self):
        files=[{'path':'z.lean','text':'P1'},{'path':'a.lean','text':'V07 P1 G49.01 A+B'}]
        self.assertEqual(self.invoke(files),[expected('a.lean',list(BY_ID)),expected('z.lean',['P1'])])
        command=[sys.executable,'-B',str(TOOL)];payload=json.dumps({'files':files,'ownership':OWNERS}).encode()
        self.assertEqual(subprocess.check_output(command,input=payload),subprocess.check_output(command,input=payload))

    def test_full_pinned_lean_corpus_against_literal_position_oracle(self):
        env={k:v for k,v in os.environ.items() if not k.startswith('GIT_')}
        env.update(GIT_NO_REPLACE_OBJECTS='1',GIT_NO_LAZY_FETCH='1',GIT_OPTIONAL_LOCKS='0')
        def git(*args,**kwargs):return subprocess.check_output(['git','--no-replace-objects',*args],cwd=ROOT,env=env,**kwargs)
        self.assertEqual(git('rev-parse',BASE+'^{tree}').decode().strip(),'114f3a4e901fc282cec56d9e210fcffb2776e0cd')
        entries=[]
        for raw in git('ls-tree','-rz','--full-tree',BASE).split(b'\0')[:-1]:
            header,path=raw.split(b'\t',1); mode,kind,oid=header.split()
            name=path.decode('utf-8',errors='surrogateescape')
            if name.endswith('.lean'):
                self.assertEqual(kind,b'blob');entries.append((name,oid.decode()))
        self.assertEqual(len(entries),4184)
        objects=list(dict.fromkeys(oid for _,oid in entries))
        batch=git('cat-file','--batch',input=('\n'.join(objects)+'\n').encode())
        blobs={};offset=0
        for wanted in objects:
            end=batch.index(b'\n',offset);oid,kind,length=batch[offset:end].split()
            self.assertEqual((oid.decode(),kind),(wanted,b'blob'))
            offset=end+1;size=int(length);blobs[wanted]=batch[offset:offset+size].decode('utf-8',errors='replace')
            offset+=size;self.assertEqual(batch[offset:offset+1],b'\n');offset+=1
        self.assertEqual(offset,len(batch))
        files=[{'path':name,'text':blobs[oid]} for name,oid in entries]
        actual=self.invoke(files)
        self.assertEqual(len(actual),4184)
        wanted=[]
        for file in sorted(files,key=lambda f:f['path']):
            text=file['path']+'\n'+file['text']
            wanted.append(expected(file['path'],[i for i in BY_ID if literal_token(text,i)]))
        self.assertEqual(actual,wanted)
        self.assertEqual(hashlib.sha256(TOOL.read_bytes()).hexdigest(),
                         'f46f0229988885ffd21047a42ca9ae93727ae4af9bad225b63c71aaa76278f27')


if __name__=='__main__':unittest.main(verbosity=2)
