#!/usr/bin/env python3
"""Fetch published timing citations (not measurements); stdlib only.
python3 docs/audits/direction-tools/timing/citations.py --out DIR
An unavailable source remains an explicit gap, never an invented figure.
"""
import argparse,hashlib,json,pathlib,re,urllib.error,urllib.request
HERE=pathlib.Path(__file__).resolve().parent
SOURCES={
 'CakeML': 'https://raw.githubusercontent.com/CakeML/cakeml/b3e6ea34ca1aed91a57703a30549260ce6f6448e/build-instructions.sh',
 'CompCert': 'https://compcert.org/man/manual002.html',
}
def main():
    ap=argparse.ArgumentParser(); ap.add_argument('--out',type=pathlib.Path,required=True); args=ap.parse_args(); rows=[]
    for project,url in SOURCES.items():
        row={'project':project,'url':url,'kind':'cited, not measured','seconds':None,'comparable_to_serial_module_elaboration':False}
        try:
            raw=urllib.request.urlopen(url,timeout=25).read(); text=raw.decode(errors='replace'); row['source_sha256']=hashlib.sha256(raw).hexdigest()
            if project=='CakeML':
                lines=text.splitlines(); chosen=[(i+1,l) for i,l in enumerate(lines) if re.search(r'full build|~\d+ hours|much RAM',l)]
                row['excerpts']=[{'line':i,'text':l} for i,l in chosen]
                m=re.search(r'~(\d+) hours',text)
                if m: row['seconds']=int(m[1])*3600
                row['boundary']='full CakeML including bootstrapped compiler; parallelism, CPU and HOL revision unspecified; not a matched check-only timing'
            else:
                row['excerpts']=[{'text':m.group(0)} for m in re.finditer(r'.{0,100}(?:minutes|hours).{0,100}',text,re.I)]
                row['boundary']='manual installation/build duration; do not normalize without matching workload and resources'
        except (urllib.error.URLError,TimeoutError) as e:
            row['status']='unavailable'; row['error']=str(e); row['settling_measurement']='retrieve a published proof-build timing with source revision, hardware and workload boundary'
        if project=='CompCert':
            cited=json.loads((HERE/'cited-inputs.json').read_text())[project]
            denied=row.get('status')=='unavailable'
            row.update(cited); row['status']='cited-public-web-extract' if denied else 'cited-source-retrieved'
            if denied: row['shell_fetch_error']=row.pop('error')
            row['seconds']=int(re.search(r'about (\d+) minutes',cited['excerpt'])[1])*60
            row.pop('settling_measurement',None); row.pop('excerpts',None)
        rows.append(row)
    args.out.mkdir(parents=True,exist_ok=True); (args.out/'published-times.json').write_text(json.dumps(rows,indent=2)+'\n'); print(json.dumps(rows,indent=2))
if __name__=='__main__': main()
