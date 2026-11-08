#!/usr/bin/env python3
"""Exercise historical-ledger verification in a different output directory; no Lean.
python3 docs/audits/direction-tools/mutation/check_probe_history.py --out ORIGINAL_PROBE_DIR
"""
import argparse,json,subprocess,sys,tempfile
from pathlib import Path

def main():
 ap=argparse.ArgumentParser();ap.add_argument("--out",type=Path,required=True);a=ap.parse_args()
 scope=Path(__file__).resolve().parent;report=json.loads((scope/"lean-probes.json").read_text())
 ledger=json.loads((a.out/"attempts.json").read_text());n=report["total_elaborations"];assert n<10
 # Synthetic, deliberately non-executable future row belongs only to this
 # temporary regression fixture, never the real shared budget or run ledger.
 with tempfile.TemporaryDirectory(prefix="mutation-history-regression-") as tmp:
  path=Path(tmp);(path/"attempts.json").write_text(json.dumps(ledger[:n]+[{"synthetic_future_fixture":True}]))
  result=subprocess.run([sys.executable,str(scope/"verify_lean_probe.py"),"--out",str(path)],capture_output=True,text=True)
  assert result.returncode==0,result.stderr
  verified=json.loads(result.stdout);assert verified["verified_elaborations"]==n and verified["new_elaborations"]==0
 print(json.dumps({"historical_records_verified":n,"different_output_directory":True,"future_ledger_suffix_ignored":True,"new_elaborations":0},sort_keys=True))
if __name__=="__main__":main()
