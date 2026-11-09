#!/usr/bin/env python3
"""Fail-closed controls for H279 versioned audit input; no Lean invocation."""
import importlib.util, json, pathlib, sys, unittest
from unittest.mock import patch
sys.dont_write_bytecode=True
ROOT=pathlib.Path(__file__).resolve().parents[2]
sp=importlib.util.spec_from_file_location("compat",ROOT/"scripts/roadmap-v16-mixed-compatibility-v2.py")
m=importlib.util.module_from_spec(sp);sp.loader.exec_module(m)
class CompatibilityTests(unittest.TestCase):
 def setUp(self): self.d=json.loads((ROOT/m.DESCRIPTOR).read_text())
 def rejected(self):
  with self.assertRaises(m.core.Invalid):m.validate_descriptor(self.d)
 def test_actual_descriptor(self):
  policy=m.validate_descriptor(self.d);old=json.loads((ROOT/m.POLICY).read_text())
  for field in old.keys()-{"axiomPins","dependencyPins"}:self.assertEqual(policy[field],old[field])
 def test_changed_baseline(self):self.d["baselinePolicySha256"]="0"*64;self.rejected()
 def test_changed_original_ledger(self):self.d["originalLedgerSha256"]="0"*64;self.rejected()
 def test_changed_checked_ledger(self):self.d["checkedLedgerSha256"]="0"*64;self.rejected()
 def test_changed_production_tree(self):self.d["productionLeanTreeSha256"]="0"*64;self.rejected()
 def test_wrong_production_revision(self):self.d["productionRevision"]=m.PUBLIC;self.rejected()
 def test_changed_lake_config(self):self.d["lakefileSha256"]="0"*64;self.rejected()
 def test_abbreviated_revision(self):self.d["productionRevision"]=self.d["productionRevision"][:12];self.rejected()
 def test_symbolic_revision(self):self.d["productionRevision"]="HEAD";self.rejected()
 def test_actual_lake_file_binding(self):
  original=pathlib.Path.read_bytes
  def altered(path):
   data=original(path)
   return data+b"\n# changed runtime configuration\n" if path==ROOT/"lakefile.toml" else data
  with patch.object(pathlib.Path,"read_bytes",altered):
   with self.assertRaisesRegex(m.core.Invalid,"checked Lake configuration drift"):m.capture_binding()
 def test_missing_extractor(self):self.d["extractors"].pop(next(iter(self.d["extractors"])));self.rejected()
 def test_missing_producer(self):self.d["producers"].pop(next(iter(self.d["producers"])));self.rejected()
 def test_wrong_checked_producer(self):next(iter(self.d["producers"].values()))["checked"]="0"*64;self.rejected()
 def test_wrong_original_producer(self):next(iter(self.d["producers"].values()))["original"]="0"*64;self.rejected()
 def test_wrong_relocation(self):self.d["privateModuleRelocations"][next(iter(self.d["privateModuleRelocations"]))]="arbitrary";self.rejected()
 def test_wrong_previous_pin(self):next(iter(self.d["pinDelta"]["dependencyPins"].values()))["before"]=["invented"];self.rejected()
 def test_sorry_axiom(self):next(iter(self.d["pinDelta"]["axiomPins"].values()))["after"]=["sorryAx"];self.rejected()
 def test_native_shortcut(self):next(iter(self.d["pinDelta"]["dependencyPins"].values()))["after"]=["Lean.ofReduceBool"];self.rejected()
 def test_public_statement_override(self):self.d["theorems"]={};self.rejected()
 def test_deletion_waiver(self):next(iter(self.d["pinDelta"]["dependencyPins"].values()))["after"]=None;self.rejected()
if __name__=="__main__":unittest.main()
