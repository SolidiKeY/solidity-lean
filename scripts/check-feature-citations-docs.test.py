#!/usr/bin/env python3
"""Negative control for truthful progress documentation after citation loss."""
import copy
import importlib.util
import json
from pathlib import Path
import unittest
ROOT=Path(__file__).resolve().parents[1]
s=importlib.util.spec_from_file_location("citation_docs",ROOT/"scripts/check-feature-citations-docs.py")
docs=importlib.util.module_from_spec(s);s.loader.exec_module(docs)
class DocumentationMetric(unittest.TestCase):
    def test_uncited_partial_is_reported_truthfully(self):
        data=json.loads((ROOT/"docs/solidity-features.json").read_text())
        partials=[r for r in data["features"] if r["current"]=="partial"]
        before=sum(bool(r["theorems"]) for r in partials)
        row=next(r for r in partials if r["theorems"])
        row["theorems"]=[]
        _,metric=docs.generated(data)
        self.assertIn(f"cited partial rows: {before-1}/{len(partials)}",metric)
        self.assertIn("partial=1",metric)
        self.assertNotIn(f"all {len(partials)} partial rows are cited",metric)
if __name__=="__main__":unittest.main(verbosity=2)
