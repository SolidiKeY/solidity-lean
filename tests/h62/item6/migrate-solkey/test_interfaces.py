#!/usr/bin/env python3
"""Negative controls for interface hashing; these do not replace Lean runs."""
import copy
import importlib.util
import json
from pathlib import Path
import unittest

ROOT=Path(__file__).resolve().parents[4]
SPEC=importlib.util.spec_from_file_location('interfaces',ROOT/'scripts/h62/item6/migrate-solkey/interfaces.py')
I=importlib.util.module_from_spec(SPEC); SPEC.loader.exec_module(I)


def entries():
    data=[{'name':m+'.example','module':m,'levelParams':[], 'typeExpr':'type',
           'valueExpr':'body','isTheorem':False,'kind':'definition'} for m in sorted(I.MODULES)]
    data += [{'name':n,'module':'Solidity.Solkey.Constructors','levelParams':[],
              'typeExpr':'statement','valueExpr':'proof','isTheorem':True,'kind':'theorem'} for n in sorted(I.THEOREMS)]
    return data


def log(data):
    return json.dumps(data)+'\n'+'\n'.join("'"+n+"' does not depend on any axioms" for n in sorted(I.THEOREMS))


class InterfaceControls(unittest.TestCase):
    def test_missing_coverage_and_duplicate_names(self):
        for data in [entries()[1:], entries()+[entries()[0]], entries()[:-1]]:
            with self.assertRaises(ValueError): I.normalize(log(data))

    def test_type_and_executable_definition_changes(self):
        original=I.normalize(log(entries()))
        for field in ['typeExpr','valueExpr']:
            changed=entries(); changed[0][field]='changed'
            self.assertEqual(I.compare(original,I.normalize(log(changed)))['status'],'INTERFACE_DRIFT')

    def test_proof_expression_changes_are_reported(self):
        original=I.normalize(log(entries())); changed=entries(); changed[-1]['valueExpr']='different proof'
        result=I.compare(original,I.normalize(log(changed)))
        self.assertEqual(result['status'],'FROZEN_INTERFACES_PASS')
        self.assertEqual(len(result['changed_proof_expressions']),1)

    def test_opaque_body_and_kind_drift(self):
        before=entries(); before[0]['kind']='opaque'
        original=I.normalize(log(before))
        changed=copy.deepcopy(before); changed[0]['valueExpr']='changed opaque body'
        self.assertEqual(I.compare(original,I.normalize(log(changed)))['status'],'INTERFACE_DRIFT')
        changed=copy.deepcopy(before); changed[0]['kind']='definition'
        self.assertEqual(I.compare(original,I.normalize(log(changed)))['status'],'INTERFACE_DRIFT')
        changed=copy.deepcopy(before); changed[0]['kind']='axiom'
        with self.assertRaises(ValueError): I.normalize(log(changed))

    def test_forbidden_or_missing_axiom_output(self):
        text=log(entries())
        name=sorted(I.THEOREMS)[0]
        text=text.replace("'"+name+"' does not depend on any axioms", "'"+name+"' depends on axioms: [sorryAx]")
        with self.assertRaises(ValueError): I.normalize(text)
        with self.assertRaises(ValueError): I.normalize(json.dumps(entries()))


if __name__=='__main__': unittest.main()
