#!/usr/bin/env python3
"""Generate the stdlib-only serializer probe; it must fail full-scope acceptance."""
import argparse,pathlib
p=argparse.ArgumentParser();p.add_argument("--output",type=pathlib.Path,required=True);a=p.parse_args()
root=pathlib.Path(__file__).resolve().parents[4]
source=(root/"tests/h62/item6/migrate-examples/InterfaceDump.lean").read_text()
assert source.count("import SolidityExamples\n")==1
source=source.replace("import SolidityExamples\n","")
controls='''run_cmd do
  let dotted := Name.str .anonymous "a.b"
  let nested := Name.str (Name.str .anonymous "a") "b"
  if nameJson dotted == nameJson nested then throwError "structural names collapsed"
  let natural := Name.num .anonymous 1
  let string := Name.str .anonymous "1"
  if nameJson natural == nameJson string then throwError "numeric/string components collapsed"
  let expression := mkConst ``Nat
  unless typeJson expression == typeJson (.mdata {} expression) do
    throwError "metadata normalization changed the expression"
end H62MigrateExamplesAudit'''
assert source.count("end H62MigrateExamplesAudit")==1
a.output.write_text(source.replace("end H62MigrateExamplesAudit",controls))
