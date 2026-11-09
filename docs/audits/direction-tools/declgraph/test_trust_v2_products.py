#!/usr/bin/env python3
"""Failed-product quarantine, exact success artifacts and log-path fixtures."""
import json,pathlib,runpy,tempfile
M=runpy.run_path(str(pathlib.Path(__file__).with_name('warm_trust_v2.py')))
def reject(fn):
 try:fn()
 except AssertionError:return
 raise AssertionError('Invalid warm capture accepted')
def main():
 with tempfile.TemporaryDirectory() as d:
  root=pathlib.Path(d);view=root/'view';rel=pathlib.Path(M['MODULE'].replace('.','/'));o=view/rel.with_suffix('.olean');i=view/rel.with_suffix('.ilean');o.parent.mkdir(parents=True);o.write_text('artifact');i.write_text(json.dumps({'module':M['MODULE']}));products={str(f):M['SHA'](f) for f in (o,i)}
  M['verify_products'](view,0,products)
  for bad in ({},{str(o):products[str(o)]},dict(products,extra='wrong')):reject(lambda:M['verify_products'](view,0,bad))
  i.write_text('{"module":"Wrong"}');reject(lambda:M['verify_products'](view,0,{str(f):M['SHA'](f) for f in (o,i)}));i.unlink();o.unlink()
  M['verify_products'](view,124,{})
  o.write_text('partial');reject(lambda:M['verify_products'](view,124,{}));o.unlink()
  reject(lambda:M['verify_products'](view,124,products))
  source=root/'source';out=root/'out';logs=root/'logs';M['safe_paths'](source,view,out,logs)
  for bad in (source/'logs',view/'logs',out/'logs',root):reject(lambda:M['safe_paths'](source,view,out,bad))
 print('TRUST_V2_PRODUCTS_PASS exact_success module_identity failed_absence safe_log_paths')
if __name__=='__main__':main()
