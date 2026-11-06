"""Shared read-only inventory logic for the numeric-literal acceptance gate."""
import hashlib,json,os,pathlib,re,subprocess
ROOT=pathlib.Path(__file__).resolve().parents[2]
FOLDER=ROOT/'tests/sol-numeric-literals'
BASE='6f3eedf0788ee1f8a3bcf230558c712ecdca04d5'
ADOPTED_MASTER='3883c64ef750dd49acdb7d83adcdf0f101d42c6c'
PREFIX='Solidity.Frontend.NumericLiteralProofs.'

def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()
def git(*args):return subprocess.check_output(['git',*args],cwd=ROOT,text=True).strip()
def blank_lean(s):
 out=list(s);i=0;depth=0
 while i<len(s):
  if depth:
   if s.startswith('/-',i):out[i:i+2]='  ';depth+=1;i+=2
   elif s.startswith('-/',i):out[i:i+2]='  ';depth-=1;i+=2
   else:
    if s[i]!='\n':out[i]=' '
    i+=1
  elif s.startswith('/-',i):out[i:i+2]='  ';depth=1;i+=2
  elif s.startswith('--',i):
   while i<len(s) and s[i]!='\n':out[i]=' ';i+=1
  elif s[i]=='"':
   out[i]=' ';i+=1
   while i<len(s):
    ch=s[i];out[i]=' ';i+=1
    if ch=='\\' and i<len(s):out[i]=' ';i+=1
    elif ch=='"':break
  else:i+=1
 return ''.join(out)

def source_snapshot():
 modules=[]
 for path in sorted((ROOT/'Solidity/Frontend/NumericLiteralProofs').rglob('*.lean')):
  rel=path.relative_to(ROOT).as_posix();text=path.read_text();clean=blank_lean(text)
  matches=list(re.finditer(r'^(inductive|structure|abbrev|def|theorem|opaque|instance|class)\s+([\w.]+)',clean,re.M))
  authored=[]
  for k,m in enumerate(matches):
   end=matches[k+1].start() if k+1<len(matches) else len(text)
   block=text[m.start():end];header=block if m[1] in ('inductive','structure','class') else block.split(':=',1)[0]
   authored.append(dict(name=PREFIX+m[2],kind=m[1],signature_source=header.strip()))
  modules.append(dict(path=rel,name=rel[:-5].replace('/','.'),sha256=sha(path),imports=re.findall(r'^import ([\w.]+)',clean,re.M),authored=authored))
 return modules

def normalized_inventory(rows):
 out=[]
 for row in rows:
  row=dict(row);row['axioms']=sorted(row['axioms']);out.append(row)
 return sorted(out,key=lambda r:r['name'])

CONSTRUCTOR_CONTROLS={
'Tail.nil':'control_tail_nil','Tail.digit':'control_tail_digit','Tail.separated':'control_tail_separated','Tail.other':'control_tail_other','Tail.finalUnderscore':'control_tail_final','Tail.badUnderscore':'control_tail_bad',
'Digits.first':'control_digits','NoDigits.nil':'control_nodigits_nil','NoDigits.other':'control_nodigits_other',
'IntegerPart.absent':'control_integer_absent','IntegerPart.present':'control_integer_present',
'FractionPart.nil':'control_fraction_nil','FractionPart.absent':'control_fraction_absent','FractionPart.present':'control_fraction_present',
'Exponent.absent':'control_exponent_absent','Exponent.unsigned':'control_exponent_unsigned','Exponent.negative':'control_exponent_negative',
'Decimal.mk':'control_decimal','HexDigits.single':'control_hex_single','HexDigits.adjacent':'control_hex_adjacent','HexDigits.separated':'control_hex_separated','Hexadecimal.mk':'control_hexadecimal',
'Tail.below.nil':'control_tail_below_nil','Tail.below.digit':'control_tail_below_digit','Tail.below.separated':'control_tail_below_separated','Tail.below.other':'control_tail_below_other','Tail.below.finalUnderscore':'control_tail_below_final','Tail.below.badUnderscore':'control_tail_below_bad',
'HexDigits.below.single':'control_hex_below_single','HexDigits.below.adjacent':'control_hex_below_adjacent','HexDigits.below.separated':'control_hex_below_separated',
'FixtureObservation.mk':'fixture_row_control'}

REQUIRED_THEOREMS=['tail_iff','digits_iff','hex_digits_iff','decimal_iff','hexadecimal_iff','digitsVal_append','decimal_fold','decimal_decode_mantissa','decimal_decode_value','hexVal_lt16','toFin16_value','hex_fold','hexadecimal_decode_value','decNumber_erasure','hexNumber_erasure','classify_numeric','decimal_trailing_underscore_refused','decimal_doubled_underscore_refused','decimal_leading_underscore_refused','decimal_bad_underscore_follower_refused','decimal_exponent_underscore_refused','decimal_negative_exponent_underscore_refused','decimal_plus_exponent_refused','octal_refused','missing_fraction_refused','missing_exponent_refused','missing_negative_exponent_refused','hex_doubled_underscore_refused','hex_trailing_underscore_refused','hex_leading_underscore_refused','hex_invalid_byte_refused','empty_hex_number','digits1_consumption_range','numberSpan_reprint','lex_glued_digit','lex_glued_dot','lex_numeric_range','denomination_separation','scanner_controls_pass','checksum_controls','checksum_length_controls','fixture_observations_pass']

def controls():
 text=(ROOT/'Solidity/Frontend/NumericLiteralProofs/Controls.lean').read_text()
 return re.findall(r'^\s*\("([^"]+)",',text,re.M)

def case_families():
 ids=controls();families=[]
 for family,prefix in [('decimal digit tail','tail.'),('mandatory first digit','digits.'),('decimal number','decimal.'),('hex digits and number','hex.'),('source token boundaries','source.'),('Yul numeric boundaries','yul.'),('numeric span arms','span.'),('source ranges','range.')]:
  families.append(dict(family=family,controls=[x for x in ids if x.startswith(prefix)]))
 families += [dict(family='checksum length/case/nibble boundaries',theorems=['checksum_controls','checksum_length_controls','eip55_other_length']),dict(family='all fixed compiler spellings and lexical/compiler stage differences',fixtures=[r['id'] for r in json.loads((FOLDER/'spellings.json').read_text())],theorems=['fixture_observations_pass']),dict(family='all word-table prefix cases',prefix_proofs=439,theorems=['solWordTable_no_num'])]
 return families

# H26 assigns SOL-NL; coordinator H10/H12 idle-lane rebalance assigns G25-CONST-1105.
# permitted() is the exact union of those two authorized exclusive scopes.
def permitted(path):return path.startswith(('Solidity/Frontend/NumericLiteralProofs/','tests/sol-numeric-literals/','Solidity/Backend/PrimitivePackets/Constants/','tests/primitive-packets-1105/Constants/')) or path in ('scripts/check-sol-numeric-literals.py','docs/feature-work/numeric-literal-proofs.md','docs/feature-work/primitive-packets-1105-Constants.md')
