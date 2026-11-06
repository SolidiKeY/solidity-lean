export const controls = [
  ['memoryguard-dynamic', 'object "A" { code { let n := calldatasize() let p := memoryguard(n) pop(p) } }'],
  ['datasize-dynamic', 'object "A" { code { let n := calldatasize() let p := datasize(n) pop(p) } }'],
  ['wrong-datacopy-arity', 'object "A" { code { datacopy(0, 0) } }'],
  ['loadimmutable-dynamic', 'object "A" { code { let n := calldatasize() let p := loadimmutable(n) pop(p) } }'],
  ['unknown-builtin', 'object "A" { code { vt1_unknown(0) } }'],
  ['malformed-object', 'object "A" { code { stop() }'],
];
export const expected = {
  'memoryguard-dynamic':['TypeError','Function expects direct literals as arguments.'],
  'datasize-dynamic':['TypeError','Function expects direct literals as arguments.'],
  'wrong-datacopy-arity':['TypeError','Function "datacopy" expects 3 arguments but got 2.'],
  'loadimmutable-dynamic':['TypeError','Function expects direct literals as arguments.'],
  'unknown-builtin':['DeclarationError','Function "vt1_unknown" not found.'],
  'malformed-object':['ParserError','Expected keyword "data" or "object" or "}".'],
};
