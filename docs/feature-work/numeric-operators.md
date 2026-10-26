# Resolved operator aliases

User-defined operators (`using {f as +} for T global`) on scalar UDVTs. The
numeric-operators group is otherwise incomplete.

## Supported

- solc records the resolved pure free function in the `function` field of a
  `UnaryOperation`/`BinaryOperation`. The reader checks that identity against
  the declaration table and emits a direct call to the unique
  `solcFunction<ID>` helper. It never resolves by name and never falls back to
  the builtin. All sixteen signatures: unary `-`, `~`; binary `&`, `|`, `^`,
  `+`, `/`, `%`, `*`, `-`, `==`, `>`, `>=`, `<`, `<=`, `!=`.
- `operatorAlias?` (`Frontend/SolcJson/Body.lean`) validates the annotation,
  positive identities, a pure free definition, arity, the UDVT declaration,
  identical nominal operand identities and the result (bool for comparisons,
  the same UDVT otherwise). Admission calls the same validator, records
  `operatorAliases` and adds the aliases to the call graph, so an alias body's
  features and callees are scanned.
- A call elaborates to the ordinary `Stmt.call`. Aliased operands are captured
  left to right in both pipelines; builtin binary operations keep the
  pipeline's order. Calls stay inside lazy boolean and conditional branches,
  the callee keeps its own checked/unchecked body, and a discarded result still
  runs the call. `pureExpr` treats an alias as a call.
- `hoistArgs` holds an earlier non-simple argument before hoisting a later
  one, so a later cast, bounds check or narrow/modular guard cannot fail first.
  Captures keep byte/address/enum/function metadata and width.
- Scalar UDVTs over narrow integers, fixed bytes, bool, address and payable
  address. Entry bounds use the underlying type.

Regressions: `tests/operators-0.8.38/OperatorAliases.sol` (meanings that
disagree with the builtins), `Examples/Tactics/OperatorAliasesImport.lean`
(every signature, distinct UDVTs over one primitive, nested aliases, lazy
branches, division by zero accepted by a custom alias, failure priority, a
universal `customZero` proof and the refuted `falseBuiltin`).

## Refused, and why

- Null, malformed, missing, nonpositive, foreign or signature-mismatched
  annotations, in admission and in lowering. Equal underlying primitives do not
  make two UDVTs equal: modern fixtures keep the `typeIdentifier`, and
  historical fixtures without it must be regenerated.
- Conditional function callees with aliased or effectful arguments (the
  conservative rewrite).
- UDVT compound assignment and ambiguous same-scope overloads in a `using`
  directive: solc rejects them, and the reference pins that.

## Cost

Extra captures enlarge elaborated programs and change output pins. The design
keeps `1a7d5b0e` (one callee body elaborated once) and `63ac4b63` (split Elab).

## Left

- UDVT fields and aggregate shapes, nominal enums, general function dispatch.
- General signed shifts and complements, contextual literal promotion, nested
  numeric positions.
- Failure order outside argument lists (other hoist policies are unchanged).

## Reference check

```sh
node scripts/check-operator-aliases.mjs SOLJSON_FILE NODE_MODULES_DIRECTORY
```

Runs the EVM vectors and upstream rejection cases against the pinned solc
0.8.38, comparing actual revert bytes (`Panic(0x01)`, `Panic(0x11)`, empty).
Ordinary Lean runs assert only failure, not the panic code.
