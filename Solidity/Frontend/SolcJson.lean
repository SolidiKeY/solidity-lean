import Solidity.Frontend.SolcJson.Body
import Solidity.Frontend.SolcJson.Contract

/-!
# solc's JSON AST, printed as `sol` text

The front end reads a contract from the AST solc writes
(`scripts/solc-ast.mjs` makes the fixture) and prints each function's body
as the text `sol_raw!{ … }` reads, so the one lowering path is the macros'
(`Syntax.lean`): nothing here builds a `RawStmt`.  The printer only
normalises what the grammar spells differently from Solidity:

* an expression of literals only (solc's type `int_const …` or
  `rational_const …`) is folded to its decimal value, in exact rational
  arithmetic as solc evaluates it at compile time (`2**256 - 1`,
  `7 / 2 * 2` is `7`), units (`1 gwei`, `2 days`, `unitFactor?`) and
  spellings (`0xff`, `1_000`, `2e3`, `0.5 ether`) included; a value that is
  not an integer is a `Gap`;
* a conversion to `address`, `address payable` or a contract is the address
  itself (an `address` is a `uint`), so `payable(owner)` is `owner`;
* `++`/`--` are spelt from solc's `prefix` flag, the decrement `−−` (two
  U+2212: `--` opens a Lean comment);
* a `bool` key of a mapping is the `uint` solc encodes it as, `0` or `1`: the
  mapping is declared `mapping(uint => V)` and `m[b]` is `m[b ? 1 : 0]`;
* a member of a pushed element reads the element through a storage local
  declared before the statement
  (`T storage pushRef1 = x.push(); pushRef1.f = v;`), only where that is
  solc's order: the left-hand side of an assignment of a constant, or a
  declaration's whole initial value.  Anywhere else (a right-hand side that
  reads state, a condition, a short-circuit operand) the hoisted push would
  run before, or instead of, what solc runs first, so it is a `Gap`;
* named arguments, `h({b: 1, a: 2})`, are put in the callee's parameter
  order, the order solc evaluates them in;
* a local named like a state variable or a Lean keyword is renamed with a
  trailing `_`, by its declaration (`referencedDeclaration`), so a member of
  the same name is untouched;
* a struct is the struct table's (`Semantics.structDef`), under the renames
  the import names, when its members are the table's, member by member;
  any other is the contract's own, declared as a `struct` member
  (`readStructs`, `ownStructMembers`);
* a tuple of several components is printed where solkey reads one
  (`SolJSONParser.parseTupleStatement`): `(a, , b) = v`,
  `(uint x, , bool y) = v` and `return (a, b)`, the value a tuple or a call
  of a function by name (`requireTupleValue`);
* `(bool ok, ) = R.call{value: V}("")`, matched exactly as
  `SolJSONParser.isValueCall` matches it, is kept as written: a send that
  forwards all the gas (`Stmt.send`'s `full`), so its callee may call back
  under either `transferSemantics` (solkey reads it as `bool ok = R.send(V)`,
  its bug 5, `docs/options.md`); any other value call is a `Gap`;
* an unnamed value a `try`'s call returns is bound to a fresh `tryRetN`,
  which nothing reads;
* a loop is printed as written, `while`, `for`, `do … while`, `break`,
  `continue` (the macros lower them), its `/// @custom:key` clauses above it
  from the fixture's `loopSpec` (`loopSpec`);
* every function called by name is a `contract!` member
  (`SolcContract.funMembers`), callees first: a call is inlined where it is
  called.  A call that recurses, or of a function left out, leaves the
  caller out.

What the printer cannot write is a `Gap`, reported with its source line:
`excluded` where the model has no counterpart (a struct recursive through a
mapping), `unsupported` where the printer or the grammar lacks the form.
What would change a function's meaning if it were dropped is a `Gap` too:
an unsupported modifier. Supported constants are inlined by declaration
identity, and so is an immutable nothing writes (its initializer or its
default); one the constructor writes is a storage root. Unsupported
constant types remain gaps. Overloads receive distinct internal
names, their calls resolve by solc declaration identity, and reports retain
their source signatures. Enums become their ordinal values and primitive
user-defined value types their underlying types. Numeric bounds and wrappers
retain arithmetic casts, including signedness and width. Narrow aliases remain
unsupported; a conversion `E(x)` into an enum is printed as written, the
enum a `contract!` member, and the elaborator asserts that `x` names one of
its members.

The constructor (`kind` `constructor`, which solc names `""`) is read as a
function named `constructor` (`SolcContract.ctor`), as solkey's
`SolidityOutline` names it: a root of the calls, whatever its visibility,
and its supported modifiers run through the existing inliner. A mutable state
variable's initializer is printed with it, `uint x = 5;`
(`SolcContract.initMembers`), and a deployment runs it first.  One that
does not print, or calls a function left out, leaves the constructor out,
not the variable: a function's obligation holds from any well-typed storage
(solkey's do too), so no function needs it.

Inheritance is flattened: every base version of a function is its own
member, so a `super.f` names one statically (`PState.superNames`), and the
base constructors join the most-derived one in a single member in solc's
legacy order (`compositeBody`; `docs/solc-alignment.md`, "Constructors"),
a body with modifiers or a base's with a `return` as a member it calls
(`bodyMember?`).

The module is split by topic, each piece importing the one before
(`Frontend/SolcJson/Body.lean`, `Frontend/SolcJson/Contract.lean`);
this module imports them all.
-/
