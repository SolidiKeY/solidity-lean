import Solidity.Syntax.Raw
import Solidity.Syntax.Grammar
import Solidity.Syntax.Contract

/-!
# The grammar and the contract

What a program is written in, before it is typed: Solidity's grammar
(`sol_stmt`, `sol_expr`, `sol_ty`), the raw syntax it is read into
(`RawStmt`, `RawExpr`), the contract a program is written against
(`contract!{ … }`, `Contract`) and the types the typed syntax is indexed by
(`ArrTy`, `IndexTy`).  The typed syntax itself is `Syntax/Scoped.lean`'s:
every value indexed by its type and every local by its position in the
context it is read in, so a statement no rule can run cannot be written
(`alice.balance = 1;`, no such member; `alice = 1;`, a `uint` for a
`Person`; `wallet = wallet;`, a copy of a mapping).

`sol[C]{ … }` reads Solidity statements, elaborates them against the
contract `C` (`Syntax/Elab.lean`), each local typed at its position, and
splices the result into the file as a term (`Syntax/Splice.lean`);
`sol{ … }` is the same against the file's `InContract` instance.  The
elaborator is an ordinary function run at compile time; its result is
turned back into a term with every proof `Eq.refl`, so the kernel re-checks
each one: nothing the elaborator computed is trusted.

Two spellings differ from Solidity's.  A decrement is `x−−`, `−−x` (two
U+2212 MINUS SIGN): `--` opens a comment in Lean, so it cannot appear in a
`sol{ … }` block, and `x -= 1` is another statement.  And a value has no
effects: an `++`/`−−` inside an expression, or a conditional whose branches
are references, is captured by the elaborator into a fresh local before its
statement (`hoist`), in the order solc evaluates the operands.  A statement
ending in a block (`if (c) { … }`, `unchecked { … }`) may leave out its `;`
(`solSemi`), and `else if` nests an `if` in the `else` branch.

`while`, `for`, `do … while`, `break` and `continue` are lowered to one
loop, `Stmt.loop`, solkey's lowered `while`, by solkey's `LoopLowering`
(`lowerLoops`): a jump sets a flag, and a `return` inside a loop too.  The
`/// @custom:key` lines above a loop are its annotation (`LoopAnn`), which
chooses the rule that proves it.

A contract declares its internal functions (`contract!{ function f(uint x)
returns (uint r) { … } }`), each calling only the ones declared before it.
A call (`f(a);`, `y = f(a);`, `uint y = f(a);`) is elaborated by inlining:
`Stmt.call` carries the callee's parameters bound to the arguments, its
return variables and the body, every local of the callee renamed fresh for
this call (`elabCall`), as KeY's `FunctionBodyStatement` carries the function
it stands for.  A call is a statement or a whole right-hand side, as KeY
writes it (`res = f(a)@C;`); one inside an expression is captured before its
statement.  A push used as a target, `values.push() = e;`, is the push
`values.push(e);`, as the front end normalises it.  A body's
`return e;` ends it: an assignment to the return variable, the statements
after it moved into the branches that do not return (`lowerReturns`).

A function may return a memory reference (`returns (Person memory p)`), and
its call is then KeY's expansion written out: the callee's fresh return
variable is declared by the call's frame (`CallRet.mem`, a fresh default
object, as solc allocates one on entry), and the statement after the call
binds the caller's local to its identity (`Person memory mv1 =
mv2;`, `m = mv2;`, KeY's `resultVar = freshReturn`).  The printers write the
two statements as the call they are (`Person memory mv1 =
choosePersonMem();`), which reads back to them.  A member of a call's value
is a member of that capture (`choosePersonMem().account = a;`).

A single storage return (`returns (uint[] storage r)`) instead enters with
an unset alias and exports that alias without allocation (`CallRet.storage`).
Storage-local declarations and rebinding consume it; a direct call receiver
is retained as an unsupported case until its native capture taclet is added.

The module is split by topic, each piece importing the one before
(`Syntax/Raw.lean`, `Syntax/Grammar.lean`, `Syntax/Contract.lean`);
this module imports them all.
-/
