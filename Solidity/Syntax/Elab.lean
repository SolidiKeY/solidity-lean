import Solidity.Syntax.Elab.Context
import Solidity.Syntax.Elab.Values
import Solidity.Syntax.Elab.Lower
import Solidity.Syntax.Elab.Arms
import Solidity.Syntax.Elab.Stmt

/-!
# The elaborator

`sol[C]{ … }` reads Solidity statements (`Syntax.lean`'s grammar, `RawStmt`)
and this module types them against the contract `C`, into the scoped syntax
(`Syntax/Scoped.lean`): a local is the position `Idx Γ t` of the newest
local of its name in the context it is read in (`NCtx.find`), which says
when a name is not declared or is declared at another type.  Synthesis returns a path or a value with its type;
checking takes the expected primitive type, which is how a literal gets one.
Every proof a constructor needs comes from a `match h : …` on the check that
justifies it.  A local shadows nothing: a declaration may not reuse the name
of a local in scope or of a state variable.

The passes on the raw syntax come first and are untouched by the typing:
the contract's evaluation order (`hoist`, `captureExpr`: a value read before a later
operand's effect is held in a fresh local), the narrow and cast captures,
loops (`lowerLoops`), `return`s (`lowerReturns`), modifiers (`wrapMods`), a
callee's locals renamed fresh (`renameStmts`, `ElabScope.inlined`), named
arguments (`orderNamed`), `unchecked` (`uncheckStmts`) and a flat block's
locals renamed apart (`freshenBlocks`).  `hoist` returns the raw residual,
so a statement's captures are emitted first and its values typed after, in
the context the captures leave.

A statement is emitted as an `SStmt`, typed in the named context it was
elaborated in, and a block is the `SStmt`s chained into a `Prog`
(`SProg.chain`): each is placed where the one before leaves, weakened past
the locals that are in scope but no longer named (a flat block's `{ … }`,
which the elaborator closes but solkey's program keeps until its scope
ends, and a memory return's binder).  A branch, a loop's body, a `try`'s
clauses and a call's body are nested blocks, each from the context it is
entered in; a call's body from its frame, its return variables on its
parameters (`CallRet`, `Args`).

The entry points are `Syntax/Splice.lean`'s.  The elaborator is split by
topic, each piece importing the one before (`Syntax/Elab/Context.lean`,
`Syntax/Elab/Values.lean`, `Syntax/Elab/Lower.lean`, `Syntax/Elab/Arms.lean`,
`Syntax/Elab/Stmt.lean`); this module imports them all.
-/
