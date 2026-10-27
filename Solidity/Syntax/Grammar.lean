import Solidity.Syntax.Raw

/-!
# The grammar

The grammar of `sol{ … }` and the schema forms of the taclets, expanded.

A piece of `Syntax.lean`, whose docstring describes the whole.
-/

namespace Solidity

open Semantics

/-! ## The grammar -/

declare_syntax_cat sol_expr (behavior := both)
syntax:max num : sol_expr
/-- A nonempty fixed memory array literal; its element type is inferred before allocation. -/
syntax:max (name := solInlineArray) "[" sol_expr,+ "]" : sol_expr
syntax:max ident : sol_expr
/-- `"ab"`: a literal of bytes, a `bytesN`'s left-aligned or a `bytes`/`string`'s
(`RawExpr.bytesLit`). -/
syntax:max str : sol_expr
/-- `hex"6162"`: the bytes the hex digits spell. -/
syntax:max &"hex" str : sol_expr
syntax:max sol_expr:max "." ident : sol_expr
syntax:max sol_expr:max "[" sol_expr "]" : sol_expr
/-- `b[i:j]`, `b[i:]`, `b[:j]`: a slice of a calldata array, a view of it
(`RawStmt.sliceViews`, `Syntax/Elab.lean`): `RawExpr.call "#slice" [b, i, j]`. -/
syntax:max (name := solSlice) sol_expr:max "[" sol_expr ":" sol_expr "]" : sol_expr
@[inherit_doc solSlice]
syntax:max (name := solSliceFrom) sol_expr:max "[" sol_expr ":" "]" : sol_expr
@[inherit_doc solSlice]
syntax:max (name := solSliceTo) sol_expr:max "[" ":" sol_expr "]" : sol_expr
/-- Both endpoints omitted: the whole calldata view. -/
syntax:max (name := solSliceAll) sol_expr:max "[" ":" "]" : sol_expr
/-- `T[]` where a type stands in an expression: `abi.decode(d, (uint[]))`
(`RawExpr.name "uint[]"`). -/
syntax:max (name := solArrTyExpr) atomic(ident "[" "]") : sol_expr
/-- `T[][]` where a type stands in an expression: `abi.decode(d, (uint[][]))`. -/
syntax:max (name := solArrTyExpr2) atomic(ident "[" "]" "[" "]") : sol_expr
syntax:max "(" sol_expr ")" : sol_expr
/-- `(a, b)`: a tuple, the right-hand side of a tuple assignment or of a
`return` of several values (`RawExpr.tuple`). -/
syntax:max (name := solTupleExpr) "(" sol_expr ", " sol_expr,+ ")" : sol_expr
/-- An assignment inside an expression, parenthesized: `(x = e)`, `(x += e)`. -/
syntax:max "(" sol_expr " = " sol_expr ")" : sol_expr
syntax:max "(" sol_expr " += " sol_expr ")" : sol_expr
syntax:max "(" sol_expr " -= " sol_expr ")" : sol_expr
syntax:max "(" sol_expr " *= " sol_expr ")" : sol_expr
syntax:max "(" sol_expr " /= " sol_expr ")" : sol_expr
syntax:max "(" sol_expr " %= " sol_expr ")" : sol_expr
syntax:max "(" sol_expr " &= " sol_expr ")" : sol_expr
syntax:max "(" sol_expr " |= " sol_expr ")" : sol_expr
syntax:max "(" sol_expr " ^= " sol_expr ")" : sol_expr
syntax:max "(" sol_expr " <<= " sol_expr ")" : sol_expr
syntax:max "(" sol_expr " >>= " sol_expr ")" : sol_expr
syntax:80 "!" sol_expr:80 : sol_expr
syntax:80 "-" sol_expr:80 : sol_expr
/-- `a ** b`, right-associative and tighter than `*` (solc ≥ 0.8). -/
syntax:75 sol_expr:76 " ** " sol_expr:75 : sol_expr
syntax:70 sol_expr:70 " * " sol_expr:71 : sol_expr
syntax:70 sol_expr:70 " / " sol_expr:71 : sol_expr
syntax:70 sol_expr:70 " % " sol_expr:71 : sol_expr
syntax:65 sol_expr:65 " + " sol_expr:66 : sol_expr
syntax:65 sol_expr:65 " - " sol_expr:66 : sol_expr
/-- solc's precedence: `+ -` > `<< >>` > `&` > `^` > `|` > comparisons. -/
syntax:60 sol_expr:60 " << " sol_expr:61 : sol_expr
syntax:60 sol_expr:60 " >> " sol_expr:61 : sol_expr
syntax:58 sol_expr:58 " & " sol_expr:59 : sol_expr
syntax:56 sol_expr:56 " ^ " sol_expr:57 : sol_expr
syntax:54 sol_expr:54 " | " sol_expr:55 : sol_expr
/-- `~x`.  The category reads a leading atom as a non-reserved keyword, which
`~` (no Lean token) cannot be: `ppAllowUngrouped` makes it not the first. -/
syntax:80 ppAllowUngrouped "~" sol_expr:80 : sol_expr
/-- The wrapping arithmetic of an `unchecked { … }` block, spelt as Zig spells
it: `a +% b` is `a + b` modulo `2^256`.  Not Solidity: it is what the printers
write for an operator inside `unchecked`, and it reads back. -/
syntax:75 sol_expr:76 " **% " sol_expr:75 : sol_expr
syntax:70 sol_expr:70 " *% " sol_expr:71 : sol_expr
syntax:65 sol_expr:65 " +% " sol_expr:66 : sol_expr
syntax:65 sol_expr:65 " -% " sol_expr:66 : sol_expr
syntax:50 sol_expr:51 " < " sol_expr:51 : sol_expr
syntax:50 sol_expr:51 " > " sol_expr:51 : sol_expr
syntax:50 sol_expr:51 " <= " sol_expr:51 : sol_expr
syntax:50 sol_expr:51 " >= " sol_expr:51 : sol_expr
syntax:45 sol_expr:46 " == " sol_expr:46 : sol_expr
syntax:45 sol_expr:46 " != " sol_expr:46 : sol_expr
syntax:35 sol_expr:36 " && " sol_expr:35 : sol_expr
syntax:30 sol_expr:31 " || " sol_expr:30 : sol_expr
syntax:20 sol_expr:21 " ? " sol_expr:21 " : " sol_expr:20 : sol_expr
/-! `++` and `−−` inside an expression (`values[i++] = 1;`).  A decrement is
spelled with two minus signs `−` (U+2212): `--` opens a line comment in Lean,
so `x--` cannot be written in a `sol{ … }` block, and `x -= 1` is another
statement.  The postfix forms have precedence `arg`, below a member access,
so that a statement `x++;` (whose target is read at `max`) is not read as an
expression. -/
syntax:arg sol_expr:max "++" : sol_expr
syntax:arg sol_expr:max "−−" : sol_expr
syntax:max "++" sol_expr:max : sol_expr
syntax:max "−−" sol_expr:max : sol_expr
/-- `new uint[](n)`: a fresh memory array. -/
syntax:max &"new" sol_ty "(" sol_expr ")" : sol_expr
/-! `address(this).balance`, the contract's own funds: one form, since an
`address(…)` conversion is not otherwise an expression here.  `msg.sender`,
`msg.value` and `block.timestamp` arrive as identifiers (`expandIdent`). -/
syntax:max &"address" "(" &"this" ")" "." &"balance" : sol_expr

/-! What elaborates away (`sol{ … }` reads it, no statement or value holds
it): an ether or time unit on a number literal (`2 ether`, `3 days`), the
casts `payable(e)` and `address(e)` retain their kind until frontend typing (the model value is a
`uint`), a struct constructor with named arguments (`T({f: a, g: b})`), and
a call's (`f({q: b, p: a})`). -/

/-- `2 ether`, `3 days`: the literal times its unit (`wei gwei ether`,
`seconds minutes hours days weeks`). -/
syntax:max atomic(num ident) : sol_expr
/-- `payable(e)`: `e`. -/
syntax:max atomic(&"payable" "(") sol_expr ")" : sol_expr
/-- `address(e)`: `e` (not `address(this)`, which is no value here). -/
syntax:max atomic(&"address" "(") sol_expr ")" : sol_expr
/-- `T({f: a, g: b})`: a struct constructor with named arguments. -/
syntax:max atomic(ident "(" "{") (ident ": " sol_expr),* "}" ")" : sol_expr

/-- `f(a, b)` inside an expression (`x = f(a) + 1;`), captured before its
statement (`hoist`).  At precedence `arg`, as a postfix `++`: a statement
`f(a);` reads its callee at `max`, so it stays the call statement, and the
call statements below are preferred (`priority := high`) where both
readings take the same text (`y = f(a);`, `lsv = values.push();`). -/
syntax:arg (name := solCallExpr) sol_expr:max "(" sol_expr,* ")" : sol_expr
/-- `choosePersonMem().account`: a member of a call's value, a memory
reference (`hoist` captures the call).  At `max`, as a member is; `atomic`,
so that a call with no member after it is left to the readings above. -/
syntax:max (name := solCallMember) sol_expr:max atomic("(" sol_expr,* ")" ".") ident : sol_expr
/-- A call's storage reference indexed, `matrixRef()[i]`: the call before the index. -/
syntax:max (name := solCallIndex) sol_expr:max atomic("(" sol_expr,* ")" "[") sol_expr "]" : sol_expr
/-- A call of a call's value, `choose(b)(x)`: a function value returned
(`callValueName`). -/
syntax:max (name := solCallCall) sol_expr:max atomic("(" sol_expr,* ")" "(") sol_expr,* ")" : sol_expr

declare_syntax_cat sol_stmt (behavior := both)
declare_syntax_cat sol_block (behavior := both)

section Semi
open Lean Parser PrettyPrinter

/-- The last token of a node: an atom or an identifier. -/
partial def lastToken? : Syntax → Option Syntax
  | .node _ _ args => args.reverse.findSome? lastToken?
  | .missing => none
  | s => some s

/-- `;` after a statement, which a statement ending in a block (`if (c) { … }`,
`unchecked { … }`) may leave out: it is then read as if written, so the
statement's syntax is the same either way. -/
def solSemiFn : ParserFn := fun c s =>
  let s' := symbolFn ";" c s
  if s'.hasError && (lastToken? s.stxStack.back).any (·.isToken "}") then
    s.pushSyntax (mkAtom ";")
  else s'

def solSemi : Parser :=
  { fn := solSemiFn, info := { collectTokens := (";" :: ·) } }

@[combinator_formatter solSemi]
def solSemi.formatter : Formatter := Formatter.symbolNoAntiquot.formatter ";"

@[combinator_parenthesizer solSemi]
def solSemi.parenthesizer : Parenthesizer := Parenthesizer.symbolNoAntiquot.parenthesizer ";"

end Semi

syntax "{" (sol_stmt solSemi)* "}" : sol_block
syntax sol_expr " = " sol_expr : sol_stmt
syntax sol_ty ident : sol_stmt
syntax sol_ty ident " = " sol_expr : sol_stmt
syntax sol_ty &"storage" ident : sol_stmt
syntax sol_ty &"storage" ident " = " sol_expr : sol_stmt
syntax sol_ty &"memory" ident : sol_stmt
syntax sol_ty &"memory" ident " = " sol_expr : sol_stmt
/-- A read-only calldata local retains its slice descriptor, unlike memory. -/
syntax (name := solCalldataLocal) sol_ty &"calldata" ident " = " sol_expr : sol_stmt
syntax (name := solDelete) "delete" ppSpace sol_expr : sol_stmt
-- `.push(`, `.push()` and `.pop()` are tokens, so a push on a member or an
-- entry is spelt with them; one on a name is an identifier `values.push`
-- called.
syntax sol_expr ".push(" sol_expr ")" : sol_stmt
syntax sol_expr ".push()" : sol_stmt
syntax (name := solPushAddAssign) sol_expr ".push()" " += " sol_expr : sol_stmt
syntax (name := solPushSubAssign) sol_expr ".push()" " -= " sol_expr : sol_stmt
syntax (name := solPushMulAssign) sol_expr ".push()" " *= " sol_expr : sol_stmt
syntax (name := solPushDivAssign) sol_expr ".push()" " /= " sol_expr : sol_stmt
syntax (name := solPushModAssign) sol_expr ".push()" " %= " sol_expr : sol_stmt
syntax (name := solPushPreInc) "++" sol_expr ".push()" : sol_stmt
syntax (name := solPushPreDec) "−−" sol_expr ".push()" : sol_stmt
syntax (name := solPushPostInc) sol_expr ".push()" "++" : sol_stmt
syntax (name := solPushPostDec) sol_expr ".push()" "−−" : sol_stmt
syntax (name := solPushCallPreInc) "++" sol_expr:max "(" ")" : sol_stmt
syntax (name := solPushCallPreDec) "−−" sol_expr:max "(" ")" : sol_stmt
syntax (name := solPushCallPostInc) sol_expr:max "(" ")" "++" : sol_stmt
syntax (name := solPushCallPostDec) sol_expr:max "(" ")" "−−" : sol_stmt
syntax sol_expr ".pop()" : sol_stmt
syntax sol_expr " = " sol_expr ".push()" : sol_stmt
/-- `values .push() = e;`, `a[i].push() = e;`: a push used as a target spelt
with the `.push()` token; on a name or a member chain it is the push
`b.push(e);`, on another receiver refused (`expandStmt.pushTarget`). -/
syntax (name := solPushTarget) sol_expr ".push()" " = " sol_expr : sol_stmt
syntax sol_ty &"storage" ident " = " sol_expr ".push()" : sol_stmt
/-- `uint y = values.push();`: the slot appended, `y` its default. -/
syntax sol_ty ident " = " sol_expr ".push()" : sol_stmt
syntax sol_expr ".transfer(" sol_expr ")" : sol_stmt
syntax sol_expr " = " sol_expr ".send(" sol_expr ")" : sol_stmt
syntax sol_ty ident " = " sol_expr ".send(" sol_expr ")" : sol_stmt
/-- `(ok, ) = r.call{value: a}("");`: a send with all the gas (`RawStmt.send`). -/
syntax (name := solValueCall) "(" sol_expr ", " ")" " = " sol_expr:max "{" &"value" ": " sol_expr "}"
  "(" str ")" : sol_stmt
/-- `(bool ok, ) = r.call{value: a}("");`. -/
syntax (name := solValueCallDecl) "(" sol_ty ident ", " ")" " = " sol_expr:max "{" &"value" ": "
  sol_expr "}" "(" str ")" : sol_stmt
syntax sol_expr:max "(" ")" : sol_stmt
syntax sol_expr:max "(" sol_expr ")" : sol_stmt
syntax (priority := high) sol_expr " = " sol_expr:max "(" ")" : sol_stmt
/-- A call of the contract's function with two arguments or more. -/
syntax sol_expr:max "(" sol_expr ", " sol_expr,+ ")" : sol_stmt
/-- `y = f(a, b);`: a call assigned. -/
syntax (priority := high) sol_expr " = " sol_expr:max "(" sol_expr,+ ")" : sol_stmt
/-- `uint y = f(a);`: a call declared. -/
syntax (priority := high) sol_ty ident " = " sol_expr:max "(" sol_expr,* ")" : sol_stmt
/-- `return e;`, `return;`: anywhere in a function's body (`lowerReturns`). -/
syntax (name := solReturn) "return " sol_expr : sol_stmt
syntax (name := solReturnNone) "return" : sol_stmt
syntax (priority := high) sol_ty &"storage" ident " = " sol_expr:max "(" ")" : sol_stmt
syntax sol_expr:max "++" : sol_stmt
syntax "++" sol_expr : sol_stmt
syntax sol_expr " = " sol_expr:max "++" : sol_stmt
syntax sol_expr " = " "++" sol_expr : sol_stmt
syntax sol_expr:max "−−" : sol_stmt
syntax "−−" sol_expr : sol_stmt
syntax sol_expr " = " sol_expr:max "−−" : sol_stmt
syntax sol_expr " = " "−−" sol_expr : sol_stmt
syntax sol_expr " += " sol_expr : sol_stmt
syntax sol_expr " -= " sol_expr : sol_stmt
syntax sol_expr " *= " sol_expr : sol_stmt
syntax sol_expr " /= " sol_expr : sol_stmt
syntax sol_expr " %= " sol_expr : sol_stmt
syntax sol_expr " &= " sol_expr : sol_stmt
syntax sol_expr " |= " sol_expr : sol_stmt
syntax sol_expr " ^= " sol_expr : sol_stmt
syntax sol_expr " <<= " sol_expr : sol_stmt
syntax sol_expr " >>= " sol_expr : sol_stmt
/-- `unchecked { … }`: its `+ - * **` wrap at `2^256` instead of reverting. -/
syntax (name := solUnchecked) &"unchecked" ppSpace sol_block : sol_stmt
/-- `checked { … }`: an overflow in it fails as an `assert` does
(`Prog.checkOF`), not as a revert. -/
syntax (name := solChecked) &"checked" ppSpace sol_block : sol_stmt
/-- `ignoringOverflow { … }`: a run in which an operation leaves its range
proves anything (`Prog.ignoreOF`), under either modality. -/
syntax (name := solIgnoringOverflow) &"ignoringOverflow" ppSpace sol_block : sol_stmt
syntax "if " "(" sol_expr ") " sol_block (" else " sol_block)? : sol_stmt
/-- `if (c) { … } else if (d) { … } else { … }`: the `if`s nested. -/
syntax (name := solIfChain) "if " "(" sol_expr ") " sol_block
  (atomic(" else " "if ") "(" sol_expr ") " sol_block)+ (" else " sol_block)? : sol_stmt
syntax (name := solRequire) &"require" "(" sol_expr ")" : sol_stmt
syntax (name := solAssert) &"assert" "(" sol_expr ")" : sol_stmt
syntax (name := solRevert) &"revert" "(" ")" : sol_stmt
/-- `assume(false);`: not Solidity; the statement `ignoringOverflow { … }`
writes where an operation leaves its range (`Stmt.assumeFalse`). -/
syntax (name := solAssumeFalse) &"assume" "(" &"false" ")" : sol_stmt
/-- `emit E(a, b);`: the arguments evaluated (`RawStmt.eval`), the log dropped. -/
syntax (name := solEmit) &"emit" ident "(" sol_expr,* ")" : sol_stmt
/-- `require(c, "msg");`: `require(c);`, the reason kept where a `try` reads
it (`RawStmt.requireMsg`). -/
syntax (name := solRequireMsg) (priority := high) &"require" "(" sol_expr ", " str ")" : sol_stmt
syntax (name := solRequireReason) &"require" "(" sol_expr ", " sol_expr ")" : sol_stmt
/-- `require(c, Err(a));`: `RawStmt.requireErr`. -/
syntax (name := solRequireErr) &"require" "(" sol_expr ", " ident "(" sol_expr,* ")" ")" : sol_stmt
/-- `revert Err(a);`: `RawStmt.revertErr`; `revert();` where no `try` reads
the data, since a revert undoes whatever evaluating `a` did. -/
syntax (name := solRevertErr) &"revert" ident "(" sol_expr,* ")" : sol_stmt
/-- `revert("msg");`: `revert();`, the reason kept where a `try` reads it
(`RawStmt.revertMsg`). -/
syntax (name := solRevertMsg) (priority := high) &"revert" "(" str ")" : sol_stmt
syntax (name := solRevertReason) &"revert" "(" sol_expr ")" : sol_stmt
syntax (name := solRevertRaw) &"assembly" "{" &"revert" "(" &"add" "(" ident "," num ")" ","
  &"mload" "(" ident ")" ")" "}" : sol_stmt
/-- `_;`: where a modifier's body runs the function's (`contract!{ … }`). -/
syntax (name := solHole) "_" : sol_stmt
/-- `(a, , b) = e;`: a tuple assignment, a component left out discarded
(`RawStmt.tupleAssign`).  One comma at least, so that it is not `(a) = e;`. -/
syntax (name := solTupleAssign) "(" (sol_expr)? (", " (sol_expr)?)+ ")" " = " sol_expr : sol_stmt
/-- `(uint a, , bool b) = e;`: a tuple declaration (`RawStmt.tupleDecl`). -/
syntax (name := solTupleDecl) "(" (sol_ty ident)? (", " (sol_ty ident)?)+ ")" " = " sol_expr :
  sol_stmt
/-- `{ … }`: a block (`RawStmt.block`). -/
syntax (name := solBlockStmt) "{" (sol_stmt solSemi)* "}" : sol_stmt
/-- `while (c) { … }` -/
syntax (name := solWhile) "while " "(" sol_expr ") " sol_block : sol_stmt
/-- `for (init; c; upd) { … }`, each of the three parts optional. -/
syntax (name := solFor) "for " "(" (sol_stmt)? "; " (sol_expr)? "; " (sol_stmt)? ") " sol_block :
  sol_stmt
/-- `do { … } while (c);` -/
syntax (name := solDoWhile) "do " sol_block " while " "(" sol_expr ")" : sol_stmt
/-- `break;` -/
syntax (name := solBreak) "break" : sol_stmt
/-- `continue;` -/
syntax (name := solContinue) "continue" : sol_stmt
/-! `/// @custom:key invariant e`, `/// @custom:key decreases e` above a loop,
solkey's loop specification, and, Lean only, `/// @custom:key unwind k`
(`RawLoopSpec`).  A clause is a category of its own: a statement's leading
atom must already be a token (`sol_stmt` reads leading keywords as
identifiers too), and `///` is not one. -/
declare_syntax_cat sol_loop_clause
syntax "/// " "@" &"custom" ":" &"key" ident sol_expr : sol_loop_clause
/-- A quantified invariant's body: an expression, `a -> c`, or another
`\forall`. -/
declare_syntax_cat sol_loop_inv
syntax "\\" noWs &"forall " ident ident "; " sol_loop_inv : sol_loop_inv
syntax sol_expr " -> " sol_expr : sol_loop_inv
syntax sol_expr : sol_loop_inv
/-- `/// @custom:key invariant \forall uint q; a -> c`: a quantified clause. -/
syntax (name := solLoopForall) "/// " "@" &"custom" ":" &"key" &"invariant" "\\" noWs &"forall "
  ident ident "; " sol_loop_inv : sol_loop_clause
syntax (name := solLoopSpec) sol_loop_clause ppSpace sol_stmt : sol_stmt
/-! `try e.f(a) returns (uint v) { … } catch Error(string memory m) { … }
catch Panic(uint c) { … } catch (bytes memory d) { … } catch { … }`: an
external call.  A clause's parameter is `sol_tparam`: a type, `memory` for
`string`/`bytes`, an optional name. -/
declare_syntax_cat sol_tparam (behavior := both)
syntax sol_ty (ppSpace &"memory")? (ppSpace ident)? : sol_tparam
declare_syntax_cat sol_rparam (behavior := both)
syntax sol_ty (ppSpace (&"memory" <|> &"storage"))? (ppSpace ident)? : sol_rparam
declare_syntax_cat sol_catch (behavior := both)
syntax (name := solCatchError) "catch " &"Error" "(" sol_tparam ") " sol_block : sol_catch
syntax (name := solCatchPanic) "catch " &"Panic" "(" sol_tparam ") " sol_block : sol_catch
syntax (name := solCatchData) "catch " "(" sol_tparam ") " sol_block : sol_catch
syntax (name := solCatchAll) "catch " sol_block : sol_catch
syntax (name := solTry) "try " sol_expr (ppSpace &"returns" " (" sol_tparam,* ")")? ppSpace sol_block
  (ppSpace sol_catch)+ : sol_stmt
/-- `T memory t = T(a, b);`: a struct constructor declared. -/
syntax sol_ty &"memory" ident " = " sol_expr "(" sol_expr,* ")" : sol_stmt
/-- `todos.push(Todo(a, b));`: a struct constructor pushed. -/
syntax sol_expr "(" sol_expr "(" sol_expr,* ")" ")" : sol_stmt
syntax sol_expr ".push(" sol_expr "(" sol_expr,* ")" ")" : sol_stmt

/-! The schema forms of the taclets (`Calculus/RuleSyntax.lean`): an
escape `‹t›` to any Lean term, and the operator schema variables.  They live
with the grammar, whose tokens they extend. -/

/-- `‹t›`: any Lean term, in a program position. -/
syntax:max "‹" term "›" : sol_expr
syntax "‹" term "›" : sol_stmt
/-- A block that is a schema variable: `if (se) thn else els`. -/
syntax ident : sol_block
syntax "‹" term "›" : sol_block
/-- A binary operator schema variable `op`. -/
syntax:65 sol_expr:65 " ⊕ " sol_expr:66 : sol_expr
/-- A unary operator schema variable `op`. -/
syntax:80 "⊖" sol_expr:80 : sol_expr
/-- An increment or decrement schema variable `op`. -/
syntax sol_expr "⊕⊕" : sol_stmt
syntax sol_expr " = " sol_expr "⊕⊕" : sol_stmt
/-- A compound assignment with an operator schema variable `op`. -/
syntax sol_expr " ⊕= " sol_expr : sol_stmt

/-- `sol_raw!{ s₁; s₂; … }`: the raw statements, before elaboration. -/
syntax "sol_raw!{" (sol_stmt solSemi)* "}" : term

/-- The dot-separated parts of a name: `alice.account` is `["alice", "account"]`. -/
def nameParts : Lean.Name → List String
  | .anonymous => []
  | .str p s => nameParts p ++ [s]
  | .num p n => nameParts p ++ [toString n]

section Expand
open Lean

/-- A type as a function type's spelling writes it (`fnTyStr`): a name as
written, a function type spelled. -/
partial def spellFnTy (T : TSyntax `sol_ty) : MacroM String := do
  if T.raw.isOfKind ``solFnTy then
    let component (t : Syntax) : MacroM String := do
      let base ← spellFnTy ⟨t[0]⟩
      let loc := (t[1].find? fun a => a.isAtom &&
        ["memory", "storage", "calldata"].contains a.getAtomVal).map (·.getAtomVal)
      pure (base ++ loc.getD "")
    let ps ← T.raw[2].getSepArgs.toList.mapM component
    let ext := T.raw[4].getArgs.any fun m =>
      (m.find? fun a => a.isAtom && a.getAtomVal == "external").isSome
    -- `(returns (…))?`: a null node of its four parts, or of none
    let r := T.raw[5]
    let rs ← if r.getNumArgs == 4 then r[2].getSepArgs.toList.mapM component else pure []
    return fnTyStr ps rs ext
  match T with
  | `(sol_ty| $x:ident) => pure (x.getId.toString false)
  | `(sol_ty| address payable) => pure "address"
  | `(sol_ty| mapping ( $k => $v )) => return s!"mapping({← spellFnTy k}=>{← spellFnTy v})"
  | `(sol_ty| $t[]) => return (← spellFnTy t) ++ "[]"
  | `(sol_ty| $t[$n]) => return s!"{← spellFnTy t}[{n.getNat}]"
  | _ => Macro.throwUnsupported

partial def expandTy (T : TSyntax `sol_ty) : MacroM Term := do
  if T.raw.isOfKind ``solFnTy then return ← `(RawTy.named $(quote (← spellFnTy T)))
  expandTy1 T
where
  expandTy1 : TSyntax `sol_ty → MacroM Term
  | `(sol_ty| $x:ident) => `(RawTy.named $(quote (x.getId.toString false)))
  | `(sol_ty| address payable) => `(RawTy.named "address")
  | `(sol_ty| mapping ( $k => $v )) => do `(RawTy.mapping $(← expandTy k) $(← expandTy v))
  | `(sol_ty| $t[]) => do `(RawTy.array $(← expandTy t))
  | `(sol_ty| $t[$n]) => do `(RawTy.fixed $(← expandTy t) $n)
  | _ => Macro.throwUnsupported

/-- What a unit multiplies a literal by: `1 gwei` is `10^9`, `1 days` is
`86400`. -/
def unitFactor? : String → Option Nat
  | "wei" => some 1
  | "gwei" => some (10 ^ 9)
  | "ether" => some (10 ^ 18)
  | "seconds" => some 1
  | "minutes" => some 60
  | "hours" => some 3600
  | "days" => some 86400
  | "weeks" => some 604800
  | _ => none

/-- The constructor's name, to splice. -/
def EnvKey.ident : EnvKey → Ident
  | .msgSender => mkIdent ``EnvKey.msgSender
  | .msgValue => mkIdent ``EnvKey.msgValue
  | .timestamp => mkIdent ``EnvKey.timestamp
  | .selfBalance => mkIdent ``EnvKey.selfBalance
  | .selfAddress => mkIdent ``EnvKey.selfAddress

/-- A name, as a string literal. -/
def strLit (x : Ident) : Term := quote (x.getId.toString false)

/-- `e.f.g`: the members `fs` of `e`. -/
def fieldChain (e : Term) (fs : List String) : MacroM Term :=
  foldFields (mkIdent ``RawExpr.field) e fs

/-- `alice.account.age` arrives as one identifier; split it into members;
`msg.sender` and `block.timestamp` are the environment's. -/
def expandIdent (x : Ident) : MacroM Term := do
  match nameParts x.getId with
  | [] => Macro.throwError "empty identifier"
  | ["true"] => `(RawExpr.bool true)
  | ["false"] => `(RawExpr.bool false)
  | ["this"] => `(RawExpr.env .selfAddress)
  | root :: f :: flds =>
    match EnvKey.ofParts root f with
    | some k => fieldChain (← `(RawExpr.env $(k.ident))) flds
    | none => fieldChain (← `(RawExpr.name $(quote root))) (f :: flds)
  | root :: flds => fieldChain (← `(RawExpr.name $(quote root))) flds

/-- `abi.encode`, `abi.encodePacked`, `abi.decode`, `string.concat`,
`bytes.concat`: builtins the elaborator lowers (`abiEncode`, `Syntax/Elab.lean`). -/
def builtinMember (n g : String) : Bool :=
  (n == "abi" && ["encode", "encodePacked", "decode", "encodeWithSelector",
    "encodeWithSignature", "encodeCall"].contains g) ||
    ((n == "string" || n == "bytes") && g == "concat")

/-- A builtin whose value is a fresh memory `bytes`: `abi.encode`,
`abi.encodePacked`, the two `concat`s. -/
def encodeBuiltin (f : String) : Bool :=
  ["abi.encode", "abi.encodePacked", "string.concat", "bytes.concat", "abi.encodeWithSelector",
    "abi.encodeWithSignature", "abi.encodeCall"].contains f

/-- A builtin that reads byte strings whole: the hashes, the ABI's, the
`concat`s (and `#abiDecode`, `abi.decode`'s lowering); `ecrecover`, whose
arguments it encodes. -/
def byteBuiltin (f : String) : Bool :=
  encodeBuiltin f || isHashName f || ["abi.decode", "#abiDecode"].contains f

/-- `f`, a function's name: an identifier with no member access. -/
def funName? (f : TSyntax `sol_expr) : Option String :=
  match f with
  | `(sol_expr| $x:ident) =>
    match nameParts x.getId with
    | [g] => some g
    -- the builtins under a namespace: `abi.encode`, `string.concat`, …
    | [n, g] => if builtinMember n g then some s!"{n}.{g}" else none
    | _ => none
  | _ => none

/-- `a ⊕ b` for an operator of the table (`BinOp.ofSym?`): a node
`[a, ⊕, b]`, whatever its kind. -/
def binParts? (s : Syntax) : Option (BinOp × Syntax × Syntax) :=
  if s.getNumArgs == 3 && s[1].isAtom then
    (BinOp.ofSym? s[1].getAtomVal).map (·, s[0], s[2])
  else none

/-- `e++`, `−−e`: a node `[e, tok]` or `[tok, e]` (`IncDec.ofTok?`). -/
def incDecParts? (s : Syntax) : Option (IncDec × Syntax) :=
  if s.getNumArgs != 2 then none
  else if s[1].isAtom then (IncDec.ofTok? false s[1].getAtomVal).map (·, s[0])
  else if s[0].isAtom then (IncDec.ofTok? true s[0].getAtomVal).map (·, s[1])
  else none

/-- The receiver of a method named `push`, before its empty argument list. -/
def pushMethodBase? : TSyntax `sol_expr → MacroM (Option (TSyntax `sol_expr))
  | `(sol_expr| $x:ident) => do
    match (nameParts x.getId).reverse with
    | "push" :: r :: rs =>
      let n := (r :: rs).reverse.foldl (fun n s => Name.str n s) Name.anonymous
      return some (← `(sol_expr| $(mkIdentFrom x n):ident))
    | _ => return none
  | `(sol_expr| $b:sol_expr . $f:ident) =>
    pure (if (f.getId.toString false) == "push" then some b else none)
  | _ => pure none

/-- `b.push()` as a compound or increment lvalue, optionally parenthesized. -/
partial def pushLvalueBase? : TSyntax `sol_expr → MacroM (Option (TSyntax `sol_expr))
  | `(sol_expr| $f:sol_expr ( )) => pushMethodBase? f
  | `(sol_expr| ($e:sol_expr)) => pushLvalueBase? e
  | _ => pure none

/-- Both the fused `.push()` token and an ordinary method-call expression
can spell `rows[i].push() += rhs`. -/
def pushCompoundParts? (s : Syntax) : MacroM (Option (BinOp × TSyntax `sol_expr × TSyntax `sol_expr)) := do
  let fixed := match s.getKind with
    | ``solPushAddAssign => some BinOp.add | ``solPushSubAssign => some BinOp.sub
    | ``solPushMulAssign => some BinOp.mul | ``solPushDivAssign => some BinOp.div
    | ``solPushModAssign => some BinOp.mod | _ => none
  if let some op := fixed then return some (op, ⟨s[0]⟩, ⟨s[3]⟩)
  if s.getNumArgs == 3 && s[1].isAtom && s[1].getAtomVal.endsWith "=" then
    if let some op := BinOp.ofSym? (s[1].getAtomVal.dropRight 1) then
      if let some b ← pushLvalueBase? ⟨s[0]⟩ then return some (op, b, ⟨s[2]⟩)
  return none

/-- A discarded push increment/decrement, including calls whose callee
lexes as the dotted identifier `values.push`. -/
def pushIncrementParts? (s : Syntax) : MacroM (Option (IncDec × TSyntax `sol_expr)) := do
  match s.getKind with
  | ``solPushPreInc => return some (.preInc, ⟨s[1]⟩)
  | ``solPushPreDec => return some (.preDec, ⟨s[1]⟩)
  | ``solPushPostInc => return some (.postInc, ⟨s[0]⟩)
  | ``solPushPostDec => return some (.postDec, ⟨s[0]⟩)
  | ``solPushCallPreInc | ``solPushCallPreDec =>
    let some b ← pushMethodBase? ⟨s[1]⟩ | return none
    return some ((if s.isOfKind ``solPushCallPreInc then .preInc else .preDec), b)
  | ``solPushCallPostInc | ``solPushCallPostDec =>
    let some b ← pushMethodBase? ⟨s[0]⟩ | return none
    return some ((if s.isOfKind ``solPushCallPostInc then .postInc else .postDec), b)
  | _ =>
    if let some (op, l) := incDecParts? s then
      if let some b ← pushLvalueBase? ⟨l⟩ then return some (op, b)
    return none

/-- Of an ambiguous parse, the readings `good` accepts first, then all of them;
of an unambiguous one, itself. -/
def readings (s : Syntax) (good : Syntax → Bool) : Array Syntax :=
  if s.isOfKind choiceKind then s.getArgs.filter good ++ s.getArgs else #[s]

/-- Of an ambiguous parse, the first reading `good` accepts (else the first). -/
def preferReading (s : Syntax) (good : Syntax → Bool) : Syntax :=
  (readings s good)[0]?.getD s

/-- What a call's callee must be. -/
def callMsg : String := "a call's callee is a function's name"

/-- What a push used as a target is written on. -/
def pushTargetMsg : String :=
  "`b.push() = e;` is written on a name or a member chain, `bucket.tokens`"

/-- The expressions and blocks of a node, its atoms and groupings dropped. -/
partial def payload (s : Syntax) : Array Syntax :=
  if s.isAtom then #[]
  else if s.getKind == nullKind || s.getKind == groupKind then s.getArgs.flatMap payload
  else #[s]

/-- `type(T).max`, `type(T).min`: an integer type's bound as a value of `T`
(`uint8(255)`, `int8(-128)`: solc types it `T`, so `type(uint8).max + 1`
overflows at `uint8`); an enum's, its first or last member, which the
elaborator reads (`enumLit?`, the member `type(max)`) -/
def typeBoundExpr (f : TSyntax `sol_expr) (as : Array (TSyntax `sol_expr)) (g : Ident) :
      MacroM (Option Term) := do
  unless funName? f == some "type" do return none
  let #[a] := as | return none
  let some T := funName? a | return none
  let m := (g.getId.toString false)
  unless m == "max" || m == "min" do
    Macro.throwErrorAt g s!"type({T}).{m}: only `max` and `min` are modelled"
  match castTy? T with
  | some (p, n) =>
    let v : Int := if p == .int then
        (if m == "max" then 2 ^ (n - 1) - 1 else -(2 ^ (n - 1) : Int))
      else (if m == "max" then 2 ^ n - 1 else 0)
    let lit ← if v < 0 then `(RawExpr.unop .neg (.num $(quote v.natAbs)))
      else `(RawExpr.num $(quote v.toNat))
    return some (← `(RawExpr.call $(quote T) [$lit]))
  | none => return some (← `(RawExpr.field (.name $(quote T)) $(quote s!"type({m})")))

/-- Keep byte-literal elaboration depth logarithmic: a quoted cons spine
otherwise exceeds the default recursion depth before the typed reader runs.
Each leaf is small; concatenation preserves every byte in source order. -/
private partial def quoteBytes (bytes : List Nat) : MacroM Term := do
  if bytes.length ≤ 32 then return quote bytes
  let half := bytes.length / 2
  let left ← quoteBytes (bytes.take half)
  let right ← quoteBytes (bytes.drop half)
  `(List.append $left $right)

partial def expandExpr (e : TSyntax `sol_expr) : MacroM Term := do
  if e.raw.isOfKind ``solInlineArray then
    return ← `(RawExpr.call "#array" [$(← e.raw[1].getSepArgs.mapM (expandExpr ⟨·⟩)),*])
  if e.raw.isOfKind ``solTupleExpr then
    let es := #[e.raw[1]] ++ e.raw[3].getSepArgs
    return ← `(RawExpr.tuple [$(← es.mapM (expandExpr ⟨·⟩)),*])
  -- `(l = r)`, `(l ⊕= r)`: by their tokens
  let r := e.raw
  if r.getNumArgs == 5 && r[0].isAtom && r[0].getAtomVal == "(" && r[2].isAtom &&
      r[2].getAtomVal.endsWith "=" && r[4].isAtom then
    let sym := r[2].getAtomVal
    if sym == "=" then
      return ← `(RawExpr.assign $(← expandExpr ⟨r[1]⟩) $(← expandExpr ⟨r[3]⟩))
    if let some op := BinOp.ofSym? (sym.dropRight 1) then
      return ← `(RawExpr.opAssign $(ctorIdent ``BinOp op) $(← expandExpr ⟨r[1]⟩)
        $(← expandExpr ⟨r[3]⟩))
  -- the operators, by their table: one arm for all of them
  if let some (op, a, b) := binParts? e then
    return ← `(RawExpr.binop $(ctorIdent ``BinOp op) $(← expandExpr ⟨a⟩) $(← expandExpr ⟨b⟩))
  if let some (op, a) := incDecParts? e then
    return ← `(RawExpr.incDec $(ctorIdent ``IncDec op) $(← expandExpr ⟨a⟩))
  expandExpr1 e
where
  expandExpr1 : TSyntax `sol_expr → MacroM Term
  | `(sol_expr| $n:num) => `(RawExpr.num $n)
  | `(sol_expr| $t:str) => do
    `(RawExpr.bytesLit $(← quoteBytes (t.getString.toUTF8.toList.map (·.toNat))))
  | `(sol_expr| hex $t:str) =>
    match hexBytes? t.getString with
    | some bs => do `(RawExpr.bytesLit $(← quoteBytes bs))
    | none => Macro.throwErrorAt t "hex\"…\": pairs of hex digits"
  | `(sol_expr| $x:ident) => expandIdent x
  | `(sol_expr| $e:sol_expr . $f:ident) => do fieldChain (← expandExpr e) (nameParts f.getId)
  | `(sol_expr| $e:sol_expr [ $k:sol_expr ]) => do
      `(RawExpr.index $(← expandExpr e) $(← expandExpr k))
  | `(sol_expr| $x:ident [ ]) => `(RawExpr.name $(quote ((x.getId.toString false) ++ "[]")))
  | `(sol_expr| $x:ident [ ] [ ]) => `(RawExpr.name $(quote ((x.getId.toString false) ++ "[][]")))
  | `(sol_expr| $e:sol_expr [ $i:sol_expr : $j:sol_expr ]) => do
      `(RawExpr.call "#slice" [$(← expandExpr e), $(← expandExpr i), $(← expandExpr j)])
  | `(sol_expr| $e:sol_expr [ $i:sol_expr : ]) => do
      let b ← expandExpr e
      `(RawExpr.call "#slice" [$b, $(← expandExpr i), RawExpr.call "#sliceEnd" []])
  | `(sol_expr| $e:sol_expr [ : ]) => do
      `(RawExpr.call "#slice" [$(← expandExpr e), RawExpr.num 0, RawExpr.call "#sliceEnd" []])
  | `(sol_expr| $e:sol_expr [ : $j:sol_expr ]) => do
      `(RawExpr.call "#slice" [$(← expandExpr e), RawExpr.num 0, $(← expandExpr j)])
  | `(sol_expr| ( $e:sol_expr )) => expandExpr e
  | `(sol_expr| ! $a) => do `(RawExpr.unop .not $(← expandExpr a))
  | `(sol_expr| - $a) => do `(RawExpr.unop .neg $(← expandExpr a))
  | `(sol_expr| ~ $a) => do `(RawExpr.unop .bnot $(← expandExpr a))
  | `(sol_expr| $c ? $a : $b) => do
      `(RawExpr.ternary $(← expandExpr c) $(← expandExpr a) $(← expandExpr b))
  | `(sol_expr| new $T:sol_ty ( $n:sol_expr )) => do
      `(RawExpr.newArr $(← expandTy T) $(← expandExpr n))
  | `(sol_expr| address ( this ) . balance) => `(RawExpr.env .selfBalance)
  | `(sol_expr| $n:num $u:ident) => do
      let some k := unitFactor? (u.getId.toString false) |
        Macro.throwErrorAt u "a unit is one of wei gwei ether seconds minutes hours days weeks"
      `(RawExpr.num $(quote (n.getNat * k)))
  | `(sol_expr| payable ( $e:sol_expr )) => do `(RawExpr.call "address" [$(← expandExpr e)])
  | `(sol_expr| address ( $e:sol_expr )) => do `(RawExpr.call "address" [$(← expandExpr e)])
  | `(sol_expr| $f:ident ( { $[$ns:ident : $as:sol_expr],* } )) => do
      `(RawExpr.named $(strLit f) [$(ns.map strLit),*] [$(← as.mapM expandExpr),*])
  | `(sol_expr| $f:sol_expr ( $as:sol_expr,* ) . $g:ident) => do
      if let some t ← typeBoundExpr f as.getElems g then return t
      fieldChain (← expandCall f as.getElems callMsg) (nameParts g.getId)
  | `(sol_expr| $f:sol_expr ( $as:sol_expr,* ) [ $k:sol_expr ]) => do
      `(RawExpr.index $(← expandCall f as.getElems callMsg) $(← expandExpr k))
  | `(sol_expr| $f:sol_expr ( $as:sol_expr,* ) ( $bs:sol_expr,* )) => do
      `(RawExpr.call callValueName
        [$(← expandCall f as.getElems callMsg), $(← bs.getElems.mapM expandExpr),*])
  | `(sol_expr| $f:sol_expr ( $as:sol_expr,* )) => expandCall f as.getElems callMsg
  | _ => Macro.throwUnsupported
  -- `f(a, b)`, a call of the function `f` (or a struct's constructor, `msg`
  -- says which): `RawExpr.call`
  expandCall (f : TSyntax `sol_expr) (as : Array (TSyntax `sol_expr)) (msg : String) :
      MacroM Term := do
  let some g := funName? f |
      -- a callee that is not a name: a function value (`callValueName`)
    `(RawExpr.call callValueName [$(← expandExpr f), $(← as.mapM expandExpr),*])
  `(RawExpr.call $(quote g) [$(← as.mapM expandExpr),*])

partial def expandStmt (s : TSyntax `sol_stmt) : MacroM Term := do
  -- `delete x` also parses as a declaration `T x` of a type called
  -- `delete`, and `require(c)` as a call (the categories read keywords as
  -- identifiers too): of an ambiguous parse, take the reading that starts
  -- with a keyword.
  if s.raw.isOfKind choiceKind then
    for alt in readings s (·[0].isAtom) do
      try return ← expandStmt ⟨alt⟩ catch _ => pure ()
    Macro.throwUnsupported
  -- `x++;`, `−−x;` and `l ⊕= r;`: by their tokens.  (`y = x++;` is read as
  -- an assignment of the expression `x++`, which `hoistStmt` makes an
  -- `assignIncDec` when `y` is a local: its other parse is not expanded.)
  let r := s.raw
  if let some (op, b, rhs) ← pushCompoundParts? r then
    return ← `(RawStmt.pushOpAssign $(ctorIdent ``BinOp op) $(← expandExpr b) $(← expandExpr rhs))
  if let some (op, b) ← pushIncrementParts? r then
    return ← `(RawStmt.pushIncDec $(ctorIdent ``IncDec op) $(← expandExpr b))
  if let some (op, l) := incDecParts? r then
    return ← `(RawStmt.incDec $(ctorIdent ``IncDec op) $(← expandExpr ⟨l⟩))
  if r.getNumArgs == 3 && r[1].isAtom && r[1].getAtomVal.endsWith "=" then
    if let some op := BinOp.ofSym? (r[1].getAtomVal.dropRight 1) then
      return ← `(RawStmt.opAssign $(ctorIdent ``BinOp op) $(← expandExpr ⟨r[0]⟩)
        $(← expandExpr ⟨r[2]⟩))
  -- the four keyword statements, by their node kind: a quotation pattern
  -- for them would be as ambiguous as the parse
  match s.raw.getKind with
  | ``solDelete => `(RawStmt.delete $(← expandExpr ⟨s.raw[1]⟩))
  | ``solRequire => `(RawStmt.require $(← expandExpr ⟨s.raw[2]⟩))
  | ``solAssert => `(RawStmt.assert $(← expandExpr ⟨s.raw[2]⟩))
  | ``solRevert => `(RawStmt.revert)
  | ``solAssumeFalse => `(RawStmt.assumeFalse)
  | ``solReturn => `(RawStmt.ret (some $(← expandExpr ⟨s.raw[1]⟩)))
  | ``solReturnNone => `(RawStmt.ret none)
  | ``solTry => expandTry s
  | ``solEmit => `(RawStmt.eval [$(← exprs s.raw[3]),*])
  | ``solRequireMsg =>
    let some m := s.raw[4].isStrLit? | Macro.throwErrorAt s.raw[4] "a string literal"
    `(RawStmt.requireMsg $(← expandExpr ⟨s.raw[2]⟩) $(quote m))
  | ``solRequireReason =>
    `(RawStmt.requireReason $(← expandExpr ⟨s.raw[2]⟩) $(← expandExpr ⟨s.raw[4]⟩))
  | ``solRequireErr =>
    `(RawStmt.requireErr $(← expandExpr ⟨s.raw[2]⟩) $(quote (s.raw[4].getId.toString false))
      [$(← exprs s.raw[6]),*])
  | ``solRevertErr => `(RawStmt.revertErr $(quote (s.raw[1].getId.toString false)) [$(← exprs s.raw[3]),*])
  | ``solRevertMsg =>
    let some m := s.raw[2].isStrLit? | Macro.throwErrorAt s.raw[2] "a string literal"
    `(RawStmt.revertMsg $(quote m))
  | ``solRevertReason => `(RawStmt.revertReason $(← expandExpr ⟨s.raw[2]⟩))
  | ``solRevertRaw => do
    unless s.raw[8].isNatLit? == some 32 && s.raw[6].getId == s.raw[13].getId do
      Macro.throwErrorAt s "raw rethrow expects revert(add(data, 32), mload(data))"
    `(RawStmt.revertRaw (RawExpr.name $(quote (s.raw[6].getId.toString false))))
  | ``solHole => `(RawStmt.hole)
  | ``solBreak => `(RawStmt.brk)
  | ``solContinue => `(RawStmt.cont)
  | ``solWhile | ``solFor | ``solDoWhile => expandStmt.loop s (← `({}))
  | ``solLoopSpec => do
    -- the clauses down to the loop, in the order written
    let mut cur := s.raw
    let mut inv : Array Term := #[]
    let mut dec : Option Term := none
    let mut unw : Option Term := none
    let mut qinv : Array Term := #[]
    while cur.getKind == ``solLoopSpec do
      let cl := cur[0]
      if cl.getKind == ``solLoopForall then
        qinv := qinv.push (← expandStmt.loopForall cl[8] cl[9] cl[11])
        cur := cur[1]
        continue
      let k := (cl[5].getId.toString false)
      let e := cl[6]
      match k with
      | "invariant" => inv := inv.push (← expandExpr ⟨e⟩)
      | "decreases" =>
        if dec.isSome then Macro.throwErrorAt cur "a loop has one `decreases` clause"
        dec := some (← expandExpr ⟨e⟩)
      | "unwind" =>
        let some n := e.isNatLit? <|> e[0].isNatLit? |
          Macro.throwErrorAt e "`/// @custom:key unwind k` takes a number"
        if unw.isSome then Macro.throwErrorAt cur "a loop has one `unwind` clause"
        unw := some (quote n)
      | _ => Macro.throwErrorAt cl[5] "a loop's clause is `invariant`, `decreases` or `unwind`"
      cur := cur[1]
    unless cur.getKind == ``solWhile || cur.getKind == ``solFor || cur.getKind == ``solDoWhile do
      Macro.throwErrorAt cur "a `/// @custom:key` clause stands above a loop"
    let decT ← match dec with
      | some d => `(some $d)
      | none => `(none)
    let unwT ← match unw with
      | some n => `(some $n)
      | none => `(none)
    expandStmt.loop ⟨cur⟩
      (← `({ inv := [$inv,*], dec := $decT, unwind := $unwT, qinv := [$qinv,*] : RawLoopSpec }))
  | ``solPushTarget =>
    expandStmt.pushTarget s ⟨s.raw[0]⟩ (← expandExpr ⟨s.raw[0]⟩) (← expandExpr ⟨s.raw[3]⟩)
  | ``solUnchecked => `(RawStmt.unchecked $(← expandStmt.expandBlock ⟨s.raw[1]⟩))
  | ``solChecked => `(RawStmt.checked .checking $(← expandStmt.expandBlock ⟨s.raw[1]⟩))
  | ``solIgnoringOverflow =>
    `(RawStmt.checked .ignoring $(← expandStmt.expandBlock ⟨s.raw[1]⟩))
  | ``solBlockStmt => `(RawStmt.block [$(← (payload s.raw[1]).mapM (expandStmt ⟨·⟩)),*])
  | ``solTupleAssign =>
    let ts ← (#[s.raw[1]] ++ s.raw[2].getArgs).mapM fun o => do
      match payload o with
      | #[e] => `(some $(← expandExpr ⟨e⟩))
      | _ => `(none)
    `(RawStmt.tupleAssign [$ts,*] $(← expandExpr ⟨s.raw[5]⟩))
  | ``solTupleDecl =>
    let vs ← (#[s.raw[1]] ++ s.raw[2].getArgs).mapM fun o => do
      match payload o with
      | #[T, x] => `(some ($(← expandTy ⟨T⟩), $(strLit ⟨x⟩)))
      | _ => `(none)
    `(RawStmt.tupleDecl [$vs,*] $(← expandExpr ⟨s.raw[5]⟩))
  | ``solIfChain =>
    -- `if (c₀) b₀ else if (c₁) b₁ … else e`: nested, from the last branch out
    let arms := payload s.raw[5]
    let last : Term ← match payload s.raw[6] with
      | #[f] => expandStmt.expandBlock ⟨f⟩
      | _ => `([])
    let els ← (List.range (arms.size / 2)).foldrM (init := last) fun k els => do
      `([RawStmt.ite $(← expandExpr ⟨arms[2 * k]!⟩) $(← expandStmt.expandBlock ⟨arms[2 * k + 1]!⟩)
        $els])
    `(RawStmt.ite $(← expandExpr ⟨s.raw[2]⟩) $(← expandStmt.expandBlock ⟨s.raw[4]⟩) $els)
  | _ => expandStmt1 s
where
  /-- The expressions of a `sol_expr,*`. -/
  exprs (as : Syntax) : MacroM (Array Term) := as.getSepArgs.mapM (expandExpr ⟨·⟩)
  /-- `\forall T x; b`, a quantified invariant clause (`RawInv`); a sort as the
  specification language reads it, an `address` a `uint`. -/
  loopForall (T x body : Syntax) : MacroM Term := do
    let p ← match (T.getId.toString false) with
      | "uint" | "address" => `(PrimTy.uint)
      | "int" => `(PrimTy.int)
      | "bool" => `(PrimTy.bool)
      | s => Macro.throwErrorAt T s!"a quantifier ranges over uint, int, bool or address, not {s}"
    let b ← match (⟨body⟩ : TSyntax `sol_loop_inv) with
      | `(sol_loop_inv| \forall $T':ident $x':ident; $b') => loopForall T' x' b'
      | `(sol_loop_inv| $a:sol_expr -> $c:sol_expr) => do
        `(RawInv.imp $(← expandExpr a) $(← expandExpr c))
      | `(sol_loop_inv| $e:sol_expr) => do `(RawInv.expr $(← expandExpr e))
      | _ => Macro.throwErrorAt body "a quantified invariant's body is `e` or `a -> c`"
    `(RawInv.all $p $(strLit ⟨x⟩) $b)
  expandStmt1 : TSyntax `sol_stmt → MacroM Term
  | `(sol_stmt| $l:sol_expr = $r:sol_expr) => do assignTo l (← expandExpr r)
  | `(sol_stmt| $l:sol_expr = $b:sol_expr .push()) => do
      `(RawStmt.assignPush $(← expandExpr l) $(← expandExpr b))
  | `(sol_stmt| $l:sol_expr = $f:sol_expr ( )) => do
      match funName? f with
      | some g => assignTo l (← `(RawExpr.call $(quote g) []))
      | none =>
        if let some b ← pushRecv? f then
          `(RawStmt.assignPush $(← expandExpr l) $b)
        else assignTo l (← expandExpr.expandCall f #[] callMsg)
  | `(sol_stmt| $l:sol_expr = $f:sol_expr ( $as:sol_expr,* )) => do
      if let some s ← send? none (← expandExpr l) f as.getElems then return s
      assignTo l (← expandExpr.expandCall f as.getElems callMsg)
  | `(sol_stmt| $T:sol_ty $x:ident = $b:sol_expr .push()) => do
      `(RawStmt.declPush $(← expandTy T) $(strLit x) $(← expandExpr b))
  | `(sol_stmt| $T:sol_ty $x:ident = $f:sol_expr ( )) => do
      match funName? f with
      | some g => `(RawStmt.decl $(← expandTy T) $(strLit x) (some (RawExpr.call $(quote g) [])))
      | none =>
        if let some b ← pushRecv? f then
          `(RawStmt.declPush $(← expandTy T) $(strLit x) $b)
        else `(RawStmt.decl $(← expandTy T) $(strLit x)
          (some $(← expandExpr.expandCall f #[] callMsg)))
  | `(sol_stmt| $T:sol_ty $x:ident = $f:sol_expr ( $as:sol_expr,* )) => do
      if let some s ← send? (some (← expandTy T)) (← `(RawExpr.name $(strLit x))) f as.getElems then
        return s
      `(RawStmt.decl $(← expandTy T) $(strLit x) (some $(← expandExpr.expandCall f as.getElems callMsg)))
  | `(sol_stmt| $f:sol_expr ( $a:sol_expr, $as:sol_expr,* )) => do
      `(RawStmt.call $(← expandExpr f) [$(← expandExpr a), $(← as.getElems.mapM expandExpr),*])
  | `(sol_stmt| $T:sol_ty memory $x:ident = $f:sol_expr ( $as:sol_expr,* )) => do
      `(RawStmt.declMemory $(← expandTy T) $(strLit x)
        (some $(← expandExpr.expandCall f as.getElems ctorMsg)))
  | `(sol_stmt| $b:sol_expr ( $g:sol_expr ( $as:sol_expr,* ) )) => do
      `(RawStmt.call $(← expandExpr b) [$(← expandExpr.expandCall g as.getElems ctorMsg)])
  | `(sol_stmt| $b:sol_expr .push( $g:sol_expr ( $as:sol_expr,* ) )) => do
      `(RawStmt.call (.field $(← expandExpr b) "push") [$(← expandExpr.expandCall g as.getElems ctorMsg)])
  | `(sol_stmt| $T:sol_ty storage $x:ident = $b:sol_expr .push()) => do
      `(RawStmt.declStoragePush $(← expandTy T) $(strLit x) $(← expandExpr b))
  | `(sol_stmt| $T:sol_ty storage $x:ident = $f:sol_expr ( )) => do
      match funName? f with
      | some g => `(RawStmt.declStorage $(← expandTy T) $(strLit x)
          (some (RawExpr.call $(quote g) [])))
      | none => `(RawStmt.declStoragePush $(← expandTy T) $(strLit x) $(← pushRecv f))
  | `(sol_stmt| $T:sol_ty storage $x:ident = $e) => do
      `(RawStmt.declStorage $(← expandTy T) $(strLit x) (some $(← expandExpr e)))
  | `(sol_stmt| $T:sol_ty storage $x:ident) => do
      `(RawStmt.declStorage $(← expandTy T) $(strLit x) none)
  | `(sol_stmt| $T:sol_ty calldata $x:ident = $e) => do
      `(RawStmt.declMemory $(← expandTy T) $(strLit x)
        (some (RawExpr.call "#sliceBind" [$(← expandExpr e)])))
  | `(sol_stmt| $T:sol_ty memory $x:ident = $e) => do
      `(RawStmt.declMemory $(← expandTy T) $(strLit x) (some $(← expandExpr e)))
  | `(sol_stmt| $T:sol_ty memory $x:ident) => do
      `(RawStmt.declMemory $(← expandTy T) $(strLit x) none)
  | `(sol_stmt| $T:sol_ty $x:ident = $e) => do
      `(RawStmt.decl $(← expandTy T) $(strLit x) (some $(← expandExpr e)))
  | `(sol_stmt| $T:sol_ty $x:ident) => do
      `(RawStmt.decl $(← expandTy T) $(strLit x) none)
  | `(sol_stmt| $b:sol_expr .push( $a:sol_expr )) => do
      `(RawStmt.call (.field $(← expandExpr b) "push") [$(← expandExpr a)])
  | `(sol_stmt| $b:sol_expr .push()) => do `(RawStmt.call (.field $(← expandExpr b) "push") [])
  | `(sol_stmt| $b:sol_expr .pop()) => do `(RawStmt.call (.field $(← expandExpr b) "pop") [])
  | `(sol_stmt| $r:sol_expr .transfer( $a:sol_expr )) => do
      `(RawStmt.call (.field $(← expandExpr r) "transfer") [$(← expandExpr a)])
  | `(sol_stmt| $l:sol_expr = $r:sol_expr .send( $a:sol_expr )) => do
      `(RawStmt.send none $(← expandExpr l) $(← expandExpr r) $(← expandExpr a) false)
  | `(sol_stmt| $T:sol_ty $x:ident = $r:sol_expr .send( $a:sol_expr )) => do
      `(RawStmt.send (some $(← expandTy T)) (.name $(strLit x)) $(← expandExpr r)
        $(← expandExpr a) false)
  | `(sol_stmt| ( $l:sol_expr , ) = $f:sol_expr { value : $a:sol_expr } ( $d:str )) => do
      unless d.getString.isEmpty do Macro.throwErrorAt d "a value call with no calldata only"
      let some r ← recvOf? "call" f | Macro.throwErrorAt f "`r.call{value: a}(\"\")`"
      `(RawStmt.send none $(← expandExpr l) $r $(← expandExpr a) true)
  | `(sol_stmt| ( $T:sol_ty $x:ident , ) = $f:sol_expr { value : $a:sol_expr } ( $d:str )) => do
      unless d.getString.isEmpty do Macro.throwErrorAt d "a value call with no calldata only"
      let some r ← recvOf? "call" f | Macro.throwErrorAt f "`r.call{value: a}(\"\")`"
      `(RawStmt.send (some $(← expandTy T)) (.name $(strLit x)) $r $(← expandExpr a) true)
  | `(sol_stmt| $f:sol_expr ( )) => do `(RawStmt.call $(← expandExpr f) [])
  | `(sol_stmt| $f:sol_expr ( $a:sol_expr )) => do
      `(RawStmt.call $(← expandExpr f) [$(← expandExpr a)])
  | `(sol_stmt| if ($c) $t $[else $f]?) => do
      let els ← match f with
        | some f => expandBlock f
        | none => `([])
      `(RawStmt.ite $(← expandExpr c) $(← expandBlock t) $els)
  | _ => Macro.throwUnsupported
  /-- A struct constructor's callee. -/
  ctorMsg : String := "a constructor's name is a struct's name"
  /-- `values.push`, `bucket.tokens.push` (one identifier) or `e.tokens.push`:
  the receiver `values`, `bucket.tokens`, `e.tokens`; none for another callee. -/
  pushRecv? (f : TSyntax `sol_expr) : MacroM (Option Term) := recvOf? "push" f
  /-- The receiver of the member `m` called: `to` of `to.send`, as
  `pushRecv?` reads `values.push`. -/
  recvOf? (m : String) (f : TSyntax `sol_expr) : MacroM (Option Term) := do
    match f with
    | `(sol_expr| $x:ident) =>
      match x.getId with
      | .str p m' => if p.isAnonymous || m' != m then pure none else some <$> expandIdent (mkIdent p)
      | _ => pure none
    | `(sol_expr| $e:sol_expr . $g:ident) =>
      match (nameParts g.getId).reverse with
      | m' :: fs => if m' == m then some <$> fieldChain (← expandExpr e) fs.reverse else pure none
      | _ => pure none
    | _ => pure none
  /-- `l = r.send(a);` and `T x = r.send(a);` where the receiver is a name or
  a member chain (`to.send` is one identifier): the send, else none. -/
  send? (T : Option Term) (l : Term) (f : TSyntax `sol_expr) (as : Array (TSyntax `sol_expr)) :
      MacroM (Option Term) := do
    let #[a] := as | pure none
    let some r ← recvOf? "send" f | pure none
    let T ← match T with
      | some T => `(some $T)
      | none => `(none)
    some <$> `(RawStmt.send $T $l $r $(← expandExpr a) false)
  /-- The receiver of `b.push` (`pushRecv?`). -/
  pushRecv (f : TSyntax `sol_expr) : MacroM Term := do
    match ← pushRecv? f with
    | some b => pure b
    | none => Macro.throwErrorAt f "only `b.push()` is a call on the right of `=`"
  /-- `l = r;`, `r` expanded: the assignment, or, when `l` is `b.push()`, the
  push `b.push(r);` (the front end normalises a push used as a target
  so).  solc evaluates `r` before the push's receiver; `b` is a name or a
  member chain, which no effect of `r` moves and which cannot revert, so
  evaluating it first, as `b.push(r)` does, is the same run, and the slot the
  push adds is written once either way. -/
  assignTo (l : TSyntax `sol_expr) (r : Term) : MacroM Term := do
    if l.raw.isOfKind ``solTupleExpr then
      let ts := #[l.raw[1]] ++ l.raw[3].getSepArgs
      return ← `(RawStmt.tupleAssign [$(← ts.mapM fun t => do `(some $(← expandExpr ⟨t⟩))),*] $r)
    if let `(sol_expr| $f:sol_expr ( $as:sol_expr,* )) := l then
      if as.getElems.isEmpty then
        if let some b ← pushRecv? f then return ← pushTarget l f b r
    `(RawStmt.assign $(← expandExpr l) $r)
  /-- `b.push() = r;`, `b` and `r` expanded: the push `b.push(r);` when the
  receiver, spelt `chain` (`b` or `b.push`), is a name or a member chain
  (`assignTo` says why the order is solc's); refused at `ref` otherwise. -/
  pushTarget (ref : Syntax) (chain : TSyntax `sol_expr) (b r : Term) : MacroM Term := do
    unless nameChain chain do Macro.throwErrorAt ref pushTargetMsg
    `(RawStmt.call (.field $b "push") [$r])
  /-- A name or a member chain of names: `values`, `bucket.tokens`,
  `bucket .tokens.push`. -/
  nameChain : TSyntax `sol_expr → Bool
    | `(sol_expr| $_:ident) => true
    | `(sol_expr| $e:sol_expr . $_:ident) => nameChain e
    | _ => false
  expandBlock : TSyntax `sol_block → MacroM Term
    | `(sol_block| { $[$ss:sol_stmt;]* }) => do `([$(← ss.mapM expandStmt),*])
    | _ => Macro.throwUnsupported
  /-- A loop, with its specification `spec`. -/
  loop (s : TSyntax `sol_stmt) (spec : Term) : MacroM Term := do
    let r := s.raw
    match r.getKind with
    | ``solWhile => `(RawStmt.whileLoop $spec $(← expandExpr ⟨r[2]⟩) $(← expandBlock ⟨r[4]⟩))
    | ``solDoWhile => `(RawStmt.doWhile $spec $(← expandBlock ⟨r[1]⟩) $(← expandExpr ⟨r[4]⟩))
    | _ =>
      let part (o : Syntax) : MacroM Term := do
        match payload o with
        | #[t] => `([$(← expandStmt ⟨t⟩)])
        | _ => `([])
      let c ← match payload r[4] with
        | #[e] => `(some $(← expandExpr ⟨e⟩))
        | _ => `(none)
      `(RawStmt.forLoop $spec $(← part r[2]) $c $(← part r[6]) $(← expandBlock ⟨r[8]⟩))
  /-- A clause's parameter: its type and its name, if it has one. -/
  tparam (p : Syntax) : MacroM (Term × Option String) := do
    let T ← expandTy ⟨p[0]⟩
    pure (T, if p[2].getNumArgs > 0 then some (p[2][0].getId.toString false) else none)
  /-- The receiver of an external call: `I(a)` and `address(a)` are `a`. -/
  extRecv (r : TSyntax `sol_expr) : MacroM Term := do
    match r with
    | `(sol_expr| $_:ident ( $a:sol_expr )) => expandExpr a
    | _ => expandExpr r
  /-- `e.f(a₁, …)`: the receiver `e`, the name `f`, the arguments. -/
  extCall (e : TSyntax `sol_expr) : MacroM (Term × String × Array Term) := do
    let `(sol_expr| $f:sol_expr ( $as:sol_expr,* )) := e
      | Macro.throwErrorAt e "`try` takes an external call `e.f(…)`"
    let args ← as.getElems.mapM expandExpr
    match f with
    | `(sol_expr| $x:ident) =>
      match (nameParts x.getId).reverse with
      | g :: r :: rs => do
        let rs := (r :: rs).reverse
        pure (← fieldChain (← expandIdent (mkIdent (.mkSimple rs.head!))) rs.tail, g, args)
      | _ => Macro.throwErrorAt e "`try` takes an external call `e.f(…)`"
    | `(sol_expr| $r:sol_expr . $g:ident) =>
      match (nameParts g.getId).reverse with
      | h :: fs => do pure (← fieldChain (← extRecv r) fs.reverse, h, args)
      | [] => Macro.throwUnsupported
    | `(sol_expr| $c:sol_expr ( $bs:sol_expr,* ) . $g:ident) => do
      let r ← match bs.getElems with
        | #[b] => if (funName? c).isSome then expandExpr b else expandExpr.expandCall c bs.getElems callMsg
        | _ => expandExpr.expandCall c bs.getElems callMsg
      match (nameParts g.getId).reverse with
      | h :: fs => do pure (← fieldChain r fs.reverse, h, args)
      | [] => Macro.throwUnsupported
    | _ => Macro.throwErrorAt e "`try` takes an external call `e.f(…)`"
  /-- `try …`, its clauses normalised as solkey's `TryStatement.of` does. -/
  expandTry (s : TSyntax `sol_stmt) : MacroM Term := do
    let r := s.raw
    let (recv, f, args) ← extCall ⟨r[1]⟩
    let mut rets : Array Term := #[]
    if r[2].getNumArgs > 0 then
      for p in r[2][2].getSepArgs do
        let (T, x) ← tparam p
        let some x := x | Macro.throwErrorAt p "an external call's return value is named"
        rets := rets.push (← `(($T, $(quote x))))
    let ok ← expandBlock ⟨r[3]⟩
    let mut err : Option Term := none
    let mut pnc : Option Term := none
    let mut code : Option String := none
    let mut other : Option Term := none
    for c in r[4].getArgs do
      let c := if c.getKind == nullKind && c.getNumArgs == 1 then c[0] else c
      match c.getKind with
      | ``solCatchError =>
        let b ← expandBlock ⟨c[5]⟩
        -- a named reason: bound by `catchData` (`catchBinder`)
        err := some (← match (← tparam c[3]) with
          | (T, some x) => `(RawStmt.declMemory $T $(quote x) (some (.name "catch$reason")) :: $b)
          | (_, none) => pure b)
      | ``solCatchPanic =>
        pnc := some (← expandBlock ⟨c[5]⟩)
        code := (← tparam c[3]).2
      | ``solCatchData =>
        let b ← expandBlock ⟨c[4]⟩
        other := some (← match (← tparam c[2]) with
          | (T, some x) => `(RawStmt.declMemory $T $(quote x) (some (.name "catch$data")) :: $b)
          | (_, none) => pure b)
      | ``solCatchAll => other := some (← expandBlock ⟨c[1]⟩)
      | _ => Macro.throwErrorAt c "a `catch` clause"
    let otherB ← match other with
      | some b => pure b
      | none => `([RawStmt.revert])
    `(RawStmt.tryCall $recv $(quote f) [$args,*] [$rets,*] $ok $(err.getD otherB)
        $(quote code) $(pnc.getD otherB) $otherB)

macro_rules
  | `(sol_raw!{ $[$ss:sol_stmt;]* }) => do
      let body ← `([$(← ss.mapM expandStmt),*])
      -- a slice read as a view (`RawStmt.sliceViews`, `Syntax/Elab.lean`)
      if ss.any (fun s => (s.raw.find? fun s =>
          [``solSlice, ``solSliceFrom, ``solSliceTo, ``solSliceAll, ``solCalldataLocal].contains s.getKind).isSome) then
        `($(mkIdent `Solidity.RawStmt.sliceViews) $body)
      else pure body

end Expand

end Solidity
