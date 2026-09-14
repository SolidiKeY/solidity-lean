# SolSpec: a Dafny-style specification language in Solidity NatSpec

SolSpec is a contract specification language written entirely in
Solidity NatSpec comments. A specified contract is still a `.sol` file
that `solc` compiles — the specification lives in `@custom:` tags, which
Solidity reserves for exactly this purpose — and the VS Code extension
(`vscode-extension/`) proves it against the executable semantics in
`Solidity/Semantics.lean`.

```solidity
/// @custom:invariant balSender + balTo <= 2**256 - 1
contract Bank {
    uint256 balSender;
    uint256 balTo;

    /// @custom:requires amount <= balSender
    /// @custom:ensures balSender == old(balSender) - amount
    /// @custom:ensures balTo == old(balTo) + amount
    /// @custom:modifies balSender, balTo
    function transfer(uint256 amount) public {
        balSender -= amount;
        balTo += amount;
    }
}
```

Save the file, and every clause gets a verdict on its own line.

## Why this is not the `.solj` judgment language

`.solj` files (the extension's other input) are raw dynamic-logic
judgments proved by `sol_wp`, and they run from **one fixed store**:
every value in the initial state is a literal, the interpreter reduces to
a verdict, and the postcondition to a ground Boolean. That is a test that
happens to be machine-checked.

SolSpec quantifies. The front-end builds the initial state out of Lean
*variables* — one per primitive storage leaf and per parameter — so
`@custom:requires`/`@custom:ensures` mean what they mean in Dafny: for
**every** state satisfying the precondition, the body establishes the
postcondition. The proof obligation is a universally quantified theorem,
and `sol_spec` (`Solidity/Spec/Tactic.lean`) discharges
it by symbolic execution plus arithmetic.

One pleasant consequence: `old(e)` needs no machinery. The pre-state maps
each name to its variable, so reading `e` "at entry" *is* reading the
variables.

## The clauses

Every clause is one line. Tags live in the `@custom:` namespace, so an
unannotated `solc` build is unaffected, and any `@custom:` tag SolSpec
does not know (`@custom:security-contact`, say) is ignored rather than
rejected.

### On a contract

| Tag | Meaning |
| --- | --- |
| `@custom:invariant P` | Assumed on entry to every non-constructor function, and proved on exit from every function including the constructor. |

### On a function

| Tag | Meaning |
| --- | --- |
| `@custom:requires P` | Assumed on entry. Repeatable; the conjunction is the precondition. |
| `@custom:ensures P` | Proved on exit. Repeatable — **one obligation per clause**, so a failure lands on the line that caused it. |
| `@custom:modifies a, b` | Frame: every storage root *not* listed still holds its entry value. `@custom:modifies` with nothing after it is the empty frame. Omit the tag entirely and no frame obligation is generated. |
| `@custom:reverts_when P` | From a state satisfying the precondition and `P`, the body must halt with `revert`. |
| `@custom:partial` | Switch to partial correctness: a `revert` discharges the obligation vacuously (the box modality). Without it, a specification is *total* — the function must not revert. |
| `@custom:free` | Assume the specification instead of proving it. The function is reported `assumed`. |
| `@custom:tactic <tac>` | Prove this function's obligations with `<tac>` instead of `sol_spec`. The escape hatch for a specification the automation cannot reach. |

### Inside a function body

| Tag | Meaning |
| --- | --- |
| `/// @custom:assert P` | An obligation at that program point — and, as in Dafny, an assumption from there on (sound, because it carries its own obligation). |
| `/// @custom:assume P` | An unchecked assumption from that point on. |

`@custom:decreases`, and `@custom:invariant` written on a *function*, are
rejected with an explanation rather than ignored: the verified fragment
has no loops, so there is nothing for them to mean.

## The expression language

Specification expressions are Solidity expressions plus the logical
vocabulary Solidity does not have. They are compiled to Lean
propositions over the state, not to Solidity code, so they are strictly
richer than what the program can compute.

| Form | Notes |
| --- | --- |
| `+ - * / % **` | `/` and `%` are truncating (`Int.tdiv`/`Int.tmod`), matching the interpreter. `**` needs a literal exponent. |
| `< > <= >= == !=` | `==` on booleans is `↔`. |
| `&& \|\| !` | |
| `==> <==>` | Implication and equivalence, right associative, looser than `? :`. |
| `c ? a : b` | |
| `a.f`, `a[i]`, `a.length` | Struct member, array element or mapping entry, array length. |
| `old(e)` | `e` evaluated in the entry state. Legal in `ensures`, invariants and ghost steps. |
| `forall i in lo .. hi :: P` | Bounded quantifier over the half-open range `[lo, hi)`. |
| `exists i in lo .. hi :: P` | Likewise. |
| `result` | The return value. A named return (`returns (uint256 out)`) is referred to by its own name. |

Parameters are read at their **current** value, as Solidity parameters
are assignable; write `old(amount)` for the entry value.

### Well-formedness

Reading `a[i]` on an *array* in a proved clause (an `ensures`, an
invariant, a ghost `assert`) adds `0 <= i && i < a.length` to that
clause's obligation — Dafny's discipline, so a specification cannot be
accidentally satisfied by an out-of-range read. Mapping reads need no
side condition (an absent key reads the type's default, as in Solidity).
`requires` clauses are *assumed as written* and carry no well-formedness
obligation.

## Arithmetic, overflow, and what `uint256` buys you

The official interpreter computes over `Int` but applies solc's checked
arithmetic at `uint256`/`int256` (`Semantics.checkArith`): an
out-of-range `+`/`-`/`*`/`**`/`++`/`--`/compound result **reverts**.
SolSpec obligations are stated over that interpreter, so overflow is a
revert to them — under the partial reading `[body] post` a
`@custom:partial` clause is discharged vacuously by an overflow, under the
total reading `⟨body⟩ post` every `ensures` fails on it. Narrower widths
(`uint8`, …) are not modelled by the interpreter, so for them SolSpec
gets bounded arithmetic the other way round:

* every integral input — storage leaf or parameter — is **assumed** to
  satisfy its declared range (`Spec.inRange 0 255 x` for a `uint8`);
* every integral storage leaf, and an integral return value, is
  **proved** to satisfy its range on exit. This is the generated
  `_range` obligation, one per function.

An overflow or an underflow therefore surfaces as a failed `_range`
obligation, at the function's own line. In the `Bank` example above,
drop `@custom:requires amount <= balSender` and `Bank_transfer_range`
stops being provable, because `balSender - amount` can go negative;
drop the contract invariant and it fails on the other side, because
`balTo + amount` can exceed `2^256 - 1`.

The bounds are emitted as decimal numerals rather than `2 ^ 256`, so the
residual goals are linear integer arithmetic and `omega` closes them.

## What is verified, and what is reported

The fragment is the one the semantics models. Everything inside it is
proved; everything outside is **reported**, never silently skipped — an
unsupported function shows up as a warning on its own line with the
reason.

**Supported.** `uintN`/`intN`/`bool`/`address` state variables and
parameters; structs with primitive and struct members; `T[]` arrays;
`mapping(K => V)`; local declarations of primitive type; assignment,
compound assignment (`+=` …), `++`/`--`; `require`, `assert`, `revert()`;
`if`/`else`; `delete`; `a.push(v)`, `a.pop()`; `x.transfer(v)`; `return`
as the last statement of a function.

**Reported as `unsupported`.** Loops (`for`, `while`, `do`) — the
semantics has no loop rule, which is also why there are no loop
invariants. Function calls and modifiers — the interpreter has no call
rule; inline the callee. `bytes`/`string`/fixed-size arrays. Memory and
storage *aliases* (`Person storage p = …`) as locals. `unchecked`,
`assembly`, `try`, `emit`. Early `return`, and ghost steps inside an
`if` branch. Non-primitive parameters, multiple return values, and a
local that shadows a state variable.

**Modelled, but opaquely.** An array's elements and a mapping's entries
are Lean variables, so `a.length` and a read-back-after-write at the same
key work, while a read at a symbolic index into an untouched array does
not reduce. Such an obligation is reported *unproved*, never proved by
accident.

## How an obligation is built

For a function `f` of contract `C`, the generator emits

* `C_f_state` — the entry state, one Lean variable per primitive storage
  leaf and per parameter, named returns bound to their type's zero;
* `C_f_body` — the body as a `List Spec.Ann`, where a ghost `assert`
  appears as `Ann.assume` (it has its own obligation) and a ghost
  `assume` as `Ann.assume`;
* one theorem per clause, each carrying the same hypotheses: the range
  of every input, then the contract invariants (except in a
  constructor, which establishes them rather than assuming them), then
  the `@custom:requires`.

The goal is `Spec.totalVC state body Q` — or `Spec.partialVC` under
`@custom:partial`, or `Spec.revertsVC state body` for
`@custom:reverts_when`. `Spec.vc` walks the annotated block through
`Semantics.execStmt`, so the obligation is stated against the same
interpreter the EVM-compiler correctness proof uses; nothing about
SolSpec is axiomatic.

`Solidity/Spec/Examples.lean` is the `Bank` contract's
obligations written by hand, in exactly the shape the generator emits.
It is the reference for the code generator: if the two stop agreeing,
one of them is wrong.

## Writing a specification in Lean: `solspec!`

The same language is a Lean notation, so a specification can be written
and proved directly without going through a `.sol` file. Each
`@custom:` tag becomes a keyword clause:

```lean
def store (age total balance amount : Int) : Semantics.State :=
  { storage :=
      [("age", SVal.int age), ("total", SVal.int total),
       ("balance", SVal.int balance)],
    env := [("amount", Binding.val (Value.int amount))] }

theorem move_spec (age total balance amount : Int) :
    solspec!{ requires (amount <= age)
              ensures (age == old(age) - amount)
              ensures (total == old(total) + amount)
              modifies age, total
              < age -= amount; total += amount > }
      (store age total balance amount) := by
  sol_spec [store]
```

`solspec!{ clauses < body > }` elaborates to a `Semantics.State -> Prop`
(`Spec.Obligation`, conjoined with `Spec.RevertObligation` when there is
a `reverts_when`), so you apply it to the entry state you want to
quantify over — and, since that state is built from Lean variables, the
obligation quantifies over every store of that shape.

The modality is the bracket, exactly as in `sol!`: `< body >` is total
correctness, `[ body ]` partial. `@custom:partial` in a `.sol` file is
the square-bracket form here, which is why there is no `partial` clause.

Ghost steps are written positionally in the body:

```lean
solspec!{ ensures (total == 1)
          < age = 1; ghost assert (age == 1); total = age > }
```

Every clause proposition is parenthesized — `requires (amount <= age)`,
not `requires amount <= age`. That is not decoration: a clause is
followed by the body's `<` or `[`, and an unparenthesized trailing
comparison would swallow it (`ensures a == b < body >` parses
`b < body` as a comparison). The parentheses are exactly what lets
comparisons be *unparenthesized inside* a clause, which the program
language cannot do at all.

### It is the program's own language

`solspec!` adds almost no grammar of its own. The body is `sol_stmt`,
wrapped by `sol_ann` only to make room for the ghost steps; clause
expressions are `sol_expr`, wrapped by `sol_prop` only to add what a
specification needs and a program cannot express — unparenthesized
comparisons (a clause is not inside the modality brackets, so there is
no trailing `>` to swallow), `==>`, `<==>`, and the bounded
quantifiers. A path with no specification-level index is handed straight
to `sexpr!`.

It is a separate notation from `sol!` rather than another `sol!` form
because the two say different things: `sol!` is a judgment about one run
of a program, `solspec!` an obligation over every entry state satisfying
a precondition.

### Where it differs from the `.sol` form

Four differences, all traceable to one cause — `solspec!` has no
contract declaration to read types from:

* **Names resolve as the program resolves them**, through
  `SoliditySyntax.rootExpr`'s fixed table (`age`, `total`, `balance`,
  `values`, `alice`, …). For a root it does not know, use the program
  language's own escape hatch: `balSender@@uint`.
* **`==` is integer equality.** Write `<==>` for boolean equivalence
  (`a == true` is recognized and treated as boolean).
* **No automatic range obligation.** Nothing declares `uint8` versus
  `uint256`, so state the bound you want as an ordinary `ensures`.
* **`modifies` is stated against the entry state's own storage list**
  rather than against the declaration list — the same meaning, computed
  from what the store actually holds (`Spec.modifiesOnly`).

One restriction: `old(e)` may not appear inside a path *index*
(`values[old(i)]`), which would need the entry state to build a program
expression. A quantifier binder, on the other hand, may: it is a Lean
`Int`, injected as an integer literal, so
`forall i in 0 .. values.length :: values[i] <= total` works. That is
the one place a specification path cannot defer to `sexpr!`.

One cost worth knowing: importing `Spec/Syntax.lean` reserves
`requires`, `ensures`, `invariant`, `modifies`, `reverts_when`, `ghost`
and `assume` as Lean tokens, so they stop being usable as identifiers in
any file that imports it. `AST.lean` already makes the same trade for
`assert`, `require`, `delete` and `revert`; the difference is that this
module is opt-in — it is in `SoliditySpec`, not
`Solidity` — so the cost is paid only where specifications are
written. The `sol_spec` tactic does not depend on it.

`Spec/SyntaxExamples.lean` has one `#check` per clause form (grammar
only) followed by the proved versions, so a parser problem and an
automation problem stay distinguishable.

## Running it

In VS Code: open a `.sol` file with `@custom:` clauses in a workspace
containing the Lake package. Every clause is verified on open and on
save; failures get a squiggle carrying Lean's message, unsupported
functions a warning, and the status bar shows `SolLoom: k/n proved`.
`SolLoom: Show Generated Lean` opens the obligation file beside it.

Headless:

```sh
cd vscode-extension && npm install && npx tsc
node out/specCli.js examples/spec/Bank.sol ..
```

One line per obligation plus a summary. Exit codes: `0` = every
obligation verified, `1` = some obligation failed, `2` = infrastructure
error. Functions reported `unsupported` do not fail the run — they were
never attempted.

The Lean side lives in its own Lake target so a broken specification run
cannot break the main build. It also depends on the interpreter alone —
the assertion layer, the `sol_spec` tactic and the `solspec!` notation
need nothing else, and the package itself has no external dependencies —
so this is a seconds-long build:

```sh
./scripts/check-spec.sh            # assertion layer, tactic, worked examples
./scripts/check-spec.sh --tactic   # just what the extension needs
```

The extension runs `lake build Solidity.Spec.Tactic`
itself before elaborating. That target depends on the interpreter and
nothing else — `sol_eval_battery` was moved out of `Wp/Verifier.lean`
into `EvalBattery.lean` precisely so it would not drag the wp layer onto
this path — so it is cheap even on a cold cache.

## Limitations worth knowing before you rely on this

* **No loops, no calls.** Both are semantics-level gaps, not front-end
  gaps: `Stmt` has neither a loop constructor nor a call rule the
  interpreter can execute. Inlining a callee by hand is the workaround.
* **Overflow is a range obligation, not a revert.** Solidity 0.8 reverts
  on overflow; the interpreter does not model that. A proved `_range`
  obligation means the function never overflows, which is the stronger
  and more useful statement — but a specification that *wants* the
  revert behaviour cannot state it.
* **`msg.sender`, `address(this)`, events, and the balance of a real
  account are not modelled.** `x.transfer(v)` books into the `net`
  ledger and nothing else.
* **A ghost `assume` is unchecked**, so `@custom:assume false` proves
  everything after it. It is reported in the generated file but not
  flagged; use it deliberately.
