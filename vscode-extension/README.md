# SolLoom — Solidity specification & verification (Lean 4)

Two input languages, both proved by the `Solidity` Lean package
(Lean 4.24.0, no external dependencies):

- **`.sol` — SolSpec.** A Dafny-style contract specification written in
  Solidity NatSpec `@custom:` tags. Each clause becomes one Lean theorem
  quantified over every state satisfying the precondition, proved by
  `sol_spec`. See [SolSpec](#solspec-specified-sol-files) below and
  `../docs/spec-language.md` for the language reference.
- **`.solj` — raw judgments.** Dynamic-logic judgments over one fixed
  store, proved by `sol_wp`. See [.solj format](#solj-format).

## SolSpec: specified `.sol` files

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

Open or save the file and every clause gets a verdict: a failed clause
gets an error squiggle on its own line carrying Lean's message, a
function outside the verified fragment (a loop, a call) gets a warning
saying why, and the status bar shows `SolLoom: k/n proved`.

Beyond the clauses you write, each function also gets a **range**
obligation — every `uintN`/`intN` still fits its declared type on exit,
which is where an overflow or underflow surfaces — and, if you wrote
`@custom:modifies`, a **frame** obligation.

`@custom:` tags are the namespace Solidity reserves for user annotations,
so a specified contract still compiles with `solc`, and tags SolLoom does
not know are ignored.

Headless:

```
node out/specCli.js <file.sol> [packageDir] [--show]
```

One line per obligation, then a summary. Exit codes: `0` = all verified,
`1` = some obligation failed, `2` = infrastructure error. `--show` prints
the generated Lean. `examples/spec/` has worked contracts.

The first run builds the Lean specification layer
(`lake build Solidity.Spec.Tactic`); later runs reuse
the cache.

## Usage

Open a workspace containing the `Solidity` Lake package (a
`lakefile.toml` next to `Solidity.lean`; auto-detected, or set
`solloom.packageDir`). Open or save a `.sol` file carrying `@custom:`
clauses, or a `.solj` file. For `.solj`:

- every judgment is proved with `sol_wp`; failed judgments get an error
  squiggle over their paragraph carrying the Lean message,
- the status bar shows `SolLoom: k/n verified` (warning background if k < n),
- the "SolLoom" output channel shows the raw `lake env lean --json` run,
- `SolLoom: Verify Current File` re-runs verification,
- `SolLoom: Show Generated Lean` opens the generated proof file beside.

Expect roughly 8 seconds per verification (a full Lean elaboration of the
generated file).

### Headless CLI

```
node out/cli.js <file.solj> [packageDir]
```

Prints `j<N> <verified|failed> (source lines A-B)` per judgment plus a
summary. Exit codes: `0` = ran ok, all verified; `1` = ran ok, some judgment
failed; `2` = infrastructure error (no package dir, lean would not run, or
errors outside every judgment span). See `examples/expected.txt`.

## .solj format
<a id="solj-format"></a>

- `//` starts a line comment (stripped before parsing).
- Judgments are paragraphs separated by one or more blank lines.
- Each paragraph must start with `<` (diamond: the program terminates and the
  postcondition holds) or `[` (box: if the program terminates normally the
  postcondition holds). Anything else is flagged without running Lean.
- The paragraph text is spliced verbatim (multi-line preserved) into
  `sol!{ … }` and proved via `theorem jN : (sol!{ … }).Holds := by sol_wp`.

```solj
// terminates with result == 10
< age = 10; result = age > (result == 10)

// vacuous: require(false) reverts
[ require(false); result = 1 ] (result == 1)
```

### Program vocabulary (StandardExample schema)

Programs run over the fixed StandardExample state: globals such as `age`, `total`,
`balance`, `alice`, `bob`, `values`, `people`, `result`, …. Statements
include assignments, field/index access (`people[alice].age`), local
declarations (`uint amount = 2`), `require(...)`, `assert(...)`, `revert()`,
`transfer`, compound assignment `+=`, and increment `++`. Anything the
`sol!{}` macro of `Solidity` accepts is fair game — the paragraph
is passed through verbatim.

## Architecture

No language server; two pipelines sharing the plumbing in `src/detect.ts`
(package detection, `lake` invocation) and `src/extension.ts` (diagnostics,
status bar, commands, output channel).

**SolSpec (`.sol`).** `src/spec/` is a pure front-end: `lexer.ts` keeps
NatSpec lines and attaches them to the declaration that follows,
`parser.ts` parses the Solidity subset and the specification-expression
grammar, `emitLean.ts` builds the symbolic entry state (one Lean variable
per primitive storage leaf and per parameter) and emits one theorem per
clause, `pipeline.ts` glues those together and maps Lean diagnostics back
to clause lines by generated-line span. `src/specCli.ts` is the same
pipeline headless; `src/test/` covers all of it with `node --test`
(`npm test`) and needs no Lean.

**Judgments (`.solj`).** The extension parses the `.solj` file in
TypeScript (`src/core.ts`, pure functions), generates
`<packageDir>/.gen/<basename>_solj.lean` containing one theorem per judgment,
and runs `lake env lean --json` (with `~/.elan/bin` prefixed to `PATH`) as a
child process. The JSON-lines diagnostics are mapped back through the
generated-line span of each theorem: a judgment with no error diagnostic in
its span is verified; any error in the span fails it with the diagnostic's
message. `src/extension.ts` is the VS Code glue (diagnostics, status bar,
commands, output channel); `src/cli.ts` is the same pipeline headless.

## Rebuild / package

```
cd vscode-extension
npm install
npm test
npx tsc
npx @vscode/vsce package --allow-missing-repository
code --install-extension ./solloom-0.1.0.vsix
```
