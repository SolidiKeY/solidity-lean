# Function specifications

Per-function `requires`/`ensures` with `\old` and `\forall`, `assignable`
frames, and the contract `invariant`, stated as one proof obligation per
function and discharged by `sol_symex` + `sol_close` over symbolic
parameters. The front end, the obligation, `sol_spec` and `#verify` are
built; the last section lists what is not.

## How solkey does it

Clauses are NatSpec lines above a function, or above the contract for
`invariant` (`keyext.solidity.examples/benchmark/*.sol`):

```solidity
/// @custom:key requires count >= 1
/// @custom:key ensures count == \old(count) - 1                 // Counter.dec
/// @custom:key ensures \forall address a; a != receiver -> balances[a] == \old(balances[a])   // Coin.mint
/// @custom:key invariant \forall address a; pendingReturns[a] >= 0     // SimpleAuction
```

- **Reading.** `speclang/natspec/KeyNatspec.java` reads `box`, `skip`,
  `invariant`, `requires`, `ensures` and `assignable` (ignored by solkey,
  since bodies are inlined).
- **Language.** `SolSpec.g4`, parsed by `SpecParser`: Solidity expressions
  plus `\old`, `\result`, `net(a)`, `->`, `<->`, `\forall`/`\exists sort x; e`.
- **Translation.** `SpecCompiler` emits `.key` text. A state variable is
  `find(storage, …)`; `\old(e)` reads `e` against the snapshots `old`/`oldNet`
  (`ensures` only, not nested); `\result` is the return variable.
- **Obligation** (`SolidityProblemSynthesizer.specifiedProblemText`), always
  a box:

  ```
  msgValue ≥ 0 & requires & CInv(storage, net) ->
    {old := storage ‖ oldNet := net ‖ net := … + msgValue ‖ selfBalance := … + msgValue}
    \[{ result = f(args)@C; }\] (CInv(storage, net) & ensures)
  ```

  Parameters are unconstrained KeY `int`s, so a bound must come from
  `requires`. The invariant is assumed on entry and proved on exit (and at
  every `transfer` under `transferSemantics:withCallback`). A constructor's
  obligation (solkey `a764703bf1`) starts from the empty storage,
  `{storage := mtSt ‖ old := mtSt ‖ oldNet := mtSt ‖
  net := storeSt(mtSt, at(msgSender), …) ‖ selfBalance := msgValue}`, and
  assumes no `CInv`. In Lean it is `spec!{constructor}`
  (`Calculus/SurfaceSpec.lean`), where `\old(net(a))` reads the empty ledger
  (`UpdElem.saveNetMt`); a `requires` that reads the state, the ledger or
  the funds is refused there (Lean only: solkey reads it of the storage the
  update discards).

The benchmark README reports 19 of 21 obligations closed; ERC20's
`mint`/`burn` stay open on internal calls.

## How the Lean side does it

**Clauses are data** (`SpecSyntax.lean`). `SpecExpr` is `SolSpec.g4`;
`SpecLoc` is an `assignable` location (`x`, `s.f`, `m[e]`, `m[*]`,
`\nothing`); `FunSpec` holds `requires`, `ensures`, `assignable`, `skip`.
`contract!{ … }` reads them where the NatSpec line stands: `requires e;`,
`ensures e;`, `assignable l, …;`, `skip;` above a function
(`FunDecl.spec`), `invariant e;` anywhere (`Contract.inv`); `payable` is kept
(`FunDecl.payable`). They stay raw because a `Contract` cannot hold an
`Fml C`.

**The compiler** is `SpecCompiler`'s (`Calculus/SurfaceSpec.lean`). A `SpecCtx`
names the storage term a clause reads, whether `\old`/`\result` are allowed,
and the locals in scope. A state variable is `find(ctx.storage, p)`;
`msg.sender`, `msg.value`, `block.timestamp`, `this.balance` are `Term.env`;
an enum member is its position; `==` between conditions is `<->`; `\exists`
is `¬∀¬`. Equations are KeY's `=` (`Fml.eq`), read in the Theory, where a
storage read is total (a word of its type, the default where nothing is
written), so the frame owes `find(storage, p) = find(old, p)` with no
guard; arithmetic is Solidity's, checked at its operands' type, where
solkey's is unbounded `int`: an overflowing side halts, and an equation with
one halting side is false (two that halt are equal, as KeY's `=` is
reflexive).

**`old` is a storage variable**, KeY's `Struct old`: the update
`{old := storage}` (`Rhs.store`) binds it (a local of type `old`, a `Storage C`), only when an
`ensures` reads `\old` or an `assignable` clause is given. `find(old, p)`
checks `p`'s indices against the current storage and reads `old`;
`sol_decide` cannot state that exactly, so `old` is outside its fragment and
`sol_close` reads it semantically. `net(a)` is an unbounded ledger integer
(`Srt.kint`), while `msg.value` is a bounded `uint`; under `\old` it is
`Tm.netOf oldNet a`, the snapshot
`oldNet` (`Rhs.saveNet`, a local of type `oldNet`), taken only when an `\old(…)`
reads `net(a)`.

**`\forall` is `Fml.all x T φ`**, a binder at its type (a `uint` in
`[0, 2^256)`). `sol_close` reads it as a Lean `∀` over the range
(`CloseS.forall_uint`, `forall_int`), and `grind` instantiates it.

Logical binders reserve `old`, `oldNet`, `result` and names starting with
`result_`, preserving the identities of snapshots and return values. A primitive
binder shadows any same-named storage or memory reference: reading that binder
as a value is valid, but using its `.length`, field or index is a type error.
These checks also apply behind false guards.

**The obligation is solkey's box** (`spec[C]{f}`; `spec!{f}` for the file's
`InContract`; `specObligation`):

```
R ∧ L ∧ M ∧ I ∧ requires →
  {old := storage ‖ oldNet := net ‖ B} [ T result = f(x₁, …, xₙ); ] (I ∧ ensures ∧ A)
```

- `R`: each parameter's range (`rangeFml`); a free local ranges over any
  value, where solkey's `int` parameters need no such fact.
- `L`: the layout premises of the state the clauses read (`layoutFmls`):
  each word has its declared type, at every key of a mapping (not inside an
  array). `⊨ᶠ` ranges over storages the contract never has, where `balances`
  may be no mapping or hold a `bool`; solkey's reads are total and typed and
  need none (`docs/solkey-feedback.md`). What only the body reads needs no
  premise, since the program reverts where a read is undefined.
- `M`: `msg.value >= 0` for a `payable` function, `msg.value == 0` otherwise.
- `I`: `Contract.inv`, assumed and owed.
- `B`: the booking of `msg.value`, KeY's `net := store(net, at(msg.sender),
  net(msg.sender) + msg.value) ‖ selfBalance := selfBalance + msg.value`
  (`UpdElem.net`, `UpdElem.selfBalance`), only for a `payable` function.
  Omitting unread snapshots and the zero booking keeps the meaning and is
  cheaper: every update element costs symbolic execution and `sol_close`.
- `A`: the frame of `assignable` (`assignableFml`): every word of the
  storage that no listed location covers is where it was,
  `find(old, p) = find(old, p) → find(storage, p) = find(old, p)`, under
  `∀ k` at a mapping, with `¬ k = e` where `m[e]` is listed; an array owes
  its length and every element; keys are read in the pre-state.

`specPieces` (`Calculus/SurfaceSpec.lean`) returns the parts apart (`R, L,
M`; `I, requires`; the update, the call, the conclusion's clauses), and
`specObligation` (`Calculus/Spec.lean`) reads them scoped, in the
parameters' context, the call placed past the locals the update declares. A function marked `skip`, or with no clause and no invariant,
has no obligation; a parameter named `old`, `oldNet`, `result` or `k<n>`, or
of reference type, is rejected.

**`sol_spec`** proves one obligation: `sol_symex`, then `sol_spec_close`
(`sol_close`'s reads, then `omega` or `grind` with its instantiation
bounded). Splitting by clause costs more, since
symbolic execution then runs once per clause. `sol_spec_try` leaves what it
cannot close as goals.

**`#verify C.f`** (`Tools/Verify.lean`) states `spec[C]{f}`, first tries exact
declaration/input compilation and complete arithmetic decision, then falls
back to `sol_spec_try` and on leftover goals searches for a counterexample
(`refuteSpec`, `Tools/Counterexample.lean`). Verdicts: proved (offered as a
`Try this:` theorem), refuted (certified when the kernel checked
`¬ ⊨ᶠ spec[C]{f}`, else tested by the interpreter), or given up on. `#verify C`
runs every function with an obligation. Pinned in `Examples/Verify.lean`.

**The exact backend** `#verify` tries first: generated scalar/struct/mapping
bounds are certified directly (`Calculus/DeclarationFacts.lean`,
`sol_decl_facts`); `declaration_read_reduce`, `declaration_static_reduce`,
`declaration_checked_reduce`, `declaration_parameter_reduce`,
`declaration_input_reduce` and `declaration_trace_reduce` reduce a leaf
exactly, returning a proof or a counterstate of the original source
(`sol_exact`, `sol_exact?` for replay). Counterexample certification proves
the quantified premises and every remaining conjunct; it does not infer a
universal premise from sampled keys. The fragment is
[complete-verification.md](complete-verification.md)'s; what stays open is
[automation.md](automation.md), M7 "What is not proved". Unsupported syntax
and resource limits fall back without a semantic verdict.

**What is proved.** With `sol_spec`: `Examples/Benchmark/{Counter,
SimpleStorage,Mapping,Coin}.lean` (`Coin.mint` only), and `Examples/Tactics/Specs.lean` (ERC20 with `msg.sender` itself, and `Tally`,
which exercises `assignable` and a `payable` function's `net(a)` clause).
`Coin.send` and ERC20's `transfer` (a debit and a credit to two keys that
may be equal) do not close, as in the benchmark. `Examples/Benchmark/{ERC20,
EtherWallet,Purchase}.lean` state their clauses as hand-written `dl!{}`
obligations, not `spec!`.

## Still open

- **The diamond over reachable states.** Every obligation is a box, so a
  reverting run satisfies it. A diamond spec needs the layout as constraints
  on reachable states (`Typing/Constructibility.lean`, `Typing/Tight.lean`).
- **A spec's invariant under callbacks**: done (`docs/options.md`, O4):
  `invariant[C]` compiles it (`specInv`), `ValidC invariant[C] spec[C]{f}`
  is the obligation with callbacks, and `sol_prove` runs `ProvesC`'s walk on
  it (`Calculus/CallbackDerive.lean`).  What is open, while something in
  the obligation calls back, is O3's "Not covered": a diamond over a loop
  whose body calls back (unsound for any rule), and a recursive call
  returning a reference.
- **A recursive function's clauses** are its contract
  (`recSpecContract`, `Calculus/Recursion.lean`): `rec_auto` proves a
  recursive call by them and them by induction over the frames of the
  unrolling (`docs/kernel-port.md`, "Recursion"), `spec!{f}` of a recursive
  `f` included.  What is open: the contract assumes no invariant, and a
  recursive call under the callback reading (`ValidC`, `ValidT`) is not
  tried.
- **`sol_decide` on `old`, `net` and `Fml.all`**: all outside its language
  (`Calculus/DecideLang.lean`).
- **The benchmarks' `net(a)` clauses** (EtherWallet, Purchase,
  SimpleAuction) are not tried.
- **The corpus's `concretized` rows** (11 in `tests/solkey/expected.tsv`,
  SolcExpressions and SolcControlFlow) fix parameters to constants, where
  solkey proves them for all. Those in `sol_decide`'s fragment could be
  symbolic diamond goals `⊨ᶠ D ∧ R ∧ pre → ⟨ body ⟩ true` (`pre` the dropped
  bounds, `R` the ranges, `D` the definedness of each storage word the body
  touches), proved by `sol_symex; sol_decide`. The change is in
  `scripts/solkey-port.mjs` and `Corpus/Basic.lean`, best done when the
  corpus is regenerated.
