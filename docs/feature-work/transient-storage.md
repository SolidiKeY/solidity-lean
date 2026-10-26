# Transient storage

`transientState` is **missing**: ordinary source elaboration and scoped
transient terms and rules do not exist. What exists is a typed supplement that
composes transient operations with the ordinary `Prog.run`. Physical layout,
raw `tload`/`tstore` and gas are outside the model. Semantics follow the
[Solidity v0.8.38 transient-storage chapter](https://github.com/argotorg/solidity/blob/1835d247de183f23e7b0e2bc4a50732af525b77c/docs/contracts/transient-storage.rst).

## Supported (`Semantics/Transient.lean`)

- `Slot L p` is a declaration position indexed by its primitive type;
  `Store L` holds exactly the declared values. Reference-typed cells cannot be
  declared. The cells are separate from `State.storage`.
- An ordinary fragment carries `Prog.within μ P = true`; a static context also
  checks `Prog.within .view P`. `Program.ordinary_frame` reuses
  `Prog.run_frame`. `Prog.within` admits only heap-neutral fragments.
- Zero-value calls to the same owning contract share persistent and transient
  cells. A child starts with fresh heap and locals, `msg.sender = selfAddress`
  and zero `msg.value`. A successful return adopts the child's storage,
  ledger, balance and transient cells and restores the caller's heap and
  transaction metadata. `TRun.tryCall` is unchanged.
- A caught revert or panic restores the whole entry `FrameState`, successful
  descendant writes to either store included. Divergence and exhaustion
  propagate. Static execution forbids transient writes in all descendants;
  pure frames cannot read transient cells.
- `Program.transact` enters through `Lifetime.World.enter`, starts from
  `Store.empty` and discards the store at exit. `transact_ok` needs actual
  successful entry and execution; `transact_ordinary` equals
  `Lifetime.System.run` for an ordinary-only body. A failed transaction
  commits nothing.
- `Calculus/Transient.lean` reads the supplement with `Modality.afterRunTR`
  (boxes exclude panic; diamonds keep the exhaustion policy) and bridges
  ordinary `Spec` proofs, including those from `Proves.valid`. It is not a new
  `Taclet` and does not extend `Fml`.

Example: `Examples/Tactics/TransientStorage.lean`.

## Refused, and why

- **A contract with any transient declaration is refused whole**, before any
  declaration is lowered: otherwise it would print as an ordinary persistent
  root. Unused declarations, public getters and functions that never mention the
  cell are covered. A structured diagnostic may replace the guard only if
  `scripts/transient-storage.test.mjs` still passes; it must not be relaxed
  because the supplement exists.
- Memory-allocating fragments and locals spanning fragment boundaries.
- Calls to another owning contract and delegate calls.

## What full support needs

- Transient declarations in `Contract`, and typed reads and writes in the
  scoped syntax, signature, updates, terms, printers, quotation, tools and
  elaborator. A transient read is a mutable value, not `Simple`: it cannot move
  across a sibling call that changes the cell. Widths, signedness, aliases and
  mutability must be kept.
- **A `State` field alone is unsound.** Callback and loop havoc must range over
  the new store, and every rebuilding, weakening, frame and anonymous-state
  proof must include it. `FrameKeeps`/`Prog.storeAt` (`2c1ce2e7`) must separate
  persistent from transient modification; a view loop frame preserves both,
  and a mutable callback cannot preserve transient cells by fiat. `holds`,
  `holdsC`, the closers, `Upd.Lands`, function and recursive contracts,
  `TGFrame` and their soundness proofs migrate together.
- A world interface with typed owner identity and rollback of all
  descendants, delegate ownership included.

## Reference check

`node scripts/check-transient-vectors.mjs SOLJSON_FILE EXTERNAL_NODE_MODULES`
runs signed transactions on the pinned solc 0.8.38 in a Cancun VM, legacy and
via-IR, including two successive transactions (reset of transient, persistence
of storage) and the compiler rejections. The false source properties panic
there; in the source runner they stay pending, which is not a refutation.
