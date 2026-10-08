import Solidity.Calculus.Notation
import Solidity.Semantics.RunErase
import Solidity.Semantics.Core.TypedRunErase

/-!
# The solkey corpus: what an obligation is

solkey's `SolidityProblemSynthesizer` makes one obligation per function of
an example contract, `\<{ f()@C; }\>(true)`: from the contract's initial
store, the body runs to its end — no `require` fails and no `assert` does.
The body is the whole specification.  `scripts/solkey-port.mjs` translates
each function into `sol[C]{ … }` over the ported contract `C` (`Syntax.lean`)
and states it as `Diamond σ P`: `holds σ dl{ ⟨ P ⟩ true }` at the store `σ`
the contract starts in (`Semantics.State.*Store`, checked against `C` by the
`initStorage_*` theorems).

Why not a validity `⊨`, which is what `sol_symex` and `sol_close` prove:

* `⊨ ⟨ P ⟩ true` quantifies over every state, including those without the
  contract's roots, where the first storage write is stuck; it is not valid
  for any `P` that touches storage (`Close.lean`'s first gap).
* `⊨ [ P ] true` says that no `assert` of `P` fails, from any state: a
  failed `assert` panics, which the box does not accept, while a failed
  `require` reverts and a stuck write stops, which it does (solkey's
  `assertSimple`).  So it is a different obligation: it does not say that
  the body runs to its end, which the diamond asks, and over every state
  it asks more of `assert` than a run from the contract's store does.
* `⊨ pre → ⟨ P ⟩ true` with `pre` describing the store would be the faithful
  validity, but `sol_close` does not close a storage write under the
  diamond, so it would prove nothing more than this form while failing on
  almost every obligation.

So the obligation is the diamond *at the store*, which is exactly solkey's
formula read in the contract's initial state.  It is decided by the kernel
(`corpus_decide`) through the typed run (`Semantics/Core/TypedRun.lean`):
the program is resolved to the scoped syntax (`Core.Prog.resolve`), and its
typed run from the store, typed (`Core.Storage.*`, a fold the kernel builds),
is evaluated by `decide +kernel` (`trunOk`).  The typed run ending is the
untyped one ending (`diamond_of_trunOk`: `Prog.run_of_trun`, then
`Prog.run_erase` back to the program resolved from), on programs off the two
place where the typed and the untyped runs part (`Prog.bridgeOk`: a copy
at a struct with a repeated member name).  The typed run has no
well-founded definition in the kernel's way: a default is the structural
`SVal.dflt`, a memory copy a fold.  `*Store_eq` states each store as the
erasure of its typed start.  A run that ends normally but that `trunOk`
cannot decide (the program does not resolve, or it is off the bridge: a
copy at a struct whose members share a name, like `BadDup`) is pinned by `#eval` of `outcome` (the untyped run) under
`#guard_msgs`, and the verdict table (`tests/solkey/expected.tsv`) says
`evaluated`; a run that does not end normally is pinned the same way and
is `open`.

`TestSuite.sol` is the exception: its obligations are stated as solkey
states them and derived by `⊢` (`Solidity/TestSuite/`), so its corpus rows
are corollaries at the initial storage, not runs decided here
(`Corpus/Imported.lean`).  The kernel decides the other suites' runs at the
default `maxHeartbeats`: their programs are short, each theorem about
100 ms (docs/testsuite-proofs.md, "M7 integration").
-/

namespace Solidity.Corpus

open Semantics

/-! ## The stores, typed -/

/-- A contract's start, typed: the storage `st`, no memory, no locals, the
funds `bal`. -/
def start {C : Contract} (st : Core.Storage C)
    (bal : PrimTy.uint.Denote := PrimTy.dflt .uint) : Core.TState C [] :=
  { Core.TState.ofStorage st with selfBalance := bal }

theorem testSuiteStore_eq :
    State.testSuiteStore =
      (start Core.Storage.testSuite ⟨1000000000, by decide⟩).erase.erase [] := by
  simp only [start, Core.TState.ofStorage, Core.TState.erase, Core.State.erase,
    Core.Storage.testSuite_erase]
  rfl

theorem solcExpressionsStore_eq :
    State.solcExpressionsStore = (start Core.Storage.solcExpressions).erase.erase [] := by
  simp only [start, Core.TState.ofStorage, Core.TState.erase, Core.State.erase,
    Core.Storage.solcExpressions_erase]
  rfl

theorem solcStructsStore_eq :
    State.solcStructsStore = (start Core.Storage.solcStructs).erase.erase [] := by
  simp only [start, Core.TState.ofStorage, Core.TState.erase, Core.State.erase,
    Core.Storage.solcStructs_erase]
  rfl

theorem solcArraysStore_eq :
    State.solcArraysStore = (start Core.Storage.solcArrays).erase.erase [] := by
  simp only [start, Core.TState.ofStorage, Core.TState.erase, Core.State.erase,
    Core.Storage.solcArrays_erase]
  rfl

theorem solcMemoryStore_eq :
    State.solcMemoryStore = (start Core.Storage.solcMemory).erase.erase [] := by
  simp only [start, Core.TState.ofStorage, Core.TState.erase, Core.State.erase,
    Core.Storage.solcMemory_erase]
  rfl

theorem solcMappingsStore_eq :
    State.solcMappingsStore = (start Core.Storage.solcMappings).erase.erase [] := by
  simp only [start, Core.TState.ofStorage, Core.TState.erase, Core.State.erase,
    Core.Storage.solcMappings_erase]
  rfl

theorem solcControlFlowStore_eq :
    State.solcControlFlowStore = (start Core.Storage.solcControlFlow).erase.erase [] := by
  simp only [start, Core.TState.ofStorage, Core.TState.erase, Core.State.erase,
    Core.Storage.solcControlFlow_erase]
  rfl

/-! ## The obligation -/

/-- solkey's `\<{ f(); }\>(true)` at the store `σ`: `σ ⊨ ⟨ P ⟩ true`. -/
abbrev Diamond {C : Contract} (σ : State) (P : Prog C) : Prop :=
  holds σ (.modal .diamond P .tt)

/-- A run that returns proves the diamond. -/
theorem diamond_of_isOk {C : Contract} {σ : State} {P : Prog C}
    (h : (Prog.run σ P).isOk = true) : Diamond σ P := by
  unfold Diamond holds Modality.afterRun Modality.after
  cases hr : Prog.run σ P with
  | ok τ => exact ⟨trivial, nofun⟩
  | error e => simp [hr, Except.isOk, Except.toBool] at h

/-- How the run of `P` from `σ` ends: `"ok"`, `"revert"`, `"panic"`, `"stuck"` or `"diverge"`.  What
`#eval` pins where the kernel cannot decide `Diamond σ P`. -/
def outcome {C : Contract} (σ : State) (P : Prog C) : String :=
  match Prog.run σ P with
  | .ok _ => "ok"
  | .error .revert => "revert"
  | .error .panic => "panic"
  | .error .stuck => "stuck"
  | .error .diverge => "diverge"

/-- The check `corpus_decide` evaluates: `P` resolves from no locals, is on
the bridge, and its typed run from `σ` ends. -/
def trunOk [FreshNames] {C : Contract} (σ : Core.TState C []) (P : Prog C) : Bool :=
  match Core.Prog.resolve [] P with
  | .ok ⟨_, Q⟩ => Q.bridgeOk && (Q.trun σ).isOk
  | .error _ => false

/-- A typed run that ends proves the diamond at its start, erased. -/
theorem diamond_of_trunOk [FreshNames] {C : Contract} (σ : Core.TState C []) {P : Prog C}
    (h : trunOk σ P = true) : Diamond (σ.erase.erase []) P := by
  unfold trunOk at h
  split at h
  · rename_i Γ' Q hres
    simp only [Bool.and_eq_true] at h
    obtain ⟨hb, hok⟩ := h
    apply diamond_of_isOk
    cases ht : Q.trun σ with
    | error e => rw [ht] at hok; cases hok
    | ok o =>
      have h2 := Core.Prog.run_erase Q (Core.Prog.resolve_fresh hres) List.nodup_nil rfl σ.erase
      rw [Core.Prog.run_of_trun hb ht, Core.Prog.resolve_erase hres] at h2
      change ResultsAgree _ (Prog.run (σ.erase.erase []) P) _ at h2
      cases hr : Prog.run (σ.erase.erase []) P with
      | ok _ => rfl
      | error _ => rw [hr] at h2; exact h2.elim
  · cases h

/-- `corpus_decide h`: rewrite the store with its typed start `h`, then let
the kernel resolve the program and run it typed. -/
macro "corpus_decide " h:term : tactic =>
  `(tactic| (rw [$h:term]; apply diamond_of_trunOk; decide +kernel))

section Examples

/-- A write through an alias, read back through the root. -/
example : Diamond State.testSuiteStore
    sol[TestSuite]{ Person storage p = alice; p.account.balance = 100;
                    assert(alice.account.balance == 100); } := by
  corpus_decide testSuiteStore_eq

/-- A fresh `Person` in memory starts at its default, the structural `SVal.dflt`. -/
example : Diamond State.testSuiteStore
    sol[TestSuite]{ Person memory m; m.age = 3; assert(m.age == 3); } := by
  corpus_decide testSuiteStore_eq

end Examples

end Solidity.Corpus
