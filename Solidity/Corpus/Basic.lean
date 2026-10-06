import Solidity.Calculus.Notation

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
(`corpus_decide`): the run is a closed term, and `decide +kernel` evaluates
it.  One thing stops the kernel: a well-founded definition — the default a
`push()` appends and a fresh memory object starts at (`defaultForTy`, even at
`uint`), and the memory-to-storage copy (`copyMToSt`) — whose `Acc` proof
does not reduce.  The *stores* are the one place that is avoided
here: `unfoldStore` spells every root's default with the structural `dflt`,
and `*Store_eq` proves it the same store.  A run that still needs one is
checked by `#eval` of `outcome` under `#guard_msgs` instead, and the verdict
table (`tests/solkey/expected.tsv`) says `evaluated` rather than `proved`.

`TestSuite.sol` is the exception: its obligations are stated as solkey
states them and derived by `⊢` (`Solidity/TestSuite/`), so its corpus rows
are corollaries at the initial storage, not runs decided here
(`Corpus/Imported.lean`).  The kernel decides the other suites' runs at the
default `maxHeartbeats`: their programs are short, each theorem about
100 ms (docs/testsuite-proofs.md, "M7 integration").
-/

namespace Solidity.Corpus

open Semantics

/-! ## Defaults the kernel can evaluate -/

/-- `defaultForTy`, by structural recursion on a depth bound.  Every struct of
`structDef` has rank below 8, so `dflt 8` is `defaultForTy` on the roots of
every ported contract (`*Store_eq` checks it store by store). -/
def dflt : Nat → Ty → SVal
  | _, .prim .bool => .bool false
  | _, .prim _ => .int 0
  | 0, .ref _ => .struct []
  | n + 1, .ref (.struct s) => .struct ((structDef s).map fun (f, t) => (f, dflt n t))
  | _ + 1, .ref (.array _) => .array [] [] false
  | n + 1, .ref (.fixed e k) => .array (List.replicate k (dflt n e)) [] true
  | n + 1, .ref (.mapping _ v) => .map [] (dflt n v)

/-- `σ` with each root of `C` at its default, spelt with `dflt`. -/
def unfoldStore (C : Contract) (σ : State) : State :=
  { σ with storage := C.vars.map fun (n, T) => (n, dflt 8 T) }

theorem testSuiteStore_eq : State.testSuiteStore = unfoldStore TestSuite State.testSuiteStore := by
  simp [unfoldStore, State.testSuiteStore, TestSuite, defaultForRef, defaultForTy,
    defaultForFields, structDef, dflt]

theorem solcExpressionsStore_eq :
    State.solcExpressionsStore = unfoldStore SolcExpressions State.solcExpressionsStore := by
  simp [unfoldStore, State.solcExpressionsStore, SolcExpressions, dflt]

theorem solcStructsStore_eq :
    State.solcStructsStore = unfoldStore SolcStructs State.solcStructsStore := by
  simp [unfoldStore, State.solcStructsStore, SolcStructs, defaultForRef, defaultForTy,
    defaultForFields, structDef, dflt]

theorem solcArraysStore_eq :
    State.solcArraysStore = unfoldStore SolcArrays State.solcArraysStore := by
  simp [unfoldStore, State.solcArraysStore, SolcArrays, dflt]

theorem solcMemoryStore_eq :
    State.solcMemoryStore = unfoldStore SolcMemory State.solcMemoryStore := by
  simp [unfoldStore, State.solcMemoryStore, SolcMemory, defaultForRef, defaultForTy,
    defaultForFields, structDef, dflt]

theorem solcMappingsStore_eq :
    State.solcMappingsStore = unfoldStore SolcMappings State.solcMappingsStore := by
  simp [unfoldStore, State.solcMappingsStore, SolcMappings, defaultForRef, defaultForTy,
    defaultForFields, structDef, dflt]

theorem solcControlFlowStore_eq :
    State.solcControlFlowStore = unfoldStore SolcControlFlow State.solcControlFlowStore := by
  simp [unfoldStore, State.solcControlFlowStore, SolcControlFlow, defaultForRef, defaultForTy,
    defaultForFields, structDef, dflt]

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

/-- `corpus_decide h`: rewrite the store with its unfolding `h`, then let the
kernel run the program. -/
macro "corpus_decide " h:term : tactic =>
  `(tactic| (rw [$h:term]; apply diamond_of_isOk; decide +kernel))

section Examples

/-- A write through an alias, read back through the root. -/
example : Diamond State.testSuiteStore
    sol[TestSuite]{ Person storage p = alice; p.account.balance = 100;
                    assert(alice.account.balance == 100); } := by
  corpus_decide testSuiteStore_eq

/-! A fresh `Person` in memory needs its default: the kernel stops there. -/

/-- info: "ok" -/
#guard_msgs in
#eval outcome State.testSuiteStore sol[TestSuite]{ Person memory m; m.age = 3; assert(m.age == 3); }

end Examples

end Solidity.Corpus
