import Solidity.Calculus.Core.Logic
import Solidity.Syntax.Resolve

/-!
# The solkey corpus: what an obligation is

solkey's `SolidityProblemSynthesizer` makes one obligation per function of
an example contract, `\<{ f()@C; }\>(true)`: from the contract's initial
store, the body runs to its end — no `require` fails and no `assert` does.
The body is the whole specification.  `scripts/solkey-port.mjs` translates
each function into `sol[C]{ … }` over the ported contract `C` (`Syntax.lean`)
and states it as `Diamond (Core.TState.init C) P`: the program resolved to
the scoped syntax (`Core.Prog.resolve`) and `⟨ P ⟩ true` read over its
typed run (`Core.holds`, `Semantics/Core/TypedRun.lean`) from the typed
state the contract starts in, every root at its default.

Why not a validity `⊨`, which is what `sol_symex` and `sol_close` prove:

* `⊨ ⟨ P ⟩ true` quantifies over every state, including those whose storage
  is not one the contract can be in; solkey's obligation asks `wt(storage)`
  for that, and its diamond over every such storage is not decided here.
* `⊨ [ P ] true` says that no `assert` of `P` fails, from any state: a
  failed `assert` panics, which the box does not accept, while a failed
  `require` reverts, which it does (solkey's `assertSimple`).  So it is a
  different obligation: it does not say that the body runs to its end,
  which the diamond asks.
* `⊨ pre → ⟨ P ⟩ true` with `pre` describing the store would be the faithful
  validity, but the closer does not close a storage write under the
  diamond, so it would prove nothing more than this form while failing on
  almost every obligation.

So the obligation is the diamond *at the store*, which is exactly solkey's
formula read in the contract's initial state.  It is decided by the kernel
(`corpus_decide`): the program is resolved and its typed run from the store
evaluated by `decide +kernel` (`trunOk`); the typed run has no well-founded
definition in the kernel's way (a default is the structural `SVal.dflt`, a
memory copy a fold).  A run that does not end normally is pinned by `#eval`
of `outcome` under `#guard_msgs`, and the verdict table
(`tests/solkey/expected.tsv`) says `open`.

`TestSuite.sol` is the exception: its obligations are stated as solkey
states them and derived by `⊢` (`Solidity/TestSuite/`), so its corpus rows
are corollaries at the initial storage, not runs decided here
(`Corpus/Imported.lean`).  The kernel decides the other suites' runs at the
default `maxHeartbeats`: their programs are short, each theorem about
100 ms (docs/testsuite-proofs.md, "M7 integration").
-/

namespace Solidity.Corpus

open Semantics

variable {C : Contract}

/-! ## The obligation -/

/-- `⟨ Q ⟩ true` (or `[ Q ] true`) of a scoped program at the typed state
`σ`: the typed reading (`Core.holds`).  Under the diamond, `Q`'s typed run
from `σ` ends (or is exhausted, a push past the bound, which KeY, modelling
no gas, never sees: decision 15); under the box, it does not panic. -/
abbrev Runs {Γ' : Core.Ctx} (m : Modality) (σ : Core.TState C []) (Q : Core.Prog C [] Γ') : Prop :=
  Core.holds σ (.modal m Q .nil .tt)

/-- solkey's `\<{ f(); }\>(true)` at the typed state `σ`: the program `P`
resolves to the scoped syntax, and its typed run from `σ` ends normally,
or is exhausted (`Runs`, decision 15). -/
def Diamond [FreshNames] (σ : Core.TState C []) (P : Prog C) : Prop :=
  match Core.Prog.resolve [] P with
  | .ok ⟨_, Q⟩ => Runs .diamond σ Q
  | .error _ => False

/-- How the typed run of `P` from `σ` ends: `"ok"`, `"revert"`, `"panic"`,
`"diverge"` or `"exhausted"`, or why `P` does not resolve.  What `#eval`
pins where the run does not end normally. -/
def outcome [FreshNames] (σ : Core.TState C []) (P : Prog C) : String :=
  match Core.Prog.resolve [] P with
  | .ok ⟨_, Q⟩ =>
    match Q.trun σ with
    | .ok _ => "ok"
    | .error .revert => "revert"
    | .error .panic => "panic"
    | .error .diverge => "diverge"
    | .error .exhausted => "exhausted"
  | .error e => s!"unresolved: {e}"

/-- The check `corpus_decide` evaluates: `P` resolves from no locals, and its
typed run from `σ` ends normally. -/
def trunOk [FreshNames] (σ : Core.TState C []) (P : Prog C) : Bool :=
  match Core.Prog.resolve [] P with
  | .ok ⟨_, Q⟩ => (Q.trun σ).isOk
  | .error _ => false

/-- A typed run that ends normally proves the diamond. -/
theorem runs_of_trun {Γ' : Core.Ctx} {σ : Core.TState C []} {Q : Core.Prog C [] Γ'}
    {o : Core.Out C σ.H Γ'} (h : Q.trun σ = .ok o) : Runs .diamond σ Q := by
  simp only [Runs, Core.holds, Core.Prog.trunFrames, h]
  exact ⟨trivial, nofun⟩

/-- `trunOk` proves the diamond. -/
theorem diamond_of_trunOk [FreshNames] (σ : Core.TState C []) {P : Prog C}
    (h : trunOk σ P = true) : Diamond σ P := by
  unfold trunOk at h
  unfold Diamond
  split at h
  · rename_i Q _
    cases ht : Q.trun σ with
    | error e => rw [ht] at h; cases h
    | ok o => exact runs_of_trun ht
  · cases h

/-- `corpus_decide`: let the kernel resolve the program and run it typed. -/
macro "corpus_decide" : tactic =>
  `(tactic| (apply diamond_of_trunOk; decide +kernel))

section Examples

/-- A write through an alias, read back through the root. -/
example : Diamond (Core.TState.init TestSuite)
    sol[TestSuite]{ Person storage p = alice; p.account.balance = 100;
                    assert(alice.account.balance == 100); } := by
  corpus_decide

/-- A fresh `Person` in memory starts at its default, the structural `SVal.dflt`. -/
example : Diamond (Core.TState.init TestSuite)
    sol[TestSuite]{ Person memory m; m.age = 3; assert(m.age == 3); } := by
  corpus_decide

/-! A failed `assert` panics: `outcome` says how the typed run ends. -/

/-- info: "panic" -/
#guard_msgs in
#eval outcome (Core.TState.init TestSuite) sol[TestSuite]{ assert(alice.age == 1); }

end Examples

end Solidity.Corpus
