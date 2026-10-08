import Solidity.Corpus.Basic
import Solidity.Calculus.Problem
import Solidity.Calculus.Core.Sound
import Solidity.Calculus.Core.Spec
import Solidity.Calculus.Core.HoldsErase
import Solidity.Calculus.Core.Close
import Solidity.Solkey.TestSuite

/-!
# The corpus's `TestSuite` is the imported one

solkey's `TestSuite.sol` reaches Lean twice: as the hand-written contract
`TestSuite` (`Syntax.lean`), which the examples write `sol[TestSuite]{ … }`
against, and as `Solkey.TestSuite`, which `solc_import` reads from solc's
AST (`Solidity/Solkey/TestSuite.lean`) and whose obligations are derived by
`⊢` (`Solidity/TestSuite/`).  The corpus now takes its `TestSuite` rows from
the second: `scripts/solkey-port.mjs` no longer translates the source, it
reads `TestSuite/Report.lean`'s pin, and `Corpus/TestSuite.lean` states each
derived obligation at the initial storage as a corollary of its theorem.

**Why the imported contract's initial state.**  The corollaries are
read over the imported contract's typed states, `Core.TState
Solkey.TestSuite []`, and need `wt(storage)` there, which is read over its
roots: the hand-written contract's typed start is a state of another
contract, which has neither `fixedByKey` nor `boolKeyed` and names two roots
differently.  The imported contract's own initial state is well-formed
(`Solkey.TestSuite.initState_wt`).

**The two contracts agree** where they overlap: every root of the
hand-written contract is a root of the imported one, at the same type, up
to two renames (`people` is `folks` and `a` is `aux` there, since those
names mean other things in other contracts).  Struct members need no check:
both contracts read `Semantics.structDef`, and both name solkey's `Triple`
`FixedTriple`.  The imported contract has two roots more (below); `tree`,
the struct recursive through a mapping, is in neither.
-/

namespace Solidity.Corpus

open Semantics

/-- The hand-written `TestSuite`'s names for two of solkey's roots. -/
def testSuiteRenames : List (Name × Name) := [("folks", "people"), ("aux", "a")]

/-- Every root of the hand-written `TestSuite` is a root of the imported
contract, at the same type, after `testSuiteRenames`. -/
theorem testSuite_agrees :
    TestSuite.vars.all (fun (n, T) =>
      lookupBy ((lookupBy n testSuiteRenames).getD n) Solkey.TestSuite.vars == some T) = true := by
  decide +kernel

/-! The roots only the imported contract has: `fixedByKey`, and the
bool-keyed mapping, its key read as a `uint` (solc encodes a bool key as
`0` or `1`). -/

/--
info: [fixedByKey, boolKeyed]
-/
#guard_msgs in
#eval IO.println ((Solkey.TestSuite.vars.filter fun (n, _) =>
  ((testSuiteRenames.map fun (a, b) => (b, a)).lookup n |>.getD n |>
    (lookupBy · TestSuite.vars)).isNone).map (·.1))

end Solidity.Corpus

/-! ## Obligations at a store, from `⊢`

The `TestSuite` obligations are derived by the scoped `⊢`
(`Core.Proves`, `docs/intrinsic.md`, W3c): `N.f.proved : ⊢ N.f.problem`, the
program resolved (`Core.Prog`).  Its corollary at the initial storage is
stated over the typed run of that program, as every other corpus row is
(`Corpus/Basic.lean`): `N.f.problem` is `wt(storage) → ⟨ Q ⟩ true`, and
`Q`'s typed run from the initial state ends (`Runs`).  It is the scoped
`⊢`'s soundness (`Core.Proves.valid`) at that state, whose storage is
well-formed (`initState_wt`); nothing is left to evaluate. -/

namespace Solidity.Corpus

variable {C : Contract}

/-- solkey's `\<{ f(); }\>(true)` at `σ`, for an obligation `φ` of no
parameters: `φ` is `wt(storage) → ⟨ Q ⟩ true` (`Core.Problem.fml`) and
`Q`'s typed run from `σ` ends. -/
def Obligation.Diamond (σ : Core.TState C []) (φ : Core.Fml C []) : Prop :=
  ∃ (Γ' : Core.Ctx) (Q : Core.Prog C [] Γ'), φ = Core.Problem.fml .diamond [] Q ∧ Runs .diamond σ Q

/-- solkey's `\[{ f(); }\](true)` at `σ`, for an obligation `φ` of no
parameters: `φ` is `wt(storage) → [ Q ] true` and `Q`'s typed run from `σ`
does not panic. -/
def Obligation.Box (σ : Core.TState C []) (φ : Core.Fml C []) : Prop :=
  ∃ (Γ' : Core.Ctx) (Q : Core.Prog C [] Γ'), φ = Core.Problem.fml .box [] Q ∧ Runs .box σ Q

/-- **A derived obligation of no parameters holds at the initial state**:
its program, run typed from there, under its modality.  `wt(storage)` there
is `initState_wt`'s, read scoped (`Core.holds_erase_fo`). -/
theorem runs_of_proved {m : Modality} {Γ' : Core.Ctx} {Q : Core.Prog C [] Γ'}
    (h : Core.Proves C .all [] .nil (Core.Problem.fml m [] Q))
    (hw : holds C.initState (Fml.wt C)) : Runs m (Core.TState.init C) Q := by
  have hwt : Core.holds (Core.TState.init C) (Core.Fml.wt C) :=
    (Core.holds_erase_fo (ns := []) (Core.Fml.wt C) (by simp only [Core.Fml.wt, Core.Fml.Plain]) rfl
      (Core.Agree.nil (Core.TState.init C).erase)).2
      (by rw [show Core.withLocals (Core.TState.init C).erase.glob [] = C.initState by
        rw [Core.TState.init_erase]; rfl]; exact hw)
  exact h.valid (Core.TState.init C) hwt

/-- A derived diamond obligation with no parameters holds at the initial
state (`runs_of_proved`). -/
theorem diamond_of_proved {Γ' : Core.Ctx} {Q : Core.Prog C [] Γ'}
    (h : Core.Proves C .all [] .nil (Core.Problem.fml .diamond [] Q))
    (hw : holds C.initState (Fml.wt C)) :
    Obligation.Diamond (Core.TState.init C) (Core.Problem.fml .diamond [] Q) :=
  ⟨_, Q, rfl, runs_of_proved h hw⟩

/-- A derived box obligation with no parameters holds at the initial state
(`runs_of_proved`). -/
theorem box_of_proved {Γ' : Core.Ctx} {Q : Core.Prog C [] Γ'}
    (h : Core.Proves C .all [] .nil (Core.Problem.fml .box [] Q))
    (hw : holds C.initState (Fml.wt C)) :
    Obligation.Box (Core.TState.init C) (Core.Problem.fml .box [] Q) :=
  ⟨_, Q, rfl, runs_of_proved h hw⟩

/-! A corollary of `Corpus/TestSuite.lean` uses the axioms of its `⊢`
theorem, which `TestSuite/Report.lean`'s pin checks, of `initState_wt`,
pinned there on one corollary, and of these two, through `Proves.valid`. -/

/--
info: 'Solidity.Corpus.diamond_of_proved' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms diamond_of_proved

/--
info: 'Solidity.Corpus.box_of_proved' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms box_of_proved

end Solidity.Corpus
