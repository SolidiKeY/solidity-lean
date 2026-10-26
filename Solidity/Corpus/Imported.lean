import Solidity.Corpus.Basic
import Solidity.Calculus.Problem
import Solidity.Calculus.Sound
import Solidity.Calculus.Spec
import Solidity.Calculus.Close
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
read over the imported contract's typed states, `State
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
`FixedTriple`. The imported contract's additional roots are listed below; `tree`,
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

/-! The roots only the current imported contract has, including the new
array-shape and signed-push fixtures. The bool-keyed mapping's key is read
as a `uint` (solc encodes a bool key as `0` or `1`). -/

/--
info: [signedValues, copySource9, copyTargetDyn, fixedGrid, fixedMapsOfFixed, dynMapsOfFixed, copyBig, copySmall, localOut, fixedByKey, emptyTokens, boolKeyed, pair]
-/
#guard_msgs in
#eval IO.println ((Solkey.TestSuite.vars.filter fun (n, _) =>
  ((testSuiteRenames.map fun (a, b) => (b, a)).lookup n |>.getD n |>
    (lookupBy · TestSuite.vars)).isNone).map (·.1))

end Solidity.Corpus

/-! ## Obligations at a store, from `⊢`

The `TestSuite` obligations are derived by the scoped `⊢`
(`Proves`, `docs/intrinsic.md`, W3c): `N.f.proved : ⊢ N.f.problem`, on
the import's scoped program `N.f` (`Prog`, W8).  Its corollary at the initial storage is
stated over the typed run of that program, as every other corpus row is
(`Corpus/Basic.lean`): `N.f.problem` has its source input premise followed
by `wt(storage) → ⟨ Q ⟩ true`, and
`Q`'s typed run from the initial state ends normally, or is exhausted
(`Runs`, decision 15).  It is the scoped
`⊢`'s soundness (`Proves.fmlValid`) at that state, whose storage is
well-formed (`initState_wt`); nothing is left to evaluate. -/

namespace Solidity.Corpus

variable {C : Contract}

/-- solkey's `\<{ f(); }\>(true)` at `σ`, for an obligation `φ` of no
parameters: `φ` has a proved source input premise before
`wt(storage) → ⟨ Q ⟩ true` (`Problem.fml`) and
`Q`'s typed run from `σ` ends normally, or is exhausted (`Runs`,
decision 15). -/
def Obligation.Diamond (σ : State C []) (φ : Fml C []) : Prop :=
  ∃ (pre : Fml C []) (Γ' : Ctx) (Q : Prog C [] Γ'),
    φ = .imp pre (Problem.fml .diamond [] Q) ∧ holds σ pre ∧ Runs .diamond σ Q

/-- solkey's `\[{ f(); }\](true)` at `σ`, for an obligation `φ` of no
parameters: `φ` has a proved source input premise before
`wt(storage) → [ Q ] true` and `Q`'s typed run from `σ`
does not panic. -/
def Obligation.Box (σ : State C []) (φ : Fml C []) : Prop :=
  ∃ (pre : Fml C []) (Γ' : Ctx) (Q : Prog C [] Γ'),
    φ = .imp pre (Problem.fml .box [] Q) ∧ holds σ pre ∧ Runs .box σ Q

/-- **A derived obligation of no parameters holds at the initial state**:
its program, run typed from there, under its modality.  `wt(storage)` there
is `initStorage_wt`'s. -/
theorem runs_of_proved {m : Modality} {Γ' : Ctx} {Q : Prog C [] Γ'}
    {pre : Fml C []} (h : Proves C .all [] .nil (.imp pre (Problem.fml m [] Q)))
    (hp : holds (State.init C) pre)
    (hw : holds (State.init C) (Fml.wt C)) : Runs m (State.init C) Q :=
  (h.fmlValid (State.init C) hp) hw

/-- A derived diamond obligation with no parameters holds at the initial
state (`runs_of_proved`). -/
theorem diamond_of_proved {Γ' : Ctx} {Q : Prog C [] Γ'}
    {pre : Fml C []} (h : Proves C .all [] .nil (.imp pre (Problem.fml .diamond [] Q)))
    (hw : holds (State.init C) (Fml.wt C)) (hp : holds (State.init C) pre) :
    Obligation.Diamond (State.init C) (.imp pre (Problem.fml .diamond [] Q)) :=
  ⟨pre, _, Q, rfl, hp, runs_of_proved h hp hw⟩

/-- A derived box obligation with no parameters holds at the initial state
(`runs_of_proved`). -/
theorem box_of_proved {Γ' : Ctx} {Q : Prog C [] Γ'}
    {pre : Fml C []} (h : Proves C .all [] .nil (.imp pre (Problem.fml .box [] Q)))
    (hw : holds (State.init C) (Fml.wt C)) (hp : holds (State.init C) pre) :
    Obligation.Box (State.init C) (.imp pre (Problem.fml .box [] Q)) :=
  ⟨pre, _, Q, rfl, hp, runs_of_proved h hp hw⟩

/-! A corollary of `Corpus/TestSuite.lean` uses the axioms of its `⊢`
theorem, which `TestSuite/Report.lean`'s pin checks, of `initState_wt`,
pinned there on one corollary, and of these two, through `Proves.fmlValid`. -/

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
