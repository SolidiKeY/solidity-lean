import Solidity.Roadmap.Contracts

/-!
# Environment versus compiler nondeterminism (S5.1)

A source semantics is nondeterministic in two different ways, and the two
must not be confused in a theorem:

- **Environment nondeterminism** is demonic: who calls, in what order, what
  every callee does (callbacks and reentrancy), the opening balances, code
  existence, and the block fields. A property holds only if it holds for
  *every* allowed environment. Here the environment is the language's `Env`
  (G01's `SessionEnv` for the source; `EnvChoice` of
  `Solidity/Semantics/Nondeterminism/Fork.lean` adds the block fields).
- **Compiler nondeterminism** is a *parameter*: the values the compiled
  artifact decides. These are solc's pipeline, and through it the expression
  evaluation order (O9, `Pipeline.order` in `Solidity/Roadmap/TypedRun.lean`),
  the artifact table (G00 Q5, `Artifact`), and the gas values of D1
  (`gasleft()`, `gas`, `msize`, `pc`), which a gas oracle supplies. A theorem
  names the choice it is stated at (`CompilerChoice`). The choice is one
  value fixed before the environment: it may not depend on the environment
  (`Controls.envToy_no_choice` in `Pipelines.lean`).

`SplitSpec` is a G01 `Lang Event Outcome` family indexed by a
`CompilerChoice`. `SplitSpec.at c` is the ordinary language at one choice.
`Holds` quantifies the environment and the bound universally at a fixed
choice. `HoldsFor` fixes the pipeline and artifact and quantifies every
oracle, because gas values are unknown to a user-facing statement.
`HoldsBoth` asks for both pipelines, each with its own artifact. In these
two user-facing forms the choice is quantified universally, like the
environment. That is sound, since a statement must hold whatever the
compiler chose. The split has content where the compiler fixes the choice:
refinement at the compiler's choice, and the oracle the target supplies
(`Pipelines.lean`). The artifact function `art` of `HoldsBoth` is any table
per pipeline. The composition instantiates it with the compiler's output for
that pipeline and optimizer setting; the optimizer setting is not a field,
so there is one `art` per setting.

Each split language declares which programs read a D1 value
(`SplitSpec.readsD1`), a Boolean fixed with the language. D1's confinement
(`SplitSpec.Confined`) is checked against that predicate, so a language
cannot pass the check by choosing the predicate afterwards.
`Solidity/Semantics/Nondeterminism/Pipelines.lean` (S5.2) relates these
forms and checks D1's non-circularity against the parameter.

The module imports only the G01 contracts, so the parameter types are
available below any source semantics (G07's whitelist names
`Solidity.Roadmap.Contracts`).
-/

namespace Solidity.Semantics.Nondeterminism

open Solidity.Roadmap

/-! ## The compiler's choice -/

/-- The D1 reads a gas oracle answers: the values that depend on the
compiled code's gas, memory and program counter. Own `codesize` and
`codecopy`, `creationCode` and `runtimeCode` read the artifact table
instead. -/
inductive OracleRead where
  | gasleft
  | gas
  | msize
  | pc
  deriving DecidableEq, Repr

/-- **A gas oracle** (D1): the word the target execution reports for the
`n`-th oracle read of kind `k` after the observable history `h`. The target
run supplies it; the source semantics only reads it. Any function is an
oracle: nothing requires `gasleft` to decrease or `msize` to be a multiple
of 32, so `HoldsFor` cannot prove such facts (a recorded limitation). -/
structure GasOracle where
  read : List Event → Nat → OracleRead → Word

/-- The oracle that answers every read with `w`. -/
def GasOracle.const (w : Word) : GasOracle := ⟨fun _ _ _ => w⟩

/-- **The compiler's choice**: the pipeline, the artifact table and the gas
oracle. -/
structure CompilerChoice where
  pipeline : Pipeline
  artifact : Artifact
  oracle : GasOracle

/-- The empty artifact table. -/
def Artifact.empty : Artifact := ⟨[], 0⟩

/-- A choice with the empty table and the oracle at `0`; the witnesses use it. -/
def CompilerChoice.plain (q : Pipeline) : CompilerChoice :=
  ⟨q, Artifact.empty, GasOracle.const ⟨0, by decide⟩⟩

/-! ## Split languages -/

/-- **A split language**: G01's session semantics as a family indexed by the
compiler's choice. `Env` holds only environment inputs; everything the
compiler decides is in `CompilerChoice`. -/
structure SplitSpec where
  Prog : Type
  Env : Type
  Res : Type
  resLE : LE Res
  Allowed : Env → Prop
  Admissible : Res → Prop
  sem : CompilerChoice → Prog → Env → Prefixes Res Event Outcome
  consistent : ∀ c p e, @Prefixes.Consistent Res Event Outcome resLE (sem c p e)
  /-- The programs that read a D1 value (`gasleft`, `gas`, `msize`, `pc`,
  own code, `type(C)` code), declared with the language. -/
  readsD1 : Prog → Bool

namespace SplitSpec

variable (L : SplitSpec)

/-- The ordinary G01 language at one compiler choice. -/
def «at» (c : CompilerChoice) : Lang Event Outcome where
  Prog := L.Prog
  Env := L.Env
  Res := L.Res
  resLE := L.resLE
  Allowed := L.Allowed
  Admissible := L.Admissible
  sem := L.sem c
  consistent := L.consistent c

theorem at_sem (c : CompilerChoice) : (L.at c).sem = L.sem c := rfl

/-- **A property at a compiler choice**: for every allowed environment and
every admissible bound. The environment is quantified, the choice is not. -/
def Holds (c : CompilerChoice) (p : L.Prog) (Φ : Prefix Event Outcome → Prop) : Prop :=
  ∀ e, L.Allowed e → ∀ r, L.Admissible r → Φ (L.sem c p e r)

/-- **The user-facing form at a pipeline and its artifact**: every gas
oracle, since a source statement cannot know gas values. -/
def HoldsFor (q : Pipeline) (art : Artifact) (p : L.Prog) (Φ : Prefix Event Outcome → Prop) :
    Prop :=
  ∀ g, L.Holds ⟨q, art, g⟩ p Φ

/-- **Under both pipelines**: each pipeline with the artifact it produces. -/
def HoldsBoth (art : Pipeline → Artifact) (p : L.Prog) (Φ : Prefix Event Outcome → Prop) : Prop :=
  ∀ q, L.HoldsFor q (art q) p Φ

/-- The language does not read the pipeline for `p`. -/
def PipelineBlind (p : L.Prog) : Prop :=
  ∀ c q, L.sem { c with pipeline := q } p = L.sem c p

/-- The language does not read the gas oracle for `p`. -/
def OracleBlind (p : L.Prog) : Prop :=
  ∀ c g, L.sem { c with oracle := g } p = L.sem c p

/-- The language does not read the artifact table for `p`. -/
def ArtifactBlind (p : L.Prog) : Prop :=
  ∀ c a, L.sem { c with artifact := a } p = L.sem c p

variable {L}

theorem Holds.env {c : CompilerChoice} {p : L.Prog} {Φ : Prefix Event Outcome → Prop}
    (h : L.Holds c p Φ) {e : L.Env} (he : L.Allowed e) {r : L.Res} (hr : L.Admissible r) :
    Φ (L.sem c p e r) :=
  h e he r hr

theorem Holds.mono {c : CompilerChoice} {p : L.Prog} {Φ Ψ : Prefix Event Outcome → Prop}
    (h : L.Holds c p Φ) (hΦΨ : ∀ x, Φ x → Ψ x) : L.Holds c p Ψ :=
  fun e he r hr => hΦΨ _ (h e he r hr)

theorem Holds.and {c : CompilerChoice} {p : L.Prog} {Φ Ψ : Prefix Event Outcome → Prop}
    (h₁ : L.Holds c p Φ) (h₂ : L.Holds c p Ψ) : L.Holds c p (fun x => Φ x ∧ Ψ x) :=
  fun e he r hr => ⟨h₁ e he r hr, h₂ e he r hr⟩

/-- `Holds` is the G01 language's universally quantified reading at the choice. -/
theorem holds_iff_at {c : CompilerChoice} {p : L.Prog} {Φ : Prefix Event Outcome → Prop} :
    L.Holds c p Φ ↔ ∀ e, (L.at c).Allowed e → ∀ r, (L.at c).Admissible r → Φ ((L.at c).sem p e r) :=
  Iff.rfl

/-- A program blind to the oracle: one oracle suffices for `HoldsFor`. -/
theorem holdsFor_of_oracleBlind {q : Pipeline} {art : Artifact} {p : L.Prog}
    {Φ : Prefix Event Outcome → Prop} (hb : L.OracleBlind p) (g : GasOracle)
    (h : L.Holds ⟨q, art, g⟩ p Φ) : L.HoldsFor q art p Φ := by
  intro g'
  have e : L.sem ⟨q, art, g'⟩ p = L.sem ⟨q, art, g⟩ p := hb ⟨q, art, g⟩ g'
  intro env he r hr
  rw [e]
  exact h env he r hr

/-- A program blind to the artifact: `HoldsFor` moves to any table. -/
theorem holdsFor_artifact {q : Pipeline} {art : Artifact} {p : L.Prog}
    {Φ : Prefix Event Outcome → Prop} (hb : L.ArtifactBlind p) (h : L.HoldsFor q art p Φ)
    (art' : Artifact) : L.HoldsFor q art' p Φ := by
  intro g env he r hr
  have e : L.sem ⟨q, art', g⟩ p = L.sem ⟨q, art, g⟩ p := hb ⟨q, art, g⟩ art'
  rw [e]
  exact h g env he r hr

/-- A program blind to the pipeline: one pipeline suffices for `HoldsBoth`. -/
theorem holdsBoth_of_pipelineBlind {art : Pipeline → Artifact} {p : L.Prog}
    {Φ : Prefix Event Outcome → Prop} (hb : L.PipelineBlind p) (hab : L.ArtifactBlind p)
    (q : Pipeline) (h : L.HoldsFor q (art q) p Φ) : L.HoldsBoth art p Φ := by
  intro q' g env he r hr
  have e₁ : L.sem ⟨q', art q', g⟩ p = L.sem ⟨q, art q', g⟩ p := hb ⟨q, art q', g⟩ q'
  have e₂ : L.sem ⟨q, art q', g⟩ p = L.sem ⟨q, art q, g⟩ p := hab ⟨q, art q, g⟩ (art q')
  rw [e₁, e₂]
  exact h g env he r hr

end SplitSpec

/-! ## A split language from a family of G01 languages -/

/-- A family of G01 languages over one program, environment and bound type
is a split language. -/
@[reducible] def SplitSpec.ofFamily (Prog Env Res : Type) [inst : LE Res] (Allowed : Env → Prop)
    (Admissible : Res → Prop) (sem : CompilerChoice → Prog → Env → Prefixes Res Event Outcome)
    (consistent : ∀ c p e, @Prefixes.Consistent Res Event Outcome inst (sem c p e))
    (readsD1 : Prog → Bool) : SplitSpec :=
  ⟨Prog, Env, Res, inst, Allowed, Admissible, sem, consistent, readsD1⟩

/-- A G01 language with no compiler-dependent value is the split language
that reads none of the choice; no program reads a D1 value. -/
def SplitSpec.const (L : Lang Event Outcome) : SplitSpec :=
  ⟨L.Prog, L.Env, L.Res, L.resLE, L.Allowed, L.Admissible, fun _ => L.sem, fun _ => L.consistent,
    fun _ => false⟩

theorem SplitSpec.const_blind (L : Lang Event Outcome) (p : L.Prog) :
    (SplitSpec.const L).PipelineBlind p ∧ (SplitSpec.const L).OracleBlind p ∧
      (SplitSpec.const L).ArtifactBlind p :=
  ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩

end Solidity.Semantics.Nondeterminism
/-- info: 'Solidity.Semantics.Nondeterminism.SplitSpec.holdsFor_of_oracleBlind' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Semantics.Nondeterminism.SplitSpec.holdsFor_of_oracleBlind
/-- info: 'Solidity.Semantics.Nondeterminism.SplitSpec.holdsFor_artifact' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Semantics.Nondeterminism.SplitSpec.holdsFor_artifact
/-- info: 'Solidity.Semantics.Nondeterminism.SplitSpec.holdsBoth_of_pipelineBlind' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Semantics.Nondeterminism.SplitSpec.holdsBoth_of_pipelineBlind
