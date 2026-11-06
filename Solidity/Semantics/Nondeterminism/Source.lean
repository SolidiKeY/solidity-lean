import Solidity.Semantics.Nondeterminism.Pipelines
import Solidity.Semantics.Nondeterminism.Fork
import Solidity.Source.Semantics

/-!
# The source semantics as a split language (S5.1, S5.2)

The independent source semantics (`Solidity/Source/Semantics.lean`) already
keeps the environment apart. G01's `SessionEnv` is its environment: requests
by history and index (callers and transaction order), the callee strategy
(callbacks and reentrancy), opening balances and code existence. The
pipeline is a field of the program (`SrcProg.pipeline`, read by
`Glob.pipeline` in `Solidity/Source/Eval.lean`). `sourceSplit` takes the
pipeline from the compiler choice instead, so the program's own field is
ignored there (`sourceSplit_own` uses it to recover `sourceLang`). Moving
the field out of `SrcProg` belongs to the source's owner.

**The source reads no D1 value today.** `gasleft()` and the code reads are
refused at admission, and `type(C)` members are a recorded gap. So
`sourceSplit` declares every program D1-free (`readsD1 := fun _ => false`)
and is confined (`sourceSplit_confined`). The parameter has nowhere to make
a wrong compiler right. When X03 and X07 add the D1 reads, they read
`CompilerChoice.artifact` and `.oracle`, replace `readsD1` with the
syntactic predicate, and owe `Confined` again. The source's G01 artifact
parameter (`SourceSpec.meaning`) is a second artifact parameter. X01
identifies the two when the source becomes a `SourceSpec`.

`sourceForked` reads the fork parameter of
`Solidity/Semantics/Nondeterminism/Fork.lean` and ignores it
(`sourceForked_blind`). The source reads no block field yet: `SrcProg.glob`
fixes `Glob.timestamp` to `0`. X02 routes `EnvChoice.block` into the source.

Witnesses (an allowed environment, the real `sourceSplit`, non-vacuity, and
"not under both pipelines") are in
`Solidity/Semantics/Nondeterminism/SourceWitness.lean`.
-/

namespace Solidity.Semantics.Nondeterminism

open Solidity.Roadmap
open Solidity.Source

/-- **The source semantics, split**: the choice supplies the pipeline. -/
def sourceSplit (E : Source.Env) : SplitSpec where
  Prog := SrcProg E
  Env := SessionEnv
  Res := Nat
  resLE := inferInstance
  Allowed := SessionEnv.Allowed
  Admissible := fun _ => True
  sem c P := sessionAt { P with pipeline := c.pipeline }
  consistent _ _ := sessionAt_consistent _
  readsD1 _ := false

/-- At the program's own pipeline the split language is `sourceLang`. -/
theorem sourceSplit_own (E : Source.Env) (P : SrcProg E) (a : Artifact) (g : GasOracle) :
    (sourceSplit E).sem ⟨P.pipeline, a, g⟩ P = (sourceLang E).sem P := rfl

/-- At any choice it is `sourceLang` at the choice's pipeline. -/
theorem sourceSplit_at (E : Source.Env) (c : CompilerChoice) (P : SrcProg E) :
    ((sourceSplit E).at c).sem P = (sourceLang E).sem { P with pipeline := c.pipeline } := rfl

/-- The environment of the split source is G01's session environment, with
its allowed set. -/
theorem sourceSplit_env (E : Source.Env) (c : CompilerChoice) :
    ((sourceSplit E).at c).Env = (sourceLang E).Env ∧
      ((sourceSplit E).at c).Allowed = (sourceLang E).Allowed :=
  ⟨rfl, rfl⟩

/-- **The source reads no D1 value**: it is blind to the artifact and the
oracle, hence confined. -/
theorem sourceSplit_confined (E : Source.Env) : (sourceSplit E).Confined :=
  SplitSpec.confined_of_blind (L := sourceSplit E) (fun _ _ _ => rfl) (fun _ _ _ => rfl)

/-- A property of `sourceLang` at the program's own pipeline is the split
property at the choice with that pipeline. -/
theorem sourceSplit_holds_iff (E : Source.Env) (P : SrcProg E) (a : Artifact) (g : GasOracle)
    (Φ : Prefix Event Outcome → Prop) :
    (sourceSplit E).Holds ⟨P.pipeline, a, g⟩ P Φ ↔
      ∀ e, (sourceLang E).Allowed e → ∀ n, Φ ((sourceLang E).sem P e n) :=
  ⟨fun h e he n => h e he n trivial, fun h e he n _ => h e he n⟩

/-- The source at every fork: it reads the session only. -/
def sourceForked (E : Source.Env) : ForkedSplit := (sourceSplit E).forked id

theorem sourceForked_blind (E : Source.Env) (P : SrcProg E) : (sourceForked E).ForkBlind P :=
  SplitSpec.forked_blind (sourceSplit E) id P

end Solidity.Semantics.Nondeterminism
/-- info: 'Solidity.Semantics.Nondeterminism.sourceSplit_confined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Semantics.Nondeterminism.sourceSplit_confined
/-- info: 'Solidity.Semantics.Nondeterminism.sourceForked_blind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Semantics.Nondeterminism.sourceForked_blind
