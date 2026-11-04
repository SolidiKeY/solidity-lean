import Solidity.Semantics.Nondeterminism.Pipelines
import Solidity.Semantics.Nondeterminism.Fork
import Solidity.Source.SemanticsExamples

/-!
# The source semantics as a split language (S5.1, S5.2)

The independent source semantics (`Solidity/Source/Semantics.lean`) already
separates the two kinds of nondeterminism. G01's `SessionEnv` is its
environment: requests by history and index (callers and transaction order),
the callee strategy (callbacks and reentrancy), opening balances and code
existence. The pipeline is a field of the program (`SrcProg.pipeline`,
read by `Glob.pipeline` in `Solidity/Source/Eval.lean`). `sourceSplit` makes
the pipeline the compiler choice's: the program's own field is replaced by
the choice's.

Today the source reads no D1 value. `gasleft()` and the code reads are
refused at admission, and `type(C)` members are a recorded gap. So
`sourceSplit` is blind to the artifact and the oracle (`sourceSplit_confined`):
the parameter has nowhere to make a wrong compiler right. When X03 and X07
add the D1 reads, they read `CompilerChoice.artifact` and
`CompilerChoice.oracle`, and `sourceSplit_confined` becomes the obligation
`Confined` for the programs that do not read them.

The witness `orderProg` is the session form of `order_legacy`/`order_viaIR`:
`g()` returns `++x + x` after `x = 1`, which is `3` under legacy and `4` via
IR. Both runs are kernel-checked, so `HoldsFor` at one pipeline does not give
`HoldsBoth` for the source.

`sourceForked` reads the fork parameter of
`Solidity/Semantics/Nondeterminism/Fork.lean` and ignores it
(`sourceForked_blind`). The source reads no block field yet: `SrcProg.glob`
fixes `Glob.timestamp` to `0`. X02 routes `BlockEnv.timestamp` and the other
fields through `EnvChoice.block`, and then `sourceForked_blind` stops holding
for programs that read them.
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
oracle, hence confined for every read predicate. -/
theorem sourceSplit_confined (E : Source.Env) (R : SrcProg E → Prop) :
    (sourceSplit E).Confined R :=
  SplitSpec.confined_of_blind (L := sourceSplit E) (fun _ _ _ => rfl) (fun _ _ _ => rfl) R

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

/-! ## Witness: the evaluation order is a compiler choice -/

namespace OrderWitness

open Solidity.Source.SemanticsExamples

/-- `x = 1; return ++x + x;` -/
def gOrder : RBody EB := ⟨[], [uint], false, [uint], [uint],
  .stmt (setX (lit 1))
    (.stmt (.retVal rfl (.binary .add (.incDec true true (.state dX dX_ty rfl)) (.state dX dX_ty)) rfl) .nil), []⟩

/-- `C` with `g()` as above. -/
def PO : Program EB where
  body d := match d.name with
    | "g" => some gOrder
    | _ => none
  consts _ := none
  inits _ := []
  ctor _ := none
  ctorLocals _ := []
  baseArgs _ := []
  contracts := ["C"]

/-- The program; its own pipeline is legacy, and the choice overrides it. -/
def orderProg : SrcProg EB := ⟨PO, .legacy, toyFixed, "C"⟩

/-- The session at address `0` under a pipeline (`sessionAt` at the toy
creation address unfolds `Evm.beBytes`, which the kernel does not reduce;
`sessionAt_eq` relates the two). -/
def at0 (q : Pipeline) (n : Nat) : Prefix Event Outcome :=
  sessionFrom { orderProg with pipeline := q } envS (addr 0) n

/-- **Legacy**: `3` (the right operand `x` is read first). -/
theorem order_legacy : (at0 .legacy 30).final = some (.success (wordBytes (toWord 3))) := by
  decide +kernel

/-- **Via IR**: `4` (source order). -/
theorem order_viaIR : (at0 .viaIR 30).final = some (.success (wordBytes (toWord 4))) := by
  decide +kernel

/-- **Negative control**: neither pipeline gives the other's result. -/
theorem order_differs : (at0 .legacy 30).final ≠ (at0 .viaIR 30).final := by
  rw [order_legacy, order_viaIR]
  decide +kernel

/-- The witness is the split source semantics at each pipeline. -/
theorem at0_split (q : Pipeline) (n : Nat) :
    sessionAt { orderProg with pipeline := q } envS n =
      sessionFrom { orderProg with pipeline := q } envS (toyFixed.createAddress envS.deployer envS.deployNonce) n :=
  rfl

end OrderWitness

end Solidity.Semantics.Nondeterminism
/-- info: 'Solidity.Semantics.Nondeterminism.sourceSplit_confined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Semantics.Nondeterminism.sourceSplit_confined
/-- info: 'Solidity.Semantics.Nondeterminism.sourceSplit_holds_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Semantics.Nondeterminism.sourceSplit_holds_iff
/-- info: 'Solidity.Semantics.Nondeterminism.sourceForked_blind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Semantics.Nondeterminism.sourceForked_blind
/-- info: 'Solidity.Semantics.Nondeterminism.OrderWitness.order_legacy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Semantics.Nondeterminism.OrderWitness.order_legacy
/-- info: 'Solidity.Semantics.Nondeterminism.OrderWitness.order_viaIR' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Semantics.Nondeterminism.OrderWitness.order_viaIR
/-- info: 'Solidity.Semantics.Nondeterminism.OrderWitness.order_differs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Semantics.Nondeterminism.OrderWitness.order_differs
