import Solidity.Correctness.Lowering.Checker.Contract

/-!
# Loop lowering: the generic output-association statement (LOW-1 / P1)

`lowerLoops` (`Solidity/Syntax/Elab/Lower.lean:543`) and intrinsic elaboration
(`elabStmtsP`, `Solidity/Syntax/Elab/Stmt.lean:817`) are opaque `partial`
recursions: the kernel cannot unfold them, so no theorem can quantify over their
successful results directly (prior-art-lowering, "Partial elaborator"). Following
the adopted P1 route, the producer stays outside the trust boundary: a total
syntactic association (`Accepts`) relates a resolved Source loop to an intrinsic
output, and one generic statement (`LowerLoopsCorrect`) says that every accepted
output reaches the semantic endpoint of the checker contract
(`Checker.SemanticSoundnessStatement`). Actual producer runs are connected by
kernel acceptance of their quoted outputs (`Loops.Correct`).

`Shape` is the loop-shape family. Each constructor is one G19 loop leaf; its
semantic proof reuses that leaf's G19 `correct` for the Source half and proves
the actual flag-lowered target program generically in the context map, the
source positions and the fresh names. No G19 proof is copied.

This module defines data and propositions only.
-/
namespace Solidity.Correctness.Lowering.Loops

open Solidity.Lowering.V07
open Solidity.Lowering.G19.AssignmentReturnFlag (boolSlot)

/-- Two Boolean source locals and their map facts: the destination `i` and the
right-hand side `a` of the G19 assignment conditions. The slot equations are
the initial typed position facts every G19 `correct` takes; they are data to
be checked on an instance (by `rfl` on a concrete map), not semantic premises. -/
structure Pair {srcΓ : Source.RCtx} {Γ : Ctx} (m : ContextMap srcΓ Γ) where
  i : Source.Idx srcΓ .bool
  a : Source.Idx srcΓ .bool
  hi : (m.slot i).1 = .val .bool
  ha : (m.slot a).1 = .val .bool
  mapI : m.slot i = ⟨.val .bool, boolSlot m i hi⟩
  mapA : m.slot a = ⟨.val .bool, boolSlot m a ha⟩

/-- Fresh names the producer chose (`Var.fresh "brk" n`, `Var.fresh "se" k`).
Names do not affect intrinsic semantics; they are free in the family. -/
structure Fresh where
  flag : Var
  capture : Var

/-- The loop-shape family. Each constructor is one G19 loop leaf whose lowering
has a proved target bridge; constructs without one are listed as uncovered in
the lane result, not admitted here. -/
inductive Shape where
  /-- `while (i = a) break;` (G19 `AssignmentWhileBreak`). -/
  | whileBreak
  deriving DecidableEq, Repr

/-- Boolean negation as the elaborator emits it. -/
def notB {C : Contract} {Γ : Ctx} (v : Val C Γ .bool) : Val C Γ .bool := .unop .not rfl rfl v

/-- `!flag && true`: the guard `notAny [brk]` puts before the synthetic `true`
condition (Lower.lean:493-496, 516-518). -/
def flagGuard {C : Contract} {Γ : Ctx} : Val C (.val .bool :: Γ) .bool :=
  .binop .and rfl rfl (notB (.simple (.local .here))) (.simple (.bool true))

/-- Iteration tail of the while/break lowering after the condition capture:
`i = se; if (!se) brk = true; if (!brk) { brk = true; }`. -/
def whileBreakTail {C : Contract} {Γ : Ctx} (j : Idx Γ (.val .bool)) :
    Prog C (.val .bool :: .val .bool :: Γ) (.val .bool :: .val .bool :: Γ) :=
  .cons (.assignLocal j.there.there (.simple (.local .here)))
    (.cons (.ite (notB (.simple (.local .here)))
        (.cons (.assignLocal Idx.here.there (.simple (.bool true))) .nil) .nil)
      (.cons (.ite (notB (.simple (.local Idx.here.there)))
          (.cons (.assignLocal Idx.here.there (.simple (.bool true))) .nil) .nil)
        .nil))

/-- Loop body: capture of the right-hand side, then the tail. -/
def whileBreakBody {C : Contract} {Γ : Ctx} (se : Var) (j b : Idx Γ (.val .bool)) :
    Prog C (.val .bool :: Γ) (.val .bool :: .val .bool :: Γ) :=
  .cons (.declLocal .bool se (some (.simple (.local b.there)))) (whileBreakTail j)

/-- Intrinsic image of the lowered `{ bool brk = false; while (!brk && true) { … } }`,
generic in the target slots `j` (destination) and `b` (right-hand side). -/
def whileBreakProg {C : Contract} {Γ : Ctx} (names : Fresh) (j b : Idx Γ (.val .bool)) :
    Prog C Γ (.val .bool :: Γ) :=
  .cons (.declLocal .bool names.flag (some (.simple (.bool false))))
    (.cons (.loop .auto flagGuard (whileBreakBody names.capture j b)) .nil)

/-- Resolved Source statement of each shape, as Source typing resolves it
(the identity conversion on the right-hand side is retained,
`Checker.SourceAssociation.resolved_eq`). -/
def Shape.source {E : Source.Env} {srcΓ : Source.RCtx} {returns : List Source.STy}
    {M l u : Bool} {Γ : Ctx} {m : ContextMap srcΓ Γ} :
    Shape → Pair m → Source.RStmt E returns M ⟨l, u⟩ srcΓ srcΓ
  | .whileBreak, p => .whileLoop (.assign (.local p.i) (.conv (.local p.a) (.inl rfl))) .brk

/-- Source horizon offset at which the shape's normal outcome is reached. A
derived constant, not a fuel/gas equation. -/
def Shape.offset : Shape → Nat
  | .whileBreak => 4

/-- The intrinsic output each shape's lowering is associated with. -/
def Shape.lowered {C : Contract} {srcΓ : Source.RCtx} {Γ : Ctx} {m : ContextMap srcΓ Γ} :
    Shape → Pair m → Fresh → Blk C Γ
  | .whileBreak, p, names => ⟨_, whileBreakProg names (boolSlot m p.i p.hi) (boolSlot m p.a p.ha)⟩

/-- Total syntactic output association: the supplied intrinsic output is the
family member. Decided for a closed quoted output by kernel reduction. -/
def Accepts {C : Contract} {srcΓ : Source.RCtx} {Γ : Ctx} {m : ContextMap srcΓ Γ}
    (k : Shape) (p : Pair m) (names : Fresh) (output : Blk C Γ) : Prop :=
  output = k.lowered p names

/-- The semantic endpoint of the P1 contract (`Checker.SemanticSoundnessStatement`)
for one resolved statement and one target program: from any aligned Source/target
pair, Source reaches a normal outcome at the stated horizon offset, the target
program runs to a state whose caller locals (through `embedding`) are related to
the Source locals, and target globals are unchanged. Both pipelines (`G`) and
every Source state are covered. Source journal and target storage stay distinct. -/
def Endpoint {E : Source.Env} {srcΓ : Source.RCtx} {returns : List Source.STy} {M : Bool}
    {k : Source.SCtx} {C : Contract} {Γ Δ : Ctx}
    (statement : Source.RStmt E returns M k srcΓ srcΓ) (offset : Nat)
    (m : ContextMap srcΓ Γ) (program : Prog C Γ Δ) (embedding : Thin Γ Δ) : Prop :=
  ∀ (G : Source.Glob E) (F : Source.Fr) (fuel nps : Nat) (ph : Option (Source.Ph E))
    (source : Source.EMState E srcΓ) (target : State C Γ)
    (R : (H : HTy) → (τ : Source.STy) → (u : LTy) →
      Source.Val E.layout τ → u.TDenote C H → Prop),
    m.Related (R target.H) source.1 target.env →
    (∀ (H : HTy) (v : Source.Val E.layout .bool) (b : Bool),
      R H .bool (.val .bool) v b → v = .bool b) →
    ∃ (ls : Source.Locals E.layout srcΓ) (out : Out C target.H Δ),
      (Source.execS G F (fuel + offset) nps ph statement source.1).run (.nil, source.2) =
        (.ok (Source.Out.normal ls), (.nil, source.2)) ∧
      program.run target = .ok out ∧
      (m.wk embedding).Related (R out.st.H) ls out.st.env ∧
      out.st.glob = target.glob

/-- **Loop lowering is correct on its accepted family.** For every shape, every
Source context, control context and pipeline, every context map with Boolean
destination/right-hand-side positions, every fresh-name choice and every
intrinsic output the association accepts, the output reaches the endpoint
against the resolved Source loop. One statement for the whole family (H112);
the finish-line component `Solidity.Goals.lowerLoopsCorrect` is meant to be
this proposition. -/
def LowerLoopsCorrect : Prop :=
  ∀ (k : Shape) {E : Source.Env} {srcΓ : Source.RCtx} {returns : List Source.STy}
    {M l u : Bool} {C : Contract} {Γ : Ctx}
    (m : ContextMap srcΓ Γ) (p : Pair m) (names : Fresh) (output : Blk C Γ),
    Accepts k p names output →
    ∃ embedding : Thin Γ output.1,
      Endpoint (k.source (E := E) (returns := returns) (M := M) (l := l) (u := u) p)
        k.offset m output.2 embedding

end Solidity.Correctness.Lowering.Loops
