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
has a proved target bridge. Not in the family (no theorem, not admitted):
`continue` other than `whileContinue`, `return` (Lower.lean:454-459, 536-538), `do … while` (:507-512),
pure conditions, real bodies and suffix guards (:429-431), nested loops and
shared return flags (:497-501), specifications (:526-530), non-Boolean or
non-local operands. -/
inductive Shape where
  /-- `while (i = a) break;` (G19 `AssignmentWhileBreak`). -/
  | whileBreak
  /-- `for (i = a; ; post) break;` (G19 `AssignmentForBreak`). -/
  | forBreak
  /-- `while (i = a) { a = false; continue; tail }` (G19 `AssignmentWhileContinue`). -/
  | whileContinue
  deriving DecidableEq, Repr

/-- Per-shape data beyond the Boolean pair. For `forBreak`: the Source update
expression and the intrinsic image of the lowered update, absent when the raw
update list is empty (Lower.lean:515). A present update is guarded by the
break flag (Lower.lean:516-517) and never runs, so the two are not associated:
the statement holds for every pair of them. For `whileContinue`: the fresh
continue flag and the Source items after `continue`, which lowering drops
(Lower.lean:427) and Source never runs. -/
def Shape.Extra (E : Source.Env) (returns : List Source.STy) (M u : Bool) (srcΓ : Source.RCtx)
    (C : Contract) (Γ : Ctx) : Shape → Type
  | .whileBreak => Unit
  | .forBreak => Source.ROptExpr E srcΓ × Option ((Δ : Ctx) × Prog C (.val .bool :: Γ) Δ)
  | .whileContinue => Var × ((tailΓ : Source.RCtx) × Source.RItems E returns M ⟨true, u⟩ srcΓ tailΓ)

/-- Boolean negation as the elaborator emits it. -/
def notB {C : Contract} {Γ : Ctx} (v : Val C Γ .bool) : Val C Γ .bool := .unop .not rfl rfl v

/-- `!flag && true`: the guard `notAny [brk]` puts before the synthetic `true`
condition (Lower.lean:493-496, 518). -/
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

/-- Intrinsic image of the lowered
`{ i = a; bool brk = false; while (!brk && true) { brk = true; if (!brk) { upd } } }`
(Lower.lean:485-487, 502, 515-518, 522, 533-539; the outer block is flattened by
elaboration). -/
def forBreakBody {C : Contract} {Γ : Ctx} :
    Option ((Δ : Ctx) × Prog C (.val .bool :: Γ) Δ) → Prog C (.val .bool :: Γ) (.val .bool :: Γ)
  | none => .cons (.assignLocal .here (.simple (.bool true))) .nil
  | some upd => .cons (.assignLocal .here (.simple (.bool true)))
      (.cons (.ite (notB (.simple (.local .here))) upd.2 .nil) .nil)

def forBreakProg {C : Contract} {Γ : Ctx} (names : Fresh) (j b : Idx Γ (.val .bool))
    (upd : Option ((Δ : Ctx) × Prog C (.val .bool :: Γ) Δ)) : Prog C Γ (.val .bool :: Γ) :=
  .cons (.assignLocal j (.simple (.local b)))
    (.cons (.declLocal .bool names.flag (some (.simple (.bool false))))
      (.cons (.loop .auto flagGuard (forBreakBody upd)) .nil))

/-- Iteration body of the while/continue lowering after its two declarations
(`se`, `cnt`): `i = se; if (!se) brk = true; if (!brk) { a = false; cnt = true; }`. -/
def whileContinueTail {C : Contract} {Γ : Ctx} (j b : Idx Γ (.val .bool)) :
    Prog C (.val .bool :: .val .bool :: .val .bool :: Γ) (.val .bool :: .val .bool :: .val .bool :: Γ) :=
  .cons (.assignLocal j.there.there.there (.simple (.local .here)))
    (.cons (.ite (notB (.simple (.local .here)))
        (.cons (.assignLocal Idx.here.there.there (.simple (.bool true))) .nil) .nil)
      (.cons (.ite (notB (.simple (.local Idx.here.there.there)))
          (.cons (.assignLocal b.there.there.there (.simple (.bool false)))
            (.cons (.assignLocal Idx.here.there (.simple (.bool true))) .nil)) .nil)
        .nil))

/-- Loop body: continue flag, condition capture, then the tail. -/
def whileContinueBody {C : Contract} {Γ : Ctx} (cnt se : Var) (j b : Idx Γ (.val .bool)) :
    Prog C (.val .bool :: Γ) (.val .bool :: .val .bool :: .val .bool :: Γ) :=
  .cons (.declLocal .bool cnt (some (.simple (.bool false))))
    (.cons (.declLocal .bool se (some (.simple (.local b.there.there)))) (whileContinueTail j b))

/-- Intrinsic image of the lowered `while (i = a) { a = false; continue; … }`
(Lower.lean:493-496 condition into the body, :453 `continue` to a flag, :427
suffix after a jump dropped, :514 continue-flag reset, :518 condition guard,
:522 break-flag declaration). -/
def whileContinueProg {C : Contract} {Γ : Ctx} (brk cnt se : Var) (j b : Idx Γ (.val .bool)) :
    Prog C Γ (.val .bool :: Γ) :=
  .cons (.declLocal .bool brk (some (.simple (.bool false))))
    (.cons (.loop .auto flagGuard (whileContinueBody cnt se j b)) .nil)

/-- Resolved Source statement of each shape, in the form Source typing gives
it (the identity conversion on the right-hand side is retained,
`Checker.SourceAssociation.resolved_eq`). That typing produces this form is
proved for the concrete samples in `Loops.Correct` only, not generically. -/
def Shape.source {E : Source.Env} {srcΓ : Source.RCtx} {returns : List Source.STy}
    {M l u : Bool} {Γ : Ctx} {m : ContextMap srcΓ Γ} :
    {C : Contract} → (k : Shape) → Pair m → k.Extra E returns M u srcΓ C Γ →
      Source.RStmt E returns M ⟨l, u⟩ srcΓ srcΓ
  | _, .whileBreak, p, _ => .whileLoop (.assign (.local p.i) (.conv (.local p.a) (.inl rfl))) .brk
  | _, .forBreak, p, x =>
    .forLoop (.expr (.assign (.local p.i) (.conv (.local p.a) (.inl rfl)))) .none x.1 .brk
  | _, .whileContinue, p, x =>
    .whileLoop (.assign (.local p.i) (.conv (.local p.a) (.inl rfl)))
      (.block (.stmt (.expr (.assign (.local p.a) (.conv (.bool false) (.inl rfl))))
        (.stmt .cont x.2.2)))

/-- Source horizon offset at which the shape's normal outcome is reached. A
derived constant, not a fuel/gas equation. -/
def Shape.offset : Shape → Nat
  | .whileBreak => 4
  | .forBreak => 5
  | .whileContinue => 9

/-- The intrinsic output each shape's lowering is associated with. -/
def Shape.lowered {E : Source.Env} {returns : List Source.STy} {M u : Bool} {C : Contract}
    {srcΓ : Source.RCtx} {Γ : Ctx} {m : ContextMap srcΓ Γ} :
    (k : Shape) → Pair m → k.Extra E returns M u srcΓ C Γ → Fresh → Blk C Γ
  | .whileBreak, p, _, names => ⟨_, whileBreakProg names (boolSlot m p.i p.hi) (boolSlot m p.a p.ha)⟩
  | .forBreak, p, x, names =>
    ⟨_, forBreakProg names (boolSlot m p.i p.hi) (boolSlot m p.a p.ha) x.2⟩
  | .whileContinue, p, x, names =>
    ⟨_, whileContinueProg names.flag x.1 names.capture (boolSlot m p.i p.hi) (boolSlot m p.a p.ha)⟩

/-- Total syntactic output association: the supplied intrinsic output is the
family member. Decided for a closed quoted output by kernel reduction. -/
def Accepts {E : Source.Env} {returns : List Source.STy} {M u : Bool} {C : Contract}
    {srcΓ : Source.RCtx} {Γ : Ctx}
    {m : ContextMap srcΓ Γ} (k : Shape) (p : Pair m) (x : k.Extra E returns M u srcΓ C Γ) (names : Fresh)
    (output : Blk C Γ) : Prop :=
  output = k.lowered p x names

/-- The semantic endpoint of the P1 contract (`Checker.SemanticSoundnessStatement`)
for one resolved statement and one target program: from any aligned Source/target
pair, Source reaches a normal outcome at the stated horizon offset, the target
program runs to a state whose caller locals (through `embedding`) are related to
the Source locals, and target globals are unchanged. Both pipelines (`G`) and
every Source state are covered. Source journal and target storage stay distinct.
Initial facts on `R`: Boolean values are related only to their reflection, and
`false` is related to `false` (both are G19's premises; the second is needed by
the `continue` leaf). -/
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
    (∀ H : HTy, R H .bool (.val .bool) (.bool false) false) →
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
against the family's Source loop. One statement for the whole family (H112).

This is a family statement: it does not mention `lowerLoops`, raw input, the
fresh counter or the memo, and only normal outcomes with an empty journal are
stated (no return, revert, error or timeout outcomes). That the actual producer
emits family members is shown per sample (`Loops.Correct`, `Loops.Capture`).
Whether `Solidity.Goals.lowerLoopsCorrect` should be this proposition is an
open owner decision; the goal is unchanged here. -/
def LowerLoopsCorrect : Prop :=
  ∀ (k : Shape) {E : Source.Env} {srcΓ : Source.RCtx} {returns : List Source.STy}
    {M l u : Bool} {C : Contract} {Γ : Ctx}
    (m : ContextMap srcΓ Γ) (p : Pair m) (x : k.Extra E returns M u srcΓ C Γ) (names : Fresh)
    (output : Blk C Γ),
    Accepts k p x names output →
    ∃ embedding : Thin Γ output.1,
      Endpoint (k.source (returns := returns) (M := M) (l := l) (u := u) p x)
        k.offset m output.2 embedding

end Solidity.Correctness.Lowering.Loops
