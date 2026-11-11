import Solidity.Correctness.Lowering.Loops.Family

/-!
# Loop lowering with `return`: the callee-body-pass family (H497)

A `return` inside a loop is lowered in two passes on a callee body
(`calleeBody`, `Solidity/Syntax/Elab/Arms.lean:826-830`): `lowerLoops` turns it
into a `ret` flag and an `if (ret) return;` after the outermost loop
(`Lower.lean:454-459, 536-538`), then `lowerReturns` (`Lower.lean:287`) lowers that
trailing `return` of a body with no return values to nothing. The endpoint is
therefore stated for the elaborated output of both passes, and keeps the
Source observation of whether the statement returned: Source ends in
`.ret ls` exactly when the target's return witness (the `ret` flag, or the
condition capture for a plain `if`) is `true`, and in `.normal ls` otherwise.

Exact scope. The target is the elaborated output of the callee-body pass
(`calleeBody`, then `elabStmtsP` under `inlinedBody`'s reader), not of the call:
the frame switch, parameter binding, `CallMemo` and `CallRet` of `inlinedBody`
and the Source call semantics (`callInternal`) are not covered. The Source side
is the resolved body statement, whose `.ret` outcome is observed directly.
Bodies are one statement (or `whileReturnThen`'s loop-then-suffix block) with
no return values (`return;`, `R = []`), no parameters and no modifiers;
`return e;` (`lowerReturn`, Lower.lean:249) is not in the family.
-/
namespace Solidity.Correctness.Lowering.Loops

open Solidity.Lowering.V07
open Solidity.Lowering.G19.AssignmentReturnFlag (boolSlot)

/-- The function-level return family. -/
inductive RetShape where
  /-- `while (i = a) return;` (G19 `WhileReturn`). -/
  | whileReturn
  /-- `do { i = a; return; } while (c);` (G19 `AssignmentDoWhileReturn`). -/
  | doReturn
  /-- `if (i = a) return;` (G19 `AssignmentReturnFlag`; no loop, lowered by
  `lowerReturns` alone). -/
  | returnFlag
  /-- `while (i = a) return; a = false;`: the statement after the loop runs
  only when the loop did not return (`lowerReturns` moves it into the `else`
  branch of the trailing `if (ret)`, Lower.lean:300-304). -/
  | whileReturnThen
  deriving DecidableEq, Repr

/-- Fresh names of a return shape's output: up to three flags/captures. -/
structure RetFresh where
  first : Var
  second : Var
  third : Var

/-- Per-shape data: for `doReturn`, the Source condition and its lowered
image; `!ret && (first || c)` short-circuits on both tests (Lower.lean:511,
518), so neither is evaluated and they are not associated. -/
def RetShape.Extra (E : Source.Env) (srcΓ : Source.RCtx) (C : Contract) (Γ : Ctx) :
    RetShape → Type
  | .whileReturn => Unit
  | .doReturn => Source.RExpr E srcΓ .bool × Val C (.val .bool :: .val .bool :: Γ) .bool
  | .returnFlag => Unit
  | .whileReturnThen => Unit

/-- Iteration body of the lowered `while (i = a) return;` after its capture:
`i = se; if (!se) brk = true; if (!brk) { ret = true; }`. -/
def whileReturnTail {C : Contract} {Γ : Ctx} (j : Idx Γ (.val .bool)) :
    Prog C (.val .bool :: .val .bool :: .val .bool :: Γ) (.val .bool :: .val .bool :: .val .bool :: Γ) :=
  .cons (.assignLocal j.there.there.there (.simple (.local .here)))
    (.cons (.ite (notB (.simple (.local .here)))
        (.cons (.assignLocal Idx.here.there.there (.simple (.bool true))) .nil) .nil)
      (.cons (.ite (notB (.simple (.local Idx.here.there.there)))
          (.cons (.assignLocal Idx.here.there (.simple (.bool true))) .nil) .nil)
        .nil))

/-- `!brk && !ret && true` (Lower.lean:518 with both exits). -/
def brkRetGuard {C : Contract} {Γ : Ctx} : Val C (.val .bool :: .val .bool :: Γ) .bool :=
  .binop .and rfl rfl (notB (.simple (.local Idx.here.there)))
    (.binop .and rfl rfl (notB (.simple (.local .here))) (.simple (.bool true)))

/-- Function-level image of `while (i = a) return;`:
`bool brk = false; bool ret = false; while (!brk && !ret && true) { bool se = a; … }; if (ret) {}`
(Lower.lean:493-496, :454-459, :518, :522, :536-538, then `lowerReturns`). -/
def whileReturnProg {C : Contract} {Γ : Ctx} (names : RetFresh) (j b : Idx Γ (.val .bool)) :
    Prog C Γ (.val .bool :: .val .bool :: Γ) :=
  .cons (.declLocal .bool names.first (some (.simple (.bool false))))
    (.cons (.declLocal .bool names.second (some (.simple (.bool false))))
      (.cons (.loop .auto brkRetGuard
        (.cons (.declLocal .bool names.third (some (.simple (.local b.there.there))))
          (whileReturnTail j)))
        (.cons (.ite (.simple (.local .here)) .nil .nil) .nil)))

/-- Function-level image of `while (i = a) return; a = false;`: as
`whileReturnProg`, with the suffix in the `else` branch of `if (ret)`. -/
def whileReturnThenProg {C : Contract} {Γ : Ctx} (names : RetFresh) (j b : Idx Γ (.val .bool)) :
    Prog C Γ (.val .bool :: .val .bool :: Γ) :=
  .cons (.declLocal .bool names.first (some (.simple (.bool false))))
    (.cons (.declLocal .bool names.second (some (.simple (.bool false))))
      (.cons (.loop .auto brkRetGuard
        (.cons (.declLocal .bool names.third (some (.simple (.local b.there.there))))
          (whileReturnTail j)))
        (.cons (.ite (.simple (.local .here)) .nil
          (.cons (.assignLocal b.there.there (.simple (.bool false))) .nil)) .nil)))

/-- Function-level image of `do { i = a; return; } while (c);`:
`bool first = true; bool ret = false; while (!ret && (first || c)) { first = false; i = a; ret = true; }; if (ret) {}`. -/
def doReturnProg {C : Contract} {Γ : Ctx} (names : RetFresh) (j b : Idx Γ (.val .bool))
    (c : Val C (.val .bool :: .val .bool :: Γ) .bool) : Prog C Γ (.val .bool :: .val .bool :: Γ) :=
  .cons (.declLocal .bool names.first (some (.simple (.bool true))))
    (.cons (.declLocal .bool names.second (some (.simple (.bool false))))
      (.cons (.loop .auto (.binop .and rfl rfl (notB (.simple (.local .here)))
          (.binop .or rfl rfl (.simple (.local Idx.here.there)) c))
        (.cons (.assignLocal Idx.here.there (.simple (.bool false)))
          (.cons (.assignLocal j.there.there (.simple (.local b.there.there)))
            (.cons (.assignLocal .here (.simple (.bool true))) .nil))))
        (.cons (.ite (.simple (.local .here)) .nil .nil) .nil)))

/-- Function-level image of `if (i = a) return;`: `bool se = a; i = se; if (se) {}`. -/
def returnFlagProg {C : Contract} {Γ : Ctx} (names : RetFresh) (j b : Idx Γ (.val .bool)) :
    Prog C Γ (.val .bool :: Γ) :=
  .cons (.declLocal .bool names.first (some (.simple (.local b))))
    (.cons (.assignLocal j.there (.simple (.local .here)))
      (.cons (.ite (.simple (.local .here)) .nil .nil) .nil))

/-- Resolved Source statement, with the identity conversion Source typing keeps. -/
def RetShape.source {E : Source.Env} {srcΓ : Source.RCtx} {M l u : Bool} {Γ : Ctx}
    {m : ContextMap srcΓ Γ} {C : Contract} :
    (k : RetShape) → Pair m → k.Extra E srcΓ C Γ → Source.RStmt E [] M ⟨l, u⟩ srcΓ srcΓ
  | .whileReturn, p, _ => .whileLoop (.assign (.local p.i) (.conv (.local p.a) (.inl rfl))) (.ret rfl)
  | .doReturn, p, x =>
    .doWhile (.block (.stmt (.expr (.assign (.local p.i) (.conv (.local p.a) (.inl rfl))))
      (.stmt (.ret rfl) .nil))) x.1
  | .returnFlag, p, _ => .ifThen (.assign (.local p.i) (.conv (.local p.a) (.inl rfl))) (.ret rfl)
  | .whileReturnThen, p, _ =>
    .block (.stmt (.whileLoop (.assign (.local p.i) (.conv (.local p.a) (.inl rfl))) (.ret rfl))
      (.stmt (.expr (.assign (.local p.a) (.conv (.bool false) (.inl rfl)))) .nil))

def RetShape.offset : RetShape → Nat
  | .whileReturn => 4
  | .doReturn => 7
  | .returnFlag => 4
  | .whileReturnThen => 7

/-- Output contexts: the flags/captures each shape leaves. -/
def RetShape.out (Γ : Ctx) : RetShape → Ctx
  | .whileReturn => .val .bool :: .val .bool :: Γ
  | .doReturn => .val .bool :: .val .bool :: Γ
  | .returnFlag => .val .bool :: Γ
  | .whileReturnThen => .val .bool :: .val .bool :: Γ

def RetShape.program {C : Contract} {srcΓ : Source.RCtx} {Γ : Ctx} {m : ContextMap srcΓ Γ}
    {E : Source.Env} : (k : RetShape) → Pair m → k.Extra E srcΓ C Γ → RetFresh →
      Prog C Γ (k.out Γ)
  | .whileReturn, p, _, n => whileReturnProg n (boolSlot m p.i p.hi) (boolSlot m p.a p.ha)
  | .doReturn, p, x, n => doReturnProg n (boolSlot m p.i p.hi) (boolSlot m p.a p.ha) x.2
  | .returnFlag, p, _, n => returnFlagProg n (boolSlot m p.i p.hi) (boolSlot m p.a p.ha)
  | .whileReturnThen, p, _, n => whileReturnThenProg n (boolSlot m p.i p.hi) (boolSlot m p.a p.ha)

/-- The target return witness: the `ret` flag, or the `if` capture. -/
def RetShape.witness (Γ : Ctx) : (k : RetShape) → Idx (k.out Γ) (.val .bool)
  | .whileReturn => .here
  | .doReturn => .here
  | .returnFlag => .here
  | .whileReturnThen => .here

/-- Caller locals past the shape's hidden locals. -/
def RetShape.embedding (Γ : Ctx) : (k : RetShape) → Thin Γ (k.out Γ)
  | .whileReturn => .drop (.drop .refl)
  | .doReturn => .drop (.drop .refl)
  | .returnFlag => .drop .refl
  | .whileReturnThen => .drop (.drop .refl)

/-- Association of a function-level output with a family member. -/
def RetAccepts {E : Source.Env} {C : Contract} {srcΓ : Source.RCtx} {Γ : Ctx}
    {m : ContextMap srcΓ Γ} (k : RetShape) (p : Pair m) (x : k.Extra E srcΓ C Γ)
    (names : RetFresh) (output : Blk C Γ) : Prop :=
  output = ⟨_, k.program p x names⟩

/-- Function-level endpoint: as `Endpoint`, but the Source outcome is `.ret ls`
or `.normal ls`, and which one is read back from the target witness. -/
def RetEndpoint {E : Source.Env} {srcΓ : Source.RCtx} {M : Bool} {k : Source.SCtx}
    {C : Contract} {Γ Δ : Ctx}
    (statement : Source.RStmt E [] M k srcΓ srcΓ) (offset : Nat)
    (m : ContextMap srcΓ Γ) (program : Prog C Γ Δ) (embedding : Thin Γ Δ)
    (witness : Idx Δ (.val .bool)) : Prop :=
  ∀ (G : Source.Glob E) (F : Source.Fr) (fuel nps : Nat) (ph : Option (Source.Ph E))
    (source : Source.EMState E srcΓ) (target : State C Γ)
    (R : (H : HTy) → (τ : Source.STy) → (u : LTy) →
      Source.Val E.layout τ → u.TDenote C H → Prop),
    m.Related (R target.H) source.1 target.env →
    (∀ (H : HTy) (v : Source.Val E.layout .bool) (b : Bool),
      R H .bool (.val .bool) v b → v = .bool b) →
    (∀ H : HTy, R H .bool (.val .bool) (.bool false) false) →
    ∃ (ls : Source.Locals E.layout srcΓ) (returned : Bool) (out : Out C target.H Δ),
      (Source.execS G F (fuel + offset) nps ph statement source.1).run (.nil, source.2) =
        (.ok (if returned then Source.Out.ret ls else Source.Out.normal ls), (.nil, source.2)) ∧
      program.run target = .ok out ∧
      TEnv.get witness out.st.env = returned ∧
      (m.wk embedding).Related (R out.st.H) ls out.st.env ∧
      out.st.glob = target.glob

/-- **Return lowering is correct on its accepted family**, at the function
level of H497: every family member (the outputs `RetAccepts` admits) reaches
`RetEndpoint`, with the shape's fixed return witness and embedding. A family statement, like
`NormalFamilyCorrect`; the producer link is per sample (`Loops.Correct`). -/
def ReturnFamilyCorrect : Prop :=
  ∀ (k : RetShape) {E : Source.Env} {srcΓ : Source.RCtx} {M l u : Bool} {C : Contract} {Γ : Ctx}
    (m : ContextMap srcΓ Γ) (p : Pair m) (x : k.Extra E srcΓ C Γ) (names : RetFresh),
    RetEndpoint (k.source (M := M) (l := l) (u := u) p x) k.offset m (k.program p x names)
      (k.embedding Γ) (k.witness Γ)

end Solidity.Correctness.Lowering.Loops
