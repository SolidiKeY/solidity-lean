import Solidity.Source.Progress.EmitBuiltins

/-! Progress for `addmod` and `mulmod` on scalar arguments: the arguments are
converted to `uint256` exactly as the evaluator does, and a zero modulus
panics rather than getting stuck. -/

namespace Solidity.Source.Progress
open EM
variable {E : Env} {Γ : RCtx}

def ScalarSource (s : STy) : Prop :=
  s.isValue = true ∨ (∃ q, s = .rational q) ∨ (∃ q k, s = .hexConst q k)

/-- The exact unsigned conversion used by addmod/mulmod. -/
def builtinU (F : Fr) (n : Nat) {s : STy} (v : RVal E.layout s) : EM E Γ Int := do
  match ← getV (← convRV F n (.int IntTy.u256) v) with
  | .int i _ => pure i

theorem builtinU_ns (F : Fr) (n : Nat) {s : STy}
    (hs : ScalarSource s) (hc : s.implicit E.isBase E.mapFree (.int IntTy.u256) = true)
    (v : RVal E.layout s) : NS (Γ := Γ) (builtinU F n v) := by
  refine NS.bind (convRV_ns F n (.inl hc) hs v) fun w => ?_
  refine NS.bind (getV_ns rfl w) fun x => ?_
  obtain ⟨i, hi, rfl⟩ := Val.eq_int x
  exact NS.pure' _

/-- Both argument orders and the existing division-by-zero panic are retained.
No nonzero runtime modulus assumption is added. -/
theorem evalBuiltin_mod_ns (G : Glob E) (F : Fr) (n : Nat) (b : Builtin)
    (hb : b = .addmod ∨ b = .mulmod) {x y k : STy} (args : RArgs E Γ [x,y,k])
    (hx : ScalarSource x) (hy : ScalarSource y) (hk : ScalarSource k)
    (cx : x.implicit E.isBase E.mapFree (.int IntTy.u256) = true)
    (cy : y.implicit E.isBase E.mapFree (.int IntTy.u256) = true)
    (ck : k.implicit E.isBase E.mapFree (.int IntTy.u256) = true)
    (ha : NS (evalArgs G F n args)) (hr : NS (evalArgsRev G F n args)) :
    NS (evalBuiltin G F (n + 1) b args (.int IntTy.u256)) := by
  have after (a : RVal E.layout x) (c : RVal E.layout y) (m : RVal E.layout k) :
      NS (Γ := Γ) (do
        let (a,c,m) ← match G.pipeline with
          | .legacy => do let m ← builtinU F n m; let c ← builtinU F n c; let a ← builtinU F n a; pure (a,c,m)
          | .viaIR => do let a ← builtinU F n a; let c ← builtinU F n c; let m ← builtinU F n m; pure (a,c,m)
        if m = 0 then lift (panic .divZero)
        else pure (.val (intWrap IntTy.u256 (if b = .addmod then (a+c)%m else (a*c)%m)) : RVal E.layout (.int IntTy.u256))) := by
    cases G.pipeline
    · refine NS.bind (builtinU_ns F n hk ck _) fun _ =>
        NS.bind (builtinU_ns F n hy cy _) fun _ =>
        NS.bind (builtinU_ns F n hx cx _) fun _ => ?_
      simp only [pure_bind]
      split
      · exact NS.lift' (by intro w h; cases h)
      · exact NS.pure' _
    · refine NS.bind (builtinU_ns F n hx cx _) fun _ =>
        NS.bind (builtinU_ns F n hy cy _) fun _ =>
        NS.bind (builtinU_ns F n hk ck _) fun _ => ?_
      simp only [pure_bind]
      split
      · exact NS.lift' (by intro w h; cases h)
      · exact NS.pure' _
  rcases hb with rfl | rfl <;> simp only [evalBuiltin] <;> split
  all_goals
    refine NS.bind (by assumption) fun vs => ?_
    cases vs with
    | cons a vs =>
      cases vs with
      | cons c vs =>
        cases vs with
        | cons m vs =>
          cases vs
          exact after a c m

#print axioms builtinU_ns
#print axioms evalBuiltin_mod_ns
end Solidity.Source.Progress
