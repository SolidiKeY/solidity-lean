import Solidity.Source.Progress.ArithmeticBuiltins

/-! Progress for `ecrecover` on scalar and string-literal arguments. The
result follows the evaluator's precompile call; see `ScalarBuiltinControls`
for its failure case. -/

namespace Solidity.Source.Progress
open EM
variable {E : Env} {Γ : RCtx}

def WordSource (s : STy) : Prop := ScalarSource s ∨ ∃ bs, s = .stringLit bs

theorem keyable_value {t : STy} (ht : t.keyable = true) : t.isValue = true := by
  cases t <;> first | rfl | cases ht

/-- The exact conversion/word extraction used by ecrecover. -/
def builtinW (F : Fr) (n : Nat) {s : STy} (t : STy) (x : RVal E.layout s) : EM E Γ Roadmap.Bytes := do
  match (← getV (← convRV F n t x)).word with
  | some w => pure (wordBytes w)
  | none => halt (.stuck "ecrecover argument")

theorem builtinW_ns (F : Fr) (n : Nat) {s : STy} (t : STy)
    (hs : WordSource s) (ht : t.keyable = true)
    (hc : s.implicit E.isBase t = true) (x : RVal E.layout s) :
    NS (Γ := Γ) (builtinW F n t x) := by
  have conv : NS (convRV (Γ := Γ) F n t x) := by
    rcases hs with hs | ⟨bs, rfl⟩
    · exact convRV_ns F n (.inl hc) hs x
    · cases t <;> first
        | (cases ht <;> done)
        | (change false = true at hc; cases hc)
        | (simp only [convRV, reduceCtorEq, ↓reduceDIte, pure_bind]; exact NS.pure' _)
  refine NS.bind conv fun y => NS.bind (getV_ns (keyable_value ht) y) fun v => ?_
  have hw := Val.word_isSome ht v
  unfold builtinW at *
  split
  · exact NS.pure' _
  · rename_i h
    rw [h] at hw
    cases hw

theorem evalBuiltin_ecrecover_ns (G : Glob E) (F : Fr) (n : Nat)
    {h v r s : STy} (args : RArgs E Γ [h,v,r,s])
    (hh : WordSource h) (hv : WordSource v) (hr : WordSource r) (hs : WordSource s)
    (ch : h.implicit E.isBase .bytes32 = true)
    (cv : v.implicit E.isBase (.int IntTy.u8) = true)
    (cr : r.implicit E.isBase .bytes32 = true)
    (cs : s.implicit E.isBase .bytes32 = true)
    (ha : NS (evalArgs G F n args)) :
    NS (evalBuiltin G F (n + 1) .ecrecover args (.address false)) := by
  simp only [evalBuiltin]
  refine NS.bind ha fun vs => ?_
  cases vs with
  | cons h vs =>
    cases vs with
    | cons v vs =>
      cases vs with
      | cons r vs =>
        cases vs with
        | cons s vs =>
          cases vs
          exact NS.bind (builtinW_ns F n .bytes32 hh rfl ch h) fun _ =>
            NS.bind (builtinW_ns F n (.int IntTy.u8) hv rfl cv v) fun _ =>
            NS.bind (builtinW_ns F n .bytes32 hr rfl cr r) fun _ =>
            NS.bind (builtinW_ns F n .bytes32 hs rfl cs s) fun _ => NS.pure' _

#print axioms builtinW_ns
#print axioms evalBuiltin_ecrecover_ns
end Solidity.Source.Progress
