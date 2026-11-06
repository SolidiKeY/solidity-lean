import Solidity.Source.Progress.RecoveryBuiltin

/-! Progress for the builtins whose arguments are string literals: hashing
(`keccak256`, `sha256`, `ripemd160`) and the `require`/`revert` messages. A
literal is allocated fresh and read back, so any starting state works. -/

namespace Solidity.Source.Progress
open EM
variable {E : Env} {Γ : RCtx}

theorem literal_value (bs : Roadmap.Bytes) (v : RVal E.layout (.stringLit bs)) :
    v = .strLit bs := by
  cases v with
  | strLit => rfl
  | val v => cases v <;> contradiction

/-- Fresh literal allocation followed by the actual heap read. This works on
any starting state: the allocated object supplies its own witness. -/
theorem literalHashInput_run (F : Fr) (n : Nat) (bs : Roadmap.Bytes)
    (l : Locals E.layout Γ) (s : St E) :
    ((do bytesOfRV F n (← convRV F n (.bytes .memory) (.strLit bs)) : EM E Γ _).run (l,s)) =
      (.ok bs, (l, {s with heap := (s.heap.alloc ⟨.bytes .memory, .bytes bs⟩).1})) := by
  have rs (x : EMState E Γ) : (st : EM E Γ _).run x = (.ok x.2, x) := rfl
  have rt (t : St E) (x : EMState E Γ) :
      (setSt t : EM E Γ _).run x = (.ok (), (x.1,t)) := rfl
  have rp {α : Type} (a : α) (x : EMState E Γ) :
      (pure a : EM E Γ _).run x = (.ok a, x) := rfl
  simp only [convRV, reduceCtorEq, ↓reduceDIte, pure_bind,
    allocRef, alloc, bytesOfRV, heapBytes, heapObj, Hoare.run_bind,
    rs, rt, rp, STy.loc?, ↓reduceDIte, Heap.alloc_get]


theorem literalHashInput_ns (F : Fr) (n : Nat) (bs : Roadmap.Bytes)
    (v : RVal E.layout (.stringLit bs)) :
    NS (Γ := Γ) (do bytesOfRV F n (← convRV F n (.bytes .memory) v)) := by
  rw [literal_value bs v]
  intro ⟨l,s⟩ w h
  rw [literalHashInput_run] at h
  cases h

/-- Hash builtins on source string/hex-string literals. Precompile failure
still returns the evaluator's empty digest; no concrete hash axiom is added. -/
theorem evalBuiltin_hashLiteral_ns (G : Glob E) (F : Fr) (n : Nat) (bs : Roadmap.Bytes)
    (b : Builtin) (hb : b = .keccak256 ∨ b = .sha256 ∨ b = .ripemd160)
    (args : RArgs E Γ [.stringLit bs]) (k : Nat) (hk : 0 < k ∧ k ≤ 32)
    (ha : NS (evalArgs G F n args)) :
    NS (evalBuiltin G F (n + 1) b args (.fixedBytes k hk)) := by
  rcases hb with rfl | rfl | rfl <;> simp only [evalBuiltin] <;>
    refine NS.bind ha fun vs => ?_
  all_goals
    cases vs with
    | cons v vs =>
      cases vs
      exact NS.bind (literalHashInput_ns F n bs v) fun _ => NS.pure' _

theorem evalBuiltin_requireLiteral_ns (G : Glob E) (F : Fr) (n : Nat) (bs : Roadmap.Bytes)
    (args : RArgs E Γ [.bool, .stringLit bs]) (ha : NS (evalArgs G F n args)) :
    NS (evalBuiltin G F (n + 1) .require args (.tuple [])) := by
  simp only [evalBuiltin]
  refine NS.bind ha fun vs => ?_
  cases vs with
  | cons c vs =>
    cases vs with
    | cons m vs =>
      cases vs
      rw [literal_value bs m]
      cases c with
      | val c =>
        obtain ⟨b, rfl⟩ := Val.eq_bool c
        cases b
        · change NS (halt (.revert (errorData bs))); exact NS.halt' fun _ h => by cases h
        · exact NS.pure' _

theorem evalBuiltin_revertLiteral_ns (G : Glob E) (F : Fr) (n : Nat) (bs : Roadmap.Bytes)
    (args : RArgs E Γ [.stringLit bs]) (ha : NS (evalArgs G F n args)) :
    NS (evalBuiltin G F (n + 1) .revert args (.tuple [])) := by
  simp only [evalBuiltin]
  refine NS.bind ha fun vs => ?_
  cases vs with
  | cons m vs =>
    cases vs
    rw [literal_value bs m]
    change NS (halt (.revert (errorData bs)))
    exact NS.halt' fun _ h => by cases h

#print axioms literalHashInput_run
#print axioms evalBuiltin_hashLiteral_ns
#print axioms evalBuiltin_requireLiteral_ns
#print axioms evalBuiltin_revertLiteral_ns
end Solidity.Source.Progress
