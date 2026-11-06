import Solidity.Backend.Passes.ValueCertificate

/-! Ordered composition of existing pure intrinsic value certificates. No
Source tuple/call semantics, new expression AST or opcode selection is added. -/
namespace Solidity.Backend.Passes
open Solidity.Evm Solidity.Evm.Memory
variable {C : Contract} {b L frame : Nat} {Γ : Ctx} {F : Frag Γ}
  {p q : PrimTy} {x : Val C Γ p} {y : Val C Γ q}
  {σ : State C Γ} {base : Nat → Fin W} {m : Machine}

/-- The second word is on top, the first immediately below it. Every other
machine component is exactly the initial one, for every saved tail. -/
theorem value_pair_success_tail (a : CompiledVal b F x) (d : CompiledVal b F y)
    (hi : StateRepr L b frame F σ base m)
    {v : p.Denote} (hx : x.evalT σ = .ok v)
    {u : q.Denote} (hy : y.evalT σ = .ok u) (tail : List Word) :
    ∃ first second, ReprV p v first ∧ ReprV q u second ∧
      run (a.code ++ d.code) {m with stack := tail} =
        .ok (({m with stack := tail}.push first).push second) 0 := by
  obtain ⟨first, hv, ha⟩ := value_success_tail a hi hx tail
  obtain ⟨second, hu, hd⟩ := value_success_tail d hi hy (first :: tail)
  refine ⟨first, second, hv, hu, ?_⟩
  rw [run_append_ok ha]
  exact hd

/-- Exact two-sided failure split. No second source success or failure is
required if the first expression reverts. Accepted values are pure, so the
reached second expression evaluates at the same intrinsic state. -/
theorem value_pair_revert_iff (a : CompiledVal b F x) (d : CompiledVal b F y)
    (hi : StateRepr L b frame F σ base m) (tail : List Word) :
    run (a.code ++ d.code) {m with stack := tail} = .revert ↔
      x.evalT σ = .error .revert ∨ ∃ v, x.evalT σ = .ok v ∧ y.evalT σ = .error .revert := by
  rcases a.cert.correct (hi.stack tail) with ⟨v, first, hx, _, ha⟩ | ⟨hx, ha⟩
  · rw [run_append_ok ha]
    have hd := value_revert_iff d hi (first :: tail)
    constructor
    · intro ht
      exact .inr ⟨v, hx, hd.mp ht⟩
    · rintro (hf | ⟨_, _, hf⟩)
      · rw [hx] at hf
        cases hf
      · exact hd.mpr hf
  · constructor
    · intro _
      exact .inl hx
    · intro _
      exact run_append_revert ha

/-- Reached failure also exposes the actual successful first word/run and
full represented input of the second certificate; no post-failure state. -/
theorem value_pair_reached_revert (a : CompiledVal b F x) (d : CompiledVal b F y)
    (hi : StateRepr L b frame F σ base m)
    {v : p.Denote} (hx : x.evalT σ = .ok v)
    (hy : y.evalT σ = .error .revert) (tail : List Word) :
    ∃ first, ReprV p v first ∧
      run a.code {m with stack := tail} = .ok ({m with stack := tail}.push first) 0 ∧
      StateRepr L b frame F σ base ({m with stack := tail}.push first) ∧
      run d.code ({m with stack := tail}.push first) = .revert ∧
      run (a.code ++ d.code) {m with stack := tail} = .revert := by
  obtain ⟨first, hv, ha⟩ := value_success_tail a hi hx tail
  have hd := (value_revert_iff d hi (first :: tail)).mpr hy
  exact ⟨first, hv, ha, hi.stack (first :: tail), hd,
    by rw [run_append_ok ha]; exact hd⟩

end Solidity.Backend.Passes
