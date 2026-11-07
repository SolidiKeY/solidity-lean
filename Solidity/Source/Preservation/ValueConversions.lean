import Solidity.Source.Preservation.Combinators

/-! Preservation for the value fragment's actual implicit conversion paths.
The source conversion/fragment premises are retained; every halt preserves memory.
-/
namespace Solidity.Source.Preservation
open EM
variable {E : Env}

theorem convRV_pres {Γ : RCtx} (F : Fr) (n : Nat) {σ τ : STy} (hc : Conv E.isBase E.mapFree σ τ)
    (hσ : σ.isValue = true ∨ (∃ q, σ = .rational q) ∨ (∃ q k, σ = .hexConst q k)) (v : RVal E.layout σ) :
    MemPres (convRV (Γ := Γ) F n τ v) := by
  have hl := loc_of_frag hσ
  unfold convRV
  split
  · -- a constant
    dsimp only
    split
    · exact MemPres.pure' _
    · rename_i he
      exact MemPres.bind (MemPres.pure' _) fun _ => MemPres.bind (MemPres.lift' _)
        fun _ => MemPres.pure' _
  · -- a hexadecimal constant to `bytesN`
    dsimp only
    split
    · exact MemPres.pure' _
    · exact MemPres.bind (MemPres.pure' _) fun _ => MemPres.pure' _
  · -- a hexadecimal constant to another type
    rename_i hτ
    dsimp only
    split
    · exact MemPres.pure' _
    · rename_i he
      exact MemPres.bind (MemPres.pure' _) fun _ => MemPres.bind (MemPres.lift' _) fun _ => MemPres.pure' _
  all_goals first
    | (exfalso; rcases hσ with h | ⟨_, h⟩ | ⟨_, _, h⟩ <;> cases h)
    | (rename_i h; rw [hl] at h; cases h)
    | skip
  · -- a plain value
    rename_i x hr hh _ _ _ _ _ _ _
    dsimp only
    split
    · exact MemPres.pure' _
    · rename_i he
      have hv : σ.isValue = true := by
        rcases hσ with hσ | ⟨q, rfl⟩ | ⟨q, k, rfl⟩
        · exact hσ
        · exact (hr q _ rfl HEq.rfl).elim
        · exact (hh q k _ rfl HEq.rfl).elim
      exact MemPres.bind (MemPres.pure' _) fun _ =>
        MemPres.bind (MemPres.lift' _) fun _ => MemPres.pure' _
  · -- not a plain value: impossible for the fragment's types
    rename_i hr hh _ _ _ hval _ _ _ _
    exfalso
    rcases hσ with hσ | ⟨q, rfl⟩ | ⟨q, k, rfl⟩
    · cases v with
      | val x => exact hval x rfl
      | const _ => cases hσ
      | strLit _ => cases hσ
      | hex _ _ => cases hσ
      | tuple _ => cases hσ
    · exact hr q v rfl HEq.rfl
    · exact hh q k v rfl HEq.rfl

#print axioms convRV_pres
end Solidity.Source.Preservation
