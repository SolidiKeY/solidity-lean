import Solidity.Yul.Views.CanonicalMemory

/-! Word soundness for the existing callback-based array decoder. -/
namespace Solidity.Yul.Views

/-- A successful array decode inherits its concrete element decoder's exact
word reconstruction, without a second array decoder or additional size bound. -/
theorem decodeArrayWith_word {D : Source.Layout} {τ : Source.STy}
    (decode : Roadmap.Word → Option (Source.Val D τ))
    (sound : ∀ w v, decode w = some v → v.word = some w)
    (n : Nat) (m : ByteView) (base : Nat) (values : Fin n → Source.Val D τ)
    (decoded : decodeArrayWith decode n m base = some values) :
    ∀ i, (values i).word = some (mload m (base + i.val * 32)) := by
  induction n generalizing base with
  | zero => intro i; exact Fin.elim0 i
  | succ n ih =>
    change (do let head ← decode (mload m base)
               let tail ← decodeArrayWith decode n m (base + 32)
               pure (Fin.cases head tail)) = some values at decoded
    cases dh : decode (mload m base) with
    | none => rw [dh] at decoded; cases decoded
    | some head =>
      cases dt : decodeArrayWith decode n m (base + 32) with
      | none => rw [dh, dt] at decoded; cases decoded
      | some tail =>
        rw [dh, dt] at decoded
        cases decoded
        intro i
        refine Fin.cases ?_ (fun j => ?_) i
        · simpa only [Fin.cases_zero, Fin.val_zero, Nat.zero_mul, Nat.add_zero]
            using sound _ head dh
        · have eq : base + j.succ.val * 32 = base + 32 + j.val * 32 := by
            simp only [Fin.val_succ]; omega
          simpa only [Fin.cases_succ, eq] using ih (base + 32) tail dt j

end Solidity.Yul.Views
