import Solidity.Calculus.ProvesDerive
import Solidity.Calculus.Surface
import Solidity.Calculus.Closers

/-!
# Rigid loop conditions and a failing diamond prefix

The branch condition is read back through local updates while unrelated
memory writes remain execution obligations of the live branch.
-/
namespace Solidity.Examples.Tactics.Rigid
local instance : InContract := ⟨StandardExample⟩
open scoped Solidity.Scoped

/-- Branch pruning retains the writes and the loop's successful execution. -/
theorem memoryLoop : ⊢ dl!{
    ⟨ uint[] memory xs = new uint[](2); uint i = 0;
      while (i < 8) { xs[0] = i; i++; }; ⟩ i == 8 } := by
  sol_prove

private def doubleUpdate : Upd StandardExample [.val .uint] [.val .uint] :=
  .snoc .nil (.local .here (.val (.app2 (.binop .add rfl) (.pvV .here) (.pvV .here))))

private def doubled : Nat → Hyps StandardExample [] [.val .uint]
  | 0 => .upd .nil .diamond (.decl .nil (.user "x") (.val (.lit ⟨0, rfl⟩)))
  | n + 1 => .upd (doubled n) .diamond doubleUpdate

private def zero : Fml StandardExample [.val .uint] := .eq (.pvV .here) (.lit ⟨0, rfl⟩)

-- Forty substitutions would duplicate the condition over a trillion times.
#guard (doubled 40).groundS zero
#guard ((doubled 40).rigid zero).isNone
#guard !Seq.refuteLanded (doubled 40) zero

-- The fast path deliberately ignores a contradictory context's premises.
#guard Seq.refuteS (C := StandardExample) (.pre .nil .ff) .tt
#guard !Seq.refuteLanded (C := StandardExample) (.pre .nil .ff) .tt

private def stopped : Fml StandardExample [] := dl!{
  ⟨ uint z = 0; uint x = 1 / z; if (false) { revert(); }; ⟩ true }

-- Refuting the dead branch must not hide a prefix that cannot land.
#guard match Seq.residueWithin 128 .all .nil stopped with
  | some leaves => !leaves.isEmpty
  | none => false

theorem stopped_invalid : ¬Fml.Valid stopped := by
  intro h
  have hf : holds (State.init StandardExample) stopped := h (State.init StandardExample)
  change THalt.revert = THalt.exhausted ∧ _ at hf
  cases hf.1

end Solidity.Examples.Tactics.Rigid
