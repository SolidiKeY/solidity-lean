import Solidity.MultiStep
import Solidity.RuleSoundness

/-!
# Compositional soundness for block rewriting

Per-rule theorems in `RuleSoundness.lean` compare one source statement with
its residual block modulo the calculus' scratch aliases.  This module lifts
such a local theorem through an untouched block suffix and then through a
reflexive-transitive rewrite derivation.

This bridge deliberately requires a semantic theorem for every step being
composed.  In particular, it does not identify a terminal rule's empty
residual with a no-op: terminal rules denote genuine state updates and need a
state-carrying theorem rather than ordinary residual-block equivalence.
-/

namespace Solidity

open Semantics
open RuleSoundness

/-- Executing concatenated blocks is monadic sequencing. -/
theorem Semantics.execBlock_append (s : State) (pre suffix : List Stmt) :
    execBlock s (pre ++ suffix) =
      (execBlock s pre >>= fun t => execBlock t suffix) := by
  induction pre generalizing s with
  | nil => rfl
  | cons stmt rest ih =>
      rw [List.cons_append, execBlock, execBlock]
      cases h : execStmt s stmt with
      | error e => rfl
      | ok t => exact ih t

namespace RuleSoundness.EnvAgreeExcept

theorem trans {ns : List Name} {s t u : State}
    (hst : EnvAgreeExcept ns s t) (htu : EnvAgreeExcept ns t u) :
    EnvAgreeExcept ns s u := by
  constructor
  · exact hst.storage.trans htu.storage
  · exact hst.heap.trans htu.heap
  · exact hst.nextId.trans htu.nextId
  · exact hst.net.trans htu.net
  · intro n hn
    exact (hst.env n hn).trans (htu.env n hn)
  · exact hst.selfBalance.trans htu.selfBalance

end RuleSoundness.EnvAgreeExcept

namespace RuleSoundness.ResultsAgree

theorem trans {ns : List Name} {x y z : Res State}
    (hxy : ResultsAgree ns x y) (hyz : ResultsAgree ns y z) :
    ResultsAgree ns x z := by
  cases x <;> cases y <;> cases z <;>
    simp only [ResultsAgree] at hxy hyz ⊢
  · exact hxy.trans hyz
  · exact EnvAgreeExcept.trans hxy hyz

end RuleSoundness.ResultsAgree

/-- Interpreter agreement for whole blocks, modulo a fixed set of scratch
environment names. -/
def BlockExecAgree (ns : List Name)
    (before after : SolidityBlock) : Prop :=
  ∀ s, ResultsAgree ns
    (execBlock s before.stmts) (execBlock s after.stmts)

/-- Lift the semantic theorem for a rule at the head of a block through an
untouched suffix.  Freshness is exactly what makes the suffix insensitive to
scratch bindings introduced by the residual block. -/
theorem BlockStep.head_execAgree {ns : List Name}
    {sm : SolidityModality} {lhs : Stmt} {cond : Prop}
    {rhs rest : Block} (_hrule : RuleStep sm lhs cond rhs)
    (hsound : ∀ s, ResultsAgree ns
      (execStmt s lhs) (execBlock s rhs))
    (hfresh : ∀ n ∈ ns, blockUsesVar rest n = false) :
    BlockExecAgree ns ⟨sm, lhs :: rest⟩ ⟨sm, rhs ++ rest⟩ := by
  intro s
  rw [execBlock, Semantics.execBlock_append]
  apply ResultsAgree.bind (hsound s)
  intro s₁ s₂ hagree
  exact execBlock_agree hagree rest hfresh

namespace BlockExecAgree

theorem refl (ns : List Name) (b : SolidityBlock) :
    BlockExecAgree ns b b :=
  fun _ => ResultsAgree.refl _ _

theorem trans {ns : List Name} {a b c : SolidityBlock}
    (hab : BlockExecAgree ns a b) (hbc : BlockExecAgree ns b c) :
    BlockExecAgree ns a c :=
  fun s => ResultsAgree.trans (hab s) (hbc s)

end BlockExecAgree

/-! The context congruence the rewrite layer cannot have.  `⇝` fires at the
head statement, so `MultiStep.lean`'s framing lemmas carry a suffix and
*consume* a prefix.  Here the relation quantifies over the start state, so both
sides are available -- and the side conditions come out the other way round:
a prefix needs none, because both sides bind the very same prefix result,
whereas a suffix needs the freshness that `head_execAgree` already asks for. -/

namespace BlockExecAgree

/-- Prefix congruence: unconditional. -/
theorem append_left {ns : List Name} {sm₁ sm₂ : SolidityModality}
    {pre a b : Block} (h : BlockExecAgree ns ⟨sm₁, a⟩ ⟨sm₂, b⟩) :
    BlockExecAgree ns ⟨sm₁, pre ++ a⟩ ⟨sm₂, pre ++ b⟩ := by
  intro s
  show ResultsAgree ns (execBlock s (pre ++ a)) (execBlock s (pre ++ b))
  rw [Semantics.execBlock_append, Semantics.execBlock_append]
  cases execBlock s pre with
  | error e => exact ResultsAgree.refl _ _
  | ok t => exact h t

/-- Suffix congruence: the suffix must not read a scratch alias the two sides
are allowed to disagree on, which is `head_execAgree`'s hypothesis. -/
theorem append_right {ns : List Name} {sm₁ sm₂ : SolidityModality}
    {a b suffix : Block} (h : BlockExecAgree ns ⟨sm₁, a⟩ ⟨sm₂, b⟩)
    (hfresh : ∀ n ∈ ns, blockUsesVar suffix n = false) :
    BlockExecAgree ns ⟨sm₁, a ++ suffix⟩ ⟨sm₂, b ++ suffix⟩ := by
  intro s
  show ResultsAgree ns (execBlock s (a ++ suffix)) (execBlock s (b ++ suffix))
  rw [Semantics.execBlock_append, Semantics.execBlock_append]
  exact ResultsAgree.bind (h s)
    (fun _ _ hagree => execBlock_agree hagree suffix hfresh)

end BlockExecAgree

/-- Any reflexive-transitive derivation made exclusively of semantically
sound steps is semantically sound. -/
theorem BlockReflMultiStep.execAgree {ns : List Name}
    (hsound : ∀ {a b}, BlockStep a b → BlockExecAgree ns a b)
    {before after : SolidityBlock}
    (hsteps : BlockReflMultiStep before after) :
    BlockExecAgree ns before after := by
  induction hsteps with
  | refl => exact BlockExecAgree.refl _ _
  | step hstep _ ih =>
      exact BlockExecAgree.trans (hsound hstep) ih

end Solidity
