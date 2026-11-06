import Solidity.Yul.Views.RetainedAliasSub

/-! Caller-side memory safety of the actual substituted ownership sequence.
Storage operations and alias assignments preserve the original heap on every
branch. Restored caller locals therefore retain their own original RefOK;
callee-local validity or global alias completeness is not assumed or inferred. -/
namespace Solidity.Yul.Views.RetainedAliasSubSafety
open RetainedAliasOwnership RetainedAliasSequence

theorem heap_one {E τ b child active Γ σ G F n s dst src prior layout fixed history written word r}
    (p : @Plan E τ b child active Γ σ G F n s dst src prior layout fixed history written word r) : (RetainedAliasOwnership.execute p).1.2.2.heap=s.2.heap := by
  first | (simp only;done) | skip
  cases mode : F.static
  · rw [RetainedAliasOwnership.nonstatic p mode]
  · rw [RetainedAliasOwnership.static p mode]

theorem heap_sequence {E τ b child active Γ σ G F n s dst src prior layout fixed history written word r}
    (p : @Plan E τ b child active Γ σ G F n s dst src prior layout fixed history written word r)
    {τ2 b2 child2 active2 σ2 G2 F2 n2 dst2 src2 layout2 fixed2 history2 written2 word2}
    (q : @NextPlan E τ b child active Γ σ G F n s dst src prior layout fixed history written word r p
      τ2 b2 child2 active2 σ2 G2 F2 n2 dst2 src2 layout2 fixed2 history2 written2 word2) : (executeThen p q).1.2.2.heap=s.2.heap := by
  first | (simp only;done) | skip
  cases mode : F.static
  · rw [RetainedAliasSequence.next p q mode,heap_one q,heap_one p]
  · rw [RetainedAliasSequence.first_static p q mode]
    exact heap_one p

theorem heap {E τ b child active Γ σ G F n s dst src prior layout fixed history written word r}
    (p : @Plan E τ b child active Γ σ G F n s dst src prior layout fixed history written word r)
    {τ2 b2 child2 active2 σ2 G2 F2 n2 dst2 src2 layout2 fixed2 history2 written2 word2}
    (q : @NextPlan E τ b child active Γ σ G F n s dst src prior layout fixed history written word r p
      τ2 b2 child2 active2 σ2 G2 F2 n2 dst2 src2 layout2 fixed2 history2 written2 word2) {Δ} (caller : Source.Locals E.layout Δ) :
    (RetainedAliasSub.execute p q caller).1.2.2.heap=s.2.heap := by
  rw [RetainedAliasSub.actual p q caller]
  exact heap_sequence p q

theorem MemOK {E τ b child active Γ σ G F n s dst src prior layout fixed history written word r}
    (p : @Plan E τ b child active Γ σ G F n s dst src prior layout fixed history written word r)
    {τ2 b2 child2 active2 σ2 G2 F2 n2 dst2 src2 layout2 fixed2 history2 written2 word2}
    (q : @NextPlan E τ b child active Γ σ G F n s dst src prior layout fixed history written word r p
      τ2 b2 child2 active2 σ2 G2 F2 n2 dst2 src2 layout2 fixed2 history2 written2 word2) {Δ} (caller : Source.Locals E.layout Δ)
    (H : Source.HeapTy) (ok : Source.MemOK E H (caller,s.2)) :
    Source.MemOK E H (RetainedAliasSub.execute p q caller).1.2 := by
  first | (simp only;done) | skip
  have sameHeap := heap p q caller
  have sameLocals := RetainedAliasSub.caller p q caller
  refine ⟨⟨⟨?_,?_⟩,?_⟩,?_,?_⟩
  · rw [sameHeap]; exact ok.1.1.heap
  · rw [sameHeap]; exact ok.1.1.le
  · rw [sameHeap,sameLocals]; exact ok.1.2
  · rw [sameHeap]; exact ok.2.1
  · rw [sameHeap]; exact ok.2.2

end Solidity.Yul.Views.RetainedAliasSubSafety
