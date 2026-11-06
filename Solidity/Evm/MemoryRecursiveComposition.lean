import Solidity.Evm.MemoryRecursiveNesting

/-! Actual compiler constructor laws, without a second AST or assumed
soundness field. Body contexts/fragments remain their actual dependent indices. -/
namespace Solidity.Evm.Memory.Recursive.Composition
variable {C : Contract}

def block {b Γ Δ F P} (out : CompiledProg (C:=C) b (Γ:=Γ) (Δ:=Δ) F P) :
    CompiledStmt b F (.block P) := ⟨out.frag.restrict Γ,out.code,.block out.cert⟩

theorem block_found {b Γ Δ F P} (out : CompiledProg (C:=C) b (Γ:=Γ) (Δ:=Δ) F P)
    (found : compileProg b P F=some out) : compileStmt b (.block P) F=some (block out) := by
  change (do
    let inner ← compileProg b P F
    pure (⟨inner.frag.restrict Γ,inner.code,.block inner.cert⟩ : CompiledStmt b F (.block P)))=_
  rw [found]
  rfl

def branch {b Γ Δ Ξ F P Q} {c : Val C Γ .bool} (condition : Memory.CompiledVal b F c)
    (yes : CompiledProg b (Γ:=Γ) (Δ:=Δ) F P) (no : CompiledProg b (Γ:=Γ) (Δ:=Ξ) F Q) :
    CompiledStmt b F (.ite c P Q) :=
  ⟨(yes.frag.restrict Γ).meet (no.frag.restrict Γ),conditionalCode condition.code yes.code no.code,
    .ite condition.cert yes.cert no.cert⟩

theorem branch_found {b Γ Δ Ξ F P Q} {c : Val C Γ .bool} (condition : Memory.CompiledVal b F c)
    (yes : CompiledProg b (Γ:=Γ) (Δ:=Δ) F P) (no : CompiledProg b (Γ:=Γ) (Δ:=Ξ) F Q)
    (hc : Memory.compileVal b F c=some condition) (hy : compileProg b P F=some yes)
    (hn : compileProg b Q F=some no) : compileStmt b (.ite c P Q) F=some (branch condition yes no) := by
  change (do
    let test ← Memory.compileVal b F c
    let left ← compileProg b P F
    let right ← compileProg b Q F
    pure (⟨(left.frag.restrict Γ).meet (right.frag.restrict Γ),conditionalCode test.code left.code right.code,
      .ite test.cert left.cert right.cert⟩ : CompiledStmt b F (.ite c P Q)))=_
  rw [hc,hy,hn]
  rfl

def cons {b Γ Δ Ξ F s P} (head : CompiledStmt (C:=C) b (Γ:=Γ) (Δ:=Δ) F s)
    (tail : CompiledProg b (Γ:=Δ) (Δ:=Ξ) head.frag P) : CompiledProg b F (.cons s P) :=
  ⟨tail.frag,head.code++tail.code,.cons head.cert tail.cert⟩

theorem cons_found {b Γ Δ Ξ F s P} (head : CompiledStmt (C:=C) b (Γ:=Γ) (Δ:=Δ) F s)
    (tail : CompiledProg b (Γ:=Δ) (Δ:=Ξ) head.frag P)
    (hs : compileStmt b s F=some head) (hp : compileProg b P head.frag=some tail) :
    compileProg b (.cons s P) F=some (cons head tail) := by
  change (do
    let first ← compileStmt b s F
    let last ← compileProg b P first.frag
    pure (⟨last.frag,first.code++last.code,.cons first.cert last.cert⟩ : CompiledProg b F (.cons s P)))=_
  rw [hs]
  simp only [bind,Option.bind]
  rw [hp]
  rfl

theorem block_need {b Γ Δ F P} (out : CompiledProg (C:=C) b (Γ:=Γ) (Δ:=Δ) F P) :
    (block out).cert.need=max Γ.length out.cert.need := rfl

theorem branch_need {b Γ Δ Ξ F P Q} {c : Val C Γ .bool} (condition : Memory.CompiledVal b F c)
    (yes : CompiledProg b (Γ:=Γ) (Δ:=Δ) F P) (no : CompiledProg b (Γ:=Γ) (Δ:=Ξ) F Q) :
    (branch condition yes no).cert.need=max Γ.length (max yes.cert.need no.cert.need) := rfl

theorem cons_need {b Γ Δ Ξ F s P} (head : CompiledStmt (C:=C) b (Γ:=Γ) (Δ:=Δ) F s)
    (tail : CompiledProg b (Γ:=Δ) (Δ:=Ξ) head.frag P) :
    (cons head tail).cert.need=max head.cert.need tail.cert.need := rfl

theorem block_allocates {b Γ Δ F P} (out : CompiledProg (C:=C) b (Γ:=Γ) (Δ:=Δ) F P) :
    (block out).cert.allocates=out.cert.allocates := rfl

theorem branch_allocates {b Γ Δ Ξ F P Q} {c : Val C Γ .bool} (condition : Memory.CompiledVal b F c)
    (yes : CompiledProg b (Γ:=Γ) (Δ:=Δ) F P) (no : CompiledProg b (Γ:=Γ) (Δ:=Ξ) F Q) :
    (branch condition yes no).cert.allocates=(yes.cert.allocates || no.cert.allocates) := rfl

end Solidity.Evm.Memory.Recursive.Composition
