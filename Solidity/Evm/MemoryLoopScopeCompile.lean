import Solidity.Evm.MemoryLoopScopeRoom
namespace Solidity.Evm.Memory.LoopScopes
variable {C : Contract}

structure CompiledStmt (b : Nat) {Γ Δ : Ctx} (F : Frag Γ) (s : Stmt C Γ Δ) where
  frag : Frag Δ
  code : List Instr
  cert : StmtCert b F frag s code
structure CompiledProg (b : Nat) {Γ Δ : Ctx} (F : Frag Γ) (P : Prog C Γ Δ) where
  frag : Frag Δ
  code : List Instr
  cert : ProgCert b F frag P code

private def compileBase (b : Nat) {Γ Δ : Ctx} (F : Frag Γ) (s : Stmt C Γ Δ) :
    Option (CompiledStmt b F s) := do
  let result ← Loops.compileStmt b F s
  pure ⟨result.frag, result.code, .base result.cert⟩

mutual
private def compileStmtM (b : Nat) {Γ Δ : Ctx} (s : Stmt C Γ Δ) (F : Frag Γ) :
    Option (CompiledStmt b F s) :=
  match s with
  | .block body => do
    let result ← compileProgM b body F
    pure ⟨result.frag.restrict Γ, result.code, .block result.cert⟩
  | .ite c thn els => do
    let condition ← Memory.compileVal b F c
    let left ← compileProgM b thn F
    let right ← compileProgM b els F
    pure ⟨(left.frag.restrict Γ).meet (right.frag.restrict Γ), _,
      .ite condition.cert left.cert right.cert⟩
  | s => compileBase b F s
termination_by structural s
private def compileProgM (b : Nat) {Γ Δ : Ctx} (P : Prog C Γ Δ) (F : Frag Γ) :
    Option (CompiledProg b F P) :=
  match P with
  | .nil => some ⟨F, [], .nil F⟩
  | .cons s P => do
    let head ← compileStmtM b s F
    let tail ← compileProgM b P head.frag
    pure ⟨tail.frag, head.code ++ tail.code, .cons head.cert tail.cert⟩
termination_by structural P
end

/-- Enclosing scopes recurse; loop bodies retain the old finite compiler. -/
@[implemented_by compileStmtM]
def compileStmt (b : Nat) {Γ Δ : Ctx} (s : Stmt C Γ Δ) :
    (F : Frag Γ) → Option (CompiledStmt b F s) := by
  induction s using Solidity.Stmt.rec
    (motive_2 := fun Γ Δ P => (F : Frag Γ) → Option (CompiledProg b F P))
  case block body ih =>
    first | intro F | rename_i F
    exact do
      let result ← ih F
      pure ⟨result.frag.restrict _, result.code, .block result.cert⟩
  case ite c thn els iht ihe =>
    first | intro F | rename_i F
    exact do
      let condition ← Memory.compileVal b F c
      let left ← iht F
      let right ← ihe F
      pure ⟨(left.frag.restrict _).meet (right.frag.restrict _), _,
        .ite condition.cert left.cert right.cert⟩
  case nil F =>
    exact some ⟨F, [], .nil F⟩
  case cons s P ihs ihp F =>
    exact do
      let head ← ihs F
      let tail ← ihp head.frag
      pure ⟨tail.frag, head.code ++ tail.code, .cons head.cert tail.cert⟩
  all_goals
    first | intro F | rename_i F
    exact compileBase b F _

@[implemented_by compileProgM]
def compileProg (b : Nat) {Γ Δ : Ctx} (P : Prog C Γ Δ) :
    (F : Frag Γ) → Option (CompiledProg b F P) := by
  induction P using Solidity.Prog.rec
    (motive_1 := fun Γ Δ P => (F : Frag Γ) → Option (CompiledStmt b F P))
  case block body ih F =>
    exact do
      let result ← ih F
      pure ⟨result.frag.restrict _, result.code, .block result.cert⟩
  case ite c thn els iht ihe F =>
    exact do
      let condition ← Memory.compileVal b F c
      let left ← iht F
      let right ← ihe F
      pure ⟨(left.frag.restrict _).meet (right.frag.restrict _), _,
        .ite condition.cert left.cert right.cert⟩
  case nil =>
    first | intro F | rename_i F
    exact some ⟨F, [], .nil F⟩
  case cons s P ihs ihp =>
    first | intro F | rename_i F
    exact do
      let head ← ihs F
      let tail ← ihp head.frag
      pure ⟨tail.frag, head.code ++ tail.code, .cons head.cert tail.cert⟩
  all_goals
    first | intro F | rename_i F
    exact compileBase b F _

private theorem compileStmt_eq (b : Nat) {Γ Δ : Ctx} (s : Stmt C Γ Δ) :
    ∀ F, compileStmt b s F = compileStmtM b s F := by
  induction s using Solidity.Stmt.rec
    (motive_2 := fun Γ Δ P => ∀ F, compileProg b P F = compileProgM b P F)
  case block body ih =>
    intro F
    change Option.bind (compileProg b body F) _ = _
    rw [ih F]
    rfl
  case ite c thn els iht ihe =>
    intro F
    change Option.bind (Memory.compileVal b F c) _ = _
    congr 1
    funext cond
    change Option.bind (compileProg b thn F) _ = _
    rw [iht F]
    congr 1
    funext left
    change Option.bind (compileProg b els F) _ = _
    rw [ihe F]
    rfl
  case nil F => rfl
  case cons s P ihs ihp F =>
    change Option.bind (compileStmt b s F) _ = _
    rw [ihs F]
    congr 1
    funext head
    change Option.bind (compileProg b P head.frag) _ = _
    rw [ihp head.frag]
    rfl
  all_goals intro F; rfl

private theorem compileProg_eq (b : Nat) {Γ Δ : Ctx} (P : Prog C Γ Δ) :
    ∀ F, compileProg b P F = compileProgM b P F := by
  induction P using Solidity.Prog.rec
    (motive_1 := fun Γ Δ s => ∀ F, compileStmt b s F = compileStmtM b s F)
  case block body ih F =>
    change Option.bind (compileProg b body F) _ = _
    rw [ih F]
    rfl
  case ite c thn els iht ihe F =>
    change Option.bind (Memory.compileVal b F c) _ = _
    congr 1
    funext cond
    change Option.bind (compileProg b thn F) _ = _
    rw [iht F]
    congr 1
    funext left
    change Option.bind (compileProg b els F) _ = _
    rw [ihe F]
    rfl
  case nil =>
    intro F
    rfl
  case cons s P ihs ihp =>
    intro F
    change Option.bind (compileStmt b s F) _ = _
    rw [ihs F]
    congr 1
    funext head
    change Option.bind (compileProg b P head.frag) _ = _
    rw [ihp head.frag]
    rfl
  all_goals rename_i F; rfl


theorem compileProg_nil (b : Nat) {Γ : Ctx} (F : Frag Γ) :
    compileProg (C := C) b .nil F = some ⟨F, [], .nil F⟩ := rfl

theorem compileProg_cons (b : Nat) {Γ Δ Ξ : Ctx} (F : Frag Γ)
    (s : Stmt C Γ Δ) (P : Prog C Δ Ξ) :
    compileProg b (.cons s P) F = (do
      let head ← compileStmt b s F
      let tail ← compileProg b P head.frag
      pure ⟨tail.frag, head.code ++ tail.code, .cons head.cert tail.cert⟩) := by
  rw [compileProg_eq]
  change Option.bind (compileStmtM b s F) _ = _
  rw [← compileStmt_eq]
  congr 1
  funext head
  change Option.bind (compileProgM b P head.frag) _ = _
  rw [← compileProg_eq]
  rfl

theorem compileStmt_block (b : Nat) {Γ Δ : Ctx} (F : Frag Γ) (P : Prog C Γ Δ) :
    compileStmt b (.block P) F = (do
      let inner ← compileProg b P F
      pure ⟨inner.frag.restrict Γ, inner.code, .block inner.cert⟩) := by
  rw [compileStmt_eq]
  change Option.bind (compileProgM b P F) _ = _
  rw [← compileProg_eq]
  rfl

theorem compileStmt_ite (b : Nat) {Γ Δ Ξ : Ctx} (F : Frag Γ)
    (c : Val C Γ .bool) (thn : Prog C Γ Δ) (els : Prog C Γ Ξ) :
    compileStmt b (.ite c thn els) F = (do
      let condition ← Memory.compileVal b F c
      let left ← compileProg b thn F
      let right ← compileProg b els F
      pure ⟨(left.frag.restrict Γ).meet (right.frag.restrict Γ), _,
        .ite condition.cert left.cert right.cert⟩) := by
  rw [compileStmt_eq]
  change Option.bind (Memory.compileVal b F c) _ = _
  congr 1
  funext condition
  change Option.bind (compileProgM b thn F) _ = _
  rw [← compileProg_eq]
  congr 1
  funext left
  change Option.bind (compileProgM b els F) _ = _
  rw [← compileProg_eq]
  rfl


theorem compileStmt_loop (b : Nat) {Γ Δ : Ctx} (F : Frag Γ)
    (a : LoopAnn C Γ) (c : Val C Γ .bool) (body : Prog C Γ Δ) :
    compileStmt b (.loop a c body) F = (do
      let result ← Loops.compileStmt b F (.loop a c body)
      pure ⟨result.frag, result.code, .base result.cert⟩) := by
  rw [compileStmt_eq]
  rfl

theorem compileStmt_declLocal (b : Nat) {Γ : Ctx} (F : Frag Γ)
    (p : PrimTy) (x : Var) (e : Option (Val C Γ p)) :
    compileStmt b (.declLocal p x e) F = (do
      let result ← Memory.compileStmt b F (.declLocal p x e)
      pure ⟨result.frag, result.code, .base (.finite result.cert)⟩) := by
  rw [compileStmt_eq]
  change Option.bind (Option.bind (Memory.compileStmt b F (.declLocal p x e))
    (fun r => some (Loops.CompiledStmt.mk r.frag r.code (.finite r.cert)))) _ = _
  rw [Option.bind_assoc]
  rfl

theorem compile_loop_clause (b : Nat) {Γ Δ : Ctx} (F : Frag Γ)
    (a : LoopAnn C Γ) (c : Val C Γ .bool) (body : Prog C Γ Δ) :
    Loops.compileStmt b F (.loop a c body) = (do
      let condition ← Memory.compileVal b F c
      let compiled ← Memory.compileProg b F body
      if stable : compiled.frag.restrict Γ = F then
        pure ⟨F, [.loop condition.code compiled.code],
          .loop a c body condition.code compiled.code compiled.frag condition.cert compiled.cert stable⟩
      else none) := rfl

end Solidity.Evm.Memory.LoopScopes
