import Solidity.Evm.MemoryRecursiveSound
namespace Solidity.Evm.Memory.Recursive
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
  let result ← LoopScopes.compileStmt b s F
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
  | .loop a c body => do
    let condition ← Memory.compileVal b F c
    let out ← compileProgM b body F
    if stable : out.frag.restrict Γ=F then
      pure ⟨F,[.loop condition.code out.code],.loop a condition.cert out.cert stable⟩
    else none
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

/-- Enclosing scopes and loop bodies recurse through the actual source AST. -/
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
  case loop a c body ih =>
    first | intro F | rename_i F
    exact do
      let condition ← Memory.compileVal b F c
      let out ← ih F
      if stable : out.frag.restrict _=F then
        pure ⟨F,[.loop condition.code out.code],.loop a condition.cert out.cert stable⟩
      else none
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
  case loop a c body ih F =>
    exact do
      let condition ← Memory.compileVal b F c
      let out ← ih F
      if stable : out.frag.restrict _=F then
        pure ⟨F,[.loop condition.code out.code],.loop a condition.cert out.cert stable⟩
      else none
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
  case loop a c body ih =>
    first | intro F | rename_i F
    change Option.bind (Memory.compileVal b F c) _ = _
    congr 1
    funext condition
    change Option.bind (compileProg b body F) _ = _
    rw [ih F]
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
  case loop a c body ih F =>
    change Option.bind (Memory.compileVal b F c) _ = _
    congr 1
    funext condition
    change Option.bind (compileProg b body F) _ = _
    rw [ih F]
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


/-- Exact initial relation, computed frame need and real reached demand room.
There is no generic soundness or desired final result as an input. -/
def CompiledProg.Input {b Γ Δ F P} (out : CompiledProg (C:=C) b (Γ:=Γ) (Δ:=Δ) F P)
    (L frame : Nat) (σ : State C Γ) (base : Nat → Fin W) (m : Machine) : Prop :=
  StateRepr L b frame F σ base m ∧ b+out.cert.need≤frame ∧ Room out.cert frame σ base m

theorem CompiledProg.correct {b Γ Δ F P} (out : CompiledProg (C:=C) b (Γ:=Γ) (Δ:=Δ) F P)
    {L frame} {σ : State C Γ} {base : Nat → Fin W} {m : Machine}
    (input : out.Input L frame σ base m) :
    LoopScopes.Result L b frame out.frag σ base m (fun o amount=>Cost out.cert σ o amount)
      (P.run σ) (run out.code m) := out.cert.correct σ base m input.1 input.2.1 input.2.2

end Solidity.Evm.Memory.Recursive
