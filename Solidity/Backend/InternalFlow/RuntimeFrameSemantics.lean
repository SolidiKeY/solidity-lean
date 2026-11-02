import Solidity.Semantics.Run

/-! Runtime call-frame normalization over existing intrinsic syntax.
The quotation index of callRec is not an execution/admission bound. This
normalization preserves the existing body, including recBase exhaustion; it
does not supply unbounded source lowering or a new evaluator. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame
variable {C : Contract}

mutual
  def statement {Γ Δ : Ctx} : Stmt C Γ Δ → Stmt C Γ Δ
    | .call f args ret body => .call f args ret (program body)
    | .callRec f _ args ret body => .call f args ret (program (body ()))
    | .block body => .block (program body)
    | .ite c thn els => .ite c (program thn) (program els)
    | .loop a c body => .loop a c (program body)
    | other => other
  def program {Γ Δ : Ctx} : Prog C Γ Δ → Prog C Γ Δ
    | .nil => .nil
    | .cons s rest => .cons (statement s) (program rest)
end

theorem statement_run {Γ Δ : Ctx} (s : Stmt C Γ Δ) :
    (statement s).runR = s.runR := by
  induction s using Stmt.rec
    (motive_2 := fun Γ Δ P => (program P).runR = P.runR) with
  | call f args ret body ih =>
    change TRun.call args ret (program body).ext (program body).runR =
      TRun.call args ret body.ext body.runR
    rw [ih]
    congr 1 <;> exact Subsingleton.elim _ _
  | callRec f d args ret body ih =>
    change TRun.call args ret (program (body ())).ext (program (body ())).runR =
      TRun.call args ret (body ()).ext (body ()).runR
    rw [ih ()]
    congr 1 <;> exact Subsingleton.elim _ _
  | block body ih =>
    change TRun.block (program body).ext (program body).runR = TRun.block body.ext body.runR
    rw [ih]
    congr 1 <;> exact Subsingleton.elim _ _
  | ite c thn els ih₁ ih₂ =>
    change TRun.ite c (program thn).ext (program thn).runR (program els).ext (program els).runR =
      TRun.ite c thn.ext thn.runR els.ext els.runR
    rw [ih₁,ih₂]
    congr 1 <;> exact Subsingleton.elim _ _
  | loop a c body ih =>
    change TRun.loop c (program body).ext (program body).runR = TRun.loop c body.ext body.runR
    rw [ih]
    congr 1 <;> exact Subsingleton.elim _ _
  | cons s rest ih₁ ih₂ =>
    change TRun.seq (statement s).runR (program rest).runR = TRun.seq s.runR rest.runR
    rw [ih₁,ih₂]
  | _ => rfl

theorem program_run : {Γ Δ : Ctx} → (P : Prog C Γ Δ) → (program P).runR = P.runR
  | _,_,.nil => rfl
  | _,_,.cons s rest => by
    change TRun.seq (statement s).runR (program rest).runR = TRun.seq s.runR rest.runR
    rw [statement_run s,program_run rest]

/-- Every existing halt, including exhaustion and divergence, is retained. -/
theorem program_outcome {Γ Δ : Ctx} (P : Prog C Γ Δ) (σ : State C Γ) :
    (program P).run σ = P.run σ := congrFun (program_run P) σ
end Solidity.Backend.InternalFlow.RuntimeFrame
