import Solidity.Source.Progress.ReadyReturns

/-! Complete function coverage combining the existing P9 value-call graph and
ready single-return bodies. The memory entries store syntax/readiness and actual
selected-body equality, not semantic progress. Coverage is checked explicitly;
all conclusions refer to actual internal calls in the elaborated program. -/
namespace Solidity.Source.Progress
open EM Solidity.Lowering.P9

def ReadyReturnCatalogue (res : Resolution) (G : Glob res.env) (c : String)
    (values memory : List Decl) : Prop :=
  ∀ d ∈ memory, d ∈ WholeProgram.functions res ∧
    ∃ (ps : List STy) (τ : STy) (e : RExpr res.env (returnContext ps τ) τ)
      (same : τ.implicit res.env.isBase res.env.mapFree τ = true),
      d.fnSig res.env = some (ps,[τ]) ∧ PlainResultType τ ∧
      ReadyExpr (fun d => d ∈ values) e ∧ ZeroReady res.env τ ∧
      G.prog.body (G.dispatchFn c d) = some (singleReturningBody ps τ e same)

def readyCoverage (res : Resolution) (values memory : List Decl) : Bool :=
  (WholeProgram.functions res).all (fun d => decide (d ∈ values ∨ d ∈ memory))

def ReadyProgramCalls (res : Resolution) (G : Glob res.env) (c : String) : Prop :=
  ∀ F, F.contract = c → ∀ d {ps rs : List STy},
    d.fnSig res.env = some (ps,rs) → d ∈ WholeProgram.functions res →
    ∀ (vs : Vals res.env.layout ps) H n,
    NS (callInternal G F n d vs rs) ∧
    Hoare (fun y => MemOK res.env H y ∧ RValsOK res.env y.2.heap.ty vs.toR)
      (callInternal G F n d vs rs)
      (fun v y => MemOK res.env H y ∧ RValOK res.env y.2.heap.ty v) (fun _ y => MemOK res.env H y)

theorem ready_program_calls (res : Resolution) (elaborated : (Source.elaborate res).isSome = true)
    (G : Glob res.env) (program : G.prog = Source.progOf res.env) (c : String) (values memory : List Decl)
    (checked : WholeProgram.check res G c values = true)
    (catalogue : ReadyReturnCatalogue res G c values memory)
    (complete : readyCoverage res values memory = true) : ReadyProgramCalls res G c := by
  have calls := WholeProgram.from_elaborate res elaborated G program c values checked
  intro F contract d ps rs signature declared vs H n
  have covered : d ∈ values ∨ d ∈ memory :=
    of_decide_eq_true ((List.all_eq_true.mp complete) d declared)
  rcases covered with value | ready
  · exact ⟨callInternal_callFrag_ns calls F contract n d signature value vs,
      (Preservation.fragMemAt calls n).call F contract d signature value vs H⟩
  · obtain ⟨member,inputs,τ,e,same,sig,plain,expression,defaults,body⟩ := catalogue d ready
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Option.some.inj (sig.symm.trans signature))
    exact single_return_progress_and_memory calls F contract d inputs τ e same plain expression defaults
      (by rw [contract]; exact body) vs H n

theorem ready_program_call_context (res : Resolution) (elaborated : (Source.elaborate res).isSome = true)
    (G : Glob res.env) (program : G.prog = Source.progOf res.env) (c : String) (values memory : List Decl)
    (checked : WholeProgram.check res G c values = true)
    (catalogue : ReadyReturnCatalogue res G c values memory)
    (complete : readyCoverage res values memory = true) (F : Fr) (contract : F.contract = c) (n : Nat) :
    CallNS (fun d => d ∈ WholeProgram.functions res) G F n := by
  intro d ps rs signature declared vs
  exact (ready_program_calls res elaborated G program c values memory checked catalogue complete
    F contract d signature declared vs (Heap.empty : Heap res.env.layout).ty n).1

theorem ready_program_expr_context (res : Resolution) (elaborated : (Source.elaborate res).isSome = true)
    (G : Glob res.env) (program : G.prog = Source.progOf res.env) (c : String) (values memory : List Decl)
    (checked : WholeProgram.check res G c values = true)
    (catalogue : ReadyReturnCatalogue res G c values memory)
    (complete : readyCoverage res values memory = true) (F : Fr) (contract : F.contract = c) :
    ∀ n, ExprNSAt (fun d => d ∈ WholeProgram.functions res) G F n
  | 0 => exprNSAt_zero _ _ _
  | n+1 => exprNSAt_step
      (ready_program_expr_context res elaborated G program c values memory checked catalogue complete F contract n)
      (ready_program_call_context res elaborated G program c values memory checked catalogue complete F contract n)

theorem ready_program_expr_ns (res : Resolution) (elaborated : (Source.elaborate res).isSome = true)
    (G : Glob res.env) (program : G.prog = Source.progOf res.env) (c : String) (values memory : List Decl)
    (checked : WholeProgram.check res G c values = true)
    (catalogue : ReadyReturnCatalogue res G c values memory)
    (complete : readyCoverage res values memory = true) (F : Fr) (contract : F.contract = c)
    (n : Nat) {Γ : RCtx} {τ : STy} (e : RExpr res.env Γ τ)
    (fragment : e.ValFragC (fun d => d ∈ WholeProgram.functions res)) (operations : e.OpsOK) : NS (evalE G F n e) :=
  (ready_program_expr_context res elaborated G program c values memory checked catalogue complete F contract n).val
    e fragment operations

#print axioms ready_program_calls
#print axioms ready_program_call_context
#print axioms ready_program_expr_ns
end Solidity.Source.Progress
