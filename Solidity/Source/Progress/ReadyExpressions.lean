import Solidity.Source.Progress.NewArray
import Solidity.Source.Preservation.AllocatingFragment

/-! Readiness-decorated allocating expressions, over the existing intrinsic
syntax and preservation admission. Reference locals, identity conversions and
reference-result conditionals compose with ready dynamic-new parents. The old
value-call graph remains separately checked; no memory-call recursion is added. -/
namespace Solidity.Source.Progress
open EM
variable {E : Env}

inductive ReadyExpr (A : Decl → Prop) {Γ : RCtx} : {τ : STy} → RExpr E Γ τ → Prop
  | value {τ} {e : RExpr E Γ τ} : e.ValFragC A → e.OpsOK → ReadyExpr A e
  | «local» {τ} (i : Idx Γ τ) : ReadyExpr A (.local i)
  | same {τ} {e : RExpr E Γ τ} (h : Conv E.isBase τ τ) :
      ReadyExpr A e → ReadyExpr A (.conv e h)
  | branch {τ} {c : RExpr E Γ .bool} {a b : RExpr E Γ τ} :
      ReadyExpr A c → ReadyExpr A a → ReadyExpr A b → ReadyExpr A (.cond c a b)
  | newArray {τ σ : STy} (ready : NewReady E τ) {len : RExpr E Γ σ}
      (indexable : σ.isIndex = true) : ReadyExpr A len →
      ReadyExpr A (.newArray ready.newable len indexable)

theorem ReadyExpr.allocating {A : Decl → Prop} {Γ : RCtx} {τ : STy}
    {e : RExpr E Γ τ} (ready : ReadyExpr A e) : Preservation.AllocatingExpr A e := by
  induction ready with
  | value fragment operations => exact .value fragment operations
  | «local» i => exact .local i
  | same h child ih => exact .same h ih
  | branch guard left right ihg ihl ihr => exact .branch ihg ihl ihr
  | newArray ready indexable child ih => exact .newArray ready.newable indexable ih

theorem eval_ready_expr_ns {A : Decl → Prop} {G : Glob E} {c : String}
    (calls : CallsOK A G c) (F : Fr) (contract : F.contract = c) :
    ∀ n {Γ : RCtx} {τ : STy} (e : RExpr E Γ τ), ReadyExpr A e → NS (evalE G F n e)
  | 0, _, _, _, _ => NS.halt' (fun _ h => by cases h)
  | n+1, _, _, e, ready => by
    cases ready with
    | value fragment operations => exact evalE_callFrag_ns calls F contract (n+1) e fragment operations
    | «local» i =>
      rw [evalE]
      exact NS.bind NS.locals' (fun _ => NS.pure' _)
    | @same τ e h child =>
      rw [evalE]
      refine NS.bind (eval_ready_expr_ns calls F contract n e child) (fun v => ?_)
      simp only [convRV]
      exact NS.pure' _
    | @branch τ guard left right hg hl hr =>
      rw [evalE]
      refine NS.bind (eval_ready_expr_ns calls F contract n guard hg) (fun v => ?_)
      refine NS.bind (getV_ns rfl v) (fun x => ?_)
      split
      · exact eval_ready_expr_ns calls F contract n left hl
      · exact eval_ready_expr_ns calls F contract n right hr
    | newArray ready indexable child =>
      exact eval_new_ns G F n ready _ indexable (eval_ready_expr_ns calls F contract n _ child)

theorem ready_progress_and_preservation {A : Decl → Prop} {G : Glob E} {c : String}
    (calls : CallsOK A G c) (F : Fr) (contract : F.contract = c) (n : Nat)
    {Γ : RCtx} {τ : STy} (e : RExpr E Γ τ) (ready : ReadyExpr A e) (H : HeapTy) :
    NS (evalE G F n e) ∧
    Hoare (MemOK E H) (evalE G F n e)
      (fun v y => MemOK E H y ∧ RValOK E y.2.heap.ty v) (fun _ y => MemOK E H y) :=
  ⟨eval_ready_expr_ns calls F contract n e ready,
    Preservation.eval_allocating_mem calls F contract n e ready.allocating H⟩

theorem ready_from_elaborate (res : Resolution) (elaborated : (Source.elaborate res).isSome = true)
    (G : Glob res.env) (program : G.prog = Source.progOf res.env) (c : String) (values : List Decl)
    (checked : Solidity.Lowering.P9.WholeProgram.check res G c values = true)
    (F : Fr) (contract : F.contract = c) (n : Nat) {Γ : RCtx} {τ : STy}
    (e : RExpr res.env Γ τ) (ready : ReadyExpr (fun d => d ∈ values) e) (H : HeapTy) :
    NS (evalE G F n e) ∧
    Hoare (MemOK res.env H) (evalE G F n e)
      (fun v y => MemOK res.env H y ∧ RValOK res.env y.2.heap.ty v) (fun _ y => MemOK res.env H y) :=
  ready_progress_and_preservation
    (Solidity.Lowering.P9.WholeProgram.from_elaborate res elaborated G program c values checked)
    F contract n e ready H

#print axioms eval_ready_expr_ns
#print axioms ready_progress_and_preservation
#print axioms ready_from_elaborate
end Solidity.Source.Progress
