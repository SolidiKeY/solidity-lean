import Solidity.Source.Progress.ReadyExpressions
import Solidity.Source.Preservation.ReferenceArguments

/-! Exact-type ready arguments combine non-stuck extraction with the existing
reference-preserving argument evaluator. Primitive values and memory references
are plain; constants needing conversion and other reference locations are not
silently added to this certificate. -/
namespace Solidity.Source.Progress
open EM
variable {E : Env}

def PlainResultType (τ : STy) : Prop := τ.isValue = true ∨ τ.loc? = some .memory

theorem getV_plain_ns {Γ : RCtx} {τ : STy} (plain : PlainResultType τ) (v : RVal E.layout τ) :
    NS (getV (Γ := Γ) v) := by
  rcases plain with value | memory
  · exact getV_ns value v
  · cases v with
    | val x => exact NS.lift' (NotStuckR.pure _)
    | const _ => cases memory
    | strLit _ => cases memory
    | hex _ _ => cases memory
    | tuple _ => cases memory

inductive ReadyArgs (A : Decl → Prop) {Γ : RCtx} : {ts : List STy} → RConvArgs E Γ ts → Prop
  | nil : ReadyArgs A .nil
  | cons {τ ts} {e : RExpr E Γ τ} {es : RConvArgs E Γ ts}
      (same : τ.implicit E.isBase τ = true) (plain : PlainResultType τ) :
      ReadyExpr A e → ReadyArgs A es → ReadyArgs A (.cons e same es)

theorem ReadyArgs.exact {A : Decl → Prop} {Γ : RCtx} {ts : List STy}
    {es : RConvArgs E Γ ts} (ready : ReadyArgs A es) : Preservation.ExactArgs A es := by
  induction ready with
  | nil => exact .nil
  | cons same plain head tail ih => exact .cons same head.allocating ih

theorem eval_ready_args_ns {A : Decl → Prop} {G : Glob E} {c : String}
    (calls : CallsOK A G c) (F : Fr) (contract : F.contract = c) :
    ∀ n {Γ : RCtx} {ts : List STy} (es : RConvArgs E Γ ts), ReadyArgs A es → NS (evalConvArgs G F n es)
  | 0, _, _, _, _ => NS.halt' (fun _ h => by cases h)
  | n+1, _, _, es, ready => by
    cases ready with
    | nil => exact NS.pure' _
    | cons same plain head tail =>
      rw [evalConvArgs]
      refine NS.bind (eval_ready_expr_ns calls F contract n _ head) (fun v => ?_)
      simp only [convRV,↓reduceDIte,pure_bind]
      refine NS.bind (getV_plain_ns plain v) (fun x => ?_)
      exact NS.bind (eval_ready_args_ns calls F contract n _ tail) (fun _ => NS.pure' _)

theorem ready_args_progress_and_preservation {A : Decl → Prop} {G : Glob E} {c : String}
    (calls : CallsOK A G c) (F : Fr) (contract : F.contract = c) (n : Nat)
    {Γ : RCtx} {ts : List STy} (es : RConvArgs E Γ ts) (ready : ReadyArgs A es) (H : HeapTy) :
    NS (evalConvArgs G F n es) ∧
    Hoare (MemOK E H) (evalConvArgs G F n es)
      (fun vs y => MemOK E H y ∧ RValsOK E y.2.heap.ty vs.toR) (fun _ y => MemOK E H y) :=
  ⟨eval_ready_args_ns calls F contract n es ready,
    Preservation.eval_exact_args_mem calls F contract n es ready.exact H⟩

theorem ready_args_from_elaborate (res : Resolution) (elaborated : (Source.elaborate res).isSome = true)
    (G : Glob res.env) (program : G.prog = Source.progOf res.env) (c : String) (values : List Decl)
    (checked : Solidity.Lowering.P9.WholeProgram.check res G c values = true)
    (F : Fr) (contract : F.contract = c) (n : Nat) {Γ : RCtx} {ts : List STy}
    (es : RConvArgs res.env Γ ts) (ready : ReadyArgs (fun d => d ∈ values) es) (H : HeapTy) :
    NS (evalConvArgs G F n es) ∧
    Hoare (MemOK res.env H) (evalConvArgs G F n es)
      (fun vs y => MemOK res.env H y ∧ RValsOK res.env y.2.heap.ty vs.toR) (fun _ y => MemOK res.env H y) :=
  ready_args_progress_and_preservation
    (Solidity.Lowering.P9.WholeProgram.from_elaborate res elaborated G program c values checked)
    F contract n es ready H

#print axioms ready_args_from_elaborate
#print axioms eval_ready_args_ns
#print axioms ready_args_progress_and_preservation
end Solidity.Source.Progress
