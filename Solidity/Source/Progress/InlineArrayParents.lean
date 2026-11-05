import Solidity.Source.Progress.ReadyArguments
import Solidity.Source.Preservation.MemoryBodies

/-! Progress for inline-array allocation parents with syntactically ready
exact arguments. Preservation is derived from the existing memory-body rule;
no child execution premise, evaluator change or new call graph is introduced. -/
namespace Solidity.Source.Progress
open EM
variable {E : Env}

theorem inline_array_ns {A : Decl → Prop} {G : Glob E} {c : String}
    (calls : CallsOK A G c) (F : Fr) (contract : F.contract = c) :
    ∀ n {Γ : RCtx} {σ : STy} {m : Nat} (args : RConvArgs E Γ (List.replicate m σ))
      (word : σ.oneWord = true), ReadyArgs A args → NS (evalE G F n (.inlineArray args word))
  | 0, _, _, _, _, _, _ => NS.halt' (fun _ h => by cases h)
  | n+1, _, _, _, args, word, ready => by
    rw [evalE]
    refine NS.bind (eval_ready_args_ns calls F contract n args ready) (fun values => ?_)
    exact NS.bind (allocRef_ns rfl (inlineData values)) (fun _ => NS.pure' _)

theorem inline_array_progress_and_memory {A : Decl → Prop} {G : Glob E} {c : String}
    (calls : CallsOK A G c) (F : Fr) (contract : F.contract = c) (n : Nat)
    {Γ : RCtx} {σ : STy} {m : Nat} (args : RConvArgs E Γ (List.replicate m σ))
    (word : σ.oneWord = true) (ready : ReadyArgs A args) (H : HeapTy) :
    NS (evalE G F n (.inlineArray args word)) ∧
    Hoare (MemOK E H) (evalE G F n (.inlineArray args word))
      (fun v y => MemOK E H y ∧ RValOK E y.2.heap.ty v) (fun _ y => MemOK E H y) :=
  ⟨inline_array_ns calls F contract n args word ready,
    Preservation.eval_body_expr_mem calls F contract n _ (.inlineArray word ready.exact) H⟩

theorem inline_array_statement_ns {A : Decl → Prop} {G : Glob E} {c : String}
    (calls : CallsOK A G c) (F : Fr) (contract : F.contract = c)
    {R : List STy} {M : Bool} {k : SCtx} {Γ : RCtx} {σ : STy} {m : Nat}
    (args : RConvArgs E Γ (List.replicate m σ)) (word : σ.oneWord = true)
    (ready : ReadyArgs A args) (nps : Nat) (ph : Option (Ph E)) (locals : Locals E.layout Γ) :
    ∀ n, NS (execS G F n nps ph (.expr (R:=R) (M:=M) (k:=k) (.inlineArray args word)) locals)
  | 0 => by rw [execS.eq_1]; exact NS.halt' (fun _ h => by cases h)
  | n+1 => by
    rw [execS]
    have child : NS (sub (Γ:=[]) locals (evalE G F n (.inlineArray args word))) := NSP.ns (NSP.sub' (Q:=fun _ => True) (NSP.weaken
      (NSP.of_ns (inline_array_ns calls F contract n args word ready)) (fun _ _ _ => trivial)))
    exact NS.bind child (fun _ => NS.pure' _)

theorem inline_array_statement_progress_and_memory {A : Decl → Prop} {G : Glob E} {c : String}
    (calls : CallsOK A G c) (F : Fr) (contract : F.contract = c) (n : Nat)
    {R : List STy} {M : Bool} {k : SCtx} {Γ : RCtx} {σ : STy} {m : Nat}
    (args : RConvArgs E Γ (List.replicate m σ)) (word : σ.oneWord = true)
    (ready : ReadyArgs A args) (nps : Nat) (ph : Option (Ph E)) (locals : Locals E.layout Γ) (H : HeapTy) :
    NS (execS G F n nps ph (.expr (R:=R) (M:=M) (k:=k) (.inlineArray args word)) locals) ∧
    Hoare (fun y => MemOK E H y ∧ LocalsOK E y.2.heap.ty locals)
      (execS G F n nps ph (.expr (R:=R) (M:=M) (k:=k) (.inlineArray args word)) locals)
      (fun out y => MemOK E H y ∧ Preservation.OutRefsOK (E:=E) y.2.heap.ty out)
      (fun _ y => MemOK E H y) :=
  ⟨inline_array_statement_ns calls F contract args word ready nps ph locals n,
    (Preservation.memory_body_at calls n).stmt F contract nps ph _
      (.expr (.inlineArray word ready.exact)) locals H⟩

theorem inline_array_from_elaborate (res : Resolution)
    (elaborated : (Source.elaborate res).isSome = true) (G : Glob res.env)
    (program : G.prog = Source.progOf res.env) (c : String) (values : List Decl)
    (checked : Solidity.Lowering.P9.WholeProgram.check res G c values = true)
    (F : Fr) (contract : F.contract = c) (n : Nat) {Γ : RCtx} {σ : STy} {m : Nat}
    (args : RConvArgs res.env Γ (List.replicate m σ)) (word : σ.oneWord = true)
    (ready : ReadyArgs (fun d => d ∈ values) args) (H : HeapTy) :
    NS (evalE G F n (.inlineArray args word)) ∧
    Hoare (MemOK res.env H) (evalE G F n (.inlineArray args word))
      (fun v y => MemOK res.env H y ∧ RValOK res.env y.2.heap.ty v) (fun _ y => MemOK res.env H y) :=
  inline_array_progress_and_memory
    (Solidity.Lowering.P9.WholeProgram.from_elaborate res elaborated G program c values checked)
    F contract n args word ready H

#print axioms inline_array_ns
#print axioms inline_array_progress_and_memory
#print axioms inline_array_statement_ns
#print axioms inline_array_statement_progress_and_memory
#print axioms inline_array_from_elaborate
end Solidity.Source.Progress
