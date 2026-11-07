import Solidity.Source.Preservation.ReferenceArguments
import Solidity.Source.Preservation.EncodingVariants

/-! Syntactic ABI arguments with allocating expression children and raw string
literals. The evaluator keeps its exact argument order and all original halts;
no argument-evaluation preservation premise is assumed. -/
namespace Solidity.Source.Preservation
open EM

inductive EncodingArgs {E : Env} (A : Decl → Prop) {Γ : RCtx} :
    {ts : List STy} → RArgs E Γ ts → Prop
  | nil : EncodingArgs A .nil
  | cons {τ ts} {e : RExpr E Γ τ} {es : RArgs E Γ ts} :
      AllocatingExpr A e → EncodingArgs A es → EncodingArgs A (.cons e es)
  | string {ts} (bs : List UInt8) {es : RArgs E Γ ts} :
      EncodingArgs A es → EncodingArgs A (.cons (.str bs) es)

theorem eval_encoding_args_mem {E : Env} {A : Decl → Prop} {G : Glob E} {c : String}
    (calls : CallsOK A G c) (F : Fr) (hc : F.contract = c) :
    ∀ n {Γ : RCtx} {ts : List STy} (args : RArgs E Γ ts), EncodingArgs A args →
      MemPres (evalArgs G F n args)
  | 0, _, _, _, _ => MemPres.halt' _
  | n+1, Γ, _, args, admitted => by
    cases admitted with
    | nil => exact MemPres.pure' _
    | cons head tail =>
      rw [evalArgs]
      have hm : MemPres (evalE G F n _) := fun H =>
        Hoare.conseq (eval_allocating_mem calls F hc n _ head H)
          (fun _ h => h) (fun _ _ h => h.1) (fun _ _ h => h)
      exact MemPres.bind hm (fun _ => MemPres.bind
        (eval_encoding_args_mem calls F hc n _ tail) (fun _ => MemPres.pure' _))
    | string bs tail =>
      rw [evalArgs]
      have hm : MemPres (evalE G F n (Γ := Γ) (.str bs)) := by
        cases n with
        | zero => exact MemPres.halt' _
        | succ n => exact MemPres.pure' _
      exact MemPres.bind hm (fun _ => MemPres.bind
        (eval_encoding_args_mem calls F hc n _ tail) (fun _ => MemPres.pure' _))

#print axioms eval_encoding_args_mem
end Solidity.Source.Preservation
