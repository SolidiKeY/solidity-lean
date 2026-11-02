import Solidity.Lowering.P9.FunctionCatalog
import Solidity.Source.Preservation.Fragment

/-! Whole-program call-fragment progress for actually elaborated and checked
complete function catalogues. `CallsOK` and recursive preservation are derived,
not user premises. Existing fragment, operation and frame conditions remain.
No world/ABI entrypoint, SourceSpec, termination or compiler claim follows.
-/
namespace Solidity.Source.Progress
open Solidity.Lowering.P9
open Preservation
variable {res : Resolution} {G : Glob res.env} {c : String}

theorem checked_fragments (ha : (Source.elaborate res).isSome = true)
    (hg : G.prog = Source.progOf res.env) (hc : WholeProgram.checkFunctions res G c = true)
    (n : Nat) :
    Source.FragAt (fun d => d ∈ WholeProgram.functions res) G c n ∧
      FragMemAt (fun d => d ∈ WholeProgram.functions res) G c n :=
  progress_and_preservation (WholeProgram.functions_from_elaborate res ha G hg c hc) n

theorem checked_expr (ha : (Source.elaborate res).isSome = true)
    (hg : G.prog = Source.progOf res.env) (hc : WholeProgram.checkFunctions res G c = true)
    (F : Fr) (hF : F.contract = c) (n : Nat) {Γ : RCtx} {t : STy} (e : RExpr res.env Γ t)
    (hf : e.ValFragC (fun d => d ∈ WholeProgram.functions res)) (ho : e.OpsOK) (H : HeapTy) :
    NS (evalE G F n e) ∧
      Hoare (MemOK res.env H) (evalE G F n e)
        (fun v y => MemOK res.env H y ∧ RValOK res.env y.2.heap.ty v)
        (fun _ y => MemOK res.env H y) := by
  have hcalls := WholeProgram.functions_from_elaborate res ha G hg c hc
  exact ⟨Source.evalE_callFrag_ns hcalls F hF n e hf ho,
    evalE_fragment_mem hcalls F hF n e hf ho H⟩

theorem checked_call (ha : (Source.elaborate res).isSome = true)
    (hg : G.prog = Source.progOf res.env) (hc : WholeProgram.checkFunctions res G c = true)
    (F : Fr) (hF : F.contract = c) (n : Nat) (d : Decl) {ps rs : List STy}
    (hs : d.fnSig res.env = some (ps, rs)) (hd : d ∈ WholeProgram.functions res)
    (vs : Vals res.env.layout ps) (H : HeapTy) :
    NS (callInternal G F n d vs rs) ∧
      Hoare (fun y => MemOK res.env H y ∧ RValsOK res.env y.2.heap.ty vs.toR)
        (callInternal G F n d vs rs)
        (fun v y => MemOK res.env H y ∧ RValOK res.env y.2.heap.ty v)
        (fun _ y => MemOK res.env H y) := by
  have hcalls := WholeProgram.functions_from_elaborate res ha G hg c hc
  exact ⟨(Source.fragAt hcalls n).call F hF d hs hd vs,
    (fragMemAt hcalls n).call F hF d hs hd vs H⟩

theorem checked_items (ha : (Source.elaborate res).isSome = true)
    (hg : G.prog = Source.progOf res.env) (hc : WholeProgram.checkFunctions res G c = true)
    (F : Fr) (hF : F.contract = c) (n nps : Nat) (ph : Option (Ph res.env))
    {R : List STy} {M : Bool} {k : SCtx} {Γ Δ : RCtx} (b : RItems res.env R M k Γ Δ)
    (l : Locals res.env.layout Γ) (hf : b.ValFragC (fun d => d ∈ WholeProgram.functions res))
    (ho : b.OpsOK) (hframe : BodyFrame nps R Γ) (H : HeapTy) :
    NS (execItems G F n nps ph b l) ∧
      Hoare (fun y => MemOK res.env H y ∧ LocalsOK res.env y.2.heap.ty l)
        (execItems G F n nps ph b l)
        (fun o y => MemOK res.env H y ∧ OutRefsOK (E := res.env) y.2.heap.ty o)
        (fun _ y => MemOK res.env H y) := by
  have hcalls := WholeProgram.functions_from_elaborate res ha G hg c hc
  exact ⟨((Source.fragAt hcalls n).stmt.execItems F hF nps ph b l hf ho hframe).ns,
    (fragMemAt hcalls n).stmt.execItems F hF nps ph b l hf ho H⟩

#print axioms checked_fragments
#print axioms checked_expr
#print axioms checked_call
#print axioms checked_items
end Solidity.Source.Progress
