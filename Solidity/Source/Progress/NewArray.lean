import Solidity.Source.Preservation.NewArrayFragment
import Solidity.Lowering.P9.FunctionCatalog

/-! Non-stuck dynamic allocation for explicit ready memory types. Array
readiness retains the evaluator's element-default requirement; allocation panic
and timeout remain possible. Length progress and memory preservation are derived
from the existing checked call fragment, without changing its syntax. -/
namespace Solidity.Source.Progress
open EM
variable {E : Env} {Γ : RCtx}

inductive NewReady (E : Env) : STy → Prop
  | bytes : NewReady E (.bytes .memory)
  | string : NewReady E (.string .memory)
  | array (σ : STy) (word : σ.oneWord = true)
      (defaults : (Val.default E.layout σ).isSome = true) : NewReady E (.array .memory σ none)

theorem NewReady.newable {τ : STy} (ready : NewReady E τ) : τ.newable = true := by
  cases ready with
  | bytes => rfl
  | string => rfl
  | array σ word defaults => exact word

theorem NewReady.location {τ : STy} (ready : NewReady E τ) : τ.loc? = some .memory := by
  cases ready <;> rfl

theorem NewReady.array_default {σ : STy} (ready : NewReady E (.array .memory σ none)) :
    (Val.default E.layout σ).isSome = true := by
  cases ready
  assumption

theorem newData_ns {τ : STy} (ready : NewReady E τ) (len : Nat) :
    NotStuckR (newData (D := E.layout) τ len) := by
  cases ready with
  | bytes => exact NotStuckR.pure _
  | string => exact NotStuckR.pure _
  | array σ word defaults =>
    obtain ⟨v,actual⟩ := Option.isSome_iff_exists.mp defaults
    rw [newData,actual]
    exact NotStuckR.pure _

theorem alloc_ns {τ : STy} (data : Data E.layout τ) : NS (alloc (Γ := Γ) data) :=
  fun _ _ h => by cases h

theorem allocRef_ns {τ : STy} (memory : τ.loc? = some .memory) (data : Data E.layout τ) :
    NS (allocRef (Γ := Γ) data) := by
  unfold allocRef
  refine NS.bind (alloc_ns data) (fun a => ?_)
  rw [dif_pos memory]
  exact NS.pure' _

theorem index_amount {σ : STy} (indexable : σ.isIndex = true) : σ.isAmount = true := by
  cases σ <;> try (cases indexable)
  case int t => exact indexable
  case rational q =>
    have fits : q.FitsInt IntTy.u256 := of_decide_eq_true indexable
    simp only [STy.isAmount,fits.1,Bool.true_and,decide_eq_true_eq]
    exact fits.2.1
  case hexConst q k =>
    have fits : q.FitsInt IntTy.u256 := of_decide_eq_true indexable
    simp only [STy.isAmount,fits.1,Bool.true_and,decide_eq_true_eq]
    exact fits.2.1

theorem eval_new_ns (G : Glob E) (F : Fr) (n : Nat) {τ σ : STy}
    (ready : NewReady E τ) (len : RExpr E Γ σ) (indexable : σ.isIndex = true)
    (child : NS (evalE G F n len)) :
    NS (evalE G F (n+1) (.newArray ready.newable len indexable)) := by
  rw [evalE]
  refine NS.bind child (fun v => NS.bind (NS.lift' (amount_ok (index_amount indexable) v)) (fun k => ?_))
  split
  · exact NS.lift' (by intro w h; cases h)
  · refine NS.bind (NS.lift' (newData_ns ready k)) (fun data => ?_)
    exact NS.bind (allocRef_ns ready.location data) (fun _ => NS.pure' _)

theorem new_fragment_ns {A : Decl → Prop} {G : Glob E} {c : String}
    (calls : CallsOK A G c) (F : Fr) (contract : F.contract = c) (n : Nat)
    {τ σ : STy} (ready : NewReady E τ) (len : RExpr E Γ σ)
    (indexable : σ.isIndex = true) (fragment : len.ValFragC A) (operations : len.OpsOK) :
    NS (evalE G F (n+1) (.newArray ready.newable len indexable)) :=
  eval_new_ns G F n ready len indexable (evalE_callFrag_ns calls F contract n len fragment operations)

theorem new_fragment_all_ns {A : Decl → Prop} {G : Glob E} {c : String}
    (calls : CallsOK A G c) (F : Fr) (contract : F.contract = c)
    {τ σ : STy} (ready : NewReady E τ) (len : RExpr E Γ σ)
    (indexable : σ.isIndex = true) (fragment : len.ValFragC A) (operations : len.OpsOK) :
    ∀ n, NS (evalE G F n (.newArray ready.newable len indexable))
  | 0 => NS.halt' (fun _ h => by cases h)
  | n+1 => new_fragment_ns calls F contract n ready len indexable fragment operations

/-- Successful elaboration and the executable P9 call-graph check derive
length progress; the source allocation parent needs no assumed CallsOK. -/
theorem new_from_elaborate (res : Resolution) (elaborated : (Source.elaborate res).isSome = true)
    (G : Glob res.env) (program : G.prog = Source.progOf res.env) (c : String) (values : List Decl)
    (checked : Solidity.Lowering.P9.WholeProgram.check res G c values = true)
    (F : Fr) (contract : F.contract = c) (n : Nat) {Γ : RCtx} {τ σ : STy}
    (ready : NewReady res.env τ) (len : RExpr res.env Γ σ) (indexable : σ.isIndex = true)
    (fragment : len.ValFragC (fun d => d ∈ values)) (operations : len.OpsOK) (H : HeapTy) :
    NS (evalE G F (n+1) (.newArray ready.newable len indexable)) ∧
    Hoare (MemOK res.env H) (evalE G F (n+1) (.newArray ready.newable len indexable))
      (fun v y => MemOK res.env H y ∧ RValOK res.env y.2.heap.ty v) (fun _ y => MemOK res.env H y) := by
  have calls := Solidity.Lowering.P9.WholeProgram.from_elaborate res elaborated G program c values checked
  exact ⟨new_fragment_ns calls F contract n ready len indexable fragment operations,
    Preservation.eval_new_fragment_mem calls F contract n H ready.newable len indexable fragment operations⟩

#print axioms eval_new_ns
#print axioms new_fragment_ns
#print axioms new_fragment_all_ns
#print axioms new_from_elaborate
end Solidity.Source.Progress
