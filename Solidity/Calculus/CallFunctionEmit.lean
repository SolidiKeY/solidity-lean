import Solidity.Calculus.CallFunctionSearch

/-! # Size-checked emission of complete shared call leaves
Selection alone is not emission: the actual complete candidate must shrink
the old assignment leaf and respect the retained output cap. This module
does not yet alter the default closer or its ordinary fallback path.
-/
namespace Solidity.CallFunctionEmit
open CallFunctionPlan CallFunctionSearch
variable {C : Contract} {Γ : Ctx}

/-- Internal complete emitted-leaf cap, not a user option or semantic premise. -/
def outputCap : Nat := 512

def tableName : Var := .fresh "callTable" 0
def inputName : Var := .fresh "callInput" 0
def resultName : Var := .fresh "callResult" 0

/-- The actual original leaf being replaced, with its original post untouched. -/
def original (m : Modality) (target : Idx Γ (.val .uint))
    (out : Tm C Γ (.val .uint)) (φ : Fml C Γ) : Fml C Γ :=
  .upd m (Upd.nil.snoc (.local target (.val out))) φ

/-- A returning actual old assignment has exactly its whole caller post.
Keeping the result term abstract avoids repeating deep elaborator reduction. -/
theorem holds_original_of_eval (m : Modality) (target : Idx Γ (.val .uint))
    (out : Tm C Γ (.val .uint)) (φ : Fml C Γ) (σ : State C Γ) (v : CallFunctionTable.Key)
    (hv : out.eval σ = some v) :
    holds σ (original m target out φ) ↔ holds (σ.setLocal target v) φ := by
  have hc : holds σ (original m target out φ) ↔
      holds σ (CallResultRestore.leaf m resultName .refl target out φ) :=
    ⟨fun hh => CallResultCapture.complete resultName target out φ σ hh,
      fun hh => CallResultCapture.sound resultName target out φ σ hh⟩
  exact hc.trans (CallResultRestore.holds_leaf_of_eval m resultName .refl target out φ σ v hv)

/-- An emitted leaf carries actual checked selection and size evidence,
indexed by the precise old term, target, modality and continuation. -/
structure Emission (m : Modality) (target : Idx Γ (.val .uint))
    (out : Tm C Γ (.val .uint)) (φ : Fml C Γ) where
  plan : Plan out
  smaller : (plan.leaf m tableName inputName resultName target φ).tmSize <
    (original m target out φ).tmSize
  capped : (plan.leaf m tableName inputName resultName target φ).tmSize ≤ outputCap

/-- Produce only an actual smaller complete leaf, never a size-only placeholder. -/
def emit? (m : Modality) (target : Idx Γ (.val .uint))
    (out : Tm C Γ (.val .uint)) (φ : Fml C Γ) : Option (Emission m target out φ) := do
  let plan ← search? out
  let candidate := plan.leaf m tableName inputName resultName target φ
  if hs : candidate.tmSize < (original m target out φ).tmSize then
    if hc : candidate.tmSize ≤ outputCap then some ⟨plan, hs, hc⟩ else none
  else none

/-- The complete emitted intrinsic formula, including all fresh logical locals. -/
def Emission.formula {m : Modality} {target : Idx Γ (.val .uint)}
    {out : Tm C Γ (.val .uint)} {φ : Fml C Γ} (e : Emission m target out φ) : Fml C Γ :=
  e.plan.leaf m tableName inputName resultName target φ

/-- Actual emission preserves every old-context observation, including program
modalities, ordinary failure and both original box/diamond verdicts. -/
theorem Emission.holds {m : Modality} {target : Idx Γ (.val .uint)}
    {out : Tm C Γ (.val .uint)} {φ : Fml C Γ} (e : Emission m target out φ) (σ : State C Γ) :
    holds σ e.formula ↔ holds σ (original m target out φ) :=
  e.plan.holds m tableName inputName resultName target φ σ

/-- The emitted full syntax is strictly smaller than this actual old leaf. -/
theorem Emission.size_lt {m : Modality} {target : Idx Γ (.val .uint)}
    {out : Tm C Γ (.val .uint)} {φ : Fml C Γ} (e : Emission m target out φ) :
    e.formula.tmSize < (original m target out φ).tmSize := e.smaller

/-- The output cap applies to the complete actual emitted leaf. -/
theorem Emission.size_cap {m : Modality} {target : Idx Γ (.val .uint)}
    {out : Tm C Γ (.val .uint)} {φ : Fml C Γ} (e : Emission m target out φ) :
    e.formula.tmSize ≤ outputCap := e.capped

/-- Optional replacement is exactly equivalent on success and identical on
refusal; consumers still need to integrate ordinary fallback explicitly. -/
def replace (m : Modality) (target : Idx Γ (.val .uint))
    (out : Tm C Γ (.val .uint)) (φ : Fml C Γ) : Fml C Γ :=
  match emit? m target out φ with
  | some e => e.formula
  | none => original m target out φ

theorem holds_replace (m : Modality) (target : Idx Γ (.val .uint))
    (out : Tm C Γ (.val .uint)) (φ : Fml C Γ) (σ : State C Γ) :
    holds σ (replace m target out φ) ↔ holds σ (original m target out φ) := by
  unfold replace
  split
  · rename_i e he
    exact e.holds σ
  · rfl

/-- Replacement never enlarges the original complete assignment leaf. -/
theorem replace_size (m : Modality) (target : Idx Γ (.val .uint))
    (out : Tm C Γ (.val .uint)) (φ : Fml C Γ) :
    (replace m target out φ).tmSize ≤ (original m target out φ).tmSize := by
  unfold replace
  split
  · rename_i e he
    exact Nat.le_of_lt e.size_lt
  · exact Nat.le_refl _

end Solidity.CallFunctionEmit
