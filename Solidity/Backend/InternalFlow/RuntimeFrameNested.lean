import Solidity.Backend.InternalFlow.RuntimeFrameMutation

/-! Nested direct-call scratch certificates over the existing intrinsic syntax.
The expansion count is computed from that finite syntax, never supplied as an
admission/search cutoff. Every returned certificate retains the existing
compiler's execution/representation/allocation proof and derived scratch law.
This is not unbounded recursive execution or a new evaluator. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.Nested
open Evm Evm.Memory
variable {C : Contract}

private abbrev Expander (C : Contract) (b : Nat) :=
  {Γ Δ : Ctx} → (F : Frag Γ) → (s : Stmt C Γ Δ) → Option (Composition.Statement b F s)

mutual
private def statementUsing (b : Nat) (expand : Expander C b) {Γ Δ : Ctx} (F : Frag Γ) :
    (s : Stmt C Γ Δ) → Option (Composition.Statement b F s)
  | .block body => do
    let out ← programUsing b expand F body
    pure (Composition.block out)
  | .ite condition thn els => do
    let cond ← Memory.compileVal b F condition
    let left ← programUsing b expand F thn
    let right ← programUsing b expand F els
    pure (Composition.branch condition cond left right)
  | s => match Mutation.compileStatement b F s with
    | some out => some out
    | none => expand F s
private def programUsing (b : Nat) (expand : Expander C b) {Γ Δ : Ctx} (F : Frag Γ) :
    (P : Prog C Γ Δ) → Option (Composition.Program b F P)
  | .nil => some (Composition.nil b F)
  | .cons s rest => do
    let head ← statementUsing b expand F s
    let tail ← programUsing b expand head.checked.frag rest
    pure (Composition.cons head tail)
end

private def callUsing (b : Nat)
    (previous : {Γ Δ : Ctx} → (F : Frag Γ) → (P : Prog C Γ Δ) → Option (Composition.Program b F P))
    {Γ ps rs Δ Γf : Ctx} (F : Frag Γ) (name : Name)
    (args : Args C Γ ps) (ret : CallRet Γ rs Δ) (body : Prog C (rs ++ ps) Γf) :
    Option (Composition.Statement b F (.call name args ret body)) :=
  CallRet.casesOn (motive := fun rs _ ret => (body : Prog C (rs ++ ps) Γf) →
      Option (Composition.Statement b F (.call name args ret body))) ret
    (fun body => do
      let selected ← previous F (Calls.expandNone args body)
      pure (Composition.equivalent selected (Calls.expandNone_run name args body)))
    (fun p result destination body => do
      let selected ← previous F (Calls.expandVal args p result destination body)
      pure (Composition.equivalent selected (Calls.expandVal_run name args p result destination body)))
    (fun _ _ => none)
    (fun R result hd hm body => do
      let selected ← previous F (Calls.expandMem args R result hd hm body)
      if bound : (.mem R :: (ps ++ Γ)).length ≤ selected.checked.need then
        pure (Composition.memoryReturn name args R result hd hm body selected bound)
      else none)
    (fun _ _ _ => none) body

private def expandCall (b : Nat)
    (previous : {Γ Δ : Ctx} → (F : Frag Γ) → (P : Prog C Γ Δ) → Option (Composition.Program b F P))
    {Γ Δ : Ctx} (F : Frag Γ) : (s : Stmt C Γ Δ) → Option (Composition.Statement b F s)
  | .call name args ret body => callUsing b previous F name args ret body
  | _ => none

private def atHeight (b : Nat) : Nat → {Γ Δ : Ctx} → (F : Frag Γ) →
    (P : Prog C Γ Δ) → Option (Composition.Program b F P)
  | 0,_,_,F,P => Mutation.compileProgram b F P
  | n+1,_,_,F,P => programUsing b (expandCall b (atHeight b n)) F P

mutual
/-- Number of nested ordinary-call bodies in THIS finite intrinsic syntax. -/
def statementHeight {Γ Δ : Ctx} : Stmt C Γ Δ → Nat
  | .call _ _ _ body => height body + 1
  | .block body => height body
  | .ite _ thn els => max (height thn) (height els)
  | _ => 0

def height {Γ Δ : Ctx} : Prog C Γ Δ → Nat
  | .nil => 0
  | .cons s rest => max (statementHeight s) (height rest)
end

/-- No public call-depth input. Unsupported leaves/signatures retain none. -/
def compile (b : Nat) {Γ Δ : Ctx} (F : Frag Γ) (P : Prog C Γ Δ) :
    Option (Composition.Program b F P) := atHeight b (height P) F P

theorem compile_without_calls (b : Nat) {Γ Δ : Ctx} (F : Frag Γ) (P : Prog C Γ Δ)
    (noCalls : height P = 0) : compile b F P = Mutation.compileProgram b F P := by
  simp only [compile,noCalls,atHeight]

theorem height_call {Γ ps rs Δ Γf : Ctx} (name : Name) (args : Args C Γ ps)
    (ret : CallRet Γ rs Δ) (body : Prog C (rs ++ ps) Γf) :
    height (.cons (.call name args ret body) .nil) = height body + 1 := by
  change max (height body + 1) 0 = height body + 1
  exact Nat.max_eq_left (Nat.zero_le _)

def reflagProgram {b : Nat} {Γ Δ : Ctx} {F G : Frag Γ} (equal : F = G)
    {P : Prog C Γ Δ} (selected : Composition.Program b G P) : Composition.Program b F P :=
  equal.symm ▸ selected

theorem reflagProgram_code {b : Nat} {Γ Δ : Ctx} {F G : Frag Γ} (equal : F = G)
    {P : Prog C Γ Δ} (selected : Composition.Program b G P) :
    (reflagProgram equal selected).checked.code = selected.checked.code := by
  cases equal
  rfl

/-- Retain the SAME checked code/fragment/cost and actual derived footprint
across the existing exact finite callRec normalization. -/
def normalizeProgram {b : Nat} {Γ Δ : Ctx} {F : Frag Γ} (source : Prog C Γ Δ)
    (selected : Composition.Program b F (RuntimeFrame.program source)) :
    Composition.Program b F source where
  checked := {
    frag := selected.checked.frag
    code := selected.checked.code
    need := selected.checked.need
    cost := selected.checked.cost
    allocates := selected.checked.allocates
    zeroCost := selected.checked.zeroCost
    sound := by
      intro L frame σ base m repr room capacity
      have result := selected.checked.sound repr room capacity
      rw [RuntimeFrame.program_outcome source σ] at result
      exact result }
  safe := selected.safe

theorem normalized_fields {b : Nat} {Γ Δ : Ctx} {F : Frag Γ} (source : Prog C Γ Δ)
    (selected : Composition.Program b F (RuntimeFrame.program source)) :
    ((normalizeProgram source selected).checked.code,
      (normalizeProgram source selected).checked.frag,
      (normalizeProgram source selected).checked.need,
      (normalizeProgram source selected).checked.cost) =
    (selected.checked.code,selected.checked.frag,selected.checked.need,selected.checked.cost) := rfl

/-- Only supplied finite thunks are normalized, including their genuine
exhaustion/refusals. This does NOT compile an unbounded recursive dispatcher; a recursive unrolling
(ending in `Prog.recBase`) is refused. -/
def compileNormalized (b : Nat) {Γ Δ : Ctx} (F : Frag Γ) (source : Prog C Γ Δ) :
    Option (Composition.Program b F source) :=
  (compile b F (RuntimeFrame.program source)).map (normalizeProgram source)

end Solidity.Backend.InternalFlow.RuntimeFrame.Nested
