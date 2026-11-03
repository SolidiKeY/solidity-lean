import Solidity.Yul.WordSyntax

/-! Universal interpreter/calculus composition for the REAL binder-wrapped
loop shape emitted by extraction. These strengthen the nonempty splice facts:
initializers evaluate once, fresh slots are dropped on loop completion/leave,
and a preceding leave suppresses its continuation. Actual Program/Term/Model
profiles are explicit real premises; there is no assumed completion/termination.
This is Word AST composition, not independent source-derivation semantics or
Source/state/compiler correspondence. -/
namespace Solidity.Yul.Logic
open Solidity.Yul.Closed
open Solidity (Modality)

theorem modal_for_skip {F c n} (mode : Modality) (model : Model F)
    (condition : Term F n 1) (step : Program F ⟨c.function,false⟩ n)
    (body : Program F ⟨c.function,true⟩ n) (post : Flow c → Fml n) (vars : Values n) :
    (Fml.modal mode model (Program.for_ (c := c) Program.skip condition step body) post).holds vars ↔
      (Fml.loopModal c mode model condition step body post).holds vars := by
  rw [modal_for]
  exact modal_completed mode model Program.skip
    (loopPrePost mode model condition step body post) vars ⟨vars,.normal⟩ (fuel := 1) rfl

theorem termModal_post_congr {F n r} (mode : Modality) (model : Model F)
    (term : Term F n r) (left right : Values r → Fml n)
    (same : ∀ values vars, (left values).holds vars ↔ (right values).holds vars)
    (vars : Values n) :
    (Fml.termModal mode model term left).holds vars ↔
      (Fml.termModal mode model term right).holds vars := by
  cases mode with
  | box =>
      constructor
      · intro all fuel values ran
        exact (same values vars).mp (all fuel values ran)
      · intro all fuel values ran
        exact (same values vars).mpr (all fuel values ran)
  | diamond =>
      constructor
      · rintro ⟨fuel,values,ran,after⟩
        exact ⟨fuel,values,ran,(same values vars).mp after⟩
      · rintro ⟨fuel,values,ran,after⟩
        exact ⟨fuel,values,ran,(same values vars).mpr after⟩

/-- The initializer may call recursive functions or return multiple words.
Neither its success nor loop termination is assumed. -/
theorem modal_initialized_loop {F c n r} (mode : Modality) (model : Model F)
    (initializer : Term F n r) (condition : Term F (r+n) 1)
    (step : Program F ⟨c.function,false⟩ (r+n))
    (body : Program F ⟨c.function,true⟩ (r+n))
    (post : Flow c → Fml n) (vars : Values n) :
    (Fml.modal mode model (Program.let_ initializer
      (Program.for_ (c := c) Program.skip condition step body)) post).holds vars ↔
    (Fml.termModal mode model initializer (fun values =>
      .subst (extendValues values)
        (.loopModal c mode model condition step body (dropPost r post)))).holds vars := by
  rw [modal_let]
  apply termModal_post_congr
  intro values original
  change (Fml.modal mode model (Program.for_ (c := c) Program.skip condition step body)
    (dropPost r post)).holds (extendValues values original) ↔ _
  exact modal_for_skip mode model condition step body (dropPost r post) _

theorem modal_zeroed_loop {F c n} (mode : Modality) (model : Model F) (count : Nat)
    (condition : Term F (count+n) 1)
    (step : Program F ⟨c.function,false⟩ (count+n))
    (body : Program F ⟨c.function,true⟩ (count+n))
    (post : Flow c → Fml n) (vars : Values n) :
    (Fml.modal mode model (Program.zero count
      (Program.for_ (c := c) Program.skip condition step body)) post).holds vars ↔
    (Fml.subst (extendValues (fun _ : Fin count => word 0))
      (.loopModal c mode model condition step body (dropPost count post))).holds vars := by
  rw [modal_zero]
  exact modal_for_skip mode model condition step body (dropPost count post) _

/-- This is control transfer, not a claim that a nonempty continuation executes. -/
theorem modal_leave_sequence {F loop n} (mode : Modality) (model : Model F)
    (continuation : Program F ⟨true,loop⟩ n)
    (post : Flow ⟨true,loop⟩ → Fml n) (vars : Values n) :
    (Fml.modal mode model (Program.leave.sequence continuation) post).holds vars ↔
      (post (.leave_ rfl)).holds vars := by
  rw [modal_sequence]
  exact modal_completed mode model Program.leave
    (sequencePost mode model continuation post) vars ⟨vars,.leave_ rfl⟩ (fuel := 1) rfl

theorem modal_initialized_leave {F loop n r} (mode : Modality) (model : Model F)
    (initializer : Term F n r) (continuation : Program F ⟨true,loop⟩ (r+n))
    (post : Flow ⟨true,loop⟩ → Fml n) (vars : Values n) :
    (Fml.modal mode model (Program.let_ initializer
      (Program.leave.sequence continuation)) post).holds vars ↔
    (Fml.termModal mode model initializer (fun values =>
      .subst (extendValues values) (.subst (dropValues r) (post (.leave_ rfl))))).holds vars := by
  rw [modal_let]
  apply termModal_post_congr
  intro values original
  change (Fml.modal mode model (Program.leave.sequence continuation) (dropPost r post)).holds
    (extendValues values original) ↔ _
  exact modal_leave_sequence mode model continuation (dropPost r post) _

end Solidity.Yul.Logic
