import Solidity.Yul.Views.RetainedTupleProducers

/-! Capture of actual logical evaluation, preserving the unexecuted right branch.
Runtime operands are observed before getV, including tuples on a failing branch.
This instruments the operator boundary, not recursive operand intermediates. -/
namespace Solidity.Yul.Views

/-- Capture an actual runtime-producing computation before its actual getV. -/
def captureGetVRun {E Γ σ} (F : Source.Fr) (prior : List (EntryReferenceScope E))
    (m : Source.EM E Γ (Source.RVal E.layout σ)) (s : Source.EMState E Γ) :=
  let first := captureRuntimeRun F prior m s
  match first.1.1 with
  | .error error => ((Except.error error,first.1.2),first.2)
  | .ok value => ((Source.getV value).run first.1.2,first.2)

theorem captureGetVRun_source {E Γ σ} (F : Source.Fr) (prior)
    (m : Source.EM E Γ (Source.RVal E.layout σ)) (s : Source.EMState E Γ) :
    (captureGetVRun F prior m s).1=(m >>= Source.getV).run s := by
  first | (simp only;done) | decide | omega | rfl | skip
  rw [Source.Hoare.run_bind]
  unfold captureGetVRun captureRuntimeRun
  cases actual : m.run s with
  | mk result after => cases result <;> rfl

theorem captureGetVRun_scopes {E Γ σ} (F : Source.Fr) (prior)
    (m : Source.EM E Γ (Source.RVal E.layout σ)) (s : Source.EMState E Γ) :
    (captureGetVRun F prior m s).2=(captureRuntimeRun F prior m s).2 := by
  first | (simp only;done) | decide | omega | rfl | skip
  unfold captureGetVRun
  dsimp only
  split <;> rfl

def captureLogicalRun {E Γ σ} (G : Source.Glob E) (F : Source.Fr) (n : Nat)
    (op : Source.BinOp) (left right : Source.RExpr E Γ σ)
    (prior : List (EntryReferenceScope E)) (s : Source.EMState E Γ) :=
  match n with
  | 0 => captureRuntimeRun F prior (Source.evalE G F 0 (.binary op left right)) s
  | n+1 =>
    let first := captureGetVRun F prior (Source.evalE G F n left) s
    match first.1.1 with
    | .error error => ((Except.error error,first.1.2),first.2)
    | .ok x =>
      match x.key with
      | none => ((Except.error (.stuck "logical operand"),first.1.2),first.2)
      | some kx =>
        if (op = Source.BinOp.and && kx = 0) || (op = Source.BinOp.or && kx = 1) then
          ((Except.ok (.val x),first.1.2),first.2)
        else
          let second := captureGetVRun F first.2 (Source.evalE G F n right) first.1.2
          ((second.1.1.map Source.RVal.val,second.1.2),second.2)

theorem captureLogicalRun_source {E Γ σ} (G : Source.Glob E) (F : Source.Fr) (n : Nat)
    (op : Source.BinOp) (left right : Source.RExpr E Γ σ) (prior) (s : Source.EMState E Γ)
    (logical : (decide (op = Source.BinOp.and) || decide (op = Source.BinOp.or)) = true) :
    (captureLogicalRun G F n op left right prior s).1=(Source.evalE G F n (.binary op left right)).run s := by
  first | (simp only;done) | decide | omega | rfl | skip
  cases n with
  | zero => rfl
  | succ n =>
    simp only [Source.evalE, logical, ↓reduceIte]
    rw [← bind_assoc]
    change (captureLogicalRun G F (n+1) op left right prior s).1=
      (((Source.evalE G F n left) >>= Source.getV) >>= fun x => do
        match x.key with
        | some kx =>
          if (op = Source.BinOp.and && kx = 0) || (op = Source.BinOp.or && kx = 1) then return .val x
          else return .val (← Source.getV (← Source.evalE G F n right))
        | none => Source.EM.halt (.stuck "logical operand")).run s
    rw [Source.Hoare.run_bind]
    unfold captureLogicalRun
    dsimp only
    have first := captureGetVRun_source F prior (Source.evalE G F n left) s
    cases actual : ((Source.evalE G F n left) >>= Source.getV).run s with
    | mk result after =>
      rw [actual] at first
      rw [first]
      cases result with
      | error error => rfl
      | ok x =>
        cases key : x.key with
        | none => simp only [key]; rfl
        | some kx =>
          simp only [key]
          split
          · rfl
          · have second := captureGetVRun_source F (captureGetVRun F prior (Source.evalE G F n left) s).2 (Source.evalE G F n right) after
            rw [second]
            conv => rhs; rw [← bind_assoc, Source.Hoare.run_bind]
            cases run : ((Source.evalE G F n right) >>= Source.getV).run after with
            | mk result final => cases result <;> rfl
/-- Left operand observations survive every later logical outcome. -/
theorem captureLogicalRun_keeps_left {E Γ σ} (G : Source.Glob E) (F : Source.Fr) (n : Nat)
    (op : Source.BinOp) (left right : Source.RExpr E Γ σ) (prior) (s : Source.EMState E Γ)
    (scope) (member : scope∈(captureRuntimeRun F prior (Source.evalE G F n left) s).2) :
    scope∈(captureLogicalRun G F (n+1) op left right prior s).2 := by
  first | (simp only;done) | decide | omega | rfl | skip
  have inner : scope∈(captureGetVRun F prior (Source.evalE G F n left) s).2 := by
    rw [captureGetVRun_scopes]
    exact member
  unfold captureLogicalRun
  dsimp only
  split
  · exact inner
  · split
    · exact inner
    · split
      · exact inner
      · rw [captureGetVRun_scopes]
        exact captureRuntimeRun_prefix F _ _ _ scope inner
end Solidity.Yul.Views
