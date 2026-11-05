import Solidity.Yul.Views.RetainedTupleProducers

/-! Actual expression-statement transport retains tuple constituents before the
owner discards the runtime value. The typed Source statement result, locals,
state, timeout and horizons are unchanged. Arbitrary recursive expression
intermediates are not thereby instrumented. -/
namespace Solidity.Yul.Views

def captureTupleStatement {E Γ types} (G : Source.Glob E) (F : Source.Fr) (n : Nat)
    (es : Source.RArgs E Γ types) (prior : List (EntryReferenceScope E))
    (l : Source.Locals E.layout Γ) (s : Source.EMState E []) :
    (Except Source.Halt (Source.Out E.layout Γ Γ) × Source.EMState E []) × List (EntryReferenceScope E) :=
  match n with
  | 0 => ((.error .timeout,s),prior++[entryLocalScope F l])
  | n+1 =>
    let captured := captureTupleRun G F n es prior (l,s.2)
    ((captured.1.1.map (fun _=>.normal captured.1.2.1),(s.1,captured.1.2.2)),captured.2)

theorem captureTupleStatement_source {E Γ types R M k} (G : Source.Glob E) (F : Source.Fr) (n nps : Nat)
    (ph : Option (Source.Ph E)) (es : Source.RArgs E Γ types) (prior)
    (l : Source.Locals E.layout Γ) (s : Source.EMState E []) :
    (captureTupleStatement G F n es prior l s).1=
      (Source.execS G F n nps ph (R:=R) (M:=M) (k:=k) (.expr (.tuple es)) l).run s := by
  first | solve | rfl
        | cases n with
          | zero => rfl
          | succ n =>
            change (fun result : Except Source.Halt (Source.RVal E.layout (.tuple types)) × Source.EMState E Γ =>
              (result.1.map (fun _=>Source.Out.normal result.2.1),(s.1,result.2.2)))
                (captureTupleRun G F n es prior (l,s.2)).1=_
            rw [captureTupleRun_source]
            rw [Source.execS,Source.Hoare.run_bind]
            unfold Source.EM.sub
            rcases s with ⟨outer,st⟩
            dsimp only [ExceptT.run]
            cases run : (Source.evalE G F n (.tuple es)).run (l,st) with
            | mk result after =>
              dsimp only [ExceptT.run] at run
              cases result <;> simp only [ExceptT.mk,run,Except.map] <;> rfl

theorem captureTupleStatement_prior {E Γ types} (G : Source.Glob E) (F : Source.Fr) (n : Nat)
    (es : Source.RArgs E Γ types) (prior) (l : Source.Locals E.layout Γ) (s : Source.EMState E [])
    (scope) (member : scope∈prior) : scope∈(captureTupleStatement G F n es prior l s).2 := by
  first | solve | simp only
        | cases n with
          | zero => exact List.mem_append_left _ member
          | succ n =>
            cases n with
            | zero => exact captureRuntimeRun_prefix F prior _ _ scope member
            | succ n => exact captureArgumentsRun_prefix G F n es prior (l,s.2) scope member

/-- Every constituent of actual successful argument production survives its
statement's discard. No single-Val conversion or observed-trace input. -/
theorem captureTupleStatement_covers {E Γ types} (G : Source.Glob E) (F : Source.Fr) (n : Nat)
    (es : Source.RArgs E Γ types) (prior) (l : Source.Locals E.layout Γ) (s : Source.EMState E [])
    (values : Source.RVals E.layout types) (after : Source.EMState E Γ)
    (run : (Source.evalArgs G F n es).run (l,s.2)=(.ok values,after)) (p)
    (inside : p∈runtimeValuesPaths values) :
    ∃ scope∈(captureTupleStatement G F (n+2) es prior l s).2,scope.account=F.this ∧ p∈scope.paths := by
  first | solve | simp only
        | exact captureTupleRun_covers G F n es prior (l,s.2) after values run p inside

/-- A successful head is retained even if a later argument prevents any tuple
or normal statement result from being returned. -/
theorem captureTupleStatement_head {E Γ σ types} (G : Source.Glob E) (F : Source.Fr) (n : Nat)
    (head : Source.RExpr E Γ σ) (tail : Source.RArgs E Γ types) (prior)
    (l : Source.Locals E.layout Γ) (s : Source.EMState E []) (after : Source.EMState E Γ) (v : Source.RVal E.layout σ)
    (run : (Source.evalE G F n head).run (l,s.2)=(.ok v,after)) :
    runtimeScope F v∈(captureTupleStatement G F (n+3) (.cons head tail) prior l s).2 := by
  first | solve | simp only
        | exact captureArgumentsRun_head G F n head tail prior (l,s.2) after v run

/-- Removing an adjacent duplicate preserves stable capture union, including
its order after any real live/history prefix. -/
theorem uniqueVisitIndices_duplicate (seen xs : List Nat) (i : Nat) (rest : List Nat) :
    uniqueVisitIndices seen (xs++i::i::rest)=uniqueVisitIndices seen (xs++i::rest) := by
  first | solve | simp only [uniqueVisitIndices]
        | induction xs generalizing seen with
          | nil =>
            by_cases member : i∈seen
            · simp only [List.nil_append,uniqueVisitIndices,if_pos member]
            · simp only [List.nil_append,uniqueVisitIndices,if_neg member,List.mem_cons_self,ite_true]
          | cons head xs ih =>
            simp only [List.cons_append,uniqueVisitIndices]
            split <;> rw [ih]

end Solidity.Yul.Views
