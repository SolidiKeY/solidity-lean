import Solidity.Yul.Views.RetainedTupleStatement

/-! A tuple expression-statement prefix composes with actual owner execItems.
Earlier captures survive every subsequent tail outcome. The tail is executed
by Source itself, not recursively instrumented by this prefix adapter. -/
namespace Solidity.Yul.Views

def captureTupleItems {E Γ Γ' types R M k} (G : Source.Glob E) (F : Source.Fr) (n nps : Nat)
    (ph : Option (Source.Ph E)) (es : Source.RArgs E Γ types) (rest : Source.RItems E R M k Γ Γ')
    (prior : List (EntryReferenceScope E)) (l : Source.Locals E.layout Γ) (s : Source.EMState E []) :
    (Except Source.Halt (Source.Out E.layout Γ Γ') × Source.EMState E []) × List (EntryReferenceScope E) :=
  match n with
  | 0 => ((.error .timeout,s),prior++[entryLocalScope F l])
  | n+1 =>
    let first := captureTupleStatement G F n es prior l s
    let result := match first.1.1 with
      | .error error => (.error error,first.1.2)
      | .ok (.normal l1) => ((do let out ← Source.execItems G F n nps ph rest l1; Source.EM.lift (out.up Γ)) : Source.EM E [] (Source.Out E.layout Γ Γ')).run first.1.2
      | .ok (.brk l1) => (.ok (.brk l1),first.1.2)
      | .ok (.cont l1) => (.ok (.cont l1),first.1.2)
      | .ok (.ret l1) => (.ok (.ret l1),first.1.2)
    (result,first.2)

theorem captureTupleItems_source {E Γ Γ' types R M k} (G : Source.Glob E) (F : Source.Fr) (n nps : Nat)
    (ph : Option (Source.Ph E)) (es : Source.RArgs E Γ types) (rest : Source.RItems E R M k Γ Γ')
    (prior) (l : Source.Locals E.layout Γ) (s : Source.EMState E []) :
    (captureTupleItems G F n nps ph es rest prior l s).1=
      (Source.execItems G F n nps ph (.stmt (.expr (.tuple es)) rest) l).run s := by
  first | solve | rfl
        | cases n with
          | zero => rfl
          | succ n =>
            unfold captureTupleItems
            dsimp only
            rw [captureTupleStatement_source G F n nps ph]
            rw [Source.execItems,Source.Hoare.run_bind]
            cases first : (Source.execS G F n nps ph (.expr (.tuple es)) l).run s with
            | mk result after => cases result with
              | error error => rfl
              | ok out => cases out <;> rfl

/-- The whole previously captured scope list survives arbitrary tail results,
including early control, failed scope restoration and late Source halt. -/
theorem captureTupleItems_scopes {E Γ Γ' types R M k} (G : Source.Glob E) (F : Source.Fr) (n nps : Nat)
    (ph : Option (Source.Ph E)) (es : Source.RArgs E Γ types) (rest : Source.RItems E R M k Γ Γ')
    (prior) (l : Source.Locals E.layout Γ) (s : Source.EMState E []) :
    (captureTupleItems G F (n+1) nps ph es rest prior l s).2=
      (captureTupleStatement G F n es prior l s).2 := rfl

theorem captureTupleItems_prior {E Γ Γ' types R M k} (G : Source.Glob E) (F : Source.Fr) (n nps : Nat)
    (ph : Option (Source.Ph E)) (es : Source.RArgs E Γ types) (rest : Source.RItems E R M k Γ Γ')
    (prior) (l : Source.Locals E.layout Γ) (s : Source.EMState E []) (scope) (member : scope∈prior) :
    scope∈(captureTupleItems G F n nps ph es rest prior l s).2 := by
  first | solve | simp only
        | cases n with
          | zero => exact List.mem_append_left _ member
          | succ n => exact captureTupleStatement_prior G F n es prior l s scope member

theorem captureTupleItems_head {E Γ Γ' σ types R M k} (G : Source.Glob E) (F : Source.Fr) (n nps : Nat)
    (ph : Option (Source.Ph E)) (head : Source.RExpr E Γ σ) (tail : Source.RArgs E Γ types)
    (rest : Source.RItems E R M k Γ Γ') (prior) (l : Source.Locals E.layout Γ) (s : Source.EMState E [])
    (after : Source.EMState E Γ) (v : Source.RVal E.layout σ)
    (run : (Source.evalE G F n head).run (l,s.2)=(.ok v,after)) :
    runtimeScope F v∈(captureTupleItems G F (n+4) nps ph (.cons head tail) rest prior l s).2 := by
  first | solve | simp only
        | exact captureTupleStatement_head G F n head tail prior l s after v run

/-- All actual tuple constituents remain covered after arbitrary owner tail
execution, even when the sequence returns no normal result. -/
theorem captureTupleItems_covers {E Γ Γ' types R M k} (G : Source.Glob E) (F : Source.Fr) (n nps : Nat)
    (ph : Option (Source.Ph E)) (es : Source.RArgs E Γ types) (rest : Source.RItems E R M k Γ Γ')
    (prior) (l : Source.Locals E.layout Γ) (s : Source.EMState E [])
    (values : Source.RVals E.layout types) (after : Source.EMState E Γ)
    (run : (Source.evalArgs G F n es).run (l,s.2)=(.ok values,after)) (p)
    (inside : p∈runtimeValuesPaths values) :
    ∃ scope∈(captureTupleItems G F (n+3) nps ph es rest prior l s).2,scope.account=F.this ∧ p∈scope.paths := by
  first | solve | simp only
        | exact captureTupleStatement_covers G F n es prior l s values after run p inside

end Solidity.Yul.Views
