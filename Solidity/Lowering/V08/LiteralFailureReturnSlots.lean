import Solidity.Lowering.V08.LiteralFailureDynamicReturn

/-! Exact existing return-frame construction and extraction, over arbitrary
indexed Source values. No new frame/evaluator or source admission is defined. -/
namespace Solidity.Lowering.V08.LiteralFailureReturnSlots
open Solidity Source

theorem get_older {D : Source.Layout} {types Γ : RCtx}
 (values : Source.Vals D types) (parameters : Locals D Γ) (k : Nat) (τ : STy) :
 (values.onto parameters).getAt (types.length+k) τ=parameters.getAt k τ := by
 induction values generalizing Γ k with
 | nil => simp only [Vals.onto,List.length_nil,Nat.zero_add]
 | @cons τ types value values ih =>
  simp only [Vals.onto,List.length_cons]
  have position : types.length+1+k=types.length+(k+1) := by omega
  rw [position,ih]
  rfl

/-- Original return order is recovered from the reverse-pushed local slots. -/
theorem extraction {D : Source.Layout} {types Γ : RCtx}
 (values : Source.Vals D types) (parameters : Locals D Γ) :
 retVals (values.onto parameters) 0 types=.ok values.toR := by
 induction values generalizing Γ with
 | nil => rfl
 | @cons τ types value values ih =>
  have head := get_older values (.cons value parameters) 0 τ
  simp only [Nat.add_zero,Locals.getAt,↓reduceDIte] at head
  simp only [Vals.onto,retVals,Nat.zero_add,Vals.toR]
  rw [head,ih]
  rfl

/-- Updating an older slot preserves the independently pushed prefix. -/
theorem set_older {D : Source.Layout} {types Γ : RCtx} {τ : STy}
 (values : Source.Vals D types) (parameters : Locals D Γ) (k : Nat) (value : Source.Val D τ) :
 (values.onto parameters).setAt (types.length+k) value=
 (parameters.setAt k value).map (fun changed=>values.onto changed) := by
 induction values generalizing Γ k with
 | nil =>
  simp only [Vals.onto,List.length_nil,Nat.zero_add]
  cases result : parameters.setAt k value <;> rfl
 | @cons τ types first values ih =>
  simp only [Vals.onto,List.length_cons]
  have position : types.length+1+k=types.length+(k+1) := by omega
  rw [position,ih]
  simp only [Locals.setAt]
  cases result : parameters.setAt k value <;> rfl

/-- All actual return slots are overwritten, while parameter locals remain. -/
theorem overwrite {D : Source.Layout} {types Γ : RCtx}
 (values old : Source.Vals D types) (parameters : Locals D Γ) :
 setRets (old.onto parameters) 0 values=.ok (values.onto parameters) := by
 induction values generalizing Γ with
 | nil => cases old; rfl
 | @cons τ types value values ih =>
  cases old with
  | cons oldFirst oldRest =>
   have head := set_older oldRest (.cons oldFirst parameters) 0 value
   simp only [Nat.add_zero,Locals.setAt,↓reduceDIte] at head
   simp only [Vals.onto,setRets,Nat.zero_add]
   rw [head]
   exact ih oldRest (.cons value parameters)
/-- The actual tuple-return statement consumes a supplied argument execution.
Concrete clients must discharge it; this is not a compiler/success oracle. -/
theorem tuple_statement {E : Env} {types Γ : RCtx}
 (G : Glob E) (F : Fr) (n : Nat) (old values : Source.Vals E.layout types)
 (parameters : Locals E.layout Γ) (initial : Locals E.layout (types.reverseAux Γ))
 (arguments : RConvArgs E (types.reverseAux Γ) types) (state final : St E)
 (run : (evalConvArgs G F n arguments).run (initial,state)=
  (.ok values,(old.onto parameters,final))) :
 (execS G F (n+1) Γ.length none
  (.retTuple arguments : RStmt E types false .body (types.reverseAux Γ) (types.reverseAux Γ))
  initial).run (L0 E,state)=
 (.ok (.ret (values.onto parameters)),(L0 E,final)) := by
 have base : (types.reverseAux Γ).length-(Γ.length+types.length)=0 := by
  simp only [List.reverseAux_eq,List.length_append,List.length_reverse]
  omega
 dsimp only [ExceptT.run] at run
 simp only [execS,base,EM.sub,EM.lift,bind,pure,ExceptT.bind,ExceptT.pure,
  ExceptT.bindCont,ExceptT.run,ExceptT.mk,StateT.bind,StateT.pure,run,overwrite]
end Solidity.Lowering.V08.LiteralFailureReturnSlots
