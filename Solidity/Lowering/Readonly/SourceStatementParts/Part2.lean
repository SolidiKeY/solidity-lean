import Solidity.Lowering.Readonly.SourceDispatchEffects

/-! Generated actual typed Source statement-history cuts; smaller-bound hypotheses retained. -/
namespace Solidity.Lowering.Readonly.SourceHistory
open Solidity.Source
theorem execS_block_succ {E : Env} (G : Glob E) (F : Fr) (fuel : Nat) (_history : At G fuel) (nps : Nat) (ph : Option (Ph E)) {R : List STy} {M : Bool} {k : SCtx} {Γ Γ' : RCtx} (b : RItems E R M k Γ Γ') (locals : Locals E.layout Γ) :
    Effect F.static (execS G F (fuel+1) nps ph ((RStmt.block (E := E) (R := R) (M := M) b) : RStmt E R M k Γ Γ) locals) := by
  simp only [Solidity.Source.execS]
  repeat' first
     | (with_reducible exact Effect.pure F.static _)
     | (with_reducible exact Effect.halt F.static _)
     | (with_reducible exact Effect.lift F.static _)
     | (with_reducible exact Effect.st F.static)
     | (with_reducible exact Effect.modSt F.static _ (fun _ => rfl))
     | (with_reducible exact _history.execItems F _ _ _ _)
     | refine Effect.bind _ _ _ ?_ (fun value => ?_)
     | (with_reducible apply Effect.sub F.static)
     | split
     | dsimp only

theorem execS_ifThen_succ {E : Env} (G : Glob E) (F : Fr) (fuel : Nat) (_history : At G fuel) (nps : Nat) (ph : Option (Ph E)) {R : List STy} {M : Bool} {k : SCtx} {Γ Γ₁ : RCtx} (c : RExpr E Γ .bool) (s : RStmt E R M k Γ Γ₁) (locals : Locals E.layout Γ) :
    Effect F.static (execS G F (fuel+1) nps ph ((RStmt.ifThen (E := E) (R := R) (M := M) c s) : RStmt E R M k Γ Γ) locals) := by
  simp only [Solidity.Source.execS]
  repeat' first
     | (with_reducible exact Effect.pure F.static _)
     | (with_reducible exact Effect.halt F.static _)
     | (with_reducible exact Effect.lift F.static _)
     | (with_reducible exact Effect.st F.static)
     | (with_reducible exact Effect.modSt F.static _ (fun _ => rfl))
     | (with_reducible exact _history.evalE F _)
     | (with_reducible exact _history.execS F _ _ _ _)
     | (with_reducible exact getV_effect F.static _)
     | refine Effect.bind _ _ _ ?_ (fun value => ?_)
     | (with_reducible apply Effect.sub F.static)
     | split
     | dsimp only

theorem execS_ifElse_succ {E : Env} (G : Glob E) (F : Fr) (fuel : Nat) (_history : At G fuel) (nps : Nat) (ph : Option (Ph E)) {R : List STy} {M : Bool} {k : SCtx} {Γ Γ₁ Γ₂ : RCtx} (c : RExpr E Γ .bool) (s : RStmt E R M k Γ Γ₁) (t : RStmt E R M k Γ Γ₂) (locals : Locals E.layout Γ) :
    Effect F.static (execS G F (fuel+1) nps ph ((RStmt.ifElse (E := E) (R := R) (M := M) c s t) : RStmt E R M k Γ Γ) locals) := by
  simp only [Solidity.Source.execS]
  repeat' first
     | (with_reducible exact Effect.pure F.static _)
     | (with_reducible exact Effect.halt F.static _)
     | (with_reducible exact Effect.lift F.static _)
     | (with_reducible exact Effect.st F.static)
     | (with_reducible exact Effect.modSt F.static _ (fun _ => rfl))
     | (with_reducible exact _history.evalE F _)
     | (with_reducible exact _history.execS F _ _ _ _)
     | (with_reducible exact getV_effect F.static _)
     | refine Effect.bind _ _ _ ?_ (fun value => ?_)
     | (with_reducible apply Effect.sub F.static)
     | split
     | dsimp only

theorem execS_whileLoop_succ {E : Env} (G : Glob E) (F : Fr) (fuel : Nat) (_history : At G fuel) (nps : Nat) (ph : Option (Ph E)) {R : List STy} {M : Bool} {l u : Bool} {Γ Γ₁ : RCtx} (c : RExpr E Γ .bool) (s : RStmt E R M ⟨true, u⟩ Γ Γ₁) (locals : Locals E.layout Γ) :
    Effect F.static (execS G F (fuel+1) nps ph ((RStmt.whileLoop (E := E) (R := R) (M := M) c s) : RStmt E R M ⟨l, u⟩ Γ Γ) locals) := by
  simp only [Solidity.Source.execS]
  repeat' first
     | (with_reducible exact Effect.pure F.static _)
     | (with_reducible exact Effect.halt F.static _)
     | (with_reducible exact Effect.lift F.static _)
     | (with_reducible exact Effect.st F.static)
     | (with_reducible exact Effect.modSt F.static _ (fun _ => rfl))
     | (with_reducible exact _history.evalE F _)
     | (with_reducible exact _history.execS F _ _ _ _)
     | (with_reducible exact getV_effect F.static _)
     | refine Effect.bind _ _ _ ?_ (fun value => ?_)
     | (with_reducible apply Effect.sub F.static)
     | split
     | dsimp only

theorem execS_doWhile_succ {E : Env} (G : Glob E) (F : Fr) (fuel : Nat) (_history : At G fuel) (nps : Nat) (ph : Option (Ph E)) {R : List STy} {M : Bool} {l u : Bool} {Γ Γ₁ : RCtx} (s : RStmt E R M ⟨true, u⟩ Γ Γ₁) (c : RExpr E Γ .bool) (locals : Locals E.layout Γ) :
    Effect F.static (execS G F (fuel+1) nps ph ((RStmt.doWhile (E := E) (R := R) (M := M) s c) : RStmt E R M ⟨l, u⟩ Γ Γ) locals) := by
  simp only [Solidity.Source.execS]
  repeat' first
     | (with_reducible exact Effect.pure F.static _)
     | (with_reducible exact Effect.halt F.static _)
     | (with_reducible exact Effect.lift F.static _)
     | (with_reducible exact Effect.st F.static)
     | (with_reducible exact Effect.modSt F.static _ (fun _ => rfl))
     | (with_reducible exact _history.evalE F _)
     | (with_reducible exact _history.execS F _ _ _ _)
     | (with_reducible exact getV_effect F.static _)
     | refine Effect.bind _ _ _ ?_ (fun value => ?_)
     | (with_reducible apply Effect.sub F.static)
     | split
     | dsimp only

theorem execS_forLoop_succ {E : Env} (G : Glob E) (F : Fr) (fuel : Nat) (_history : At G fuel) (nps : Nat) (ph : Option (Ph E)) {R : List STy} {M : Bool} {l u : Bool} {Γ Γ₁ Γ₂ : RCtx} (init : RStmt E R M ⟨true, u⟩ Γ Γ₁) (c : ROptBool E Γ₁) (post : ROptExpr E Γ₁) (s : RStmt E R M ⟨true, u⟩ Γ₁ Γ₂) (locals : Locals E.layout Γ) :
    Effect F.static (execS G F (fuel+1) nps ph ((RStmt.forLoop (E := E) (R := R) (M := M) init c post s) : RStmt E R M ⟨l, u⟩ Γ Γ) locals) := by
  simp only [Solidity.Source.execS]
  repeat' first
     | (with_reducible exact Effect.pure F.static _)
     | (with_reducible exact Effect.halt F.static _)
     | (with_reducible exact Effect.lift F.static _)
     | (with_reducible exact Effect.st F.static)
     | (with_reducible exact Effect.modSt F.static _ (fun _ => rfl))
     | (with_reducible exact _history.execS F _ _ _ _)
     | (with_reducible exact _history.forIter F _ _ _ _ _ _)
     | refine Effect.bind _ _ _ ?_ (fun value => ?_)
     | (with_reducible apply Effect.sub F.static)
     | split
     | dsimp only

end Solidity.Lowering.Readonly.SourceHistory
