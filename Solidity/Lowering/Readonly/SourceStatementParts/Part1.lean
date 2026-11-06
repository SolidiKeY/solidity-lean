import Solidity.Lowering.Readonly.SourceDispatchEffects

/-! Generated actual typed Source statement-history cuts; smaller-bound hypotheses retained. -/
namespace Solidity.Lowering.Readonly.SourceHistory
open Solidity.Source
theorem execS_expr_succ {E : Env} (G : Glob E) (F : Fr) (fuel : Nat) (_history : At G fuel) (nps : Nat) (ph : Option (Ph E)) {R : List STy} {M : Bool} {k : SCtx} {Γ : RCtx} {τ : STy} (e : RExpr E Γ τ) (locals : Locals E.layout Γ) :
    Effect F.static (execS G F (fuel+1) nps ph ((RStmt.expr (E := E) (R := R) (M := M) e) : RStmt E R M k Γ Γ) locals) := by
  simp only [Solidity.Source.execS]
  repeat' first
     | (with_reducible exact Effect.pure F.static _)
     | (with_reducible exact Effect.halt F.static _)
     | (with_reducible exact Effect.lift F.static _)
     | (with_reducible exact Effect.st F.static)
     | (with_reducible exact Effect.modSt F.static _ (fun _ => rfl))
     | (with_reducible exact _history.evalE F _)
     | refine Effect.bind _ _ _ ?_ (fun value => ?_)
     | (with_reducible apply Effect.sub F.static)
     | split
     | dsimp only

theorem execS_declVar_succ {E : Env} (G : Glob E) (F : Fr) (fuel : Nat) (_history : At G fuel) (nps : Nat) (ph : Option (Ph E)) {R : List STy} {M : Bool} {k : SCtx} {Γ : RCtx} (τ : STy) (locals : Locals E.layout Γ) :
    Effect F.static (execS G F (fuel+1) nps ph ((RStmt.declVar (E := E) (R := R) (M := M) τ) : RStmt E R M k Γ (τ :: Γ)) locals) := by
  simp only [Solidity.Source.execS]
  repeat' first
     | (with_reducible exact Effect.pure F.static _)
     | (with_reducible exact Effect.halt F.static _)
     | (with_reducible exact Effect.lift F.static _)
     | (with_reducible exact Effect.st F.static)
     | (with_reducible exact Effect.modSt F.static _ (fun _ => rfl))
     | (with_reducible exact (zero_histories F.static fuel).2.1 _)
     | refine Effect.bind _ _ _ ?_ (fun value => ?_)
     | (with_reducible apply Effect.sub F.static)
     | split
     | dsimp only

theorem execS_declInit_succ {E : Env} (G : Glob E) (F : Fr) (fuel : Nat) (_history : At G fuel) (nps : Nat) (ph : Option (Ph E)) {R : List STy} {M : Bool} {k : SCtx} {Γ : RCtx} {σ τ : STy} (e : RExpr E Γ σ) (h : σ.implicit E.isBase E.mapFree τ = true) (locals : Locals E.layout Γ) :
    Effect F.static (execS G F (fuel+1) nps ph ((RStmt.declInit (E := E) (R := R) (M := M) e h) : RStmt E R M k Γ (τ :: Γ)) locals) := by
  simp only [Solidity.Source.execS]
  repeat' first
     | (with_reducible exact Effect.pure F.static _)
     | (with_reducible exact Effect.halt F.static _)
     | (with_reducible exact Effect.lift F.static _)
     | (with_reducible exact Effect.st F.static)
     | (with_reducible exact Effect.modSt F.static _ (fun _ => rfl))
     | (with_reducible exact _history.evalE F _)
     | (with_reducible exact getV_effect F.static _)
     | (with_reducible exact convRV_effect F.static F fuel _ _)
     | refine Effect.bind _ _ _ ?_ (fun value => ?_)
     | (with_reducible apply Effect.sub F.static)
     | split
     | dsimp only

theorem execS_skip_succ {E : Env} (G : Glob E) (F : Fr) (fuel : Nat) (_history : At G fuel) (nps : Nat) (ph : Option (Ph E)) {R : List STy} {M : Bool} {k : SCtx} {Γ : RCtx} (locals : Locals E.layout Γ) :
    Effect F.static (execS G F (fuel+1) nps ph ((RStmt.skip (E := E) (R := R) (M := M) ) : RStmt E R M k Γ Γ) locals) := by
  simp only [Solidity.Source.execS]
  repeat' first
     | (with_reducible exact Effect.pure F.static _)
     | (with_reducible exact Effect.halt F.static _)
     | (with_reducible exact Effect.lift F.static _)
     | (with_reducible exact Effect.st F.static)
     | (with_reducible exact Effect.modSt F.static _ (fun _ => rfl))
     | refine Effect.bind _ _ _ ?_ (fun value => ?_)
     | (with_reducible apply Effect.sub F.static)
     | split
     | dsimp only

theorem execS_brk_succ {E : Env} (G : Glob E) (F : Fr) (fuel : Nat) (_history : At G fuel) (nps : Nat) (ph : Option (Ph E)) {R : List STy} {M : Bool} {u : Bool} {Γ : RCtx} (locals : Locals E.layout Γ) :
    Effect F.static (execS G F (fuel+1) nps ph ((RStmt.brk (E := E) (R := R) (M := M) ) : RStmt E R M ⟨true, u⟩ Γ Γ) locals) := by
  simp only [Solidity.Source.execS]
  repeat' first
     | (with_reducible exact Effect.pure F.static _)
     | (with_reducible exact Effect.halt F.static _)
     | (with_reducible exact Effect.lift F.static _)
     | (with_reducible exact Effect.st F.static)
     | (with_reducible exact Effect.modSt F.static _ (fun _ => rfl))
     | refine Effect.bind _ _ _ ?_ (fun value => ?_)
     | (with_reducible apply Effect.sub F.static)
     | split
     | dsimp only

theorem execS_cont_succ {E : Env} (G : Glob E) (F : Fr) (fuel : Nat) (_history : At G fuel) (nps : Nat) (ph : Option (Ph E)) {R : List STy} {M : Bool} {u : Bool} {Γ : RCtx} (locals : Locals E.layout Γ) :
    Effect F.static (execS G F (fuel+1) nps ph ((RStmt.cont (E := E) (R := R) (M := M) ) : RStmt E R M ⟨true, u⟩ Γ Γ) locals) := by
  simp only [Solidity.Source.execS]
  repeat' first
     | (with_reducible exact Effect.pure F.static _)
     | (with_reducible exact Effect.halt F.static _)
     | (with_reducible exact Effect.lift F.static _)
     | (with_reducible exact Effect.st F.static)
     | (with_reducible exact Effect.modSt F.static _ (fun _ => rfl))
     | refine Effect.bind _ _ _ ?_ (fun value => ?_)
     | (with_reducible apply Effect.sub F.static)
     | split
     | dsimp only

theorem execS_ret_succ {E : Env} (G : Glob E) (F : Fr) (fuel : Nat) (_history : At G fuel) (nps : Nat) (ph : Option (Ph E)) {R : List STy} {M : Bool} {k : SCtx} {Γ : RCtx} (h : R = []) (locals : Locals E.layout Γ) :
    Effect F.static (execS G F (fuel+1) nps ph ((RStmt.ret (E := E) (R := R) (M := M) h) : RStmt E R M k Γ Γ) locals) := by
  simp only [Solidity.Source.execS]
  repeat' first
     | (with_reducible exact Effect.pure F.static _)
     | (with_reducible exact Effect.halt F.static _)
     | (with_reducible exact Effect.lift F.static _)
     | (with_reducible exact Effect.st F.static)
     | (with_reducible exact Effect.modSt F.static _ (fun _ => rfl))
     | refine Effect.bind _ _ _ ?_ (fun value => ?_)
     | (with_reducible apply Effect.sub F.static)
     | split
     | dsimp only

end Solidity.Lowering.Readonly.SourceHistory
