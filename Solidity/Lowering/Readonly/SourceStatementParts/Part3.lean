import Solidity.Lowering.Readonly.SourceDispatchEffects

/-! Generated actual typed Source statement-history cuts; smaller-bound hypotheses retained. -/
namespace Solidity.Lowering.Readonly.SourceHistory
open Solidity.Source
theorem execS_placeholder_succ {E : Env} (G : Glob E) (F : Fr) (fuel : Nat) (_history : At G fuel) (nps : Nat) (ph : Option (Ph E)) {R : List STy} {M : Bool} {k : SCtx} {Γ : RCtx} (h : M = true) (locals : Locals E.layout Γ) :
    Effect F.static (execS G F (fuel+1) nps ph ((RStmt.placeholder (E := E) (R := R) (M := M) h) : RStmt E R M k Γ Γ) locals) := by
  simp only [Solidity.Source.execS]
  repeat' first
     | (with_reducible exact Effect.pure F.static _)
     | (with_reducible exact Effect.halt F.static _)
     | (with_reducible exact Effect.lift F.static _)
     | (with_reducible exact Effect.st F.static)
     | (with_reducible exact Effect.modSt F.static _ (fun _ => rfl))
     | (with_reducible exact _history.runMods F _ _ _)
     | (with_reducible exact zeroInner_effect F.static fuel _ _)
     | refine Effect.bind _ _ _ ?_ (fun value => ?_)
     | (with_reducible apply Effect.sub F.static)
     | split
     | dsimp only

theorem execS_declTuple_succ {E : Env} (G : Glob E) (F : Fr) (fuel : Nat) (_history : At G fuel) (nps : Nat) (ph : Option (Ph E)) {R : List STy} {M : Bool} {k : SCtx} {Γ : RCtx} {σs : List STy} (slots : List (Option STy)) (e : RExpr E Γ (.tuple σs)) (h : slotsFit E.isBase slots σs = true) (locals : Locals E.layout Γ) :
    Effect F.static (execS G F (fuel+1) nps ph ((RStmt.declTuple (E := E) (R := R) (M := M) slots e h) : RStmt E R M k Γ (pushTys slots Γ)) locals) := by
  simp only [Solidity.Source.execS]
  repeat' first
     | (with_reducible exact Effect.pure F.static _)
     | (with_reducible exact Effect.halt F.static _)
     | (with_reducible exact Effect.lift F.static _)
     | (with_reducible exact Effect.st F.static)
     | (with_reducible exact Effect.modSt F.static _ (fun _ => rfl))
     | (with_reducible exact _history.evalE F _)
     | (with_reducible exact pushVals_effect F.static F fuel _ _ _)
     | refine Effect.bind _ _ _ ?_ (fun value => ?_)
     | (with_reducible apply Effect.sub F.static)
     | split
     | dsimp only

theorem execS_retVal_succ {E : Env} (G : Glob E) (F : Fr) (fuel : Nat) (_history : At G fuel) (nps : Nat) (ph : Option (Ph E)) {R : List STy} {M : Bool} {k : SCtx} {Γ : RCtx} {σ τ : STy} (hR : R = [τ]) (e : RExpr E Γ σ) (h : σ.implicit E.isBase τ = true) (locals : Locals E.layout Γ) :
    Effect F.static (execS G F (fuel+1) nps ph ((RStmt.retVal (E := E) (R := R) (M := M) hR e h) : RStmt E R M k Γ Γ) locals) := by
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

theorem execS_retTuple_succ {E : Env} (G : Glob E) (F : Fr) (fuel : Nat) (_history : At G fuel) (nps : Nat) (ph : Option (Ph E)) {R : List STy} {M : Bool} {k : SCtx} {Γ : RCtx} (es : RConvArgs E Γ R) (locals : Locals E.layout Γ) :
    Effect F.static (execS G F (fuel+1) nps ph ((RStmt.retTuple (E := E) (R := R) (M := M) es) : RStmt E R M k Γ Γ) locals) := by
  simp only [Solidity.Source.execS]
  repeat' first
     | (with_reducible exact Effect.pure F.static _)
     | (with_reducible exact Effect.halt F.static _)
     | (with_reducible exact Effect.lift F.static _)
     | (with_reducible exact Effect.st F.static)
     | (with_reducible exact Effect.modSt F.static _ (fun _ => rfl))
     | (with_reducible exact _history.evalConvArgs F _)
     | refine Effect.bind _ _ _ ?_ (fun value => ?_)
     | (with_reducible apply Effect.sub F.static)
     | split
     | dsimp only

end Solidity.Lowering.Readonly.SourceHistory
