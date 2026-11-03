import Solidity.Lowering.Readonly.SourceTryEffects

/-! Generated actual typed Source statement-history cuts; smaller-bound hypotheses retained. -/
namespace Solidity.Lowering.Readonly.SourceHistory
open Solidity.Source
theorem execS_emit_succ {E : Env} (G : Glob E) (F : Fr) (fuel : Nat) (_history : At G fuel) (nps : Nat) (ph : Option (Ph E)) {R : List STy} {M : Bool} {k : SCtx} {Γ : RCtx} {ps : List STy} (ev : Decl) (h : ev.paramTys E = some ps) (args : RConvArgs E Γ ps) (locals : Locals E.layout Γ) :
    Effect F.static (execS G F (fuel+1) nps ph ((RStmt.emit (E := E) (R := R) (M := M) ev h args) : RStmt E R M k Γ Γ) locals) := by
  simp only [Solidity.Source.execS]
  repeat' first
     | (with_reducible exact Effect.pure F.static _)
     | (with_reducible exact Effect.halt F.static _)
     | (with_reducible exact Effect.lift F.static _)
     | (with_reducible exact Effect.st F.static)
     | (with_reducible exact Effect.modSt F.static _ (fun _ => rfl))
     | (with_reducible exact _history.evalConvArgs F _)
     | (with_reducible exact encodeVals_effect F.static F fuel _ _)
     | refine Effect.bind _ _ _ ?_ (fun value => ?_)
     | (with_reducible apply Effect.sub F.static)
     | split
     | dsimp only

theorem execS_revertError_succ {E : Env} (G : Glob E) (F : Fr) (fuel : Nat) (_history : At G fuel) (nps : Nat) (ph : Option (Ph E)) {R : List STy} {M : Bool} {k : SCtx} {Γ : RCtx} {ps : List STy} (er : Decl) (h : er.paramTys E = some ps) (args : RConvArgs E Γ ps) (locals : Locals E.layout Γ) :
    Effect F.static (execS G F (fuel+1) nps ph ((RStmt.revertError (E := E) (R := R) (M := M) er h args) : RStmt E R M k Γ Γ) locals) := by
  simp only [Solidity.Source.execS]
  repeat' first
     | (with_reducible exact Effect.pure F.static _)
     | (with_reducible exact Effect.halt F.static _)
     | (with_reducible exact Effect.lift F.static _)
     | (with_reducible exact Effect.st F.static)
     | (with_reducible exact Effect.modSt F.static _ (fun _ => rfl))
     | (with_reducible exact _history.evalConvArgs F _)
     | (with_reducible exact encodeVals_effect F.static F fuel _ _)
     | refine Effect.bind _ _ _ ?_ (fun value => ?_)
     | (with_reducible apply Effect.sub F.static)
     | split
     | dsimp only

theorem execS_rethrow_succ {E : Env} (G : Glob E) (F : Fr) (fuel : Nat) (_history : At G fuel) (nps : Nat) (ph : Option (Ph E)) {R : List STy} {M : Bool} {k : SCtx} {Γ : RCtx} (i : Idx Γ (.bytes .memory)) (locals : Locals E.layout Γ) :
    Effect F.static (execS G F (fuel+1) nps ph ((RStmt.rethrow (E := E) (R := R) (M := M) i) : RStmt E R M k Γ Γ) locals) := by
  simp only [Solidity.Source.execS]
  repeat' first
     | (with_reducible exact Effect.pure F.static _)
     | (with_reducible exact Effect.halt F.static _)
     | (with_reducible exact Effect.lift F.static _)
     | (with_reducible exact Effect.st F.static)
     | (with_reducible exact Effect.modSt F.static _ (fun _ => rfl))
     | (with_reducible exact heapBytes_effect F.static _)
     | refine Effect.bind _ _ _ ?_ (fun value => ?_)
     | (with_reducible apply Effect.sub F.static)
     | split
     | dsimp only

theorem execS_tryCall_succ {E : Env} (G : Glob E) (F : Fr) (fuel : Nat) (_history : At G fuel) (nps : Nat) (ph : Option (Ph E)) {R : List STy} {M : Bool} {k : SCtx} {Γ Γ₁ Γ₂ : RCtx} {dn : DeclName} {ps rs : List STy} (target : RExpr E Γ (.contract dn)) (d : Decl) (h : d.fnSig E = some (ps, rs)) (args : RConvArgs E Γ ps) (ok : RItems E R M k (rs.reverseAux Γ) Γ₁) (cbind : Bool) (cat : RItems E R M k (catchCtx cbind Γ) Γ₂) (locals : Locals E.layout Γ) :
    Effect F.static (execS G F (fuel+1) nps ph ((RStmt.tryCall (E := E) (R := R) (M := M) target d h args ok cbind cat) : RStmt E R M k Γ Γ) locals) := by
  rw [Try.equation]
  apply Effect.bind
  · exact Effect.sub _ _ _ (Try.payload_effect G F fuel _history target d h args)
  · intro pair
    exact Try.finish_effect G F fuel nps _history ph ok cbind cat pair.1 pair.2

end Solidity.Lowering.Readonly.SourceHistory
