import Solidity.Lowering.Readonly.SourceKnownHistory

/-! Guard-parametric factoring of the existing contract try computation.
Regression purpose: a delegated body may use contract/plain/bytes try while
calldata is unavailable; original try behavior and all Source statements stay
unchanged. This factors the exact interpreter and supplies journal histories. -/
namespace Solidity.Lowering.Readonly.SourceHistory
open Solidity.Source
open Solidity.Roadmap (Bytes Outcome)
namespace TryKnown
def payload {E : Env} {Γ : RCtx} {dn : DeclName} {ps : List STy}
    (G : Glob E) (F : Fr) (n : Nat) (known : Bool) (target : RExpr E Γ (.contract dn))
    (d : Decl) (args : RConvArgs E Γ ps) : EM E Γ Outcome := do
  let a ← match ← getV (← evalE (calldataKnown := known) G F n target) with | .contract x => pure x
  let vs ← evalConvArgs (calldataKnown := known) G F n args
  let declared := match d.fnSig E with | some (ps, _) => ps | none => []
  let input := G.selector (sigOf E.layout d.name declared) ++ (← encodeVals F n false vs.toR)
  if (← instanceAt G a).isNone && !G.hasCode (← EM.st).events a then EM.halt (.revert [])
  let (out, _) ← EM.sub (L0 E) (callAddr G F n a ⟨0, by decide⟩ input
    (d.fnMut == some .view || d.fnMut == some .pure))
  pure out

def finish {E : Env} {R : List STy} {M : Bool} {k : SCtx}
    {Γ Γ₁ Γ₂ : RCtx} {rs : List STy}
    (G : Glob E) (F : Fr) (n nps : Nat) (known : Bool) (ph : Option (Ph E))
    (ok : RItems E R M k (rs.reverseAux Γ) Γ₁) (cbind : Bool)
    (cat : RItems E R M k (catchCtx cbind Γ) Γ₂)
    (out : Outcome) (locals : Locals E.layout Γ) : EM E [] (Out E.layout Γ Γ) := do
  match out with
  | .success data =>
    if data.length < 32 * rs.length then EM.halt (.revert [])
    let vs ← EM.lift (decodeVals E.layout data rs 0)
    let o ← execItems (calldataKnown := known) G F n nps ph ok (vs.onto locals)
    EM.lift (← EM.lift (o.up Γ)).close
  | .revert data =>
    match cbind, cat with
    | true, cat =>
      let r ← allocRef (Data.bytes (D := E.layout) (l := .memory) data)
      let o ← execItems (calldataKnown := known) G F n nps ph cat (.cons r locals)
      EM.lift (← EM.lift (o.up Γ)).close
    | false, cat =>
      let o ← execItems (calldataKnown := known) G F n nps ph cat locals
      EM.lift o.close

theorem payload_effect {E : Env} {Γ : RCtx} {dn : DeclName} {ps rs : List STy}
    (G : Glob E) (F : Fr) (n : Nat) (known : Bool) (history : KnownAt G n)
    (target : RExpr E Γ (.contract dn)) (d : Decl)
    (signature : d.fnSig E = some (ps,rs)) (args : RConvArgs E Γ ps) :
    Effect F.static (payload G F n known target d args) := by
  simp only [payload, signature]
  repeat' first
   | (with_reducible exact Effect.pure F.static _)
   | (with_reducible exact Effect.halt F.static _)
   | (with_reducible exact Effect.st F.static)
   | (with_reducible exact history.evalE known F _)
   | (with_reducible exact history.evalConvArgs known F _)
   | (with_reducible exact getV_effect F.static _)
   | (with_reducible exact encodeVals_effect F.static F n _ _)
   | (with_reducible exact instanceAt_effect F.static G _)
   | (with_reducible exact Effect.parent F.static _ _ (history.callAddr F _ _ _ _))
   | refine Effect.bind _ _ _ ?_ (fun value => ?_)
   | (with_reducible apply Effect.sub F.static)
   | split
   | dsimp only

theorem finish_effect {E : Env} {R : List STy} {M : Bool} {k : SCtx}
    {Γ Γ₁ Γ₂ : RCtx} {rs : List STy}
    (G : Glob E) (F : Fr) (n nps : Nat) (known : Bool) (history : KnownAt G n) (ph : Option (Ph E))
    (ok : RItems E R M k (rs.reverseAux Γ) Γ₁) (cbind : Bool)
    (cat : RItems E R M k (catchCtx cbind Γ) Γ₂)
    (out : Outcome) (locals : Locals E.layout Γ) :
    Effect F.static (finish G F n nps known ph ok cbind cat out locals) := by
  cases out <;> cases cbind <;> simp only [finish]
  all_goals repeat' first
   | (with_reducible exact Effect.pure F.static _)
   | (with_reducible exact Effect.halt F.static _)
   | (with_reducible exact Effect.lift F.static _)
   | (with_reducible exact history.execItems known F _ _ _ _)
   | (with_reducible exact allocRef_effect F.static _)
   | refine Effect.bind _ _ _ ?_ (fun value => ?_)
   | split
   | dsimp only

theorem equation {E : Env} {R : List STy} {M : Bool} {k : SCtx}
    {Γ Γ₁ Γ₂ : RCtx} {dn : DeclName} {ps rs : List STy}
    (G : Glob E) (F : Fr) (n nps : Nat) (known : Bool) (ph : Option (Ph E))
    (target : RExpr E Γ (.contract dn)) (d : Decl)
    (signature : d.fnSig E = some (ps,rs)) (args : RConvArgs E Γ ps)
    (ok : RItems E R M k (rs.reverseAux Γ) Γ₁) (cbind : Bool)
    (cat : RItems E R M k (catchCtx cbind Γ) Γ₂) (locals : Locals E.layout Γ) :
    execS (calldataKnown := known) G F (n+1) nps ph (.tryCall target d signature args ok cbind cat) locals =
      (do let pair ← EM.sub locals (payload G F n known target d args)
          finish G F n nps known ph ok cbind cat pair.1 pair.2) := by
  simp only [Solidity.Source.execS, payload, finish]
  congr 1
  funext pair
  rcases pair with ⟨out, updated⟩
  cases out <;> cases cbind <;> rfl
end TryKnown
end Solidity.Lowering.Readonly.SourceHistory

/-- info: 'Solidity.Lowering.Readonly.SourceHistory.TryKnown.payload' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Lowering.Readonly.SourceHistory.TryKnown.payload

/-- info: 'Solidity.Lowering.Readonly.SourceHistory.TryKnown.finish' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Lowering.Readonly.SourceHistory.TryKnown.finish

/-- info: 'Solidity.Lowering.Readonly.SourceHistory.TryKnown.payload_effect' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Lowering.Readonly.SourceHistory.TryKnown.payload_effect

/-- info: 'Solidity.Lowering.Readonly.SourceHistory.TryKnown.finish_effect' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Lowering.Readonly.SourceHistory.TryKnown.finish_effect

/-- info: 'Solidity.Lowering.Readonly.SourceHistory.TryKnown.equation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Lowering.Readonly.SourceHistory.TryKnown.equation
