import Solidity.Tools.Taclet

/-!
# Exact symbolic tuple VC notation

The packed VC operator retains the typed tuple, body and frame, and roundtrips
through the actual full-name rule printer. Scoped implementation escapes are
rejected by the global printer coverage check.
-/
namespace Solidity.Examples.LexRuleSyntax

open scoped Schema in
example {C : Contract} {Γ Γb : Ctx} {k n : Nat} {inv cond : Val C Γ .bool}
    {metrics : LoopMetrics C Γ (n + 2)} {brk : Bool} {qs : List (LoopQ C Γ)}
    {body : Prog C Γ Γb} {xs : List ((t : LTy) × Idx Γ t)} {hv : Option (List Name)}
    (hf : body.frame = some (xs, hv)) (hb : brk = false) (hq : qs = []) :
    dl[LeanTaclet C k]{ ⟨
      /// @custom:key invariant inv
      /// @custom:key decreases ‹metrics›
      while (cond) body;
    ⟩ ⇝ lexInvariant(inv, ‹metrics›, cond, body) } :=
  LeanTaclet.whileInvariantLexDiamond hf hb hq

/-- The erasure constructor is unavailable on exactly the new supported arm. -/
example {C : Contract} {Γ Γb : Ctx} {brk : Bool} {qs : List (LoopQ C Γ)}
    {body : Prog C Γ Γb} {xs : List ((t : LTy) × Idx Γ t)} {hv : Option (List Name)}
    (hf : body.frame = some (xs, hv)) (hb : brk = false) (hq : qs = []) :
    LoopLex.eraseAllowed .diamond brk qs body.frame = false := by
  subst hb
  subst hq
  rw [hf]
  rfl

/-- info: symbolic lexicographic rule text reconstructs its exact typed premise -/
#guard_msgs in
open scoped Schema in
run_meta do
  let info ← Lean.getConstInfo ``LeanTaclet.whileInvariantLexDiamond
  Lean.Meta.forallTelescope info.type fun _ conclusion => do
    let text ← Lean.withOptions (fun o => (o.setBool `pp.sol.dl true).setBool `pp.fullNames true) do
      pure ((← Lean.Meta.ppExpr conclusion).pretty 100000)
    unless Solidity.Tools.isRuleLine text do
      throwError "lex rule escaped a scoped implementation helper: {text}"
    unless 1 < (text.splitOn "lexInvariant").length do
      throwError "lex rule lost its packed VC operator: {text}"
    let .ok shownSyntax := Lean.Parser.runParserCategory (← Lean.getEnv) `term text
      | throwError "lex rule does not parse: {text}"
    let parsed ← Lean.Elab.Term.TermElabM.run' do
      let p ← Lean.Elab.Term.elabTermEnsuringType shownSyntax (← Lean.Meta.inferType conclusion)
      Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
      pure p
    unless ← Lean.Meta.isDefEq conclusion parsed do
      throwError "lex rule changed its source tuple, frame or typed premise: {text}"
  Lean.logInfo "symbolic lexicographic rule text reconstructs its exact typed premise"

/-- info: shadowed schema locals cannot change the packed tuple VC on replay -/
#guard_msgs in
run_meta do
  let info ← Lean.getConstInfo ``LeanTaclet.whileInvariantLexDiamond
  let packed ← `(dl_premise| lexInvariant(inv, ‹metrics›, cond, body))
  let packedKind := packed.raw.getKind
  Lean.Meta.forallTelescope info.type fun _ conclusion => do
    let premise := conclusion.appArg!
    unless premise.isAppOfArity ``LoopLex.diamondPremise 11 do
      throwError "expected the symbolic lexicographic premise"
    let args := premise.getAppArgs
    for (name, i) in [(`k, 3), (`xs, 9), (`hv, 10)] do
      Lean.Meta.withLocalDeclD name (← Lean.Meta.inferType args[i]!) fun shadow => do
        -- Same names and types, different identities: the omitted parameters
        -- would resolve to this later binder if the packed notation escaped.
        let printed ← (Solidity.Delab.ppPremiseS [] premise).run {}
        if printed.any (fun p => p.raw.getKind == packedKind) then
          throwError "packed lexicographic premise captured shadowed {name}"
        -- The actual canonical local remains eligible: reject by identity,
        -- rather than banning the name or every context with duplicate names.
        let canonical := Lean.mkAppN premise.getAppFn (args.set! i shadow)
        let printed ← (Solidity.Delab.ppPremiseS [] canonical).run {}
        unless printed.any (fun p => p.raw.getKind == packedKind) do
          throwError "canonical schema local {name} lost packed notation"
  Lean.logInfo "shadowed schema locals cannot change the packed tuple VC on replay"

#guard !(Solidity.Tools.isRuleLine "dl{ ‹Solidity.LoopLex.diamondPremise› }")

/--
info: all 181 rules of `Solidity.Taclet` print as rule lines
---
info: all 27 rules of `Solidity.LeanTaclet` print as rule lines
---
info: all 4 rules of `Solidity.CallbackTaclet` print as rule lines
-/
#guard_msgs in #check_rule_text

end Solidity.Examples.LexRuleSyntax
