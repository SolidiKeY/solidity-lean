import Solidity.Calculus.CallFunctionSearch
import Solidity.Calculus.CallFunctionTransform
import Solidity.Calculus.CallSummary
import Solidity.Calculus.Closer.Bytes
import Solidity.Calculus.Closer.Facts
import Solidity.Calculus.Closer.Leaf
import Solidity.Calculus.CondLift
import Solidity.Calculus.Decide
import Solidity.Calculus.DecideCleanTail
import Solidity.Calculus.DecideLang
import Solidity.Calculus.DecideScoped
import Solidity.Calculus.ElimFacts
import Solidity.Calculus.FirstOrder
import Solidity.Calculus.Lands
import Solidity.Calculus.LeafDerive
import Solidity.Calculus.MemRead.Pass
import Solidity.Calculus.MemRead.Spine
import Solidity.Calculus.MemoryWitness
import Solidity.Calculus.Proves
import Solidity.Calculus.ReadBounds
import Solidity.Calculus.RewritePast.Merge
import Solidity.Calculus.RewriteSyntax
import Solidity.Calculus.Rigid
import Solidity.Calculus.RuleShapes
import Solidity.Calculus.SeqRewrite
import Solidity.Calculus.StatePartsScoped
import Solidity.Calculus.Step
import Solidity.Calculus.Symex
import Solidity.Calculus.TermEq
import Solidity.Calculus.TermEval
import Solidity.Calculus.UpdRuleScoped
import Solidity.Evm.Machine
import Solidity.Evm.MemoryLoopScopeCompile
import Solidity.Evm.MemoryLoopScopeMeta
import Solidity.Evm.MemoryRecursiveCert
import Solidity.Evm.MemoryRecursiveCompile
import Solidity.Evm.MemoryRecursiveRoom
import Solidity.Frontend.QualifiedUnits.References
import Solidity.Semantics.Run
import Solidity.Semantics.RunAccel
import Solidity.Semantics.RunFuel
import Solidity.Semantics.Storage.Ops
import Solidity.Semantics.Storage.Values
import Solidity.Signature
import Solidity.Syntax.Elab.Context
import Solidity.Syntax.Elab.Values
import Solidity.Syntax.Quote
import Solidity.Tools.Counterexample
import Solidity.Yul.Views.RetainedEntryPaths
import Solidity.Yul.Views.RetainedLocationRun
import Solidity.Yul.Views.RetainedRuntimePaths
import Lean

/-! Gate G0 link audit. Guards against missing, reflexive or premise-only
"links": an accepted theorem concludes equality of the two distinct constant
heads applied to exactly the telescope variables, up to binder reordering, with no fixed
arguments or restricted expressions. A theorem requiring an extra False/equality premise is rejected.
Unsafe memo twins and extern implementations without such a logical link stay
missing; this checker never treats their compiler attributes as kernel edges. -/
open Lean Meta Elab Command

private def links (a b : Name) (type : Expr) (params : List Name) : MetaM Bool := do
  let leftInfo ← getConstInfo a
  let rightInfo ← getConstInfo b
  forallTelescope type fun xs result => do
    let some (_, lhs, rhs) := result.eq? | return false
    let valid (l r : Expr) :=
      match l.getAppFn, r.getAppFn with
      | .const ln ls, .const rn rs =>
        ln == a && rn == b && ls == rs &&
        ls.length == leftInfo.levelParams.length &&
        ls.length == rightInfo.levelParams.length && ls.length == params.length &&
        params.all (fun p => ls.contains (.param p)) &&
        ls.all (fun level => match level with | .param p => params.contains p | _ => false) &&
        l.getAppArgs == r.getAppArgs && l.getAppArgs.size == xs.size &&
        xs.all (fun x => l.getAppArgs.contains x)
      | _, _ => false
    return valid lhs rhs || valid rhs lhs

private def controlLeft (n : Nat) : Nat := n
private def controlTwin (n : Nat) : Nat := n
private def controlBad (n : Nat) : Nat := if n = 0 then 0 else n + 1
private theorem controlUniversal (n : Nat) : controlLeft n = controlTwin n := rfl
private theorem controlClosed : controlLeft 0 = controlBad 0 := rfl
private theorem controlRestricted (n : Nat) : controlLeft (n - n) = controlBad (n - n) := by
  simp only [Nat.sub_self, controlLeft, controlBad, ↓reduceIte]
private theorem controlPremise (n : Nat) (h : False) : controlLeft n = controlBad n :=
  False.elim h

private def controlBinary (a b : Nat) : Nat := a + b
private def controlBinaryTwin (a b : Nat) : Nat := a + b
private theorem controlPermuted (b a : Nat) : controlBinary a b = controlBinaryTwin a b := rfl

-- Binder ordering does not restrict a universally quantified equality.
run_elab do
  let info ← getConstInfo ``controlPermuted
  unless ← links ``controlBinary ``controlBinaryTwin info.type info.levelParams do
    throwError "universally quantified binder permutation was rejected"

universe u
private def controlULeft {α : Sort u} (a _b : α) : α := a
private def controlUTwin {α : Sort u} (a _b : α) : α := a
private def controlUBad {α : Sort u} (_a b : α) : α := b
private theorem controlUAll {α : Sort u} (a b : α) : controlULeft a b = controlUTwin a b := rfl
private theorem controlUProp (α : Prop) (a b : α) : controlULeft a b = controlUBad a b :=
  Subsingleton.elim _ _

-- Regression: equality only at universe zero is not a polymorphic link.
run_elab do
  for (candidate, right, expected) in [(``controlUAll, ``controlUTwin, true),
      (``controlUProp, ``controlUBad, false)] do
    let info ← getConstInfo candidate
    let actual ← links ``controlULeft right info.type info.levelParams
    unless actual == expected do throwError "universe link control failed: {candidate}"

-- Guards against one-point, restricted-domain and extra-premise fake links.
run_elab do
  for (candidate, right, expected) in [
      (``controlUniversal, ``controlTwin, true),
      (``controlClosed, ``controlBad, false),
      (``controlRestricted, ``controlBad, false),
      (``controlPremise, ``controlBad, false)] do
    let info ← getConstInfo candidate
    let actual ← links ``controlLeft right info.type info.levelParams
    unless actual == expected do throwError "link control failed: {candidate}"

run_elab do
  let env ← getEnv
  let constants := env.constants.toList
  let mut overridden : NameSet := {}
  for (n, _) in constants do
    if (Lean.Compiler.getImplementedBy? env n).isSome then overridden := overridden.insert n
  let mut candidates : Std.HashMap Name (Array (Name × Expr)) := {}
  for (t, info) in constants do
    unless info matches .thmInfo _ do continue
    for n in info.type.getUsedConstants do
      if overridden.contains n then
        candidates := candidates.insert n ((candidates[n]?).getD #[] |>.push (t, info.type))
  let mut rows : Array Json := #[]
  for (n, declarationInfo) in constants do
    let some i := env.getModuleIdxFor? n | continue
    let module := env.header.moduleNames[i.toNat]!.toString
    unless module == "Solidity" || module.startsWith "Solidity." do continue
    let twin := Lean.Compiler.getImplementedBy? env n
    let external := (getExternAttrData? env n).isSome
    unless twin.isSome || external do continue
    let mut found : Array String := #[]
    if let some b := twin then
      for (t, type) in (candidates[n]?).getD #[] do
        unless type.getUsedConstants.contains b do continue
        if ← links n b type (← getConstInfo t).levelParams then
          let axioms ← collectAxioms t
          unless axioms.all (fun a => [``propext, ``Classical.choice, ``Quot.sound].contains a) do
            throwError "nonstandard axiom in link {t}"
          found := found.push t.toString
    rows := rows.push <| Json.mkObj [
      ("declaration", toJson n.toString), ("module", toJson module),
      ("implementation", toJson (twin.map Name.toString)),
      ("extern", toJson external), ("links", toJson found),
      ("opaque", toJson (declarationInfo matches .opaqueInfo _)),
      ("unsafe", toJson declarationInfo.isUnsafe),
      ("implementationUnsafe", toJson (twin.any (fun t => (env.find? t).any ConstantInfo.isUnsafe)))]
  if rows.isEmpty then throwError "empty escape-hatch inventory"
  liftM <| IO.println <| "TRUST_IMPLEMENTED_BY_JSON=" ++ (Json.arr rows).compress
