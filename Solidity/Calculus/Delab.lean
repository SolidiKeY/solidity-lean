import Solidity.Calculus.DelabRules
import Solidity.Calculus.Proves

/-!
# Printing sequents

A scoped sequent `Proves C R Γ₀ H φ` as `dl{ ..H, h₁, … ⟹ φ }` (`⟹ₖ` for
solkey's rules alone, `⟹[R]` over a variable rule set), its context's
updates and hypotheses by `Calculus/PrintTerm.lean`'s and
`Calculus/PrintStmt.lean`'s printers.  The taclets, premises and formulas
print by `Calculus/DelabRules.lean`, below the judgement.
-/

namespace Solidity

open Lean Meta PrettyPrinter Delaborator SubExpr
open Solidity (ppOn isEscape fullApp)

namespace Delab

/-! ## Sequents -/

/-- An update `U` of a sequent's context, of pieces `ps`, produced under `m`:
`{U}`, or `{U} [ ]` and `{U} ⟨ ⟩` for a rule's update at a fixed modality;
none where it escapes (it would read back as a precondition). -/
def updHypS (m U : Expr) (ps : Array UPiece) : MetaM (Option (TSyntax `dl_hyp)) := do
  let u ← ppUpdPiecesS U ps
  if Solidity.isEscape u then return none
  if ← updHasSchemaVar U then
    match_expr (← whnf m) with
    | Modality.box => return some (← `(dl_hyp| $u:dl_upd [ ]))
    | Modality.diamond => return some (← `(dl_hyp| $u:dl_upd ⟨ ⟩))
    | _ => pure ()
  return some (← `(dl_hyp| $u:dl_upd))

/-- A sequent's context for the scoped printer: the rest `..H` when it is a
variable, the entries printed (a precondition by `ppFmlS`, an update by
`updHypS`, `{ havoc }`, `∀ T x`, `{ anon(…) }`), and the names of the last
scope.  What prints as nothing: an update of pops only, and the hidden
binder.  An error where an entry does not print. -/
partial def hypsPartsS (c H : Expr) : PrM (Option Lean.Name × Array (TSyntax `dl_hyp) × List Expr) := do
  let H := (← instantiateMVars H).consumeMData
  let unknown (Γ : Expr) : MetaM (List Expr) := do
    return List.replicate ((← ctxLength? Γ).getD 0) unknownVar
  if let .fvar fv := H then
    let ty ← whnfR (← fv.getType)
    return (some (← fv.getDecl).userName, #[], ← unknown (ty.getArg! 2))
  let H ← whnf H
  let args := H.getAppArgs
  match H.getAppFn.constName? with
  | some ``Hyps.nil => return (none, #[], ← unknown args[1]!)
  | some ``Hyps.pre =>
    let (r, hs, ns) ← hypsPartsS c args[3]!
    return (r, hs.push (← `(dl_hyp| $(← ppFmlS ns args[4]!):dl_fml)), ns)
  | some ``Hyps.upd =>
    let (r, hs, ns) ← hypsPartsS c args[4]!
    let U := args[6]!
    let (ps, ms) ← updPiecesS ns U
    if ps.isEmpty then return (r, hs, ms)
    let h ← updHypS args[5]! U ps
    let some h := h | throwError "an entry that does not print"
    return (r, hs.push h, ms)
  | some ``Hyps.havoc =>
    let (r, hs, ns) ← hypsPartsS c args[3]!
    return (r, hs.push (← `(dl_hyp| { havoc })), ns)
  | some ``Hyps.all =>
    let (r, hs, ns) ← hypsPartsS c args[3]!
    let some x ← Solidity.ppVar? args[4]! | throwError "an entry that does not print"
    let some T ← (do pure ((← Solidity.primName? args[5]!) <|> (← Solidity.fvarName? args[5]!)))
      | throwError "an entry that does not print"
    return (r, hs.push (← `(dl_hyp| ∀ $(mkIdent (Name.mkSimple T)):ident $x:ident)), args[4]! :: ns)
  | some ``Hyps.bind =>
    let (r, hs, ns) ← hypsPartsS c args[3]!
    return (r, hs, args[5]! :: ns)
  | some ``Hyps.anon =>
    let (r, hs, ns) ← hypsPartsS c args[3]!
    let some xs ← Solidity.listElems? args[4]! | throwError "anon"
    let xs ← xs.mapM fun x => do idxName ns (← whnf x).appArg!
    let ids ← xs.mapM fun x => (Solidity.ppVar? x : MetaM _)
    if ids.any Option.isNone then throwError "an entry that does not print"
    let ids : Array Ident := ids.filterMap id
    return (r, hs.push (← `(dl_hyp| { anon($ids,*) })), ns)
  | _ => throwError "not a context"

/-- The names of the last scope of a sequent's context `H` (`hypsPartsS`'s,
nothing printed). -/
partial def hypsNamesS (H : Expr) : PrM (List Expr) := do
  let H := (← instantiateMVars H).consumeMData
  let unknown (Γ : Expr) : MetaM (List Expr) := do
    return List.replicate ((← ctxLength? Γ).getD 0) unknownVar
  if let .fvar fv := H then return ← unknown ((← whnfR (← fv.getType)).getArg! 2)
  let H ← whnf H
  let args := H.getAppArgs
  match H.getAppFn.constName? with
  | some ``Hyps.nil => unknown args[1]!
  | some ``Hyps.pre | some ``Hyps.havoc | some ``Hyps.anon => hypsNamesS args[3]!
  | some ``Hyps.upd => return (← updShape (← hypsNamesS args[4]!) args[6]!).2
  | some ``Hyps.all => return args[4]! :: (← hypsNamesS args[3]!)
  | some ``Hyps.bind => return args[5]! :: (← hypsNamesS args[3]!)
  | _ => throwError "not a context"

/-- `Proves C R Γ₀ H φ` as a sequent; none where it does not print. -/
def provesTerm? (e : Expr) : MetaM (Option Lean.Term) := do
  let c := e.getArg! 0
  let R ← whnf (e.getArg! 1)
  let out? ← withPrinter (contract? := some c) e true do
    let some (rest, hs, ns) ← (try some <$> hypsPartsS c (e.getArg! 4) catch _ => pure none)
      | return none
    let φ ← ppFmlS ns (e.getArg! 5)
    let mut out : Array (TSyntax `dl_hyp) := #[]
    if let some r := rest then out := out.push (← `(dl_hyp| ..$(mkIdent r):ident))
    for h in hs do out := out.push ⟨← fixBlockEnds h⟩
    return some (out, (⟨← fixBlockEnds φ⟩ : TSyntax `dl_fml))
  let some (out, φ) := out? | return none
  if isEscape φ then return none
  if R.isConstOf ``RuleSet.all then return some (← `(dl{ $[$out],* ⟹ $φ:dl_fml }))
  else if R.isConstOf ``RuleSet.solkey then return some (← `(dl{ $[$out],* ⟹ₖ $φ:dl_fml }))
  else if let some r ← Solidity.fvarName? R then
    return some (← `(dl{ $[$out],* ⟹[$(Solidity.nameIdent r)] $φ:dl_fml }))
  else return none

/-- `Proves C R Γ₀ H φ`: the sequent `dl{ ..H, h₁, … ⟹ φ }` (`⟹ₖ` for
solkey's rules alone, `⟹[R]` over a variable rule set). -/
@[delab app.Solidity.Proves]
def delabProves : Delab := do
  unless ← ppOn do failure
  let e ← getExpr
  guard (e.getAppNumArgs == 6)
  let some t ← provesTerm? e | failure
  return t

end Delab

end Solidity
