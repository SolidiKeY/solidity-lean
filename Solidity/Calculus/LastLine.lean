import Solidity.Calculus.Chains

/-!
# `#last_line`: a chain ends at a last line

A worked chain (`Examples/Chains/`) ends where the printed trace ends: the
program consumed, one parallel update in front of each goal, every read
resolved and every dead capture dropped.  `#last_line chain` checks the end of
the chain named, and is silent when it is one; otherwise one error says what
is left.  Two things are checked:

* **the shape**: no `⟨[ … ]⟩` is left, and no path from the line to a goal
  passes two updates (`{U}{V} φ` wants its `~[sequentialToParallel]~>`), the
  count carried through `∧`, `→`, `havoc` and `∀`;
* **irreducibility**: no rewrite `~=>` tries — the update rules of `rwTable`,
  the term taclets, the laws of memory reads — applies to the line, under
  either modality when the chain is over a modality variable.  "Applies" is
  what `~=>` accepts (`Chain.rwSelect`): a rewrite that computes a line over
  an opaque postcondition but cannot be proved of it does not count, as it
  would not close a `~[…]~>` either.

The check runs on the chain's statement with its binders opened — a modality
`m`, postconditions `φ : Post C`, a premise of the chain — so it reads the
section's `variable`s as `#derivation` does.  A chain that is a segment of a
longer one is not checked; the composed chain is.
-/

namespace Solidity
namespace Chain

open Lean Elab Command Term Meta

/-- The goals of a line, each with the number of updates on the path to it:
through `{U}`, both sides of `∧`, the consequent of `→`, `havoc` and `∀`. -/
partial def goalsOf (e : Expr) (n : Nat) : MetaM (Array (Nat × Expr)) := do
  let e ← instantiateMVars e
  match e.getAppFnArgs with
  | (``Fml.upd, #[_, _, _, ψ]) => goalsOf ψ (n + 1)
  | (``Fml.and, #[_, φ, ψ]) => return (← goalsOf φ n) ++ (← goalsOf ψ n)
  | (``Fml.imp, #[_, _, ψ]) => goalsOf ψ n
  | (``Fml.havoc, #[_, ψ]) => goalsOf ψ n
  | (``Fml.all, #[_, _, _, ψ]) => goalsOf ψ n
  | _ => return #[(n, e)]

/-- What is wrong with the shape of the line, if anything. -/
def shapeProblems (B : Expr) : MetaM (Array MessageData) := do
  let mut out := #[]
  for (n, g) in ← goalsOf B 0 do
    if g.isAppOf ``Fml.modal then
      out := out.push m!"a program is left in front of{indentExpr g}"
    if n ≥ 2 then
      out := out.push m!"{n} updates stand in front of{indentExpr g}\n\
        (one parallel update does: `~[sequentialToParallel]~>`)"
  return out

/-- A storage term holding no write: the state variable, a storage variable, or
a member of one. -/
partial def plainStorage (s : Expr) : Bool :=
  match s.getAppFnArgs with
  | (``STerm.storage, _) | (``STerm.pv, _) => true
  | (``STerm.select, #[_, s, _]) => plainStorage s
  | _ => false

/-- A read of the state as the program found it, `find(storage, p)` or
`find(select(storage, r), p)`: nothing resolves it, and the member-wise laws
that apply to it (`findMemberCons`) only respell it. -/
def plainRead (t : Expr) : Bool :=
  match t.getAppFnArgs with
  | (``Term.find, #[_, s, _]) => plainStorage s
  | _ => false

/-- The rewrites `~=>` would accept on the line `L`, each with the line it
gives: the ones `rwSelect` selects with the line after left open, a law at
every instance but a read of the state as found. -/
def stillApplies (C L : Expr) : TermElabM (Array (String × Expr)) := do
  let mut out := #[]
  for (n, a) in ← rwAnyArrows do
    let st ← saveState
    try
      let (rs, failed) ← rwCandidatesWith (fun t => !plainRead t) C L a
      if rs.isEmpty then
        st.restore
        continue
      let ψ ← mkFreshExprMVar (mkApp (mkConst ``Fml) C)
      let (_, q, _) ← rwSelect C L ψ n rs failed
      let q ← instantiateMVars q
      st.restore
      out := out.push (n, q)
    catch _ =>
      st.restore
  return out

/-- The modality variables of a line. -/
def modalityVars (e : Expr) : MetaM (Array FVarId) := do
  let mut out := #[]
  for x in (collectFVars {} e).fvarIds do
    if (← instantiateMVars (← x.getType)).isConstOf ``Modality then out := out.push x
  return out

/-- `#last_line c`: the chain `c` ends at a last line — no program left, one
parallel update in front of each goal, and no rewrite still applies to it
(under either modality, for a chain over a modality variable).  Silent when
it does; one error listing what is left otherwise. -/
elab "#last_line " c:ident : command => Command.runTermElabM fun _ => do
  let n ← realizeGlobalConstNoOverloadWithInfo c
  let info ← getConstInfo n
  forallTelescope info.type fun _ ty => do
    let ty ← instantiateMVars ty
    let (C, B) ← match ty.getAppFnArgs with
      | (``Fml.Steps, #[C, _, B]) | (``Fml.Leads, #[C, _, B]) => pure (C, B)
      | _ => throwError "#last_line: {c} is no chain: its statement is not `A ~*> B` \
          or `A ~~> B`{indentExpr ty}"
    let B ← instantiateMVars B
    let mut problems ← shapeProblems B
    let ms ← modalityVars B
    if ms.size ≥ 2 then
      throwError "#last_line: the last line of {c} is under two modalities{indentExpr B}"
    let lines : List (Option String × Expr) := match ms[0]? with
      | some m => [(some "under the box", B.replaceFVar (.fvar m) (mkConst ``Modality.box)),
                   (some "under the diamond", B.replaceFVar (.fvar m) (mkConst ``Modality.diamond))]
      | none => [(none, B)]
    -- a line computed at a fixed modality, with `m` put back where it was
    let hasConst (e : Expr) (n : Lean.Name) : Bool := (e.find? (·.isConstOf n)).isSome
    let back (q : Expr) : Expr := match ms[0]? with
      | some m =>
        if hasConst B ``Modality.box || hasConst B ``Modality.diamond then q else
          q.replace fun e =>
            if e.isConstOf ``Modality.box || e.isConstOf ``Modality.diamond then some (.fvar m)
            else none
      | none => q
    let mut found : Array (String × Expr × Array String) := #[]
    for (where?, L) in lines do
      for (r, q) in ← stillApplies C L do
        let q := back q
        let tag := where?.getD ""
        if let some i := found.findIdx? fun (r', q', _) => r' == r && q' == q then
          found := found.modify i fun (r', q', ws) => (r', q', ws.push tag)
        else
          found := found.push (r, q, #[tag])
    for (r, q, ws) in found do
      let note := if ms.isEmpty then m!"" else
        if ws.size == 2 then m!" (under either modality)" else m!" ({ws[0]!})"
      problems := problems.push m!"{r} still applies{note}, and gives{indentExpr q}"
    unless problems.isEmpty do
      throwError "#last_line: {c} does not end at a last line:{indentExpr B}\n\
        {MessageData.joinSep problems.toList "\n"}"

end Chain
end Solidity
