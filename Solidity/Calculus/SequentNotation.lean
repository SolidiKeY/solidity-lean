import Solidity.Calculus.Proves
import Solidity.Calculus.RuleSyntax

/-!
# Scoped sequents, as input

`Calculus/Delab.lean` prints a scoped goal `Proves C R Γ₀ H φ` as
the sequent `dl{ ..H, a ⟹[R] φ }`, and the same text reads back as the
scoped judgement (since W9.4 wherever this module is imported; the closer's
sequent is `open scoped Solidity.NFmlSeq`'s, `Calculus/RuleSyntax.lean`), so
a rule of `Proves` (or a goal) can be stated as it prints.  The context is a telescope (`Hyps`), built from the left:
`..H, a, {U} [ ]` is `((H.pre a).upd .box U)`, and with no `..H` it starts
at `Hyps.nil`.

The sequent reads its entries and formulas as **schema variables and
connectives**, the shapes `Proves`'s rules are written in: a name is a
Lean variable (a `Fml`, a `Upd`, a statement, a block), `‹t›` a
Lean term; `true`, `false`, `¬`, `∧`, `→`, `{U} φ`, `{ havoc } φ`, and a
modality whose program is statements and a rest `..ω`, its frames empty.
A formula over the program's own syntax (`balances[a] == 1`) is not a
schema: it is read by `cdl!{ … }` (`Calculus/Notation.lean`), whose
parameters the sequent's names cannot bind.

| Entry | Is |
|---|---|
| `..H` (first) | the rest of the context, `H : Hyps C Γ₀ Γ` |
| `a` | `Hyps.pre` |
| `{U}`, `{U} [ ]`, `{U} ⟨ ⟩` | `Hyps.upd`, under the rule's `m`, the box, the diamond |
| `∀ T x` | `Hyps.all` |
| `{ havoc }`, `{ anon(xs) }` | `Hyps.havoc`, `Hyps.anon` |

The arrows are today's: `⟹` (`.all`), `⟹ₖ` (`.solkey`), `⟹[R]`.
-/

namespace Solidity.Sequent

open Lean (Macro MacroM mkIdent TSyntax)

/-- An update of a scoped sequent: one schema variable, or a Lean term. -/
def seqUpd (U : TSyntax `dl_upd) : MacroM Lean.Term := do
  if let `(dl_upd| ‹ $t:term ›) := U then return t
  let es := U.raw[1].getSepArgs
  if h : es.size = 1 then
    if let `(dl_upd_elem| $x:ident) := (⟨es[0]⟩ : TSyntax `dl_upd_elem) then return x
  Macro.throwErrorAt U "a scoped sequent's update is a schema variable `{U}` or a term `‹t›`"

/-- A block of a scoped modality: its statements (schema variables) before
the rest `ω`, as `Prog.cons`. -/
def seqProg (ss : Array (TSyntax `sol_stmt)) (ω : Option Lean.Term) : MacroM Lean.Term := do
  let tail ← match ω with
    | some ω => pure ω
    | none => `(Prog.nil)
  ss.foldrM (init := tail) fun (s : TSyntax `sol_stmt) acc => do
    let x := if s.raw.isIdent then s.raw else s.raw[0]!
    unless x.isIdent do Macro.throwErrorAt s "a scoped sequent's statement is a schema variable"
    `(Prog.cons $(⟨x⟩) $acc)

/-- A formula of a scoped sequent (`Fml`), from schema variables and
connectives. -/
partial def seqFml : TSyntax `dl_fml → MacroM Lean.Term
  | `(dl_fml| true) => `(Fml.tt)
  | `(dl_fml| false) => `(Fml.ff)
  | `(dl_fml| ‹ $t:term ›) => pure t
  | `(dl_fml| $x:ident) => pure x
  | `(dl_fml| ( $φ:dl_fml )) => seqFml φ
  | `(dl_fml| ¬ $φ:dl_fml) => do `(Fml.not $(← seqFml φ))
  | `(dl_fml| $φ:dl_fml ∧ $ψ:dl_fml) => do `(Fml.and $(← seqFml φ) $(← seqFml ψ))
  | `(dl_fml| $φ:dl_fml → $ψ:dl_fml) => do `(Fml.imp $(← seqFml φ) $(← seqFml ψ))
  | `(dl_fml| { havoc } $φ:dl_fml) => do `(Fml.havoc $(← seqFml φ))
  | `(dl_fml| $U:dl_upd $φ:dl_fml) => do
    `(Fml.upd $(mkIdent `m) $(← seqUpd U) $(← seqFml φ))
  | `(dl_fml| ⟨[ $[$ss:sol_stmt;]* ]⟩ $φ:dl_fml) => do
    `(Fml.modal $(mkIdent `m) $(← seqProg ss none) Frames.nil $(← seqFml φ))
  | `(dl_fml| ⟨[ $[$ss:sol_stmt;]* .. $ω:term ]⟩ $φ:dl_fml) => do
    `(Fml.modal $(mkIdent `m) $(← seqProg ss (some ω)) Frames.nil $(← seqFml φ))
  | `(dl_fml| [ $[$ss:sol_stmt;]* ] $φ:dl_fml) => do
    `(Fml.modal .box $(← seqProg ss none) Frames.nil $(← seqFml φ))
  | `(dl_fml| [ $[$ss:sol_stmt;]* .. $ω:term ] $φ:dl_fml) => do
    `(Fml.modal .box $(← seqProg ss (some ω)) Frames.nil $(← seqFml φ))
  | `(dl_fml| ⟨ $[$ss:sol_stmt;]* ⟩ $φ:dl_fml) => do
    `(Fml.modal .diamond $(← seqProg ss none) Frames.nil $(← seqFml φ))
  | `(dl_fml| ⟨ $[$ss:sol_stmt;]* .. $ω:term ⟩ $φ:dl_fml) => do
    `(Fml.modal .diamond $(← seqProg ss (some ω)) Frames.nil $(← seqFml φ))
  | φ => Macro.throwErrorAt φ
      "not a scoped sequent's formula (schema variables and connectives; `cdl!{ … }` reads a program's)"

/-- One entry of a scoped sequent's context, joined to `acc`. -/
def seqHyp (acc : Lean.Term) : TSyntax `dl_hyp → MacroM Lean.Term
  | `(dl_hyp| { havoc }) => `(Hyps.havoc $acc)
  | `(dl_hyp| { anon($xs:ident,*) }) => do
    let ts : Array Lean.Term := xs.getElems.map fun x => ⟨x.raw⟩
    `(Hyps.anon $acc [$ts,*])
  | `(dl_hyp| $U:dl_upd [ ]) => do `(Hyps.upd $acc .box $(← seqUpd U))
  | `(dl_hyp| $U:dl_upd ⟨ ⟩) => do `(Hyps.upd $acc .diamond $(← seqUpd U))
  | `(dl_hyp| $U:dl_upd) => do `(Hyps.upd $acc $(mkIdent `m) $(← seqUpd U))
  | `(dl_hyp| ∀ $T:ident $x:ident) => do `(Hyps.all $acc $x $(← Solidity.schemaPrim T))
  | stx@`(dl_hyp| .. $_:term) => Macro.throwErrorAt stx "`..H`, the rest of the context, comes first"
  | `(dl_hyp| $φ:dl_fml) => do `(Hyps.pre $acc $(← seqFml φ))
  | _ => Macro.throwUnsupported

/-- A scoped context: `..H, h₁, …` built on `H`, or on `Hyps.nil`. -/
def seqHyps (hs : Array (TSyntax `dl_hyp)) : MacroM Lean.Term := do
  if let some (h : TSyntax `dl_hyp) := hs[0]? then
    if let `(dl_hyp| .. $H:term) := h then
      return ← (hs.extract 1 hs.size).foldlM seqHyp H
  hs.foldlM seqHyp (← `(Hyps.nil))

macro_rules
  | `(dl{ $[$hs:dl_hyp],* ⟹ $φ:dl_fml }) => do
    `(Proves _ .all _ $(← seqHyps hs) $(← seqFml φ))
  | `(dl{ $[$hs:dl_hyp],* ⟹ₖ $φ:dl_fml }) => do
    `(Proves _ .solkey _ $(← seqHyps hs) $(← seqFml φ))
  | `(dl{ $[$hs:dl_hyp],* ⟹[ $R:term ] $φ:dl_fml }) => do
    `(Proves _ $R _ $(← seqHyps hs) $(← seqFml φ))

end Solidity.Sequent
