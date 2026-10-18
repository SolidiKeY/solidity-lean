import Solidity.Calculus.LinearDecision

/-!
# The arithmetic decision language, written and printed

`linear!{ [a₀, a₁, …] = c }` is a linear equation over natural variables;
`≤` gives an inequality; `¬`, `∧` and `→` combine these atoms.
Coefficients and constants are integer
terms. This is notation for the solver's arithmetic intermediate language,
not a Solidity formula or an extension of `dl!{ … }`.
-/

namespace Solidity.Linear

private def Lin.parts : Nat → Lin → List String
  | _, [] => []
  | i, a :: as =>
    if a = 0 then Lin.parts (i + 1) as
    else s!"({a})*x{i}" :: Lin.parts (i + 1) as

/-- A linear form in its numbered variables; zero coefficients are omitted. -/
def Lin.pp (a : Lin) : String :=
  match a.parts 0 with
  | [] => "0"
  | parts => String.intercalate " + " parts

/-- Print the complete arithmetic formula, including signed coefficients. -/
def AFml.pp : AFml → String
  | .tt => "true"
  | .ff => "false"
  | .eq a c => s!"({a.pp} = {c})"
  | .le a c => s!"({a.pp} ≤ {c})"
  | .not F => s!"¬{F.pp}"
  | .and F G => s!"({F.pp} ∧ {G.pp})"
  | .imp F G => s!"({F.pp} → {G.pp})"

declare_syntax_cat linear_fml
syntax ident : linear_fml
syntax:50 term:51 " = " term:51 : linear_fml
syntax:50 term:51 " ≤ " term:51 : linear_fml
syntax "(" linear_fml ")" : linear_fml
syntax:40 "¬" linear_fml:40 : linear_fml
syntax:35 linear_fml:36 " ∧ " linear_fml:35 : linear_fml
syntax:25 linear_fml:26 " → " linear_fml:25 : linear_fml
syntax "linear!{" linear_fml "}" : term

macro_rules
  | `(linear!{ true }) => `(AFml.tt)
  | `(linear!{ false }) => `(AFml.ff)
  | `(linear!{ $a:term = $c:term }) => `(AFml.eq $a $c)
  | `(linear!{ $a:term ≤ $c:term }) => `(AFml.le $a $c)
  | `(linear!{ ($F:linear_fml) }) => `(linear!{ $F })
  | `(linear!{ ¬$F:linear_fml }) => `(AFml.not (linear!{ $F }))
  | `(linear!{ $F:linear_fml ∧ $G:linear_fml }) => `(AFml.and (linear!{ $F }) (linear!{ $G }))
  | `(linear!{ $F:linear_fml → $G:linear_fml }) => `(AFml.imp (linear!{ $F }) (linear!{ $G }))

end Solidity.Linear
