import Solidity.Calculus.SurfaceNotation
import Solidity.Calculus.Delab
import Solidity.Semantics.CtxEquiv.RevertFml

/-!
# Revert data in `dl{ … }` formulas: notation and printers (S6.2)

The surface of `Solidity/Semantics/CtxEquiv/RevertFml.lean`.  A modal
formula followed by `↯` and a data predicate reads a revert's data:

    dl!{ [ revert(hex"01"); ] true ↯ [1] }
    dl!{ ⟨ s; ⟩ false ↯ Error("boom") }

`dl!{ φ ↯ ψ }` (and `dl[C]{ φ ↯ ψ }`) is `RFml.ofModal dl!{ φ } data{ ψ }`:
`φ` is any formula the existing notation reads; when it is a modality
`[ P ] φ'` or `⟨ P ⟩ φ'` the result is `RFml.revModal`, `P` ending
normally in `φ'`, reverting with data satisfying `ψ`.  It prints back as
`dl{ φ ↯ ψ }` (the scoped formulas print as `dl{ … }`, `Calculus/DelabRules.lean`),
and `dl{ φ ↯ ψ }` reads as `dl!{ φ ↯ ψ }`.

Data predicates (`data{ … }`, `DataPred`):

| Written | Meaning |
|---|---|
| `_` | any data |
| `none` | no data at all (no revert reads it) |
| `[b₁, …, bₙ]` | exactly these bytes |
| `Error("m")` | `Error(string)`'s ABI encoding of `m` (`encodeError`) |
| `Error(_)` | any data that decodes as `Error(string)` |
| `Panic(c)` | `Panic(uint256)`'s encoding of `c` |
| `selector [b₁, …]` | data starting with these bytes |
| `¬ ψ`, `ψ ∧ χ`, `ψ ∨ χ`, `(ψ)` | Boolean combinations |

Each printer is an unexpander or delaborator of the constructor it reads.
-/

namespace Solidity

open Lean PrettyPrinter Delaborator SubExpr

/-! ## Data predicates -/

declare_syntax_cat rev_data (behavior := both)
syntax:max "_" : rev_data
syntax:max &"none" : rev_data
syntax:max "[" num,* "]" : rev_data
syntax:max &"Error" "(" str ")" : rev_data
syntax:max &"Error" "(" "_" ")" : rev_data
syntax:max &"Panic" "(" num ")" : rev_data
syntax:max &"selector" " [" num,* "]" : rev_data
syntax:max "¬" rev_data:max : rev_data
syntax:35 rev_data:36 " ∧ " rev_data:35 : rev_data
syntax:30 rev_data:31 " ∨ " rev_data:30 : rev_data
syntax:max "(" rev_data ")" : rev_data

/-- `data{ ψ }`: a predicate on revert data (`DataPred`). -/
syntax "data{ " rev_data " }" : term

/-- The bytes of a string, as numeral syntax. -/
def utf8Nums (s : String) : Array (TSyntax `num) :=
  s.toUTF8.toList.toArray.map fun b => Syntax.mkNumLit (toString b.toNat)

macro_rules
  | `(data{ _ }) => `(DataPred.any)
  | `(data{ none }) => `(DataPred.none)
  | `(data{ [ $xs,* ] }) => do
    let ts : Array Term := xs.getElems.map (⟨·.raw⟩)
    `(DataPred.bytes ([$ts,*] : List UInt8))
  | `(data{ Error( $s:str ) }) => do
    let ts : Array Term := (utf8Nums s.getString).map (⟨·.raw⟩)
    `(DataPred.error ([$ts,*] : List UInt8))
  | `(data{ Error( _ ) }) => `(DataPred.errorAny)
  | `(data{ Panic( $n ) }) => `(DataPred.panic $n)
  | `(data{ selector [ $xs,* ] }) => do
    let ts : Array Term := xs.getElems.map (⟨·.raw⟩)
    `(DataPred.selector ([$ts,*] : List UInt8))
  | `(data{ ¬ $d }) => `(DataPred.not data{ $d })
  | `(data{ $a ∧ $b }) => `(DataPred.and data{ $a } data{ $b })
  | `(data{ $a ∨ $b }) => `(DataPred.or data{ $a } data{ $b })
  | `(data{ ( $d ) }) => `(data{ $d })

/-- The predicate's syntax in parentheses when `wrap` says its operator binds
too loosely for where it stands. -/
def revDataParen (wrap : Bool) (d : TSyntax `rev_data) : UnexpandM (TSyntax `rev_data) :=
  if wrap then `(rev_data| ( $d )) else pure d

def revIsAnd (d : TSyntax `rev_data) : Bool := d.raw[1].isToken "∧"
def revIsOr (d : TSyntax `rev_data) : Bool := d.raw[1].isToken "∨"

/-- Numerals of a printed list literal, if every element is one. -/
def numsOf? (xs : Array Term) : Option (Array (TSyntax `num)) :=
  xs.mapM fun x => if x.raw.isNatLit?.isSome then some ⟨x.raw⟩ else none

@[app_unexpander DataPred.any] def unexpandDataAny : Unexpander
  | `($_) => `(data{ _ })

@[app_unexpander DataPred.bytes] def unexpandDataBytes : Unexpander
  | `($_ [$xs,*]) => do
    let some ns := numsOf? xs.getElems | throw ()
    `(data{ [ $ns,* ] })
  | _ => throw ()

@[app_unexpander DataPred.error] def unexpandDataError : Unexpander
  | `($_ [$xs,*]) => do
    let some ns := numsOf? xs.getElems | throw ()
    let bytes := ns.map fun n => n.getNat.toUInt8
    let some s := String.fromUTF8? (ByteArray.mk bytes) | throw ()
    `(data{ Error( $(Syntax.mkStrLit s):str ) })
  | _ => throw ()

@[app_unexpander DataPred.errorAny] def unexpandDataErrorAny : Unexpander
  | `($_) => `(data{ Error( _ ) })

@[app_unexpander DataPred.panic] def unexpandDataPanic : Unexpander
  | `($_ $n:num) => `(data{ Panic( $n ) })
  | _ => throw ()

@[app_unexpander DataPred.selector] def unexpandDataSelector : Unexpander
  | `($_ [$xs,*]) => do
    let some ns := numsOf? xs.getElems | throw ()
    `(data{ selector [ $ns,* ] })
  | _ => throw ()

@[app_unexpander DataPred.not] def unexpandDataNot : Unexpander
  | `($_ data{ _ }) => `(data{ none })
  | `($_ data{ $d }) => do `(data{ ¬ $(← revDataParen (revIsAnd d || revIsOr d) d) })
  | _ => throw ()

@[app_unexpander DataPred.and] def unexpandDataAnd : Unexpander
  | `($_ data{ $a } data{ $b }) => do
    `(data{ $(← revDataParen (revIsAnd a || revIsOr a) a) ∧ $(← revDataParen (revIsOr b) b) })
  | _ => throw ()

@[app_unexpander DataPred.or] def unexpandDataOr : Unexpander
  | `($_ data{ $a } data{ $b }) => do `(data{ $(← revDataParen (revIsOr a) a) ∨ $b })
  | _ => throw ()

/-! ## Formulas -/

/-- `dl!{ φ ↯ ψ }`: the modality `φ` reading revert data with `ψ`, for the
file's `InContract` contract (`RFml.ofModal`). -/
syntax "dl!{ " dl_fml " ↯ " rev_data " }" : term
/-- `dl[C]{ φ ↯ ψ }`: the same at the contract `C`. -/
syntax "dl[" term "]{ " dl_fml " ↯ " rev_data " }" : term
/-- `dl{ φ ↯ ψ }`, as printed: `dl!{ φ ↯ ψ }`. -/
syntax "dl{ " dl_fml " ↯ " rev_data " }" : term

macro_rules
  | `(dl!{ $φ:dl_fml ↯ $ψ }) => `(RFml.ofModal dl!{ $φ } data{ $ψ })
  | `(dl[ $c ]{ $φ:dl_fml ↯ $ψ }) => `(RFml.ofModal dl[$c]{ $φ } data{ $ψ })
  | `(dl{ $φ:dl_fml ↯ $ψ }) => `(RFml.ofModal dl!{ $φ } data{ $ψ })

/-- Print `φ ↯ ψ` from the modal formula's expression and the predicate's. -/
def ppRev (fm ψ : Expr) : DelabM Term := do
  let φ ← Delab.ppFmlE fm
  guard !(isEscape φ)
  let ψs ← delab ψ
  match ψs with
  | `(data{ $d }) => `(dl{ $φ:dl_fml ↯ $d })
  | _ => failure

/-- `RFml.revModal m P κ φ ψ`: `dl{ [ P ] φ ↯ ψ }`. -/
@[delab app.Solidity.RFml.revModal]
def delabRevModal : Delab := do
  unless ← ppOn do failure
  let e ← getExpr
  guard (e.getAppNumArgs == 9)
  let args := e.getAppArgs
  ppRev (mkAppN (mkConst ``Fml.modal) (args.extract 0 8)) args[8]!

/-- `RFml.ofModal φ ψ`: `dl{ φ ↯ ψ }`. -/
@[delab app.Solidity.RFml.ofModal]
def delabOfModal : Delab := do
  unless ← ppOn do failure
  let e ← getExpr
  guard (e.getAppNumArgs == 4)
  ppRev (e.getArg! 2) (e.getArg! 3)

end Solidity
