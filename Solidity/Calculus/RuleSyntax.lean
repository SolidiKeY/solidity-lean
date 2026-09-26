import Solidity.Update

/-!
# The paper's notation: `dl{ … }`

The calculus is written and read as the paper writes it (mini-solkey's
`Notation.lean`).  A taclet is one line,

```
storageFieldWriteSave :
  dl{ ⟨[ sp.fld = se; ]⟩ ⇝ { storage := save(storage, sp.fld, se) } ⟨[ ]⟩ }
```

and a goal prints as the line of the derivation it is.  `set_option
pp.sol.dl false` shows the constructors again.

| notation | term |
|---|---|
| `dl_schema{ φ }` | a formula whose names are Lean variables (schema variables) |
| `dl{ ⟨[ s; ]⟩ ⇝ p }` | the taclet `Taclet C k m s p`, for either modality (solkey's `#mod`) |
| `dl{ [ s; ] ⇝ p }`, `dl{ ⟨ s; ⟩ ⇝ p }` | a taclet for the box only, the diamond only |
| `dl{ p }` | a premise |
| `⊨ φ` | `Valid φ` |

## Names are schema variables, and a name carries its kind

In a taclet every identifier is a Lean variable, bound by the constructor
(an auto-bound implicit), and what it stands for is read off its name with
trailing digits and subscripts dropped — the paper's device, so no rule
needs an `\is…` side condition to say what its variables are:

| name | is | Lean sort |
|---|---|---|
| `v`, `lv`, `vp` | a stack local | `Var` |
| `lsv` | a storage alias | `Var` |
| `mv` | a memory local | `Var` |
| `gsp` | a state variable, with its proof `hgsp` | `Name` |
| `se`, `ie`, `sadr` | a simple value | `Simple C p` |
| `e`, `nse`, `nadr` | a value | `Val C p` |
| `sp`, `nsp`, `path`, `map`, `arr` | a storage path (`map`/`arr` fix how it is indexed) | `SPath C T` |
| `nmp`, `mpath` | a memory path | `MPath C T` |
| `fld`, `fr`, with its proof `hfld`, `hfr` | a member name | `Name` |
| `lhs` | where a storage or memory read lands (`Hole`, `MHole`) | |
| `x` | where a value lands (`VHole`) | |
| `nlhs` | a member or entry a copy lands in | `Loc C T` |
| `l` | the target of `⊕=` and `++` | `OpLoc C p` |

The position says which sort an operand is read at: `sp.fld` is a location
left of `=`, a value right of it, a path under `delete`.  A copy is a write
whose right-hand side is a path (`gsp = sp`, `sp1.fld = sp2`); a write whose
right-hand side is a value (`se`, `nse`, `e`) stores it.  `⊕` is an
operator schema variable `op` (`⊖` a unary one, `⊕⊕` an increment or
decrement), with its proofs.  A declaration binds its name for the
statements after it; in a taclet's `\replacewith` a declared `se`, `sp`,
`ie`, `mv` is **fresh**, `seV k` and the like (KeY's `\newLocalVars`).

`‹t›` puts any Lean term in any position.
-/

namespace Solidity

/-! ## Grammar -/

/-- Terms of the logic.  `f(…)` is read by its head: `select`, `find`,
`store`, `save`, `delAt`, `write`, `read`, `addM`, `copySt`, `copyMem`,
`freshId`. -/
declare_syntax_cat dl_term
syntax:max num : dl_term
syntax:max ident : dl_term
syntax:max dl_term:max "." ident : dl_term
syntax:max dl_term:max "[" dl_term "]" : dl_term
syntax:max ident noWs "(" dl_term,* ")" : dl_term
syntax:65 dl_term:65 " ⊕ " dl_term:66 : dl_term
syntax:65 dl_term:65 " + " dl_term:66 : dl_term
/-- A unary operator schema variable `op`, applied. -/
syntax:80 "⊖" dl_term:80 : dl_term
/-- `t ± 1`: the increment or decrement schema variable `op`, as arithmetic. -/
syntax:65 dl_term:65 " ± " dl_term:66 : dl_term
/-- The value `t⊕⊕` has: the new one for `++t`, the old one for `t++`. -/
syntax:max dl_term:max "⊕⊕" : dl_term
syntax:65 dl_term:65 " - " dl_term:66 : dl_term
syntax:max "(" dl_term ")" : dl_term
syntax:max "‹" term "›" : dl_term

/-- One elementary update `x := t`, or `transfer(r, a)`. -/
declare_syntax_cat dl_upd_elem (behavior := both)
syntax dl_term " := " dl_term : dl_upd_elem
syntax &"transfer" "(" dl_term ", " dl_term ")" : dl_upd_elem

/-- A parallel update `{ a ‖ b }`. -/
declare_syntax_cat dl_upd (behavior := both)
syntax "{ " sepBy1(dl_upd_elem, " ‖ ") " }" : dl_upd
syntax "‹" term "›" : dl_upd

declare_syntax_cat dl_fml (behavior := both)
syntax:max &"true" : dl_fml
syntax:max &"false" : dl_fml
syntax:50 dl_term:51 " = " dl_term:51 : dl_fml
syntax:max "¬" dl_fml:50 : dl_fml
syntax:35 dl_fml:36 " ∧ " dl_fml:35 : dl_fml
syntax:25 dl_fml:26 " → " dl_fml:25 : dl_fml
syntax:max dl_upd ppSpace dl_fml:50 : dl_fml
/-- The diamond: `P` runs to the end, and `φ` holds after. -/
syntax:max "⟨ " (sol_stmt "; ")* "⟩ " dl_fml:50 : dl_fml
/-- The box: if `P` runs to the end, `φ` holds after. -/
syntax:max "[ " (sol_stmt "; ")* "] " dl_fml:50 : dl_fml
/-- Either modality, the paper's `⟨[ P ]⟩ φ` (solkey's `#mod`), in a taclet. -/
syntax:max "⟨" "[ " (sol_stmt "; ")* "]" "⟩ " dl_fml:50 : dl_fml
/-- A modality over a program that is a schema variable. -/
syntax:max "⟨ " sol_block " ⟩ " dl_fml:50 : dl_fml
syntax:max "[ " sol_block " ] " dl_fml:50 : dl_fml
syntax:max "(" dl_fml ")" : dl_fml
syntax:max "‹" term "›" : dl_fml
/-- A comparison of program values, as in Solidity: `alice.age == 10` is
`find(storage, alice.age) = 10`. -/
syntax:55 dl_term:56 " == " dl_term:56 : dl_fml
syntax:55 dl_term:56 " != " dl_term:56 : dl_fml
syntax:50 dl_fml:55 " && " dl_fml:50 : dl_fml

/-- What a taclet leaves: an update in front of the rest, statements, two
goals (a branch, each with its condition), or — for a revert — `true` or
`false` in place of the whole modality.  The modality of the premise is the
taclet's own, so it is written `⟨[ ]⟩`. -/
declare_syntax_cat dl_premise (behavior := both)
syntax dl_upd " ⟨" "[ " "]" "⟩" : dl_premise
syntax "⟨" "[ " (sol_stmt "; ")* "]" "⟩" : dl_premise
syntax dl_fml " ⟹ " "⟨" "[ " sol_block " ]" "⟩" " ; " dl_fml " ⟹ " "⟨" "[ " sol_block " ]" "⟩" :
  dl_premise
syntax dl_fml " ⟹ " "⟨" "[ " (sol_stmt "; ")* "]" "⟩" " ; "
  dl_fml " ⟹ " "⟨" "[ " (sol_stmt "; ")* "]" "⟩" : dl_premise
syntax &"true" : dl_premise
syntax &"false" : dl_premise

/-- An entry of a sequent's context: an update or a precondition. -/
declare_syntax_cat dl_hyp (behavior := both)
syntax dl_upd : dl_hyp
syntax dl_fml : dl_hyp

/-- A formula whose names are Lean variables. -/
syntax "dl_schema{ " dl_fml " }" : term
/-- A sequent `Γ ⟹ φ`. -/
syntax "dl{ " sepBy(dl_hyp, ", ") " ⟹ " dl_fml " }" : term
/-- A taclet for either modality (the paper's `⟨[ s; ]⟩`). -/
syntax "dl{ " "⟨" "[ " sol_stmt "; " "]" "⟩" " ⇝ " dl_premise " }" : term
/-- A taclet for the box only. -/
syntax "dl{ " "[ " sol_stmt "; " "]" " ⇝ " dl_premise " }" : term
/-- A taclet for the diamond only. -/
syntax "dl{ " "⟨ " sol_stmt "; " "⟩" " ⇝ " dl_premise " }" : term
syntax "dl{ " dl_premise " }" : term
/-- `⊨ φ` for a formula given as a Lean term. -/
syntax:25 "⊨ " term:26 : term
/-- A statement standing alone, as the printers show one. -/
syntax "stmt{ " sol_stmt "; " "}" : term

macro_rules
  | `(⊨ $φ:term) => `(Solidity.Valid $φ)

/-! ## Reading schemas (macros) -/

section Expand
open Lean (Ident Macro MacroM mkIdent mkIdentFrom Name TSyntax Syntax)

/-- The kind a name's spelling gives it: `sp2` and `sp₂` are `sp`. -/
def stemOf (s : String) : String :=
  let t := s.dropRightWhile fun c => c.isDigit || ('₀' ≤ c && c ≤ '₉') || c == '\''
  if t.isEmpty then s else t

/-- A name a declaration to the left bound. -/
inductive Decl where
  | val (x : Lean.Term)
  | alias (x : Lean.Term)
  | mem (x : Lean.Term)

abbrev Scope := List (String × Decl)

/-- A variable named `s`, resolved where the notation is used. -/
def schemaIdent (s : String) : Ident := mkIdent (Name.mkSimple s)

/-- The part `s` of the dotted name `x`, on its own characters. -/
def partIdent (x : Ident) (s : String) : Ident := Id.run do
  let .original _ pos _ _ := x.raw.getHeadInfo | return mkIdentFrom x (Name.mkSimple s)
  let parts := nameParts x.getId
  let some i := parts.idxOf? s | return mkIdentFrom x (Name.mkSimple s)
  let off := (parts.take i).foldl (fun n p => n + p.utf8ByteSize + 1) 0
  let start : String.Pos := ⟨pos.byteIdx + off⟩
  let stop : String.Pos := ⟨start.byteIdx + s.utf8ByteSize⟩
  let info := Lean.SourceInfo.original "".toSubstring start "".toSubstring stop
  return ⟨Syntax.ident info s.toSubstring (Name.mkSimple s) []⟩

/-- The proof that comes with a name: `hgsp` for `gsp`, `hfld` for `fld`. -/
def proofIdent (x : Ident) (s : String) : Ident := mkIdentFrom x (Name.mkSimple ("h" ++ s))

/-- The sort a program position asks for. -/
inductive Pos where
  | val | simple | spath | loc | mpath | mloc | oploc
  deriving DecidableEq

def Pos.name : Pos → String
  | .val => "a value" | .simple => "a simple value" | .spath => "a storage path"
  | .loc => "a storage location" | .mpath => "a memory path" | .mloc => "a memory location"
  | .oploc => "a compound-assignment target"

def posError (x : Lean.Syntax) (what : String) (pos : Pos) : MacroM α :=
  Macro.throwErrorAt x s!"{what} cannot stand where {pos.name} is expected"

/-- What a name is, by its stem (or its declaration in scope). -/
inductive Head where
  | local (x : Lean.Term) | alias (x : Lean.Term) | mem (x : Lean.Term)
  | root (x h : Lean.Term) | simple (x : Lean.Term) | val (x : Lean.Term)
  | spath (x : Lean.Term) | mpath (x : Lean.Term) | loc (x : Lean.Term) | mloc (x : Lean.Term)
  | other (x : Lean.Term)

def headOf (Γ : Scope) (x : Ident) : Head :=
  let s := x.getId.toString
  match Γ.lookup s with
  | some (.val v) => .local v
  | some (.alias v) => .alias v
  | some (.mem v) => .mem v
  | none => match stemOf s with
    | "v" | "lv" | "vp" => .local x
    | "lsv" => .alias x
    | "mv" => .mem x
    | "gsp" => .root x (proofIdent x s)
    | "se" | "ie" | "sadr" => .simple x
    | "e" | "nse" | "nadr" => .val x
    | "sp" | "nsp" | "path" | "map" | "arr" => .spath x
    | "nmp" | "mpath" => .mpath x
    | "nlhs" | "loc" => .loc x
    | "mloc" => .mloc x
    | _ => .other x

/-- A head at a position. -/
def headAt (pos : Pos) (stx : Lean.Syntax) : Head → MacroM Lean.Term
  | .local v => match pos with
    | .val => `(Val.simple (Simple.local $v))
    | .simple => `(Simple.local $v)
    | .oploc => `(OpLoc.local $v)
    | _ => posError stx "a stack local" pos
  | .alias v => match pos with
    | .spath => `(SPath.alias $v)
    | _ => posError stx "a storage alias" pos
  | .mem v => match pos with
    | .mpath => `(MPath.var $v)
    | _ => posError stx "a memory local" pos
  | .root r h => match pos with
    | .loc => `(Loc.root $r $h)
    | .spath => `(SPath.loc (Loc.root $r $h))
    | .val => `(Val.read (Loc.root $r $h))
    | .oploc => `(OpLoc.root $r $h)
    | _ => posError stx "a state variable" pos
  | .simple x => match pos with
    | .val => `(Val.simple $x)
    | .simple => pure x
    | _ => posError stx "a simple value" pos
  | .val x => match pos with
    | .val => pure x
    | _ => posError stx "a value" pos
  | .spath x => match pos with
    | .spath => pure x
    | _ => posError stx "a storage path" pos
  | .mpath x => match pos with
    | .mpath => pure x
    | _ => posError stx "a memory path" pos
  | .loc x => match pos with
    | .loc => pure x
    | .spath => `(SPath.loc $x)
    | .val => `(Val.read $x)
    | _ => posError stx "a storage location" pos
  | .mloc x => match pos with
    | .mloc => pure x
    | .mpath => `(MPath.loc $x)
    | .val => `(Val.readMem $x)
    | _ => posError stx "a memory location" pos
  | .other x => pure x

/-- Whether an expression is a memory path: its head is a memory local or a
memory path variable. -/
partial def isMem (Γ : Scope) : TSyntax `sol_expr → Bool
  | `(sol_expr| $x:ident) =>
    match nameParts x.getId with
    | h :: _ => match headOf Γ (mkIdent (Name.mkSimple h)) with
      | .mem _ | .mpath _ | .mloc _ => true
      | _ => false
    | [] => false
  | `(sol_expr| $e:sol_expr . $_:ident) => isMem Γ e
  | `(sol_expr| $e:sol_expr [ $_:sol_expr ]) => isMem Γ e
  | `(sol_expr| ( $e:sol_expr )) => isMem Γ e
  | _ => false

/-- Whether a write's right-hand side is a path to copy: its head is a path
variable (`sp`, `nsp`, `path`, `map`, `arr`, an alias).  A value's head is a
value variable (`se`, `nse`, `e`), a local, or a literal. -/
partial def isPath (Γ : Scope) : TSyntax `sol_expr → Bool
  | `(sol_expr| $x:ident) =>
    match nameParts x.getId with
    | h :: _ => match headOf Γ (mkIdent (Name.mkSimple h)) with
      | .spath _ | .alias _ => true
      | _ => false
    | [] => false
  | `(sol_expr| $e:sol_expr . $_:ident) => isPath Γ e
  | `(sol_expr| $e:sol_expr [ $_:sol_expr ]) => isPath Γ e
  | `(sol_expr| ( $e:sol_expr )) => isPath Γ e
  | _ => false

/-- A whole right-hand side that is a schema variable: `src`, `rhs`, `mrhs`,
`msrc`. -/
def rhsVar? (stem : String) : TSyntax `sol_expr → Option Ident
  | `(sol_expr| $x:ident) => if stemOf x.getId.toString == stem then some x else none
  | _ => none

/-- How a storage receiver is indexed: `map[ie]` by key, `arr[ie]` by
position, anything else by the schema variable `it`. -/
def indexTyOf : TSyntax `sol_expr → MacroM Lean.Term
  | `(sol_expr| $x:ident) =>
    match stemOf x.getId.toString with
    | "map" => `(IndexTy.map)
    | "arr" => `(IndexTy.arr)
    | _ => pure (schemaIdent "it")
  | _ => pure (schemaIdent "it")

mutual

/-- `b.f` at `pos`: a storage or a memory member. -/
partial def fieldAt (Γ : Scope) (pos : Pos) (stx : Lean.Syntax) (mem : Bool) (b : Lean.Term)
    (f : Ident) : MacroM Lean.Term := do
  let h := proofIdent f f.getId.toString
  if mem then
    match pos with
    | .mloc => `(MLoc.field $b $f $h)
    | .mpath => `(MPath.loc (MLoc.field $b $f $h))
    | .val => `(Val.readMem (MLoc.field $b $f $h))
    | .oploc => `(OpLoc.mfield $b $f $h)
    | _ => posError stx "a memory member" pos
  else
    match pos with
    | .loc => `(Loc.field $b $f $h)
    | .spath => `(SPath.loc (Loc.field $b $f $h))
    | .val => `(Val.read (Loc.field $b $f $h))
    | .oploc => `(OpLoc.field $b $f $h)
    | _ => posError stx "a storage member" pos

/-- `b.f₁.….fₙ`: the inner members are receivers. -/
partial def fieldsAt (Γ : Scope) (pos : Pos) (stx : Lean.Syntax) (mem : Bool) (b : Lean.Term) :
    List Ident → MacroM Lean.Term
  | [] => pure b
  | [f] => fieldAt Γ pos stx mem b f
  | f :: fs => do fieldsAt Γ pos stx mem (← fieldAt Γ (if mem then .mpath else .spath) stx mem b f) fs

/-- A program expression at the sort `pos`. -/
partial def schemaAt (Γ : Scope) (pos : Pos) : TSyntax `sol_expr → MacroM Lean.Term
  | stx@`(sol_expr| $n:num) => match pos with
    | .val => `(Val.simple (Simple.lit $n rfl))
    | .simple => `(Simple.lit $n rfl)
    | _ => posError stx "a number" pos
  | stx@`(sol_expr| $x:ident) => do
    match nameParts x.getId with
    | [] => Macro.throwError "empty identifier"
    | ["true"] | ["false"] =>
      let b ← if x.getId.toString == "true" then `(true) else `(false)
      match pos with
      | .val => `(Val.simple (Simple.bool $b))
      | .simple => `(Simple.bool $b)
      | _ => posError stx "a Boolean" pos
    | [_] => headAt pos x (headOf Γ x)
    | h :: fs =>
      let hx := partIdent x h
      let mem := match headOf Γ hx with
        | .mem _ | .mpath _ | .mloc _ => true
        | _ => false
      let b ← headAt (if mem then .mpath else .spath) x (headOf Γ hx)
      fieldsAt Γ pos stx mem b (fs.map (partIdent x))
  | stx@`(sol_expr| $e:sol_expr . $f:ident) => do
    let mem := isMem Γ e
    fieldsAt Γ pos stx mem (← schemaAt Γ (if mem then .mpath else .spath) e)
      ((nameParts f.getId).map (partIdent f))
  | stx@`(sol_expr| $e:sol_expr [ $k:sol_expr ]) => do
    if isMem Γ e then
      let b ← schemaAt Γ .mpath e
      match pos with
      | .mloc => `(MLoc.index $b $(← schemaAt Γ .val k))
      | .mpath => `(MPath.loc (MLoc.index $b $(← schemaAt Γ .val k)))
      | .val => `(Val.readMem (MLoc.index $b $(← schemaAt Γ .val k)))
      | .oploc => `(OpLoc.mindex $b $(← schemaAt Γ .simple k))
      | _ => posError stx "a memory element" pos
    else
      let b ← schemaAt Γ .spath e
      let it ← indexTyOf e
      match pos with
      | .loc => `(Loc.index $it $b $(← schemaAt Γ .val k))
      | .spath => `(SPath.loc (Loc.index $it $b $(← schemaAt Γ .val k)))
      | .val => `(Val.read (Loc.index $it $b $(← schemaAt Γ .val k)))
      | .oploc => `(OpLoc.index $it $b $(← schemaAt Γ .simple k))
      | _ => posError stx "a storage entry" pos
  | `(sol_expr| ( $e:sol_expr )) => schemaAt Γ pos e
  | `(sol_expr| ‹ $t:term ›) => pure t
  | stx@`(sol_expr| $a:sol_expr ⊕ $b:sol_expr) => do
    unless pos == .val do posError stx "an operator application" pos
    `(Val.binop (p := $(schemaIdent "p")) $(schemaIdent "op") $(schemaIdent "hop") $(schemaIdent "hq")
        $(← schemaAt Γ .val a) $(← schemaAt Γ .val b))
  | stx@`(sol_expr| ⊖ $a:sol_expr) => do
    unless pos == .val do posError stx "an operator application" pos
    `(Val.unop (p := $(schemaIdent "p")) $(schemaIdent "op") $(schemaIdent "hop") $(schemaIdent "hq")
      $(← schemaAt Γ .val a))
  | stx@`(sol_expr| $a:sol_expr && $b:sol_expr) => do
    unless pos == .val do posError stx "`&&`" pos
    `(Val.binop BinOp.and rfl rfl $(← schemaAt Γ .val a) $(← schemaAt Γ .val b))
  | stx@`(sol_expr| $a:sol_expr || $b:sol_expr) => do
    unless pos == .val do posError stx "`||`" pos
    `(Val.binop BinOp.or rfl rfl $(← schemaAt Γ .val a) $(← schemaAt Γ .val b))
  | stx@`(sol_expr| $c:sol_expr ? $a:sol_expr : $b:sol_expr) => do
    unless pos == .val do posError stx "a conditional" pos
    `(Val.ternary $(← schemaAt Γ .val c) $(← schemaAt Γ .val a) $(← schemaAt Γ .val b))
  | _ => Macro.throwUnsupported

end

/-- The variable a declaration introduces: the name itself, or — in a
taclet's `\replacewith` — the fresh variable its spelling asks for. -/
def declVar (fresh : Bool) (x : Ident) : MacroM Lean.Term := do
  unless fresh do return x
  let k := schemaIdent "k"
  match stemOf x.getId.toString with
  | "se" => `(Var.fresh "se" $k)
  | "sp" => `(Var.fresh "sp" $k)
  | "ie" => `(Var.fresh "ie" $k)
  | "mv" => `(Var.fresh "mv" $k)
  | _ => Macro.throwErrorAt x "a taclet declares only fresh `se`, `sp`, `ie` or `mv`"

/-- `sp.push` called: the receiver `sp` and the method `push`. -/
def callRecv? (f : TSyntax `sol_expr) : MacroM (Option (TSyntax `sol_expr × String)) := do
  match f with
  | `(sol_expr| $x:ident) =>
    match (nameParts x.getId).reverse with
    | m :: r :: rs =>
      let n := (r :: rs).reverse.foldl (fun n s => Name.str n s) Name.anonymous
      return some (← `(sol_expr| $(mkIdentFrom x n):ident), m)
    | _ => return none
  | `(sol_expr| $e:sol_expr . $g:ident) => return some (e, g.getId.toString)
  | _ => return none

/-- Whether an expression is a stack local, a storage alias, a memory local,
a hole — the statement it is the left of. -/
def lhsHead (Γ : Scope) : TSyntax `sol_expr → Option Head
  | `(sol_expr| $x:ident) =>
    match nameParts x.getId with
    | [_] => some (headOf Γ x)
    | _ => none
  | _ => none

mutual

partial def schemaStmt (fresh : Bool) (Γ : Scope) :
    TSyntax `sol_stmt → MacroM (Lean.Term × Scope)
  | `(sol_stmt| ‹ $t:term ›) => return (t, Γ)
  | `(sol_stmt| $l:sol_expr = $b:sol_expr .push()) => do
    let some (.alias x) := lhsHead Γ l | Macro.throwErrorAt l "`= b.push()` binds a storage alias"
    return (← `(Stmt.rebind (R := $(schemaIdent "R")) $x (ARhs.push $(← schemaAt Γ .spath b) $(schemaIdent "hd"))), Γ)
  | `(sol_stmt| $l:sol_expr = $f:sol_expr ( )) => do
    let some (b, "push") ← callRecv? f | Macro.throwErrorAt f "only `b.push()` is a call on the right"
    schemaStmt fresh Γ (← `(sol_stmt| $l:sol_expr = $b:sol_expr .push()))
  | `(sol_stmt| $T:sol_ty storage $x:ident = $f:sol_expr ( )) => do
    let some (b, "push") ← callRecv? f | Macro.throwErrorAt f "only `b.push()` is a call on the right"
    schemaStmt fresh Γ (← `(sol_stmt| $T:sol_ty storage $x:ident = $b:sol_expr .push()))
  | `(sol_stmt| $x:sol_expr = $l:sol_expr ⊕⊕) => do
    let some (.local v) := lhsHead Γ x | Macro.throwErrorAt x "the value of `++` goes to a stack local"
    return (← `(Stmt.assignIncDec (p := $(schemaIdent "p")) $v $(schemaIdent "op") $(schemaIdent "hp")
      $(← schemaAt Γ .oploc l) $(schemaIdent "hs")), Γ)
  | `(sol_stmt| $l:sol_expr ⊕⊕) => do
    return (← `(Stmt.incDec (p := $(schemaIdent "p")) $(schemaIdent "op") $(schemaIdent "hp")
      $(← schemaAt Γ .oploc l)), Γ)
  | `(sol_stmt| $l:sol_expr ⊕= $r:sol_expr) => do
    return (← `(Stmt.opAssign (p := $(schemaIdent "p")) $(schemaIdent "op") $(schemaIdent "hop") $(schemaIdent "hp")
      $(← schemaAt Γ .oploc l) $(← schemaAt Γ .val r)), Γ)
  | `(sol_stmt| $l:sol_expr = $r:sol_expr) => do
    let t ← match lhsHead Γ l with
      | some (.local v) => `(Stmt.assignLocal $v $(← schemaAt Γ .val r))
      | some (.alias x) =>
        match rhsVar? "rhs" r with
        | some v => `(Stmt.rebind $x $v)
        | none => `(Stmt.rebind $x (ARhs.path $(← schemaAt Γ .spath r)))
      | some (.mem x) =>
        if let some v := rhsVar? "mrhs" r then `(Stmt.rebindMem $x $v) else
        if isMem Γ r then `(Stmt.rebindMem $x (MRhs.alias $(← schemaAt Γ .mpath r)))
        else `(Stmt.rebindMem $x (MRhs.copy $(← schemaAt Γ .spath r) $(schemaIdent "hm")))
      | some (.other h) =>
        match h with
        | `($x:ident) =>
          match stemOf x.getId.toString with
          | "lhs" =>
            if isMem Γ r then `($(mkIdent `Solidity.MHole.fill) $x $(← schemaAt Γ .mloc r))
            else `($(mkIdent `Solidity.Hole.fill) $x $(← schemaAt Γ .spath r))
          | "x" => `($(mkIdent `Solidity.VHole.fill) $x $(← schemaAt Γ .val r))
          | _ => Macro.throwErrorAt l "not a left-hand side"
        | _ => Macro.throwErrorAt l "not a left-hand side"
      | _ =>
        if isMem Γ l then
          if let some v := rhsVar? "msrc" r then `(Stmt.assignMem $(← schemaAt Γ .mloc l) $v) else
          if isMem Γ r then `(Stmt.assignMem $(← schemaAt Γ .mloc l) (MSrc.ref $(← schemaAt Γ .mpath r)))
          else `(Stmt.assignMem $(← schemaAt Γ .mloc l) (MSrc.val $(← schemaAt Γ .val r)))
        else if isMem Γ r then
          `(Stmt.assignFromMem $(← schemaAt Γ .loc l) $(← schemaAt Γ .mpath r))
        else if let some v := rhsVar? "src" r then `(Stmt.assign $(← schemaAt Γ .loc l) $v)
        else if isPath Γ r then
          `(Stmt.assign $(← schemaAt Γ .loc l) (Src.copy $(← schemaAt Γ .spath r) $(schemaIdent "hm")))
        else `(Stmt.assign $(← schemaAt Γ .loc l) (Src.val $(← schemaAt Γ .val r)))
    return (t, Γ)
  | `(sol_stmt| $T:sol_ty storage $x:ident = $b:sol_expr .push()) => do
    let v ← declVar fresh x
    let _ := T
    let t ← `(Stmt.declStorage _ $v (some (ARhs.push $(← schemaAt Γ .spath b) $(schemaIdent "hd"))))
    return (t, (x.getId.toString, .alias v) :: Γ)
  | `(sol_stmt| $T:sol_ty storage $x:ident = $e:sol_expr) => do
    let v ← declVar fresh x
    let _ := T
    let r : Lean.Term ← match rhsVar? "rhs" e with
      | some r => pure ⟨r.raw⟩
      | none => `(ARhs.path $(← schemaAt Γ .spath e))
    let t ← `(Stmt.declStorage _ $v (some $r))
    return (t, (x.getId.toString, .alias v) :: Γ)
  | `(sol_stmt| $T:sol_ty storage $x:ident) => do
    let v ← declVar fresh x
    let _ := T
    let t ← `(Stmt.declStorage $(schemaIdent "R") $v none)
    return (t, (x.getId.toString, .alias v) :: Γ)
  | `(sol_stmt| $T:sol_ty memory $x:ident = $e:sol_expr) => do
    let v ← declVar fresh x
    let _ := T
    let r : Lean.Term ← if let some r := rhsVar? "mrhs" e then pure ⟨r.raw⟩
      else if isMem Γ e then `(MRhs.alias $(← schemaAt Γ .mpath e))
      else `(MRhs.copy $(← schemaAt Γ .spath e) $(schemaIdent "hm"))
    let t ← `(Stmt.declMem _ $v (some $r) rfl)
    return (t, (x.getId.toString, .mem v) :: Γ)
  | `(sol_stmt| $T:sol_ty memory $x:ident) => do
    let v ← declVar fresh x
    let _ := T
    let t ← `(Stmt.declMem $(schemaIdent "R") $v none $(schemaIdent "hd"))
    return (t, (x.getId.toString, .mem v) :: Γ)
  | `(sol_stmt| $T:sol_ty $x:ident = $e:sol_expr) => do
    let v ← declVar fresh x
    let _ := T
    let t ← `(Stmt.declLocal _ $v (some $(← schemaAt Γ .val e)))
    return (t, (x.getId.toString, .val v) :: Γ)
  | `(sol_stmt| $T:sol_ty $x:ident) => do
    let v ← declVar fresh x
    let _ := T
    let t ← `(Stmt.declLocal $(schemaIdent "p") $v none)
    return (t, (x.getId.toString, .val v) :: Γ)
  | `(sol_stmt| $b:sol_expr .push( $a:sol_expr )) => do
    let v : Lean.Term ← if let some r := rhsVar? "src" a then pure ⟨r.raw⟩ else if isPath Γ a then `(Src.copy $(← schemaAt Γ .spath a) $(schemaIdent "hm"))
      else `(Src.val $(← schemaAt Γ .val a))
    return (← `(Stmt.push $(← schemaAt Γ .spath b) (some $v) rfl), Γ)
  | `(sol_stmt| $b:sol_expr .push()) => do
    return (← `(Stmt.push (E := $(schemaIdent "E")) $(← schemaAt Γ .spath b) none $(schemaIdent "hd")), Γ)
  | `(sol_stmt| $b:sol_expr .pop()) => do
    return (← `(Stmt.pop $(← schemaAt Γ .spath b)), Γ)
  | `(sol_stmt| $r:sol_expr .transfer( $a:sol_expr )) => do
    return (← `(Stmt.transfer $(← schemaAt Γ .val r) $(← schemaAt Γ .val a)), Γ)
  | `(sol_stmt| $f:sol_expr ( $a:sol_expr )) => do
    let some (b, m) ← callRecv? f | Macro.throwErrorAt f "only `b.push(a)` and `r.transfer(a)` are calls"
    match m with
    | "push" => schemaStmt fresh Γ (← `(sol_stmt| $b:sol_expr .push( $a )))
    | "transfer" => schemaStmt fresh Γ (← `(sol_stmt| $b:sol_expr .transfer( $a )))
    | _ => Macro.throwErrorAt f "only `b.push(a)` and `r.transfer(a)` are calls"
  | `(sol_stmt| $f:sol_expr ( )) => do
    let some (b, m) ← callRecv? f | Macro.throwErrorAt f "only `b.push()` and `b.pop()` are calls"
    match m with
    | "push" => schemaStmt fresh Γ (← `(sol_stmt| $b:sol_expr .push()))
    | "pop" => schemaStmt fresh Γ (← `(sol_stmt| $b:sol_expr .pop()))
    | _ => Macro.throwErrorAt f "only `b.push()` and `b.pop()` are calls"
  | `(sol_stmt| if ($c:sol_expr) $t:sol_block else $f:sol_block) => do
    return (← `(Stmt.ite $(← schemaAt Γ .val c) $(← schemaBlock fresh Γ t) $(← schemaBlock fresh Γ f)), Γ)
  | stx => do
    let k := stx.raw.getKind
    if k == ``solDelete then return (← `(Stmt.delete $(← schemaAt Γ .loc ⟨stx.raw[1]⟩)), Γ)
    if k == ``solRequire then return (← `(Stmt.require $(← schemaAt Γ .val ⟨stx.raw[2]⟩)), Γ)
    if k == ``solAssert then return (← `(Stmt.assert $(← schemaAt Γ .val ⟨stx.raw[2]⟩)), Γ)
    if k == ``solRevert then return (← `(Stmt.revert), Γ)
    if k == Lean.choiceKind then
      let alts := stx.raw.getArgs
      for alt in alts.filter (·[0].isAtom) ++ alts do
        try return ← schemaStmt fresh Γ ⟨alt⟩ catch _ => pure ()
    Macro.throwUnsupported

partial def schemaProg (fresh : Bool) (Γ : Scope) (ss : Array (TSyntax `sol_stmt)) :
    MacroM (Array Lean.Term × Scope) :=
  ss.foldlM (init := (#[], Γ)) fun (ts, Γ) s => do
    let (t, Γ) ← schemaStmt fresh Γ s
    return (ts.push t, Γ)

/-- A branch: its statements (their declarations stay inside), or a schema
variable standing for all of them. -/
partial def schemaBlock (fresh : Bool) (Γ : Scope) : TSyntax `sol_block → MacroM Lean.Term
  | `(sol_block| { $[$ss:sol_stmt;]* }) => do
    let (ts, _) ← schemaProg fresh Γ ss
    `(([$ts,*] : List (Stmt _)))
  | `(sol_block| $x:ident) => pure x
  | `(sol_block| ‹ $t:term ›) => pure t
  | _ => Macro.throwUnsupported

end

/-! ### Terms -/

/-- The three sorts a term position asks for, and the memory ones. -/
inductive TPos where
  | val | path | storage | ident | addr | memory | svalue | mvalue
  deriving DecidableEq

def TPos.name : TPos → String
  | .val => "a value" | .path => "a storage path" | .storage => "a storage"
  | .ident => "a memory identity" | .addr => "a memory location" | .memory => "a memory"
  | .svalue => "a storage value" | .mvalue => "a memory value"

def tposError (x : Lean.Syntax) (what : String) (pos : TPos) : MacroM α :=
  Macro.throwErrorAt x s!"{what} is not {pos.name}"

/-- A name at a term sort: a schema variable of a program sort is lowered
(`se` is the term `se.lower`), a stack local is `pv`. -/
def headTerm (Γ : Scope) (pos : TPos) (x : Ident) : MacroM Lean.Term := do
  let n := x.getId.toString
  if (n == "true" || n == "false") && pos == .val then
    return ← `(Term.lit (.bool $(mkIdent (Name.mkSimple n))))
  if n == "storage" && pos == .storage then return ← `(STerm.storage)
  if n == "memory" && pos == .memory then return ← `(MTerm.memory)
  match headOf Γ x, pos with
  | .local v, .val => `(Term.pv $v)
  | .local v, .svalue => `(SValT.val (Term.pv $v))
  | .local v, .mvalue => `(MValT.val (Term.pv $v))
  | .alias v, .path => `(PTerm.pv $v)
  | .mem v, .ident => `(ITerm.pv $v)
  | .mem v, .mvalue => `(MValT.ref (ITerm.pv $v))
  | .root r _, .val => `(Term.find STerm.storage (PTerm.root $r))
  | .root r _, .path => `(PTerm.root $r)
  | .simple s, .val => `(Simple.lower $s)
  | .simple s, .svalue => `(SValT.val (Simple.lower $s))
  | .simple s, .mvalue => `(MValT.val (Simple.lower $s))
  | .val e, .val => `(Val.lower $e)
  | .spath p, .path => `(SPath.lower $p)
  | .mpath p, .ident => `(MPath.lower $p)
  | .mpath p, .mvalue => `(MValT.ref (MPath.lower $p))
  | .loc l, .path => `(Loc.lower $l)
  | .other o, _ => pure o
  | _, _ => tposError x s!"`{n}`" pos

/-- `mv.f₁.….fₙ` at a term sort: the inner members are identities read. -/
def memMember (pos : TPos) (stx : Lean.Syntax) : Lean.Term → List Ident → MacroM Lean.Term
  | b, [] => pure b
  | b, [f] => match pos with
    | .addr => `(MAddr.field $b $f)
    | .val => `(Term.read MTerm.memory (MAddr.field $b $f))
    | .ident => `(ITerm.read MTerm.memory (MAddr.field $b $f))
    | .mvalue => `(MValT.ref (ITerm.read MTerm.memory (MAddr.field $b $f)))
    | _ => tposError stx "a memory member" pos
  | b, f :: fs => do memMember pos stx (← `(ITerm.read MTerm.memory (MAddr.field $b $f))) fs

/-- `p.length`, however it was parsed: the path `p`. -/
def lengthBase? : TSyntax `dl_term → MacroM (Option (TSyntax `dl_term))
  | `(dl_term| $x:ident) =>
    match (nameParts x.getId).reverse with
    | "length" :: r :: rs => do
      let n := (r :: rs).reverse.foldl (fun n s => Name.str n s) Name.anonymous
      some <$> `(dl_term| $(mkIdentFrom x n):ident)
    | _ => pure none
  | `(dl_term| $t:dl_term . $f:ident) => pure (if f.getId.toString == "length" then some t else none)
  | _ => pure none

mutual

/-- A term at a sort.  At a storage or a memory value's sort, a value term is
wrapped as one; a path, `find(…)` and `copyMem(…)` are storage values of
their own, a memory path a memory value of its own. -/
partial def schemaTerm (Γ : Scope) (pos : TPos) (t : TSyntax `dl_term) : MacroM Lean.Term := do
  match pos with
  | .svalue =>
    match t with
    | `(dl_term| $f:ident($_,*)) =>
      if ["find", "copyMem"].contains f.getId.toString then schemaTerm0 Γ .svalue t
      else `(SValT.val $(← schemaTerm0 Γ .val t))
    | _ => `(SValT.val $(← schemaTerm0 Γ .val t))
  | .mvalue =>
    let memHead := match t with
      | `(dl_term| $x:ident) => match nameParts x.getId with
        | [h] => match headOf Γ (mkIdent (Name.mkSimple h)) with
          | .mem _ | .mpath _ => true
          | _ => false
        | _ => false
      | _ => false
    if memHead then `(MValT.ref $(← schemaTerm0 Γ .ident t))
    else `(MValT.val $(← schemaTerm0 Γ .val t))
  | _ => schemaTerm0 Γ pos t

partial def schemaTerm0 (Γ : Scope) (pos : TPos) : TSyntax `dl_term → MacroM Lean.Term
  | stx@`(dl_term| $n:num) =>
    match pos with
    | .val => `(Term.lit (.int $n))
    | .svalue => `(SValT.val (Term.lit (.int $n)))
    | .mvalue => `(MValT.val (Term.lit (.int $n)))
    | _ => tposError stx "a number" pos
  | stx@`(dl_term| $x:ident) => do
    match nameParts x.getId with
    | [] => Macro.throwError "empty identifier"
    | [_] => headTerm Γ pos x
    | h :: fs =>
      -- `sp.fld`: a path, or (at a memory sort) a member of a memory object
      let hx := partIdent x h
      match headOf Γ hx with
      | .mem _ | .mpath _ =>
        memMember pos stx (← headTerm Γ .ident hx) (fs.map (partIdent x))
      | _ =>
        if fs.getLast? == some "length" then
          let p' ← (fs.dropLast).foldlM (init := ← headTerm Γ .path hx) fun acc f =>
            `(PTerm.field $acc $(partIdent x f))
          match pos with
          | .val => `(Term.len STerm.storage $p')
          | _ => tposError stx "a length" pos
        else
        let p ← fs.foldlM (init := ← headTerm Γ .path hx) fun acc f =>
          `(PTerm.field $acc $(partIdent x f))
        match pos with
        | .path => pure p
        | .val => `(Term.find STerm.storage $p)
        | .svalue => `(SValT.find STerm.storage $p)
        | _ => tposError stx "a storage path" pos
  | stx@`(dl_term| $t:dl_term . $f:ident) => do
    let p ← (nameParts f.getId).foldlM (init := ← schemaTerm Γ .path t) fun acc c =>
      `(PTerm.field $acc $(partIdent f c))
    match pos with
    | .path => pure p
    | _ => tposError stx "a member" pos
  | stx@`(dl_term| $t:dl_term [ $i:dl_term ]) => do
    let mem := match t with
      | `(dl_term| $x:ident) => match nameParts x.getId with
        | h :: _ => match headOf Γ (mkIdent (Name.mkSimple h)) with
          | .mem _ | .mpath _ => true
          | _ => false
        | [] => false
      | _ => false
    if mem then
      let a ← `(MAddr.at $(← schemaTerm Γ .ident t) $(← schemaTerm Γ .val i))
      match pos with
      | .addr => pure a
      | .val => `(Term.read MTerm.memory $a)
      | .ident => `(ITerm.read MTerm.memory $a)
      | .mvalue => `(MValT.ref (ITerm.read MTerm.memory $a))
      | _ => tposError stx "a memory element" pos
    else
      let p ← `(PTerm.at $(← schemaTerm Γ .path t) $(← schemaTerm Γ .val i))
      match pos with
      | .path => pure p
      | .val => `(Term.find STerm.storage $p)
      | .svalue => `(SValT.find STerm.storage $p)
      | _ => tposError stx "an entry" pos
  | `(dl_term| $a:dl_term ⊕ $b:dl_term) => do
    `(Term.binop $(schemaIdent "op") $(schemaIdent "p") $(← schemaTerm Γ .val a) $(← schemaTerm Γ .val b))
  | `(dl_term| ⊖ $a:dl_term) => do
    `(Term.unop $(schemaIdent "op") $(schemaIdent "p") $(← schemaTerm Γ .val a))
  | `(dl_term| $a:dl_term ± $b:dl_term) => do
    `(Term.binop (IncDec.binOp $(schemaIdent "op")) $(schemaIdent "p")
        $(← schemaTerm Γ .val a) $(← schemaTerm Γ .val b))
  | `(dl_term| $a:dl_term ⊕⊕) => do
    `(Term.bumped $(schemaIdent "op") $(schemaIdent "p") $(← schemaTerm Γ .val a))
  | `(dl_term| $a:dl_term + $b:dl_term) => do
    `(Term.binop BinOp.add PrimTy.uint $(← schemaTerm Γ .val a) $(← schemaTerm Γ .val b))
  | `(dl_term| $a:dl_term - $b:dl_term) => do
    `(Term.binop BinOp.sub PrimTy.uint $(← schemaTerm Γ .val a) $(← schemaTerm Γ .val b))
  | `(dl_term| ( $t:dl_term )) => schemaTerm Γ pos t
  | `(dl_term| ‹ $t:term ›) => pure t
  | stx@`(dl_term| $f:ident($args,*)) => do
    let args := args.getElems
    let st := schemaTerm Γ .storage
    let pa := schemaTerm Γ .path
    let me := schemaTerm Γ .memory
    match f.getId.toString, args, pos with
    | "select", #[s, r], .val => `(Term.find $(← st s) $(← pa r))
    | "find", #[s, p], .val => `(Term.find $(← st s) $(← pa p))
    | "find", #[s, p], .svalue => `(SValT.find $(← st s) $(← pa p))
    | "read", #[m, a], .val => `(Term.read $(← me m) $(← schemaTerm Γ .addr a))
    | "read", #[m, a], .ident => `(ITerm.read $(← me m) $(← schemaTerm Γ .addr a))
    | "copyMem", #[_, m, i], .svalue => `(SValT.copyMem $(← me m) $(← schemaTerm Γ .ident i))
    | "freshId", #[t], .ident =>
      match t with
      | `(dl_term| addM($m)) => `(ITerm.alloc $(← me m) $(schemaIdent "R"))
      | `(dl_term| copySt($m, $v)) => `(ITerm.copy $(← me m) $(← schemaTerm Γ .svalue v))
      | _ => Macro.throwErrorAt t "`freshId(addM(m))` or `freshId(copySt(m, v))`"
    | "store", #[s, r, v], .storage => `(STerm.save $(← st s) $(← pa r) $(← schemaTerm Γ .svalue v))
    | "save", #[s, p, v], .storage =>
      -- the paper's push and pop, nested writes over the extent
      match ← lengthBase? p with
      | some b =>
        match s, v with
        | `(dl_term| save($s', $_[$_], $w)), `(dl_term| $_ + 1) =>
          `(STerm.push $(← st s') $(← pa b) $(← schemaTerm Γ .svalue w))
        | `(dl_term| delAt($s', $_[$_])), `(dl_term| $_ + 1) =>
          `(STerm.pushSlot $(← st s') $(← pa b) $(schemaIdent "E"))
        | `(dl_term| delAt($s', $_[$_])), `(dl_term| $_ - 1) =>
          `(STerm.pop $(← st s') $(← pa b))
        | _, `(dl_term| $_ + 1) => `(STerm.extend $(← st s) $(← pa b) (Ty.ref $(schemaIdent "R")))
        | _, _ => `(STerm.save $(← st s) $(← pa p) $(← schemaTerm Γ .svalue v))
      | none => `(STerm.save $(← st s) $(← pa p) $(← schemaTerm Γ .svalue v))
    | "delAt", #[s, p], .storage => `(STerm.delAt $(← st s) $(← pa p))
    | "defVal", #[_], .val => `(Term.lit (PrimTy.default $(schemaIdent "p")))
    | "write", #[m, a, v], .memory =>
      `(MTerm.write $(← me m) $(← schemaTerm Γ .addr a) $(← schemaTerm Γ .mvalue v))
    | "addM", #[m], .memory => `(MTerm.addM $(← me m) $(schemaIdent "R"))
    | "copySt", #[m, v], .memory => `(MTerm.copySt $(← me m) $(← schemaTerm Γ .svalue v))
    | _, _, _ => tposError stx s!"`{f.getId}(…)` here" pos
  | _ => Macro.throwUnsupported

end

/-- One elementary update: the sort of `x := t` is read off `x`. -/
def schemaUpdElem (Γ : Scope) : TSyntax `dl_upd_elem → MacroM Lean.Term
  | `(dl_upd_elem| transfer($r, $a)) => do
    `(UpdElem.transfer $(← schemaTerm Γ .val r) $(← schemaTerm Γ .val a))
  | `(dl_upd_elem| $l:dl_term := $r:dl_term) => do
    let `(dl_term| $x:ident) := l | Macro.throwErrorAt l "an update assigns a variable"
    let n := x.getId.toString
    if n == "storage" then return ← `(UpdElem.storage $(← schemaTerm Γ .storage r))
    if n == "memory" then return ← `(UpdElem.memory $(← schemaTerm Γ .memory r))
    match headOf Γ x with
    | .local v => `(UpdElem.val $v $(← schemaTerm Γ .val r))
    | .alias v => `(UpdElem.path $v $(← schemaTerm Γ .path r))
    | .mem v => `(UpdElem.mref $v $(← schemaTerm Γ .ident r))
    | _ => Macro.throwErrorAt x "an update assigns a local, an alias, a memory local, \
        `storage` or `memory`"
  | _ => Macro.throwUnsupported

def schemaUpd (Γ : Scope) (U : TSyntax `dl_upd) : MacroM Lean.Term := do
  if let `(dl_upd| ‹ $t:term ›) := U then return t
  -- the elements, read off the `sepBy1` node: `‖` does not splice in a pattern
  let elems ← U.raw[1].getSepArgs.mapM fun e => schemaUpdElem Γ ⟨e⟩
  `(([$elems,*] : Upd _))

/-- The modality of the formula under an update: an update is judged as the
goal it came from. -/
partial def fmlModality? : TSyntax `dl_fml → MacroM (Option Lean.Term)
  | `(dl_fml| ⟨ $[$_:sol_stmt;]* ⟩ $_:dl_fml) | `(dl_fml| ⟨ $_:sol_block ⟩ $_:dl_fml) =>
    some <$> `(Modality.diamond)
  | `(dl_fml| [ $[$_:sol_stmt;]* ] $_:dl_fml) | `(dl_fml| [ $_:sol_block ] $_:dl_fml) =>
    some <$> `(Modality.box)
  | `(dl_fml| ⟨[ $[$_:sol_stmt;]* ]⟩ $_:dl_fml) => pure (some (schemaIdent "m"))
  | `(dl_fml| $_:dl_upd $φ:dl_fml) => fmlModality? φ
  | `(dl_fml| ( $φ:dl_fml )) => fmlModality? φ
  | _ => pure none

partial def schemaFml : TSyntax `dl_fml → MacroM Lean.Term
  | `(dl_fml| true) => `(Fml.tt)
  | `(dl_fml| false) => `(Fml.not Fml.tt)
  | `(dl_fml| $a:dl_term = $b:dl_term) => do
    `(Fml.eq $(← schemaTerm [] .val a) $(← schemaTerm [] .val b))
  | `(dl_fml| ¬ $φ:dl_fml) => do `(Fml.not $(← schemaFml φ))
  | `(dl_fml| $φ:dl_fml ∧ $ψ:dl_fml) | `(dl_fml| $φ:dl_fml && $ψ:dl_fml) => do
    `(Fml.and $(← schemaFml φ) $(← schemaFml ψ))
  | `(dl_fml| $φ:dl_fml → $ψ:dl_fml) => do `(Fml.imp $(← schemaFml φ) $(← schemaFml ψ))
  | `(dl_fml| $U:dl_upd $φ:dl_fml) => do
    let m ← match ← fmlModality? φ with
      | some m => pure m
      | none => `(Modality.diamond)
    `(Fml.upd $m $(← schemaUpd [] U) $(← schemaFml φ))
  | `(dl_fml| ⟨ $[$ss:sol_stmt;]* ⟩ $φ:dl_fml) => do
    let (ts, _) ← schemaProg false [] ss
    `(Fml.modal .diamond [$ts,*] $(← schemaFml φ))
  | `(dl_fml| [ $[$ss:sol_stmt;]* ] $φ:dl_fml) => do
    let (ts, _) ← schemaProg false [] ss
    `(Fml.modal .box [$ts,*] $(← schemaFml φ))
  | `(dl_fml| ⟨[ $[$ss:sol_stmt;]* ]⟩ $φ:dl_fml) => do
    let (ts, _) ← schemaProg false [] ss
    `(Fml.modal $(schemaIdent "m") [$ts,*] $(← schemaFml φ))
  | `(dl_fml| ⟨ $b:sol_block ⟩ $φ:dl_fml) => do
    `(Fml.modal .diamond $(← schemaBlock false [] b) $(← schemaFml φ))
  | `(dl_fml| [ $b:sol_block ] $φ:dl_fml) => do
    `(Fml.modal .box $(← schemaBlock false [] b) $(← schemaFml φ))
  | `(dl_fml| ( $φ:dl_fml )) => schemaFml φ
  | `(dl_fml| ‹ $t:term ›) => pure t
  | stx@`(dl_fml| $_:dl_term == $_:dl_term) | stx@`(dl_fml| $_:dl_term != $_:dl_term) =>
    Macro.throwErrorAt stx "a program comparison is read against a contract: write `dl{ … }`"
  | _ => Macro.throwUnsupported

/-- The condition of a split's first goal; the second goal's must be its negation. -/
def splitCond (c nc : TSyntax `dl_fml) : MacroM Lean.Term := do
  let `(dl_fml| ¬ $c':dl_fml) := nc
    | Macro.throwErrorAt nc "the second branch assumes the negated condition, `¬…`"
  unless c'.raw.structEq c.raw do
    Macro.throwErrorAt nc "the second branch assumes the negation of the first one's condition"
  schemaFml c

def schemaPremise (fresh : Bool) (Γ : Scope) : TSyntax `dl_premise → MacroM Lean.Term
  | `(dl_premise| $U:dl_upd ⟨[ ]⟩) => do `($(mkIdent `Solidity.Premise.update) $(← schemaUpd Γ U))
  | `(dl_premise| ⟨[ $[$ss:sol_stmt;]* ]⟩) => do
    let (ts, _) ← schemaProg fresh Γ ss
    `($(mkIdent `Solidity.Premise.unfold) [$ts,*])
  | `(dl_premise| $c:dl_fml ⟹ ⟨[ $t:sol_block ]⟩ ; $nc:dl_fml ⟹ ⟨[ $f:sol_block ]⟩) => do
    `($(mkIdent `Solidity.Premise.split) $(← splitCond c nc) $(← schemaBlock fresh Γ t) $(← schemaBlock fresh Γ f))
  | `(dl_premise| $c:dl_fml ⟹ ⟨[ $[$ts:sol_stmt;]* ]⟩ ; $nc:dl_fml ⟹ ⟨[ $[$fs:sol_stmt;]* ]⟩) => do
    let (ts, _) ← schemaProg fresh Γ ts
    let (fs, _) ← schemaProg fresh Γ fs
    `($(mkIdent `Solidity.Premise.split) $(← splitCond c nc) ([$ts,*] : List (Stmt _)) ([$fs,*] : List (Stmt _)))
  | `(dl_premise| true) => `($(mkIdent `Solidity.Premise.done) true)
  | `(dl_premise| false) => `($(mkIdent `Solidity.Premise.done) false)
  | _ => Macro.throwUnsupported

/-- The taclet `s ⇝ p` under the modality `m`: the `\find` binds its names;
the `\replacewith` sees them, and its own declarations are fresh, numbered by
the taclet's `k`. -/
def schemaTaclet (m : Lean.Term) (s : TSyntax `sol_stmt) (p : TSyntax `dl_premise) :
    MacroM Lean.Term := do
  let (s, Γ) ← schemaStmt false [] s
  `($(mkIdent `Solidity.Taclet) $(schemaIdent "C") $(schemaIdent "k") $m $s $(← schemaPremise true Γ p))

def schemaHyp : TSyntax `dl_hyp → MacroM Lean.Term
  | `(dl_hyp| $U:dl_upd) => do `($(mkIdent `Solidity.Hyp.upd) $(schemaIdent "m") $(← schemaUpd [] U))
  | `(dl_hyp| $φ:dl_fml) => do `($(mkIdent `Solidity.Hyp.pre) $(← schemaFml φ))
  | _ => Macro.throwUnsupported

macro_rules
  | `(dl_schema{ $φ:dl_fml }) => schemaFml φ
  | `(dl{ $[$hs:dl_hyp],* ⟹ $φ:dl_fml }) => do
    `($(mkIdent `Solidity.Proves) [$(← hs.mapM schemaHyp),*] $(← schemaFml φ))
  | `(dl{ ⟨[ $s:sol_stmt; ]⟩ ⇝ $p:dl_premise }) => schemaTaclet (schemaIdent "m") s p
  | `(dl{ [ $s:sol_stmt; ] ⇝ $p:dl_premise }) => do schemaTaclet (← `(Modality.box)) s p
  | `(dl{ ⟨ $s:sol_stmt; ⟩ ⇝ $p:dl_premise }) => do schemaTaclet (← `(Modality.diamond)) s p
  | `(dl{ $p:dl_premise }) => schemaPremise false [] p
  | `(stmt{ $s:sol_stmt; }) => return (← schemaStmt false [] s).1

end Expand

end Solidity
