import Solidity.Source.Resolve

/-!
# Source units, imports and the file-level scope (G12)

S00 and S01 read one source unit.  A compilation input is a set of units
named by their source unit names; this module gives, as relations over S00's
syntax, how their `import` directives connect them and which declarations a
file-level name denotes in each unit.  The checker that decides them is
`Solidity/Frontend/Static/Units.lean`.

**Paths.**  An import path is resolved as solc's `CompilerStack` does: a
path whose first segment is `.` or `..` is relative to the importing unit's
directory (`Path.absolute`, solc's `absolutePath`), and the result is
remapped (`Remapping.apply`, solc's `ImportRemapper::apply`: the remapping
with the longest context that is a prefix of the importing unit's name wins,
then the longest prefix of the path; a later one wins a tie).  solc's path
sanitizing (duplicate slashes, a trailing `/`) is not modelled: the inputs
are source unit names, which are already normalized.

**Identity.**  A declaration's identity is its unit and its position among
the unit's declarations (`DeclId`, extending S00's `Syn.graph` across
units).  A name imported along two routes denotes one identity, so a diamond
of imports is no clash (`ScopeOK`).

**The file-level scope** (`Sees P R u x σ`), solc's rules:

- a unit's own file-level declarations (`own`);
- `import "p";` brings every name of `p`'s file-level scope, including the
  names `p` imports itself (`all`);
- `import "p" as N;` and `import * as N from "p";` bind `N` to the unit
  `p` (`ns`); a qualified `N.x` then names `x` in `p`'s scope;
- `import {a as b} from "p";` binds `b` to whatever `a` denotes in `p`
  (`sym`); without `as`, `b` is `a`.

`Sees` is a least fixpoint, so import cycles are allowed (solc allows them)
and a name reached only through a cycle of aliases denotes nothing, which
`SymsResolve` refuses (solc: "Declaration not found").  Deviation: solc
copies an imported unit's scope as it stands when the importing unit is
processed (depth-first), so inside a cycle the unit processed first sees
only the other's own declarations; `Sees` gives every unit of a cycle the
whole fixpoint (`docs/feature-work/frontend-static.md`).
-/

namespace Solidity.Source

/-! ## Paths and remappings -/

/-- The segments of a path, split at `/`. -/
def Path.split : List Char → List (List Char)
  | [] => [[]]
  | c :: cs =>
    match Path.split cs with
    | [] => [[c]]
    | s :: ss => if c = '/' then [] :: s :: ss else (c :: s) :: ss

/-- Segments joined by `/`. -/
def Path.join : List (List Char) → List Char
  | [] => []
  | [s] => s
  | s :: ss => s ++ '/' :: Path.join ss

/-- One segment of a relative path, applied to a directory. -/
def Path.step (acc : List (List Char)) (s : List Char) : List (List Char) :=
  if s = ['.', '.'] then acc.dropLast else if s = ['.'] then acc else acc ++ [s]

/-- solc's `absolutePath(path, reference)`: a path starting with a `.` or
`..` segment is resolved against the directory of `reference`; any other
path is already a source unit name. -/
def Path.absolute (path ref : String) : String :=
  match Path.split path.toList with
  | first :: rest =>
    if first = ['.'] ∨ first = ['.', '.'] then
      String.mk (Path.join ((first :: rest).foldl Path.step (Path.split ref.toList).dropLast))
    else path
  | [] => path

/-- An import remapping `context:prefix=target`. -/
structure Remapping where
  context : String := ""
  pre : String
  target : String
  deriving DecidableEq, Repr

/-- Whether `r` applies to `path` imported from `ctx`. -/
def Remapping.matches (r : Remapping) (ctx path : String) : Bool :=
  r.context.toList.isPrefixOf ctx.toList && r.pre.toList.isPrefixOf path.toList

/-- Whether `r` is at least as close a match as `b` (solc's order: the
longer context, then the longer prefix; ties go to the later one). -/
def Remapping.closer (r b : Remapping) : Bool :=
  decide (b.context.length < r.context.length) ||
    (decide (b.context.length = r.context.length) && decide (b.pre.length ≤ r.pre.length))

/-- The remapping solc selects. -/
def Remapping.select (rs : List Remapping) (ctx path : String) : Option Remapping :=
  rs.foldl (fun best r =>
    if r.matches ctx path then
      match best with
      | Option.none => Option.some r
      | Option.some b => if r.closer b then Option.some r else Option.some b
    else best) Option.none

/-- solc's `ImportRemapper::apply`: the selected remapping replaces its
prefix by its target. -/
def Remapping.apply (rs : List Remapping) (ctx path : String) : String :=
  match Remapping.select rs ctx path with
  | Option.none => path
  | Option.some r => String.mk (r.target.toList ++ path.toList.drop r.pre.length)

/-! ## Import directives -/

/-- One imported name or namespace. -/
inductive Import where
  /-- `import "p";` -/
  | all (path : String)
  /-- `import "p" as N;`, `import * as N from "p";` -/
  | ns (path alias : String)
  /-- `import {a as b} from "p";` (`b` is `a` without `as`). -/
  | sym (path symbol alias : String)
  deriving DecidableEq, Repr

/-- The path an import names. -/
def Import.path : Import → String
  | .all p | .ns p _ | .sym p _ _ => p

/-- The `{a as b, …}` pairs of a symbol import. -/
def Syn.importAliases : {c : Cat} → Syn c → List (String × String)
  | _, .cons x xs => x.importAliases ++ xs.importAliases
  | _, .importAlias s a => [(s, a.getD s)]
  | _, _ => []

/-- The import directives of a source unit, in order, one per imported name. -/
def Syn.imports : {c : Cat} → Syn c → List Import
  | _, .unit xs => xs.imports
  | _, .cons x xs => x.imports ++ xs.imports
  | _, .importPath p Option.none => [.all p]
  | _, .importPath p (Option.some a) => [.ns p a]
  | _, .importStar a p => [.ns p a]
  | _, .importSymbols x xs p => (x.importAliases ++ xs.importAliases).map fun (s, a) => .sym p s a
  | _, _ => []

/-! ## Programs and identities -/

/-- A compilation input's source units, by source unit name. -/
structure Program where
  units : List (String × Syn .unit)

/-- The unit of a name. -/
def Program.unit? (P : Program) (u : String) : Option (Syn .unit) :=
  (P.units.find? (·.1 == u)).map (·.2)

/-- The unit an import path of unit `u` names. -/
def Program.target (R : List Remapping) (u p : String) : String :=
  Remapping.apply R u (Path.absolute p u)

/-- **A declaration's identity**: its unit and its position among the unit's
declarations (S00's `Syn.graph`, across units). -/
structure DeclId where
  unit : String
  idx : Nat
  deriving DecidableEq, Repr

/-- The declaration an identity names. -/
def Program.decl? (P : Program) (i : DeclId) : Option Decl :=
  (P.unit? i.unit).bind fun s => s.decls[i.idx]?

/-- What a file-level name denotes: a declaration, or a unit imported as a
namespace. -/
inductive Sym where
  | decl (id : DeclId)
  | unit (path : String)
  deriving DecidableEq, Repr

/-- **The file-level scope**: in unit `u`, the name `x` denotes `σ`. -/
inductive Sees (P : Program) (R : List Remapping) : String → String → Sym → Prop where
  | own {u x : String} {s : Syn .unit} {i : Nat} {d : Decl} : P.unit? u = Option.some s →
      s.decls[i]? = Option.some d → d.scope = Option.none → d.name = x → x ≠ "" →
      Sees P R u x (.decl ⟨u, i⟩)
  | ns {u x p : String} {s : Syn .unit} : P.unit? u = Option.some s → Import.ns p x ∈ s.imports →
      Sees P R u x (.unit (Program.target R u p))
  | all {u x p : String} {s : Syn .unit} {σ : Sym} : P.unit? u = Option.some s →
      Import.all p ∈ s.imports → Sees P R (Program.target R u p) x σ → Sees P R u x σ
  | sym {u x p a : String} {s : Syn .unit} {σ : Sym} : P.unit? u = Option.some s →
      Import.sym p a x ∈ s.imports → Sees P R (Program.target R u p) a σ → Sees P R u x σ

/-- Every import of every unit names a unit of the program (solc: "Source
not found" otherwise). -/
def ImportsResolve (P : Program) (R : List Remapping) : Prop :=
  ∀ u s, (u, s) ∈ P.units → ∀ i, i ∈ s.imports →
    ∃ s', P.unit? (Program.target R u i.path) = Option.some s'

/-- Every symbol import `{a as b} from "p"` finds `a` in `p`'s file-level
scope (solc error 2904, "Declaration not found", otherwise; also for an
alias reachable only through a cycle of aliases). -/
def SymsResolve (P : Program) (R : List Remapping) : Prop :=
  ∀ u s, (u, s) ∈ P.units → ∀ p a b, Import.sym p a b ∈ s.imports →
    ∃ σ, Sees P R (Program.target R u p) a σ

/-- Kinds of declaration a file-level name may denote several of: free
functions and events overload, each only with its own kind. -/
def DeclKind.overloads : DeclKind → Bool
  | .function | .event => true
  | _ => false

/-- **No clash** in a unit's file-level scope: two different things a name
denotes are overloadable declarations of the same kind (solc's
`DeclarationContainer::conflictingDeclaration`: "Identifier already
declared" otherwise).  The same identity reached along two routes is one
thing. -/
def ScopeOK (P : Program) (R : List Remapping) : Prop :=
  ∀ u x σ σ', Sees P R u x σ → Sees P R u x σ' → σ ≠ σ' →
    ∃ i i' d d', σ = .decl i ∧ σ' = .decl i' ∧ P.decl? i = Option.some d ∧
      P.decl? i' = Option.some d' ∧ d.kind = d'.kind ∧ d.kind.overloads = true

/-- The source unit names are distinct. -/
def Program.Distinct (P : Program) : Prop := (P.units.map Prod.fst).Nodup

/-- **G12's resolution judgment** of a program: distinct unit names, every
import and imported symbol found, no clash in any file-level scope. -/
structure UnitsOK (P : Program) (R : List Remapping) : Prop where
  distinct : P.Distinct
  imports : ImportsResolve P R
  syms : SymsResolve P R
  scope : ScopeOK P R

end Solidity.Source
