import Solidity.Source.Resolve


namespace Solidity.Source


def Path.split : List Char → List (List Char)
  | [] => [[]]
  | c :: cs =>
    match Path.split cs with
    | [] => [[c]]
    | s :: ss => if c = '/' then [] :: s :: ss else (c :: s) :: ss

def Path.join : List (List Char) → List Char
  | [] => []
  | [s] => s
  | s :: ss => s ++ '/' :: Path.join ss

def Path.step (acc : List (List Char)) (s : List Char) : List (List Char) :=
  if s = ['.', '.'] then acc.dropLast else if s = ['.'] then acc else acc ++ [s]

def Path.absolute (path ref : String) : String :=
  match Path.split path.toList with
  | first :: rest =>
    if first = ['.'] ∨ first = ['.', '.'] then
      String.mk (Path.join ((first :: rest).foldl Path.step (Path.split ref.toList).dropLast))
    else path
  | [] => path

structure Remapping where
  context : String := ""
  pre : String
  target : String
  deriving DecidableEq, Repr

def Remapping.matches (r : Remapping) (ctx path : String) : Bool :=
  r.context.toList.isPrefixOf ctx.toList && r.pre.toList.isPrefixOf path.toList

def Remapping.closer (r b : Remapping) : Bool :=
  decide (b.context.length < r.context.length) ||
    (decide (b.context.length = r.context.length) && decide (b.pre.length ≤ r.pre.length))

def Remapping.select (rs : List Remapping) (ctx path : String) : Option Remapping :=
  rs.foldl (fun best r =>
    if r.matches ctx path then
      match best with
      | Option.none => Option.some r
      | Option.some b => if r.closer b then Option.some r else Option.some b
    else best) Option.none

def Remapping.apply (rs : List Remapping) (ctx path : String) : String :=
  match Remapping.select rs ctx path with
  | Option.none => path
  | Option.some r => String.mk (r.target.toList ++ path.toList.drop r.pre.length)


inductive Import where
  | all (path : String)
  | ns (path alias : String)
  | sym (path symbol alias : String)
  deriving DecidableEq, Repr

def Import.path : Import → String
  | .all p | .ns p _ | .sym p _ _ => p

def Syn.importAliases : {c : Cat} → Syn c → List (String × String)
  | _, .cons x xs => x.importAliases ++ xs.importAliases
  | _, .importAlias s a => [(s, a.getD s)]
  | _, _ => []

def Syn.imports : {c : Cat} → Syn c → List Import
  | _, .unit xs => xs.imports
  | _, .cons x xs => x.imports ++ xs.imports
  | _, .importPath p Option.none => [.all p]
  | _, .importPath p (Option.some a) => [.ns p a]
  | _, .importStar a p => [.ns p a]
  | _, .importSymbols x xs p => (x.importAliases ++ xs.importAliases).map fun (s, a) => .sym p s a
  | _, _ => []


structure UnitSet where
  units : List (String × Syn .unit)

def UnitSet.unit? (P : UnitSet) (u : String) : Option (Syn .unit) :=
  (P.units.find? (·.1 == u)).map (·.2)

example (P : UnitSet) (Canonical : String → Prop)
    (names : ∀ (entry : String × Syn .unit), entry ∈ P.units → Canonical entry.1)
    {u : String} {s : Syn .unit} (found : P.unit? u = some s) :
    Canonical u := by
  unfold UnitSet.unit? at found
  cases selected : P.units.find? (·.1 == u) with
  | none =>
    rw [selected] at found
    cases found
  | some entry =>
    have member := List.mem_of_find?_eq_some selected
    have same : entry.1 = u := by
      simpa using List.find?_some selected
    exact same ▸ names entry member

def UnitSet.target (R : List Remapping) (u p : String) : String :=
  Remapping.apply R u (Path.absolute p u)

structure DeclId where
  unit : String
  idx : Nat
  deriving DecidableEq, Repr

def UnitSet.decl? (P : UnitSet) (i : DeclId) : Option Decl :=
  (P.unit? i.unit).bind fun s => s.decls[i.idx]?

inductive Sym where
  | decl (id : DeclId)
  | unit (path : String)
  deriving DecidableEq, Repr

inductive Sees (P : UnitSet) (R : List Remapping) : String → String → Sym → Prop where
  | own {u x : String} {s : Syn .unit} {i : Nat} {d : Decl} : P.unit? u = Option.some s →
      s.decls[i]? = Option.some d → d.scope = Option.none → d.name = x → x ≠ "" →
      Sees P R u x (.decl ⟨u, i⟩)
  | ns {u x p : String} {s : Syn .unit} : P.unit? u = Option.some s → Import.ns p x ∈ s.imports →
      Sees P R u x (.unit (UnitSet.target R u p))
  | all {u x p : String} {s : Syn .unit} {σ : Sym} : P.unit? u = Option.some s →
      Import.all p ∈ s.imports → Sees P R (UnitSet.target R u p) x σ → Sees P R u x σ
  | sym {u x p a : String} {s : Syn .unit} {σ : Sym} : P.unit? u = Option.some s →
      Import.sym p a x ∈ s.imports → Sees P R (UnitSet.target R u p) a σ → Sees P R u x σ

def ImportsResolve (P : UnitSet) (R : List Remapping) : Prop :=
  ∀ u s, (u, s) ∈ P.units → ∀ i, i ∈ s.imports →
    ∃ s', P.unit? (UnitSet.target R u i.path) = Option.some s'

def SymsResolve (P : UnitSet) (R : List Remapping) : Prop :=
  ∀ u s, (u, s) ∈ P.units → ∀ p a b, Import.sym p a b ∈ s.imports →
    ∃ σ, Sees P R (UnitSet.target R u p) a σ

def DeclKind.overloads : DeclKind → Bool
  | .function | .event => true
  | _ => false

def ScopeOK (P : UnitSet) (R : List Remapping) : Prop :=
  ∀ u x σ σ', Sees P R u x σ → Sees P R u x σ' → σ ≠ σ' →
    ∃ i i' d d', σ = .decl i ∧ σ' = .decl i' ∧ P.decl? i = Option.some d ∧
      P.decl? i' = Option.some d' ∧ d.kind = d'.kind ∧ d.kind.overloads = true

def UnitSet.Distinct (P : UnitSet) : Prop := (P.units.map Prod.fst).Nodup

structure UnitsOK (P : UnitSet) (R : List Remapping) : Prop where
  distinct : P.Distinct
  imports : ImportsResolve P R
  syms : SymsResolve P R
  scope : ScopeOK P R

end Solidity.Source
