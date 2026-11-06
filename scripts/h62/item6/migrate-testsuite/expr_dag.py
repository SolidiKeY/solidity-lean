"""Structural Expr DAG; syntax positions and metadata order/redundancy normalized. No proof values or budget overrides."""
LEAN_CODE = r'''
open Lean
namespace H62Interface

def nameJson : Name → Json
  | .anonymous => toJson (["anonymous"] : List String)
  | .str p s => Json.arr #[toJson "str", nameJson p, toJson s]
  | .num p n => Json.arr #[toJson "num", nameJson p, toJson (toString n)]

def levelJson : Level → Json
  | .zero => toJson (["zero"] : List String)
  | .succ u => Json.arr #[toJson "succ", levelJson u]
  | .max u v => Json.arr #[toJson "max", levelJson u, levelJson v]
  | .imax u v => Json.arr #[toJson "imax", levelJson u, levelJson v]
  | .param n => Json.arr #[toJson "param", nameJson n]
  | .mvar n => Json.arr #[toJson "mvar", nameJson n.name]

def binderJson : BinderInfo → Json
  | .default => toJson "default"
  | .implicit => toJson "implicit"
  | .strictImplicit => toJson "strictImplicit"
  | .instImplicit => toJson "instImplicit"

def prereJson : Syntax.Preresolved → Json
  | .namespace n => Json.arr #[toJson "namespace",nameJson n]
  | .decl n fields => Json.arr #[toJson "decl",nameJson n,toJson fields]

def syntaxJson (s : Syntax) : Json := match s with
  | .missing => toJson (["missing"] : List String)
  | .node _ kind args => Json.arr #[toJson "node",nameJson kind,Json.arr (args.attach.map (fun child => syntaxJson child.val))]
  | .atom _ value => Json.arr #[toJson "atom",toJson value]
  | .ident _ raw value resolved => Json.arr #[toJson "ident",toJson raw.toString,nameJson value,toJson (resolved.map prereJson)]
termination_by sizeOf s
decreasing_by
  have bound := Array.sizeOf_lt_of_mem child.property
  simp_wf
  omega

def dataJson : DataValue → Json
  | .ofString s => Json.arr #[toJson "string",toJson s]
  | .ofBool b => Json.arr #[toJson "bool",toJson b]
  | .ofName n => Json.arr #[toJson "name",nameJson n]
  | .ofNat n => Json.arr #[toJson "nat",toJson (toString n)]
  | .ofInt n => Json.arr #[toJson "int",toJson (toString n)]
  | .ofSyntax s => Json.arr #[toJson "syntax",syntaxJson s]

def metadataJson (md : MData) : Json :=
  let unique := Id.run do
    let mut result : Array (Name × DataValue) := #[]
    for pair in md.entries do
      unless result.any (fun previous => previous.1 == pair.1) do result := result.push pair
    return result
  let entries := unique.qsort (fun a b => (nameJson a.1).compress < (nameJson b.1).compress)
  Json.arr (entries.map (fun (key,value) => Json.arr #[nameJson key,dataJson value]))

structure Graph where
  owner : String
  seen : Std.HashMap ExprStructEq Nat := {}
  next : Nat := 0

abbrev GraphM := StateRefT Graph IO

def emit (e : Expr) : GraphM Nat := do
  if let some id := (← get).seen[ExprStructEq.mk e]? then return id
  let triple : String × Json × Array Nat ← match e with
    | .bvar i => pure ("bvar", toJson (toString i), #[])
    | .fvar i => pure ("fvar", nameJson i.name, #[])
    | .mvar i => pure ("mvar", nameJson i.name, #[])
    | .sort u => pure ("sort", levelJson u, #[])
    | .const n us => pure ("const", Json.arr #[nameJson n, toJson (us.map levelJson)], #[])
    | .app f a => do
      let f ← emit f; let a ← emit a
      pure ("app", Json.null, #[f,a])
    | .lam n t b bi => do
      let t ← emit t; let b ← emit b
      pure ("lam", Json.arr #[nameJson n,binderJson bi], #[t,b])
    | .forallE n t b bi => do
      let t ← emit t; let b ← emit b
      pure ("forallE", Json.arr #[nameJson n,binderJson bi], #[t,b])
    | .letE n t v b nondep => do
      let t ← emit t; let v ← emit v; let b ← emit b
      pure ("letE", Json.arr #[nameJson n,toJson nondep], #[t,v,b])
    | .lit (.natVal n) => pure ("nat",toJson (toString n),#[])
    | .lit (.strVal s) => pure ("str",toJson s,#[])
    | .mdata md b => do
      let b ← emit b
      unless md.entries.all (fun (key,value) => md.entries.all (fun (other,otherValue) =>
          key != other || dataJson value == dataJson otherValue)) do
        throw (IO.userError "conflicting metadata keys")
      pure ("mdata",metadataJson md,#[b])
    | .proj n i b => do
      let b ← emit b
      pure ("proj",Json.arr #[nameJson n,toJson (toString i)],#[b])
  let state ← get
  let id := state.next
  set {state with next := id+1, seen := state.seen.insert (ExprStructEq.mk e) id}
  IO.println ("H62-NODE " ++ (Json.mkObj [("module",toJson state.owner),("id",toJson id),
    ("tag",toJson triple.1),("data",triple.2.1),("children",toJson triple.2.2)]).compress)
  return id
termination_by structural e

end H62Interface
'''
