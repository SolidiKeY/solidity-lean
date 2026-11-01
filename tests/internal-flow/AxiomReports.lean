import Lean
/-! Test-only checked-kernel dependency reporting. This does not create/check
proofs or change the builtin #print axioms implementation. Discovery records
exact standard dependency edges once; propagation from each actual axiom along
reverse edges computes per-root reachability, with visited sets handling cycles.
The cached validation gate independently uses Lean's unmodified builtin. -/
namespace InternalFlowAxiomBatch
open Lean

/-- The same dependency edges used by Lean's standard collector, from the
checked kernel environment. No elaborator declarations are trusted here. -/
def entry (env : Kernel.Environment) (name : Name) : Bool × Array Name :=
  match env.find? name with
  | some (.axiomInfo d) => (true,d.type.getUsedConstants)
  | some (.defnInfo d) => (false,d.type.getUsedConstants ++ d.value.getUsedConstants)
  | some (.thmInfo d) => (false,d.type.getUsedConstants ++ d.value.getUsedConstants)
  | some (.opaqueInfo d) => (false,d.type.getUsedConstants ++ d.value.getUsedConstants)
  | some (.ctorInfo d) => (false,d.type.getUsedConstants)
  | some (.recInfo d) => (false,d.type.getUsedConstants)
  | some (.inductInfo d) => (false,d.type.getUsedConstants ++ d.ctors.toArray)
  | some (.quotInfo _) | none => (false,#[])

structure Graph where
  seen : NameSet := {}
  parents : NameMap (Array Name) := {}
  seeds : Array Name := #[]

/-- Discover the entire union of reachable declarations once. -/
partial def discover (env : Kernel.Environment) (todo : List Name) (graph : Graph) : Graph :=
  match todo with
  | [] => graph
  | name :: rest =>
    if graph.seen.contains name then discover env rest graph else Id.run do
      let (isAx,deps) := entry env name
      let mut next := {graph with seen := graph.seen.insert name}
      if isAx then next := {next with seeds := next.seeds.push name}
      for dep in deps do
        let parents := next.parents.insert dep (((next.parents.find? dep).getD #[]).push name)
        next := {next with parents := parents}
      return discover env (deps.toList ++ rest) next

/-- Reverse reachability is exact even for cyclic declaration graphs. -/
partial def propagate (parents : NameMap (Array Name)) (seed : Name)
    (todo : List Name) (seen : NameSet) (out : NameMap NameSet) : NameMap NameSet :=
  match todo with
  | [] => out
  | name :: rest =>
    if seen.contains name then propagate parents seed rest seen out else
      let out := out.insert name (((out.find? name).getD {}).insert seed)
      propagate parents seed (((parents.find? name).getD #[]).toList ++ rest)
        (seen.insert name) out

def sorted (names : NameSet) : Array Name := Id.run do
  let mut out := #[]
  for name in names do out := out.push name
  return out.qsort Name.lt

def collect (env : Kernel.Environment) (roots : Array Name) : Array (Array Name) := Id.run do
  let graph := discover env roots.toList {}
  let mut out : NameMap NameSet := {}
  for seed in graph.seeds do
    out := propagate graph.parents seed [seed] {} out
  return roots.map fun root => sorted ((out.find? root).getD {})
open Lean Elab Command

/-- Reporting only: force the same checked kernel snapshot as #print axioms.
The ordinary builtin command remains unchanged for independent audits. -/
syntax (name := printCheckedAxioms) "#print_checked_axioms " ident,+ : command

elab_rules : command
  | `(#print_checked_axioms $ids:ident,*) => do
    let env ← getEnv
    if env.header.isModule then
      throwError "cannot report checked axioms in a module header file"
    let mut roots : Array Name := #[]
    for id in ids.getElems do
      roots := roots ++ (← liftCoreM <| realizeGlobalConstWithInfos id).toArray
    let checked := (← getEnv).checked.get
    let actual := collect checked roots
    unless actual.size == roots.size do throwError "lost checked axiom report"
    for i in [:roots.size] do
      let root := roots[i]!
      let axioms := actual[i]!
      if axioms.isEmpty then
        logInfo m!"'{root}' does not depend on any axioms"
      else
        logInfo m!"'{root}' depends on axioms: {axioms.toList}"

/- Test the real checked environment, including recursive declaration types,
repeated queries and roots with different axiom sets. No expected pin table is
used by the collector. A new environment and traversal are used for each batch. -/
run_elab do
  let roots := #[``Classical.choice,``Nat.add_comm,``Quot.sound,``Nat.add_comm,
    ``propext,``Lean.Expr,``Lean.Expr.app,``List.rec,``List.map,``Nat.add_comm]
  let env ← getEnv
  let actual := collect env.checked.get roots
  unless actual.size == roots.size do throwError "lost axiom report"
  for i in [:roots.size] do
    let reference := (← Lean.collectAxioms roots[i]!).qsort Name.lt
    unless actual[i]! == reference do
      throwError "checked axiom graph differs from builtin collector at {roots[i]!}"

/-- info: 'Nat.add_comm' does not depend on any axioms -/
#guard_msgs in #print_checked_axioms Nat.add_comm

end InternalFlowAxiomBatch
