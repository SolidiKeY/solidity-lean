import Solidity.Calculus.RewriteChains

/-!
# Writing a chain out: the pieces past the program

What `Calculus/ChainGen.lean` writes a scoped chain with, and the commands'
syntax: the rewrites a chain takes (`chainRewrite`), the bound and the
measure of the search past the program (`genNodes`, `lineSize`), the fresh
variables' spellings (`freshSpellings`), and the strategy's steps grouped
as the worked examples print them (`groupSteps`).  `#chain`, `#chain_rest`,
`#last_line`, `sol_rws` and `sol_chain?` are `Calculus/ChainGen.lean`'s and
`Calculus/LastLine.lean`'s, on scoped lines.
-/

namespace Solidity

namespace NFml.Chain

open Lean Elab Term Meta

/-- A rewrite a chain takes past the program: every one `~=>` tries but
`simplifyUpdate`, which drops the bindings nothing reads.  A chain keeps every
binding to its last line, the fresh captures (`se1`, `sp1`) included, so a
reader sees where each value went. -/
def chainRewrite (n : String) : Bool := n != "simplifyUpdate"

/-- The modality variables of a line. -/
def modalityVars (e : Expr) : MetaM (Array FVarId) := do
  let mut out := #[]
  for x in (collectFVars {} e).fvarIds do
    if (← instantiateMVars (← x.getType)).isConstOf ``Modality then out := out.push x
  return out

/-- The most lines the search past the program tries. -/
def genNodes : Nat := 150

/-- The size of a line, which the search minimises: the smaller last line is
the one with more reads resolved. -/
partial def lineSize : Expr → Nat
  | .app f a => lineSize f + lineSize a + 1
  | .lam _ t b _ | .forallE _ t b _ => lineSize t + lineSize b + 1
  | .letE _ t v b _ => lineSize t + lineSize v + lineSize b + 1
  | .mdata _ e | .proj _ _ e => lineSize e + 1
  | _ => 1

/-- The fresh variables written in `e`, by their default spellings (`se1`):
the left column of a `FreshNames` table is the name to give each. -/
partial def freshSpellings (e : Expr) : Array String :=
  let rec go (e : Expr) (acc : Array String) : Array String :=
    match e with
    | .app f a =>
      let acc := if e.isAppOfArity ``Var.fresh 2 then
          match e.appFn!.appArg!, e.appArg!.nat? <|> e.appArg!.rawNatLit? with
          | .lit (.strVal b), some k =>
            let s := s!"{b}{k}"
            if acc.contains s then acc else acc.push s
          | _, _ => acc
        else acc
      go a (go f acc)
    | .lam _ t b _ | .forallE _ t b _ => go b (go t acc)
    | .letE _ t v b _ => go b (go v (go t acc))
    | .mdata _ e | .proj _ _ e => go e acc
    | _ => acc
  go e #[]

/-! ## The links, as the worked examples print them

The worked examples print a trace
with two arrows: `⇝` for a rule, `⇝*` for a run of steps it does not dwell
on — a declaration with the binding it leaves (`uint pv = 10; Account
storage acc = alice.account;` to `{pv := 10}{acc := alice.account}`), and
`uint v = total;` to `{v := find(storage, total)}`.  They never print the
`⟨[ ]⟩` line `emptyModality` leaves.  `groupSteps` follows them: `⇝` is
`~[r]~>`, `⇝*` is `~*>`.  A run the generator leaves as several links can
be joined by hand into one `~*>`, which `sol_chain` proves alike. -/

/-- How a worked example prints a step of the strategy, by the rule that took it. -/
inductive StepKind where
  /-- a declaration dropped to its assignment, or one with no initialiser -/
  | decl
  /-- a local bound: a value assigned, an alias bound to a path -/
  | bind
  /-- a read into a local, one rule: part of the declaration it follows -/
  | read
  /-- `emptyModality`: the `⟨[ ]⟩` is never printed -/
  | empty
  /-- every other rule: an unfold, a capture, a write, a split -/
  | other
  deriving BEq

/-- The rules that drop a declaration. -/
def declRules : List String :=
  ["localValueDeclInitDrop", "valueDeclSkip", "storageLocalDeclInitDrop", "storageLocalDeclSkip",
    "memoryLocalDeclInitDrop"]

/-- The rules that bind a local to a value or a path, reading nothing. -/
def bindRules : List String :=
  ["localValueAssign", "storageLocalRootRebind", "storageFieldReadBindLocalRoot",
    "storageIndexReadMappingBindLocalRoot", "storageIndexReadArrayBindLocalRoot",
    "storageIndexReadArrayBindLocalRootMappingElement", "memoryRootRebind",
    "memoryFieldReadAliasRoot", "memoryIndexReadArrayMemory"]

/-- The rules that read a value into a local in one step. -/
def readRules : List String :=
  ["storageRootReadSelect", "storageFieldReadFind", "storageIndexReadMappingFind",
    "storageIndexReadArrayFind", "storageFieldReadStoreRoot", "storageIndexReadMappingStoreRoot",
    "storageIndexReadArrayStoreRoot", "storageLengthRead", "memoryLengthRead",
    "memoryFieldRead", "memoryIndexReadArrayValue"]

/-- The kind of the step the rule `n` takes (`""` for a rule with no name). -/
def stepKind (n : String) : StepKind :=
  if n == "emptyModality" then .empty
  else if declRules.contains n then .decl
  else if bindRules.contains n then .bind
  else if readRules.contains n then .read
  else .other

/-- The strategy's steps as the links of a chain, each with its arrow and the
line it ends at:

* a run of declarations and bindings is one `~*>` (`⇝*`): a
  declaration dropped (`StepKind.decl`), a local bound (`.bind`), and a read
  straight after a declaration, which is that declaration's initialiser
  (`.read`);
* `emptyModality` joins the link before it, so a rule and the `⟨[ ]⟩` it
  leaves are one `~*>`;
* every other step is its own `~[r]~>` (`⇝`), as is a run of one
  step. -/
def groupSteps (steps : Array (String × Expr)) : Array (String × Expr) := Id.run do
  -- each group: its rules, its last line, and whether it is a run of
  -- declarations and bindings still open
  let mut groups : Array (Array String × Expr × Bool) := #[]
  let mut prev : Option StepKind := none
  for (n, l) in steps do
    let k := stepKind n
    let openRun := match groups.back? with
      | some (_, _, o) => o
      | none => false
    let joins := match k with
      | .empty => !groups.isEmpty
      | .decl | .bind => openRun
      | .read => openRun && prev == some StepKind.decl
      | .other => false
    if joins then
      groups := groups.modify (groups.size - 1) fun (ns, _, _) =>
        (ns.push n, l, k != StepKind.empty)
    else
      groups := groups.push (#[n], l, k == StepKind.decl || k == StepKind.bind)
    prev := some k
  return groups.map fun (ns, l, _) =>
    if ns.size == 1 then
      (if ns[0]!.isEmpty then "~>" else s!"~[{ns[0]!}]~>", l)
    else ("~*>", l)

end NFml.Chain

namespace NFml.Chain
open Lean Elab Command Term Meta

/-- `#last_line c`: the chain `c` ends at a last line (`Calculus/LastLine.lean`). -/
syntax "#last_line " ident : command

/-- `#chain φ`: the chain from `φ` to its last line, as one chain term to
paste; the scoped chains' (`Calculus/ChainGen.lean`). -/
syntax "#chain " term : command

/-- `#chain_rest c`: what the chain `c` still lacks to a last line; the
scoped chains' (`Calculus/ChainGen.lean`). -/
syntax "#chain_rest " ident : command

end NFml.Chain

namespace NFml.Chain
open Lean Elab Tactic Meta

syntax "sol_rws" " [" ident,* "]" : tactic

/-- `sol_rws?`: the rewrites `#chain` takes from the line before to the line
after, suggested as `sol_rws [r₁, …, rₙ]`. -/
syntax (name := solRwsQ) "sol_rws?" : tactic

end NFml.Chain

end Solidity
