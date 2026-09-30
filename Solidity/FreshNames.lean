import Solidity.Syntax

/-!
# Fresh variables by the printed names

A rule declares `.fresh b k`, and `FreshNames` spells it: `se1`, `sp1` by
default.  The names follow what each one holds, and vary per example —
`acc` is `sp1` in the headline and `mv1` in a memory example — so an
example puts its own table in scope, a renaming of the default spellings:

```
local instance : FreshNames := .ofTable [("pv", "se1"), ("acc", "sp1")]
```

Every reader and printer resolves `FreshNames` where it runs: `dl!{ … }`
reads `pv` as `.fresh "se" 1`, `sol{ … }` numbers its captures past it, and
`#derivation`, goals and `sol_chain`'s errors write `pv`.  A table changes
spellings only: a formula read under it is the term its default spelling
gives, since freshness is by index.

A printed line reads back when the table round-trips, which
`FreshNames.clashes` checks: every row renames a default spelling to an
identifier, the names are distinct and none is itself a default spelling
(`se2`), and none is a name the readers resolve before a variable — a state
variable or an enum of the contract, a word of `FreshNames.reserved`, or a
`k1` of `Calculus/Spec.lean` — or a name a reader resolves before it in
its own position: a struct type (`Account storage Account` does not read
back) or a function of the contract.  An example guards its table with
`#guard (FreshNames.clashes C rows).isEmpty`.  What it cannot check: a table
name must not be a name of the example's own program (a local `pv` would
read as the fresh one), nor a token of the grammar (`if`, `uint`).  A table
is scoped to its example by a `namespace` or a `section`.
-/

namespace Solidity

open Semantics

/-- A table: each row a name and the default spelling it replaces,
`("pv", "se1")`. -/
abbrev FreshTable := List (String × String)

/-- `rows` renames some of `base`'s spellings: `("pv", "se1")` spells
`.fresh "se" 1` as `pv`, and reads `pv` back as it.  Every other variable is
spelled by `base`.  Its default is the package's spelling (`se1`, `sp1`, …),
not the instance in scope: a default argument is elaborated here, once.  A
file with its own prefixes passes them, `.ofTable rows (.ofPrefixes …)`.  The
lookup is by spelling, so `name` reduces wherever `base.name` does (`rfl` on a
printed program). -/
def FreshNames.ofTable (rows : FreshTable) (base : FreshNames := inferInstance) :
    FreshNames where
  name b k :=
    let d := base.name b k
    ((rows.find? (·.2 == d)).map (·.1)).getD d
  parse s := base.parse (((rows.find? (·.1 == s)).map (·.2)).getD s)

/-- The words a reader resolves before a variable: `storage` and `memory`
(`tStor`, `tMem`), `true` and `false` (`tVal`), `this`, `msg` and `block`
(the environment), `selfBalance` (the environment's, and the left side of
`{ selfBalance := selfBalance - a }`), `net` (the ledger: `{ x := net }`
saves it), and the names `Calculus/Spec.lean` fixes. -/
def FreshNames.reserved : List String :=
  ["storage", "memory", "true", "false", "this", "msg", "block", "selfBalance", "net",
   "old", "oldNet", "result"]

/-- What keeps `rows` from reading back against `C`, one line per row that
fails a check below; `[]` when none does.  The module docstring says what the
checks cannot see.  `base` is the one `rows` renames, and defaults to the
package's spelling as in `ofTable`: under a table, pass the table's base, not
the table. -/
def FreshNames.clashes (C : Contract) (rows : FreshTable)
    (base : FreshNames := inferInstance) : List String :=
  let fn : FreshNames := .ofTable rows base
  rows.filterMap fun (n, d) =>
    match base.parse d with
    | some (b, k) =>
      if base.name b k != d then some s!"{d} is not a fresh variable's spelling"
      else if n.isEmpty then some s!"{d} is given the empty name"
      else if !(n.all Lean.isIdRest && n.front.isAlpha) then some s!"{n} is not a name"
      else if (base.parse n).isSome then some s!"{n} is itself a fresh variable's spelling"
      else if fn.parse n != some (b, k) then some s!"{n} names two variables"
      else if fn.name b k != n then some s!"{d} has two names"
      else if (C.rootType n).isSome || (lookupBy n C.enums).isSome then
        some s!"{n} is a state variable or an enum of the contract"
      else if !(structDef n).isEmpty || (lookupBy n C.funs).isSome then
        some s!"{n} is a struct type or a function of the contract"
      else if FreshNames.reserved.contains n || (n.startsWith "k" && n.length > 1 &&
          (n.drop 1).all Char.isDigit) then
        some s!"{n} is a word the readers resolve first"
      else none
    | none => some s!"{d} is not a fresh variable's spelling"

end Solidity
