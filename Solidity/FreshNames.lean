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

The factory checks the universal round-trip law with `FreshNames.tableValid`.
`FreshNames.clashes` additionally checks that every row renames a default spelling to an
identifier, the names are distinct and none is itself a default spelling
(`se2`), and none is a name the readers resolve before a variable — a state
variable or an enum of the contract, a word of `FreshNames.reserved`, or a
`k1` of `Calculus/SurfaceSpec.lean` — or a name a reader resolves before it in
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

private def FreshNames.tableName (rows : FreshTable) (base : FreshNames)
    (b : String) (k : Nat) : String :=
  let d := base.name b k
  ((rows.find? (·.2 == d)).map (·.1)).getD d

private def FreshNames.tableParse (rows : FreshTable) (base : FreshNames)
    (s : String) : Option (String × Nat) :=
  base.parse (((rows.find? (·.1 == s)).map (·.2)).getD s)

/-- Aliases must not hide a base spelling, and each chosen alias must read
back to the spelling it replaces. This finite check certifies every index. -/
def FreshNames.tableValid (rows : FreshTable) (base : FreshNames := inferInstance) : Bool :=
  rows.all fun (n, d) => (base.parse n).isNone &&
    ((rows.find? (·.1 == n)).map Prod.snd == some d)

/-- `rows` renames some of `base`'s spellings: `("pv", "se1")` spells
`.fresh "se" 1` as `pv`, and reads `pv` back as it. All other variables retain
`base`'s spelling. The default base is the package's scheme, independent of
the instance in scope. The auto-parameter checks the finite alias table. -/
def FreshNames.ofTable (rows : FreshTable) (base : FreshNames := inferInstance)
    (valid : tableValid rows base = true := by decide) : FreshNames where
  name := tableName rows base
  parse := tableParse rows base
  roundTrip b hb k := by
    have law := base.roundTrip b hb k
    let p := fun (row : String × String) => (base.parse row.1).isNone &&
      ((rows.find? (·.1 == row.1)).map Prod.snd == some row.2)
    have checked : ∀ rs : FreshTable, rs.all p = true → ∀ row ∈ rs, p row = true := by
      intro rs
      induction rs with
      | nil => intro _ _ hm; cases hm
      | cons x xs ih =>
        intro h row hm
        have hs := Bool.and_eq_true_iff.mp h
        rcases List.mem_cons.mp hm with rfl | hm
        · exact hs.1
        · exact ih hs.2 row hm
    have hv := checked rows valid
    unfold tableName
    cases hf : rows.find? (·.2 == base.name b k) with
    | some row =>
      have hd : row.2 = base.name b k := by
        have ht : (row.2 == base.name b k) = true :=
          List.find?_some (p := fun x : String × String => x.2 == base.name b k) hf
        exact beq_iff_eq.mp ht
      have hr := Bool.and_eq_true_iff.mp (hv row (List.mem_of_find?_eq_some hf))
      have back := beq_iff_eq.mp hr.2
      simp only [hf, Option.map_some, Option.getD_some]
      unfold tableParse
      rw [back]
      exact hd ▸ law
    | none =>
      simp only [hf, Option.map_none, Option.getD_none]
      unfold tableParse
      cases hg : rows.find? (·.1 == base.name b k) with
      | none => simpa only [hg, Option.map_none, Option.getD_none] using law
      | some row =>
        have hn : row.1 = base.name b k := by
          have ht : (row.1 == base.name b k) = true :=
            List.find?_some (p := fun x : String × String => x.1 == base.name b k) hg
          exact beq_iff_eq.mp ht
        have hr := (Bool.and_eq_true_iff.mp (hv row (List.mem_of_find?_eq_some hg))).1
        change (base.parse row.1).isNone = true at hr
        rw [hn, law] at hr
        cases hr

/-- The words a reader resolves before a variable: `storage` and `memory`
(`tStor`, `tMem`), `true` and `false` (`tVal`), `this`, `msg` and `block`
(the environment), `selfBalance` (the environment's, and the left side of
`{ selfBalance := selfBalance - a }`), `net` (the ledger: `{ x := net }`
saves it), and the names `Calculus/SurfaceSpec.lean` fixes. -/
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
  rows.filterMap fun (n, d) =>
    match base.parse d with
    | some (b, k) =>
      if base.name b k != d then some s!"{d} is not a fresh variable's spelling"
      else if n.isEmpty then some s!"{d} is given the empty name"
      else if !(n.all Lean.isIdRest && n.front.isAlpha) then some s!"{n} is not a name"
      else if (base.parse n).isSome then some s!"{n} is itself a fresh variable's spelling"
      else if FreshNames.tableParse rows base n != some (b, k) then some s!"{n} names two variables"
      else if FreshNames.tableName rows base b k != n then some s!"{d} has two names"
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
