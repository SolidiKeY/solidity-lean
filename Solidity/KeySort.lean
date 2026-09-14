/-!
# The KeY sort lattice of solkey

A transcription of the sorts solkey declares, and of the `\extends`
relation between them, as one Lean type. Every constructor is a sort
that exists upstream, and every edge of `parents` is one line of a
`.key` header or one `new …Sort(…)` in the Java that creates sorts at
parse time. Nothing here is chosen: this file is read off
`SolidiKeY/solkey` at the commit `e67a0d7c48`, and it is the *only* model of
the lattice — `TacletAnnotations`,
`SortFaithfulness` and the `SolKey` reader's decoder all state their sort
claims against it, so the two packages cannot disagree about what
`\extends Prim` means.

The named sorts (`keyext.solidity.core/src/main/resources/org/key_project/solidity/proof/rules/`):

```
solidityDLHeader.key   any; StValue; MemValue; Prim \extends StValue, MemValue;
structHeader.key       Struct \extends StValue; Field; MapField, RefField \extends Field;
memoryHeader.key       Memory; Identity \extends MemValue; IdentityPrim;
boolHeader.key         bool \extends Prim;
intHeader.key          numbers; int \extends Prim;
listHeader.key         List;
```

The sorts the parser creates per contract
(`keyext.solidity.core/src/main/java/org/key_project/solidity/program/parser/SolJSONParser.java`):

- `DynamicArraySort`/`ArraySort` for `T[]`/`T[n]` and `MappingSort` for
  `mapping(K => V)`, each `\extends StValue` **directly** — siblings of
  `Struct`, not below it (`valueSupersort("StValue")`, lines 1015–1030);
- one `SortImpl` per contract, `\extends Prim` (line 211, "HACK, inheritance").

So the value lattice is

```
                     any
        StValue               MemValue
   Struct  T[]  mapping(K=>V)  Prim   Identity
                          int  bool  <Contract>
```

with `Field ⊃ {MapField, RefField}` and the free-standing `List`,
`Memory`, `IdentityPrim`, `numbers` beside it. `any` is the implicit top
(`SortImpl.extendsSorts` returns `{any}` for a sort with no `\extends`).

Constructor names are lowercase Lean identifiers; `name`/`ofName` carry
the KeY spelling. The KeY names `List`, `Memory` and `Field` would
otherwise shadow `List KeySort` inside this namespace and the AST's
`Field` in every file that opened it.

This module imports nothing: `AST.lean` imports it, and the maps from
Solidity static types to these sorts (`Ty.keySort`, `Ty.fieldSort`,
`localVarSort`) live there, next to `Ty`.
-/

namespace Solidity

/-- A KeY sort of solkey's calculus — see the module docstring for the
declaration each constructor transcribes. `array`, `mapping` and
`contract` are the sorts `SolJSONParser` creates per Solidity program;
the rest are declared once in the headers. -/
inductive KeySort where
  | any
  | stValue
  | memValue
  | prim
  | int
  | bool
  | struct
  | identity
  | field
  | mapField
  | refField
  | list
  | memory
  | identityPrim
  | numbers
  /-- `T[]` / `T[n]` (`DynamicArraySort`, `ArraySort`): `\extends StValue`. -/
  | array (elem : KeySort)
  /-- `mapping(K => V)` (`MappingSort`): `\extends StValue`. -/
  | mapping (key value : KeySort)
  /-- The per-contract sort, `\extends Prim`. -/
  | contract (name : String)
  deriving Repr, DecidableEq, Inhabited

namespace KeySort

/-- The direct `\extends` edges, one arm per declaration. A sort with no
`\extends` clause is directly below `any` (`SortImpl.extendsSorts`). -/
def parents : KeySort -> List KeySort
  | any => []
  | stValue => [any]                    -- solidityDLHeader.key:3
  | memValue => [any]                   -- solidityDLHeader.key:4
  | prim => [stValue, memValue]         -- solidityDLHeader.key:5
  | int => [prim]                       -- intHeader.key:3
  | bool => [prim]                      -- boolHeader.key:2
  | struct => [stValue]                 -- structHeader.key:2
  | identity => [memValue]              -- memoryHeader.key:3
  | field => [any]                      -- structHeader.key:3
  | mapField => [field]                 -- structHeader.key:4
  | refField => [field]                 -- structHeader.key:5
  | list => [any]                       -- listHeader.key:2
  | memory => [any]                     -- memoryHeader.key:2
  | identityPrim => [any]               -- memoryHeader.key:4
  | numbers => [any]                    -- intHeader.key:2
  | array _ => [stValue]                -- SolJSONParser.java:1015-1023
  | mapping _ _ => [stValue]            -- SolJSONParser.java:1028-1030
  | contract _ => [prim]                -- SolJSONParser.java:211

/-- The strict supersorts of a sort: the transitive closure of `parents`,
written out per constructor so that it is a structural function (the
refutations in `Counterexamples/` need `le` to reduce under kernel
evaluation). `ancestors_eq_closure` proves it equal to the computed
closure of `parents` (both inclusions); `parents_sub_ancestors` and
`ancestors_closed` are the two easy consequences. -/
def ancestors : KeySort -> List KeySort
  | any => []
  | stValue => [any]
  | memValue => [any]
  | prim => [stValue, memValue, any]
  | int => [prim, stValue, memValue, any]
  | bool => [prim, stValue, memValue, any]
  | struct => [stValue, any]
  | identity => [memValue, any]
  | field => [any]
  | mapField => [field, any]
  | refField => [field, any]
  | list => [any]
  | memory => [any]
  | identityPrim => [any]
  | numbers => [any]
  | array _ => [stValue, any]
  | mapping _ _ => [stValue, any]
  | contract _ => [prim, stValue, memValue, any]

/-- The subsort relation `a ≤ b` (`Sort.extendsTrans` with reflexivity):
`a` is `b` or `b` is one of its supersorts. `\generic G \extends b`
binds `G := a` exactly when this holds. -/
def le (a b : KeySort) : Bool :=
  a == b || a.ancestors.contains b

/-- The sorts the headers name directly — everything except the
per-program `array`/`mapping`/`contract` sorts. -/
def isBase : KeySort -> Bool
  | array _ => false
  | mapping _ _ => false
  | contract _ => false
  | _ => true

/-- The KeY spelling. Array and mapping sorts are named as `ArraySort` /
`MappingSort` name them (`elem + "[]"`, `"mapping(" + k + " => " + v + ")"`);
a contract sort is named after the contract. -/
def name : KeySort -> String
  | any => "any"
  | stValue => "StValue"
  | memValue => "MemValue"
  | prim => "Prim"
  | int => "int"
  | bool => "bool"
  | struct => "Struct"
  | identity => "Identity"
  | field => "Field"
  | mapField => "MapField"
  | refField => "RefField"
  | list => "List"
  | memory => "Memory"
  | identityPrim => "IdentityPrim"
  | numbers => "numbers"
  | array elem => elem.name ++ "[]"
  | mapping key value => "mapping(" ++ key.name ++ " => " ++ value.name ++ ")"
  | contract n => n

/-- The base sort a KeY name denotes — how a `\extends` bound or a
`find<[…]>` sort parameter arrives from the `.key` text. Program-created
sorts have no fixed name and are not looked up this way. -/
def ofName : String -> Option KeySort
  | "any" => some any
  | "StValue" => some stValue
  | "MemValue" => some memValue
  | "Prim" => some prim
  | "int" => some int
  | "bool" => some bool
  | "Struct" => some struct
  | "Identity" => some identity
  | "Field" => some field
  | "MapField" => some mapField
  | "RefField" => some refField
  | "List" => some list
  | "Memory" => some memory
  | "IdentityPrim" => some identityPrim
  | "numbers" => some numbers
  | _ => none

/-! ## The lattice facts -/

theorem ofName_name (s : KeySort) (h : s.isBase = true) : ofName s.name = some s := by
  cases s <;> first | rfl | exact Bool.noConfusion h

theorem le_refl (a : KeySort) : le a a = true := by
  simp [le]

theorem le_any (a : KeySort) : le a any = true := by
  cases a <;> rfl

/-- Every declared edge is in the closure. -/
theorem parents_sub_ancestors (a : KeySort) :
    a.parents.all (fun p => a.ancestors.contains p) = true := by
  cases a <;> rfl

/-- The closure is closed: a supersort's supersorts are supersorts. -/
theorem ancestors_closed (a : KeySort) :
    a.ancestors.all (fun b => b.ancestors.all (fun c => a.ancestors.contains c)) = true := by
  cases a <;> rfl

/-- The supersorts reachable from `a` by at most `fuel` `parents` edges —
the transitive closure of `parents`, computed rather than tabulated. -/
def closureFuel : Nat -> KeySort -> List KeySort
  | 0, _ => []
  | fuel + 1, a => a.parents ++ a.parents.flatMap (closureFuel fuel)

/-- `ancestors` is *exactly* the closure of `parents` (the lattice has
depth ≤ 4, so fuel 8 is saturated): every tabulated ancestor is reachable
along declared `\extends` edges, and every reachable sort is tabulated.
`parents_sub_ancestors` and `ancestors_closed` only give the second
inclusion; a stray extra row in `ancestors` would pass them and fails
this. -/
theorem ancestors_eq_closure (a : KeySort) :
    (a.ancestors.all (fun b => (closureFuel 8 a).contains b) &&
      (closureFuel 8 a).all (fun b => a.ancestors.contains b)) = true := by
  cases a <;> rfl

/-- No sort is its own strict supersort (the lattice is acyclic). -/
theorem ancestors_irrefl (a : KeySort) : a.ancestors.contains a = false := by
  cases a <;> simp [ancestors]

theorem le_trans {a b c : KeySort} (hab : le a b = true) (hbc : le b c = true) :
    le a c = true := by
  simp only [le, Bool.or_eq_true, beq_iff_eq, List.contains_iff_mem] at hab hbc ⊢
  rcases hab with rfl | hab
  · exact hbc
  rcases hbc with rfl | hbc
  · exact Or.inr hab
  right
  have hclosed := ancestors_closed a
  simp only [List.all_eq_true, List.contains_iff_mem] at hclosed
  exact hclosed b hab c hbc

-- The header lines, as theorems.
example : le prim stValue = true := by decide     -- Prim \extends StValue
example : le prim memValue = true := by decide    -- Prim \extends MemValue
example : le int prim = true := by decide         -- int \extends Prim
example : le bool prim = true := by decide        -- bool \extends Prim
example : le struct stValue = true := by decide   -- Struct \extends StValue
example : le identity memValue = true := by decide
example : le mapField field = true := by decide
example : le refField field = true := by decide
example : le (array int) stValue = true := by decide
example : le (mapping int bool) stValue = true := by decide
example : le (contract "C") prim = true := by decide
-- What is *not* below what: arrays and mappings are not `Struct`, and
-- `IdentityPrim` is not a `MemValue`.
example : le (array int) struct = false := by decide
example : le (mapping int bool) struct = false := by decide
example : le identityPrim memValue = false := by decide
example : le struct memValue = false := by decide
example : le identity stValue = false := by decide

end KeySort

end Solidity
