import Lean.Data.Json.Parser
import Lean.Data.Json.FromToJson.Basic
import Solidity.SolcValidation.IrCensus
open Lean Solidity.SolcValidation Solidity.SolcValidation.IrSyntax

/-! Kernel controls: the certifying parser on small inputs, evaluated by `rfl`. -/

def ok (s : String) : Bool := (parse s).toOption.isSome

private def wrap (body : String) : String := "object \"A\" { code { " ++ body ++ " } }"

-- Positive: hoisting, multi-return, for-init scope, switch/default, nested data.
example : ok (wrap "f() function f() {}") = true := rfl
example : ok (wrap "let a, b := g() function g() -> x, y { x := 1 y := 0x80 }") = true := rfl
example : ok (wrap "for { let i := 0 } lt(i, 3) { i := add(i, 1) } { if i { break } continue }") = true := rfl
example : ok (wrap "switch calldataload(0) case 0 { } case \"ab\" { } default { revert(0, 0) }") = true := rfl
example : ok "object \"A\" { code { } object \"B\" { code { } data \".m\" hex\"00ff\" } }" = true := rfl
example : ok (wrap "mstore(64, memoryguard(0x80)) setimmutable(0, \"k\", loadimmutable(\"k\"))") = true := rfl
example : ok (wrap "/// @src 0:1:2 \"x\"\n let z /** @src */ := linkersymbol(\"L\")") = true := rfl

-- Negative: each alteration is refused, never repaired.
example : ok (wrap "mstorx(0, 0)") = false := rfl                   -- unknown function
example : ok (wrap "pop(add(1))") = false := rfl                    -- builtin arity
example : ok (wrap "add(1, 2)") = false := rfl                      -- value discarded
example : ok (wrap "let x := 1 let x := 2") = false := rfl          -- shadowing
example : ok (wrap "let x := 1 { let x := 2 }") = false := rfl      -- shadowing in a nested block
example : ok (wrap "y := 1") = false := rfl                         -- undeclared target
example : ok (wrap "leave") = false := rfl                          -- leave outside a function
example : ok (wrap "break") = false := rfl                          -- break outside a loop
example : ok (wrap "for { } 1 { break } { }") = false := rfl         -- break in the post block
example : ok (wrap "let x := 1 function f() { pop(x) }") = false := rfl  -- no capture of locals
example : ok (wrap "f(1) function f() {}") = false := rfl           -- user arity
example : ok (wrap "let a := g() function g() -> x, y {}") = false := rfl -- return count
example : ok (wrap "pop(memoryguard(add(1, 2)))") = false := rfl    -- memoryguard literal
example : ok (wrap "setimmutable(0, k, 1)") = false := rfl          -- immutable name literal
example : ok (wrap "pop(datasize(\"a\", 1))") = false := rfl        -- datasize arity
example : ok (wrap "let x := 0x10000000000000000000000000000000000000000000000000000000000000000") = false := rfl
example : ok (wrap "let x := \"0123456789abcdef0123456789abcdef!\"") = false := rfl -- 33 bytes
example : ok "object \"A\" { code { } data \"d\" \"text\" }" = false := rfl  -- string data
example : ok "data \"d\" hex\"00\"" = false := rfl                  -- data root
example : ok (wrap "" ++ "}") = false := rfl                       -- trailing brace
example : ok (wrap "let x := 0x") = false := rfl                    -- malformed number

-- Scoping and static rules certified by `objectWf` (finder/skeptic C06 findings).
example : ok (wrap "function f() {} function f() {}") = false := rfl           -- duplicate function
example : ok (wrap "function add(a, b) -> c {}") = false := rfl                -- function named like a builtin
example : ok (wrap "function datasize() {}") = false := rfl                    -- object operation name
example : ok (wrap "function g() {} { function g() {} }") = false := rfl       -- inner function shadows outer
example : ok (wrap "function f() {} let f := 1") = false := rfl                -- variable named like a function
example : ok (wrap "function f(f) {}") = false := rfl                          -- parameter named like a function
example : ok (wrap "switch 1 let z := 1") = false := rfl                       -- switch without cases
example : ok (wrap "switch 1 case 1 {} case 1 {}") = false := rfl              -- duplicate case
example : ok (wrap ("switch 1 case \"a\" {} case 0x61" ++ String.mk (List.replicate 62 '0') ++ " {}")) = false := rfl
example : ok (wrap "for { { function g() {} } } 1 {} {}") = false := rfl       -- function in a for initializer
example : ok (wrap "for { } 1 { } { function g() {} }") = true := rfl          -- allowed in the body
example : ok (wrap "let x, y := g() x, x := g() function g() -> a, b {}") = false := rfl -- duplicate targets
example : ok (wrap "pop(pc())") = false := rfl                                 -- pc outside strict assembly
example : ok (wrap "let x := 0123") = false := rfl                             -- leading zero
example : ok (wrap "let x := \"\\b\\f\\v\\u00e9\"") = true := rfl            -- escapes solc accepts
example : ok "object \"A\" { code { } data \"d\" hex\"00\" data \"d\" hex\"01\" }" = false := rfl -- duplicate member

-- Shape: the census of a small tree, and an inner variable bound at its position.
example : (parse (wrap "pop(add(1, 2)) function f() -> r { r := mload(0) }")).toOption.map
    (fun p => (objectCensus [] p.parts.root).map fun (path, fns, ops) => (path, fns.map FnSig.name, ops)) =
    some [(["A"], ["f"], ["mload", "pop", "add"])] := by decide

-- The certificate: a successful parse reproduces the exact lexed tokens.
#check @Parsed.sound
#print axioms Parsed.sound

/-! External checks on the saved real solc 0.8.38 output (the parser is
untrusted; each success carries `Parsed.sound`). -/

private def fixtures : List (String × String × IrMode) :=
  [("Census", "unoptimized", .unoptimized), ("Census", "optimized", .optimized),
   ("LinkedMath", "unoptimized", .unoptimized), ("LinkedMath", "optimized", .optimized)]

private def sortStrings (xs : List String) : List String := (xs.toArray.qsort (· < ·)).toList

#eval show IO Unit from do
  let dir := "tests/fullscope-20261104/vt1/fixtures"
  let census ← IO.ofExcept (Json.parse (← IO.FS.readFile s!"{dir}/census.json"))
  let entries ← IO.ofExcept census.getArr?
  for (name, suffix, _) in fixtures do
    let text ← IO.FS.readFile s!"{dir}/{name}.{suffix}.yul"
    let parsed ← IO.ofExcept (parse text)
    let rows := objectCensus [] parsed.parts.root
    let fns := rows.flatMap fun (_, fs, _) => fs.map FnSig.name
    let ops := rows.flatMap fun (_, _, os) => os
    let mut expected : Option (List String) := none
    for e in entries do
      if (e.getObjValAs? String "contract").toOption == some name && (e.getObjValAs? String "mode").toOption == some suffix then
        expected := (e.getObjValAs? (List String) "functions").toOption
    let some exp := expected | throw (IO.userError s!"no census row for {name}.{suffix}")
    unless sortStrings fns == sortStrings exp do
      throw (IO.userError s!"{name}.{suffix}: census mismatch {fns.length} vs {exp.length}")
    IO.println s!"IR_PARSE_PASS {name}.{suffix}: {parsed.tokens.length} tokens, {rows.length} objects, {fns.length} functions, {ops.length} operation uses"
  let text ← IO.FS.readFile "tests/fullscope-20261104/vt1/ObjectData.yul"
  let parsed ← IO.ofExcept (parse text)
  IO.println s!"IR_PARSE_PASS ObjectData.yul: {parsed.tokens.length} tokens"

/-! Altered real fixtures: each mutation of the saved Census IR is refused. -/
#eval show IO Unit from do
  let text ← IO.FS.readFile "tests/fullscope-20261104/vt1/fixtures/Census.unoptimized.yul"
  let mutations : List (String × String × String) :=
    [("rename builtin", "mstore(64, memoryguard(128))", "mstorx(64, memoryguard(128))"),
     ("drop argument", "mstore(64, memoryguard(128))", "mstore(64)"),
     ("memoryguard variable", "memoryguard(128)", "memoryguard(_1)"),
     ("unbalanced brace", "object \"Census_134\" {", "object \"Census_134\" { {"),
     ("leave at top level", "mstore(64, memoryguard(128))", "leave"),
     ("shadow local", "let _12 := var_a_37", "let _12 := var_a_37 let _12 := 0"),
     ("undeclared target", "let _13 := var_b_39", "_99 := var_b_39")]
  for (label, old, new) in mutations do
    unless (text.splitOn old).length > 1 do throw (IO.userError s!"mutation site absent: {label}")
    let altered := text.replace old new
    match parse altered with
    | .ok _ => throw (IO.userError s!"altered fixture accepted: {label}")
    | .error reason => IO.println s!"IR_REFUSED {label}: {reason}"
