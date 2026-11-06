import Solidity.SolcValidation.IrHelperSource
open Solidity Solidity.SolcValidation Solidity.SolcValidation.IrSyntax

/-! Executable cross-check of all four imported helpers against the source
operators `BinOp.evalNum` on edge-case words. `checked_add` and `checked_mul`
are also proved (`IrHelperSource.lean`), as are `checked_sub` and the body of
`checked_div_t_int256`; this test runs all four end to end on concrete words. The
machine logs every effect and halts on `revert`. -/

abbrev Log := List (String × List Nat)

def logMachine : Machine Log where
  exec b xs s :=
    let entry := (b.name, (List.finRange _).map fun i => (xs i).val)
    if b.name == "revert" then .error (.halt (s ++ [entry]) .revert) else .ok (s ++ [entry], fun _ => 0)

def emptyCtx : ObjectCtx := ⟨[], ⟨[], List.nodup_nil⟩, fun _ => [], fun _ => none, fun _ => none⟩

def callAt (name : String) (rets : List String) (m : Mem (helperSigs ++ []) ⟨name, ["x", "y"], rets⟩) :
    Expr (helperSigs ++ []) ArgNames rets.length := .call m argPair

def subCallT := callAt "checked_sub_t_uint256" ["diff"] (.there (.there (.there (.there (.there .here)))))
def divCallT := callAt "checked_div_t_int256" ["r"] (.there (.there (.there (.there (.there (.there .here))))))
def mulCallT := callAt "checked_mul_t_uint256" ["product"]
  (.there (.there (.there (.there (.there (.there (.there .here)))))))

def W (n : Nat) : Word := Solidity.Yul.word n
def run {r : Nat} (e : Expr (helperSigs ++ []) ArgNames r) (x y : Nat) : Except String Nat :=
  match evalExpr logMachine emptyCtx 100 helperEnv e (argVals (W x) (W y)) [] with
  | .ok (_, v) => if h : 0 < r then .ok (v ⟨0, h⟩).val else .error "no value"
  | .error (.halt log .revert) =>
      match log with
      | [("mstore", [0, sel]), ("mstore", [4, code]), ("revert", [0, 36])] =>
          if sel == panicSelector.val then .error s!"panic {code}" else .error "bad selector"
      | _ => .error "unexpected effects"
  | .error _ => .error "other fault"

def edges : List Nat :=
  [0, 1, 2, 3, 7, 2 ^ 128, 2 ^ 255 - 1, 2 ^ 255, 2 ^ 255 + 1, 2 ^ 256 - 2, 2 ^ 256 - 1, 12345678901234567890]

def signedOf (n : Nat) : Int := if n < 2 ^ 255 then n else (n : Int) - 2 ^ 256

def ofSrc (r : Option Int) : Except String Nat :=
  match r with
  | some v => .ok v.toNat
  | none => .error "panic 17"

def expectU (op : String) (x y : Nat) : Except String Nat :=
  let (a, b) := ((x : Int), (y : Int))
  ofSrc <| match op with
    | "add" => (BinOp.evalNum .uint rfl a b .add rfl).map Subtype.val
    | "sub" => (BinOp.evalNum .uint rfl a b .sub rfl).map Subtype.val
    | _ => (BinOp.evalNum .uint rfl a b .mul rfl).map Subtype.val

def same (a b : Except String Nat) : Bool :=
  match a, b with
  | .ok x, .ok y => x == y
  | .error x, .error y => x == y
  | _, _ => false

#eval show IO Unit from do
  let mut n := 0
  for x in edges do
    for y in edges do
      let checks : List (String × Except String Nat × Except String Nat) :=
        [("add", run addCall x y, expectU "add" x y), ("sub", run subCallT x y, expectU "sub" x y),
         ("mul", run mulCallT x y, expectU "mul" x y)]
      let sx := signedOf x
      let sy := signedOf y
      let divExpect : Except String Nat :=
        -- The source reverts (`none`) for a zero divisor and for `min / -1`;
        -- which panic code solc uses (0x12 vs 0x11) is solc's, stated here.
        if sy = 0 then .error "panic 18"
        else match (BinOp.evalNum .int rfl sx sy .div rfl).map Subtype.val with
          | some v => .ok (W (v % 2 ^ 256).toNat).val
          | none => .error "panic 17"
      for (name, got, want) in checks ++ [("div", run divCallT x y, divExpect)] do
        unless same got want do
          throw (IO.userError s!"{name}({x}, {y}): helper {repr got}, source {repr want}")
        n := n + 1
  IO.println s!"IR_HELPER_PASS {n} helper/source agreements on edge words (add, sub, mul, int div)"

/-! Provenance of `helpersText`: it is the extracted fixture, and every
function definition in it (cut from `function` to the next one, as whole
text) is a verbatim substring of the saved solc IR. -/
#eval show IO Unit from do
  let dir := "tests/fullscope-20261104/vt1/fixtures"
  unless helpersText == (← IO.FS.readFile s!"{dir}/helpers.yul") do
    throw (IO.userError "helpersText differs from fixtures/helpers.yul")
  let census ← IO.FS.readFile s!"{dir}/Census.unoptimized.yul"
  let linked ← IO.FS.readFile s!"{dir}/LinkedMath.unoptimized.yul"
  -- Whole functions: each piece after a "function " split, up to its last
  -- closing brace, prefixed again with the keyword.
  let pieces := (helpersText.splitOn "function ").drop 1
  let mut n := 0
  for p in pieces do
    -- the last function is followed by the object's own closing braces
    let p := if p.endsWith "    }\n}\n" then p.dropRight "    }\n}\n".length else p
    let body := (p.dropRightWhile (· != '}'))
    let whole := "function " ++ body
    unless (census.splitOn whole).length > 1 || (linked.splitOn whole).length > 1 do
      throw (IO.userError s!"not a verbatim fixture substring: {whole.take 60}")
    n := n + 1
  unless n == 8 do throw (IO.userError s!"expected 8 functions, found {n}")
  IO.println s!"IR_HELPER_PROVENANCE_PASS {n} whole functions verbatim from the saved IR"
