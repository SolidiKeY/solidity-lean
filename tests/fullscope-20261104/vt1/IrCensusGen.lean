import Solidity.SolcValidation.IrParse
open Solidity.SolcValidation Solidity.SolcValidation.IrSyntax

/-! Prints the parsed trees of the saved `Census` and `LinkedMath` `--ir` fixtures
as Lean terms, one line per piece (`fixtures/census-tree.txt`), from which
`gen-census-modules.py` writes `Solidity/SolcValidation/IrCensusCreation.lean`,
`IrCensusDeployed.lean`, `IrLinkedCode.lean`, `IrCensusTree.lean` and `IrCensusMaps.lean`. Nothing here is trusted: `census_certified` and
`linked_certified` re-check the modules' trees against the quoted texts by kernel
evaluation. The printers are those of `IrLeanGen.lean`. -/

def q (s : String) : String := s.quote
def strs (xs : List String) : String := "[" ++ ", ".intercalate (xs.map q) ++ "]"

def memL {α} {L : List α} {x : α} : Mem L x → String
  | .here => ".here"
  | .there m => s!"(.there {memL m})"

def litL (l : Lit) : String :=
  match l.tok with
  | .num n => s!"⟨.num {n}, {l.value.val}, rfl⟩"
  | .str raw => s!"⟨.str {q raw}, {l.value.val}, rfl⟩"
  | .bool b => s!"⟨.bool {b}, {l.value.val}, rfl⟩"

def isPureName (n : String) : Bool :=
  ["iszero", "not", "clz", "add", "sub", "mul", "div", "sdiv", "mod", "smod", "exp", "lt", "gt",
   "slt", "sgt", "eq", "and", "or", "xor", "byte", "shl", "shr", "sar", "signextend",
   "addmod", "mulmod"].contains n

def opL {a r : Nat} : Op a r → String
  | .evm b => if isPureName b.name then s!"(.evm (.pure .«{b.name}»))" else s!"(.evm .«{b.name}»)"
  | .object o =>
    match a, r, o with
    | _, _, .datasize l => s!"(.object (.datasize {q l}))"
    | _, _, .dataoffset l => s!"(.object (.dataoffset {q l}))"
    | _, _, .datacopy => "(.object .datacopy)"
    | _, _, .setimmutable l => s!"(.object (.setimmutable {q l}))"
    | _, _, .loadimmutable l => s!"(.object (.loadimmutable {q l}))"
    | _, _, .linkersymbol l => s!"(.object (.linkersymbol {q l}))"
    | _, _, .memoryguard n => s!"(.object (.memoryguard ⟨{n.val}, by decide⟩))"

mutual
def exprL {F L r} : Expr F L r → String
  | .lit l => s!"(.lit {litL l})"
  | .var x m => s!"(.var {q x} {memL m})"
  | .op o args => s!"(.op {opL o} {argsL args})"
  | .call m args => s!"(.call {memL m} {argsL args})"
def argsL {F L k} : Args F L k → String
  | .nil => ".nil"
  | .cons e rest => s!"(.cons {exprL e} {argsL rest})"
end

def initL {F L} {xs : List String} : Option (Expr F L xs.length) → String
  | none => "none"
  | some e => s!"(some {exprL e})"

def sigL (s : FnSig) : String := s!"⟨{q s.name}, {strs s.params}, {strs s.rets}⟩"

mutual
def stmtL {F c L} : Stmt F c L → String
  | .block b => s!"(.block {blockL b})"
  | .discard e => s!"(.discard {exprL e})"
  | .assign ts e => "(.assign [" ++ ", ".intercalate (ts.map fun t => s!"⟨{q t.1}, {memL t.2}⟩") ++ s!"] {exprL e})"
  | .if_ e b => s!"(.if_ {exprL e} {blockL b})"
  | .switch e cs => s!"(.switch {exprL e} {casesL cs})"
  | .switchDefault e cs b => s!"(.switchDefault {exprL e} {casesL cs} {blockL b})"
  | .for_ lp => s!"(.for_ {loopL lp})"
  | .leave => ".leave"
  | .break_ => ".break_"
  | .continue_ => ".continue_"
def casesL {F c L} : Cases F c L → String
  | .nil => ".nil"
  | .cons l b rest => s!"(.cons {litL l} {blockL b} {casesL rest})"
def loopL {F c L} : Loop F c L → String
  | .stmt s rest => s!"(.stmt {stmtL s} {loopL rest})"
  | .let_ xs e rest => s!"(.let_ {strs xs} {initL e} {loopL rest})"
  | .run e post body => s!"(.run {exprL e} {blockL post} {blockL body})"
def itemsL {F c L g} : Items F c L g → String
  | .nil => ".nil"
  | .stmt s rest => s!"(.stmt {stmtL s} {itemsL rest})"
  | .let_ xs e rest => s!"(.let_ {strs xs} {initL e} {itemsL rest})"
  | .fn k rest => s!"(.fn ⟨{k.val}, by decide⟩ {itemsL rest})"
def blockL {F c L} : Block F c L → String
  | .mk ss bodies items =>
      "(.mk [" ++ ", ".intercalate (ss.map sigL) ++ s!"] {bodiesL bodies} {itemsL items})"
def bodiesL {G ss} : Bodies G ss → String
  | .nil => ".nil"
  | .cons b rest => s!"(.cons {blockL b} {bodiesL rest})"
end


def hexL (bytes : List (Fin 256)) : String :=
  "[" ++ ", ".intercalate (bytes.map fun b => toString b.val) ++ "]"

/-- One object: `OBJ name`, `SIGS`, one `BODY` per function, `ITEMS`, then its
children (`DATA name bytes` or nested objects), then `END`. -/
partial def objectLines : Object Code → List String
  | .object n (.mk ss bodies items) ch =>
      let rec bodyLines {G ss} : Bodies G ss → List String
        | .nil => []
        | .cons b rest => ("BODY " ++ blockL b) :: bodyLines rest
      ["OBJ " ++ n, "SIGS [" ++ ", ".intercalate (ss.map sigL) ++ "]"] ++ bodyLines bodies ++
        ["ITEMS " ++ itemsL items] ++ ch.flatMap objectLines ++ ["END"]
  | .data n bytes => ["DATA " ++ n ++ " " ++ hexL bytes]

#eval show IO Unit from do
  let dir := "tests/fullscope-20261104/vt1/fixtures"
  let mut lines : List String := []
  for f in ["Census.unoptimized", "LinkedMath.unoptimized"] do
    let text ← IO.FS.readFile s!"{dir}/{f}.yul"
    match parse text with
    | .ok p => lines := lines ++ ["FILE " ++ f] ++ objectLines p.parts.root
    | .error e => throw (IO.userError s!"{f}: {e}")
  IO.FS.writeFile s!"{dir}/census-tree.txt" ("\n".intercalate lines ++ "\n")
  IO.println s!"CENSUS_TREE {lines.length} lines"
