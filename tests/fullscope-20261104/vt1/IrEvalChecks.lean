import Lean.Data.Json.Parser
import Lean.Data.Json.FromToJson.Basic
import Solidity.SolcValidation.IrEval
import Solidity.SolcValidation.IrParse
import Solidity.Keccak
open Lean Solidity.SolcValidation Solidity.SolcValidation.IrSyntax

/-! Executable witnesses: the real solc 0.8.38 IR, parsed by the certifying
parser, run by `IrEval` on a small concrete byte-memory machine defined here
(a test fixture, not a model of the EVM: no gas, no calls, bounded memory).

The constructor runs with the saved creation bytecode as its code and the
data table placed by `generate-artifacts.py`, so the copied runtime bytes equal
the saved `deployedBytecode` by construction. What the comparison does test is
the IR's plumbing: the label it copies and returns (`…_deployed`, not the
enclosing object), the constructor argument decoded through
`datasize(<object>)`/`codesize`/`codecopy`, the `setimmutable` offsets relative
to the copy buffer, and storage. Immutable positions are zero `PUSH32` operands
of the deployed code, cross-checked against the creation code's `PUSH2 <pos>`
(`generate-artifacts.py`); no `immutableReferences` were requested from solc.
The saved bytecode was assembled from `irOptimized` (optimizer off), so for the
`unoptimized` channel the comparison is plumbing only: LinkedMath's unoptimized
`setimmutable` has no positions in that bytecode. Runtime calls read the seed
back from the constructor's returned code. `linkersymbol` is not executed
(no calls in the machine); link bytes are placed by the test. -/

structure St where
  mem : Array (Fin 256) := #[]
  storage : List (Nat × Word) := []
  calldata : Array (Fin 256) := #[]
  code : Array (Fin 256) := #[]
  callvalue : Word := 0
  self : Word := 0
  output : Array (Fin 256) := #[]

def W (n : Nat) : Word := Solidity.Yul.word n
def byteOf (n : Nat) : Fin 256 := ⟨n % 256, Nat.mod_lt _ (by decide)⟩
def readWord (a : Array (Fin 256)) (off : Nat) : Word :=
  W ((List.range 32).foldl (fun acc j => acc * 256 + (a.getD (off + j) 0).val) 0)
def wordBytes (w : Word) : Array (Fin 256) :=
  ((List.range 32).map fun j => byteOf (w.val / 256 ^ (31 - j))).toArray
def slice (a : Array (Fin 256)) (off len : Nat) : Array (Fin 256) :=
  ((List.range len).map fun j => a.getD (off + j) 0).toArray

def memLimit : Nat := 2 ^ 20

def expand (m : Array (Fin 256)) (upto : Nat) : Array (Fin 256) :=
  let target := (upto + 31) / 32 * 32
  if m.size ≥ target then m else m ++ Array.replicate (target - m.size) 0

def writeAt (m : Array (Fin 256)) (off : Nat) (bs : Array (Fin 256)) : Array (Fin 256) :=
  let m := expand m (off + bs.size)
  (List.range bs.size).foldl (fun m j => m.set! (off + j) (bs.getD j 0)) m

abbrev MRun (α : Type) := Except (MachineFault St) α

def touch (s : St) (off len : Nat) : MRun St :=
  if len = 0 then .ok s
  else if off + len > memLimit then .error (.halt s (.exceptional "memory bound"))
  else .ok { s with mem := expand s.mem (off + len) }

def sget (s : St) (k : Nat) : Word := ((s.storage.find? (·.1 == k)).map (·.2)).getD 0

def done {r : Nat} (s : St) (v : Word) : MRun (St × (Fin r → Word)) := .ok (s, fun _ => v)
def unit (s : St) : MRun (St × (Fin 0 → Word)) := .ok (s, fun i => i.elim0)

def exec : {a r : Nat} → Solidity.Yul.Builtin a r → (Fin a → Word) → St → MRun (St × (Fin r → Word))
  | _, _, .stop, _, s => .error (.halt { s with output := #[] } .stop)
  | _, _, .invalid, _, s => .error (.halt s .invalid)
  | _, _, .address, _, s => done s s.self
  | _, _, .caller, _, s => done s (W 0xCA11E5)
  | _, _, .callvalue, _, s => done s s.callvalue
  | _, _, .calldatasize, _, s => done s (W s.calldata.size)
  | _, _, .codesize, _, s => done s (W s.code.size)
  | _, _, .returndatasize, _, s => done s 0
  | _, _, .gas, _, s => done s (W 1000000)
  | _, _, .msize, _, s => done s (W s.mem.size)
  | _, _, .calldataload, xs, s => done s (readWord s.calldata (xs 0).val)
  | _, _, .mload, xs, s => do
      let s ← touch s (xs 0).val 32
      done s (readWord s.mem (xs 0).val)
  | _, _, .sload, xs, s => done s (sget s (xs 0).val)
  | _, _, .pop, _, s => unit s
  | _, _, .mstore, xs, s => do
      let s ← touch s (xs 0).val 32
      unit { s with mem := writeAt s.mem (xs 0).val (wordBytes (xs 1)) }
  | _, _, .mstore8, xs, s => do
      let s ← touch s (xs 0).val 1
      unit { s with mem := writeAt s.mem (xs 0).val #[byteOf (xs 1).val] }
  | _, _, .sstore, xs, s =>
      unit { s with storage := ((xs 0).val, xs 1) :: s.storage.filter (·.1 != (xs 0).val) }
  | _, _, .«return», xs, s => do
      let s ← touch s (xs 0).val (xs 1).val
      .error (.halt { s with output := slice s.mem (xs 0).val (xs 1).val } .return)
  | _, _, .revert, xs, s => do
      let s ← touch s (xs 0).val (xs 1).val
      .error (.halt { s with output := slice s.mem (xs 0).val (xs 1).val } .revert)
  | _, _, .calldatacopy, xs, s => do
      let s ← touch s (xs 0).val (xs 2).val
      unit { s with mem := writeAt s.mem (xs 0).val (slice s.calldata (xs 1).val (xs 2).val) }
  | _, _, .codecopy, xs, s => do
      let s ← touch s (xs 0).val (xs 2).val
      unit { s with mem := writeAt s.mem (xs 0).val (slice s.code (xs 1).val (xs 2).val) }
  | _, _, .returndatacopy, xs, s =>
      if (xs 1).val + (xs 2).val = 0 then unit s else .error (.halt s (.exceptional "returndata out of bounds"))
  | _, _, .mcopy, xs, s => do
      let s ← touch s (max (xs 0).val (xs 1).val) (xs 2).val
      unit { s with mem := writeAt s.mem (xs 0).val (slice s.mem (xs 1).val (xs 2).val) }
  | _, _, .keccak256, xs, s => do
      let s ← touch s (xs 0).val (xs 1).val
      let bytes := (slice s.mem (xs 0).val (xs 1).val).toList.map (·.val)
      done s (W (Solidity.Keccak.keccak256Nat bytes))
  | _, _, b, _, _ => .error (.unsupported s!"test machine: unsupported builtin {b.name}")

def machine : Machine St := ⟨exec⟩

/-! Artifact facts. -/

def hexBytes (s : String) : Array (Fin 256) :=
  let cs := s.toList.toArray
  ((List.range (cs.size / 2)).map fun i =>
    byteOf (((hexDigit? cs[2 * i]!).getD 0) * 16 + (hexDigit? cs[2 * i + 1]!).getD 0)).toArray

def place (a : Array (Fin 256)) (positions : List Nat) (bytes : Array (Fin 256)) : Array (Fin 256) :=
  positions.foldl (fun a p => writeAt a p bytes) a

def libAddress : Word := W 0x1111222233334444555566667777888899990000
def addressBytes (w : Word) : Array (Fin 256) := (wordBytes w).extract 12 32

def mkTable (artifact : List DataByte) (rows : List (String × Nat × Nat)) : Except String (DataTable artifact) := do
  let entries ← rows.mapM fun (label, off, size) =>
    if h : off + size ≤ artifact.length ∧ off < 2 ^ 256 ∧ size < 2 ^ 256 then
      .ok (label, (⟨⟨off, h.2.1⟩, ⟨size, h.2.2⟩, h.1⟩ : DataRef artifact))
    else .error s!"label {label} outside the artifact"
  if h : (entries.map Prod.fst).Nodup then .ok ⟨entries, h⟩ else .error "duplicate labels"

structure Facts where
  creation : Array (Fin 256)
  deployed : Array (Fin 256)
  offset : Nat
  creationLinks : List Nat
  deployedLinks : List Nat
  immutablePositions : List Nat

def loadFacts (name : String) : IO Facts := do
  let j ← IO.ofExcept (Json.parse (← IO.FS.readFile "tests/fullscope-20261104/vt1/fixtures/artifacts.json"))
  let rows ← IO.ofExcept j.getArr?
  let some row := rows.toList.find? (fun r => (r.getObjValAs? String "contract").toOption == some name)
    | throw (IO.userError s!"no artifact {name}")
  let get (k : String) : IO (List Nat) := IO.ofExcept (row.getObjValAs? (List Nat) k)
  let creationLinks ← get "creationLinks"
  let deployedLinks ← get "deployedLinks"
  let lib := addressBytes libAddress
  pure { creation := place (hexBytes ((row.getObjValAs? String "creation").toOption.getD "")) creationLinks lib
         deployed := place (hexBytes ((row.getObjValAs? String "deployed").toOption.getD "")) deployedLinks lib
         offset := (row.getObjValAs? Nat "deployedOffset").toOption.getD 0
         creationLinks, deployedLinks
         immutablePositions := ← get "immutablePositions" }

def links (l : String) : Option Word := if l == "Census.sol:LinkedMath" then some libAddress else none

def runtimeCode (p : ObjectParts) : Option Code :=
  p.children.findSome? fun | .object _ code _ => some code | .data _ _ => none

def haltName : HaltKind → String
  | .stop => "stop" | .return => "return" | .revert => "revert" | .invalid => "invalid"
  | .exceptional why => why

def outcome (r : Run St St) : String × List Nat × St :=
  match r with
  | .ok s => ("end", [], s)
  | .error (.halt s why) => (haltName why, s.output.toList.map (·.val), s)
  | .error (.stuck why) => ("stuck: " ++ why, [], {})
  | .error .fuel => ("fuel", [], {})

def wordsOut (ws : List Nat) : List Nat := (ws.map fun w => (wordBytes (W w)).toList.map (·.val)).flatten
def call (sel : Nat) (args : List Nat) : Array (Fin 256) :=
  (((wordBytes (W sel)).extract 28 32).toList ++ (wordsOut args).map byteOf).toArray
def panicData (code : Nat) : List Nat := [0x4e, 0x48, 0x7b, 0x71] ++ wordsOut [code]
def neg (n : Nat) : Nat := 2 ^ 256 - n

def expect (label : String) (got : String × List Nat × St) (why : String) (out : List Nat) : IO Unit := do
  unless got.1 == why && got.2.1 == out do
    throw (IO.userError s!"{label}: got {got.1} {got.2.1.take 40}, expected {why} {out.take 40}")
  IO.println s!"IR_EVAL_PASS {label}: {why} ({out.length} bytes)"

/-! Census: constructor against the saved bytecode, then runtime calls. -/
#eval show IO Unit from do
  let facts ← loadFacts "Census"
  let seed := 5
  let finalRuntime := place facts.deployed facts.immutablePositions (wordBytes (W seed))
  for mode in ["unoptimized", "optimized"] do
    let parsed ← IO.ofExcept (parse (← IO.FS.readFile s!"tests/fullscope-20261104/vt1/fixtures/Census.{mode}.yul"))
    let artifact := facts.creation.toList
    let table ← IO.ofExcept (mkTable artifact
      [("Census_134", 0, artifact.length), ("Census_134_deployed", facts.offset, facts.deployed.size)])
    let ctx : ObjectCtx := ⟨artifact, table, fun l => if l == "16" then facts.immutablePositions else [],
      fun _ => none, links⟩
    let s0 : St := { code := facts.creation ++ (wordBytes (W seed)), self := W 0xC0DE }
    let created := outcome (runCode machine ctx 100000 parsed.parts.code s0)
    expect s!"{mode} constructor returns the saved deployed bytecode with seed" created "return" (finalRuntime.toList.map (·.val))
    let slot0 := (Solidity.Keccak.keccak256Nat (wordsOut [0]))
    unless sget created.2.2 0 == W 1 && sget created.2.2 slot0 == W seed do
      throw (IO.userError "constructor storage: values.push(seed) not observed")
    IO.println s!"IR_EVAL_PASS {mode} constructor storage: values = [{seed}]"
    let some runtime := runtimeCode parsed.parts | throw (IO.userError "no runtime object")
    -- The deployed immutable is read back from the constructor's returned code.
    let returned := (created.2.1.map byteOf).toArray
    let stored := facts.immutablePositions.map fun p => readWord returned p
    let some seedWord := stored.head? | throw (IO.userError "no immutable position")
    unless stored.all (· == seedWord) do throw (IO.userError "immutable copies differ")
    let rctx : ObjectCtx := ⟨[], ⟨[], List.nodup_nil⟩, fun _ => [],
      fun l => if l == "16" then some seedWord else none, links⟩
    let run (cd : Array (Fin 256)) (value : Nat := 0) :=
      outcome (runCode machine rctx 100000 runtime
        { code := returned, calldata := cd, storage := created.2.2.storage, callvalue := W value, self := W 0xC0DE })
    expect s!"{mode} arithmetic(3,4)" (run (call 0x6cbb5ae3 [3, 4])) "return" (wordsOut [7, 81])
    expect s!"{mode} arithmetic overflow" (run (call 0x6cbb5ae3 [2 ^ 255, 2 ^ 255])) "revert" (panicData 0x11)
    expect s!"{mode} exponent overflow" (run (call 0x6cbb5ae3 [2, 256])) "revert" (panicData 0x11)
    expect s!"{mode} signed(-7,2)" (run (call 0x7af91e2e [neg 7, 2])) "return" (wordsOut [neg 3])
    expect s!"{mode} signed by zero" (run (call 0x7af91e2e [5, 0])) "revert" (panicData 0x12)
    expect s!"{mode} signed(min,-1)" (run (call 0x7af91e2e [2 ^ 255, neg 1])) "revert" (panicData 0x11)
    expect s!"{mode} assemblyWord(1)" (run (call 0x75059c59 [1])) "return" (wordsOut [255])
    expect s!"{mode} seed() via loadimmutable" (run (call 0x7d94792a [])) "return" (wordsOut [seed])
    expect s!"{mode} push(9)" (run (call 0x959ac484 [9])) "return" (wordsOut [9])
    expect s!"{mode} echo(0x2a)" (run (call 0x624fbfdc [0x20, 1, 0x2a * 2 ^ 248]))
      "return" (wordsOut [0x20, 1, 0x2a * 2 ^ 248])
    expect s!"{mode} non-payable with value" (run (call 0x6cbb5ae3 [3, 4]) 1) "revert" []
    expect s!"{mode} unknown selector" (run (call 0x12345678 [])) "revert" []
    expect s!"{mode} short calldata" (run (call 0x6cbb5ae3 [3])) "revert" []
    let pushed := run (call 0x959ac484 [9])
    unless sget pushed.2.2 0 == W 2 && sget pushed.2.2 (slot0 + 1) == W 9 do
      throw (IO.userError "push storage not observed")
    IO.println s!"IR_EVAL_PASS {mode} push storage: values = [{seed}, 9]"

/-! LinkedMath: constructor and the library entry point. -/
#eval show IO Unit from do
  let facts ← loadFacts "LinkedMath"
  for mode in ["unoptimized", "optimized"] do
    let parsed ← IO.ofExcept (parse (← IO.FS.readFile s!"tests/fullscope-20261104/vt1/fixtures/LinkedMath.{mode}.yul"))
    let artifact := facts.creation.toList
    let table ← IO.ofExcept (mkTable artifact
      [("LinkedMath_14", 0, artifact.length), ("LinkedMath_14_deployed", facts.offset, facts.deployed.size)])
    let ctx : ObjectCtx := ⟨artifact, table, fun _ => facts.immutablePositions, fun _ => none, links⟩
    let created := outcome (runCode machine ctx 100000 parsed.parts.code
      { code := facts.creation, self := libAddress })
    expect s!"{mode} library constructor returns the saved deployed bytecode" created "return"
      (facts.deployed.toList.map (·.val))
    let some runtime := runtimeCode parsed.parts | throw (IO.userError "no runtime object")
    let rctx : ObjectCtx := ⟨[], ⟨[], List.nodup_nil⟩, fun _ => [],
      fun l => if l == "library_deploy_address" then some libAddress else none, links⟩
    let run (cd : Array (Fin 256)) :=
      outcome (runCode machine rctx 100000 runtime { code := facts.deployed, calldata := cd, self := libAddress })
    expect s!"{mode} twice(21)" (run (call 0x3cf3bbf4 [21])) "return" (wordsOut [42])
    expect s!"{mode} twice overflow" (run (call 0x3cf3bbf4 [2 ^ 255])) "revert" (panicData 0x11)

/-! Missing object facts are static errors, never defaults. -/
#eval show IO Unit from do
  let parsed ← IO.ofExcept (parse "object \"A\" { code { pop(datasize(\"B\")) } }")
  let ctx : ObjectCtx := ⟨[], ⟨[], List.nodup_nil⟩, fun _ => [], fun _ => none, fun _ => none⟩
  match runCode machine ctx 100 parsed.parts.code {} with
  | .error (.stuck why) => IO.println s!"IR_EVAL_PASS missing label is stuck: {why}"
  | _ => throw (IO.userError "missing label not refused")
