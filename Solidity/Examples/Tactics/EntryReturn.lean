import Solidity.Tools.Upstream
import Solidity.Semantics.EntryReturn
import Solidity.Calculus.ReadRealization

/-! Typed quotations from the actual native entry bridge. Runtime compilation
produces intrinsic terms; the following execution certificates are checked by
the kernel. They are independent controls, not edits to original fixtures. -/
namespace Solidity.Examples.Tactics.EntryReturn
open Lean Elab Term Meta Semantics ReadRealization

/-- A small source-shaped self try with a primitive prefix and string result. -/
def Probe : Contract := contract!{
  uint executions;
  function g(bool b) returns (uint a, uint c) { require(b, "no"); return (1, 2); }
  function f(bool b) returns (uint x, uint y, string memory txt) {
    executions++;
    try this.g(b) returns (uint a, uint c) { x = a; y = c; txt = "ok"; }
    catch Error(string memory s) { txt = s; }
  }
}

/-- Quote the native entry's actual intrinsic program, without importing any
reference observation. Both test quotation forms share this generator. -/
def quoteEntry (C : Contract) (c : Lean.Expr) (f : String) (bytes : List Nat) : Except String Lean.Expr := do
  let some d := Semantics.lookupBy f C.funs | throw "missing exact declaration"
  let b ← Tools.Upstream.ABI.program C d f false false bytes
  pure (Prog.quoteShared c b.2).1

syntax "entry_return[" term "," str "," term "]" : term
elab_rules : term
  | `(entry_return[$c, $f, $bytes]) =>
    elabAgainst c fun q => `(quoteEntry $c $q $f $bytes)

/-- Large modifier-frame quotations use the same safe declaration path as
Prog.define: the root constructor exposes its exact type; the kernel checks
all generated syntax and proofs without a recursive elaborator inference pass.
No recursion, proof, fuel or kernel-check budget is changed. -/
syntax "#entry_return " ident " := " term "," str "," term : command
open Lean.Elab.Command in
elab_rules : command
  | `(#entry_return $n:ident := $c, $f:str, $bytes) => do
    let value ← liftTermElabM <| elabAgainst c fun q => `(quoteEntry $c $q $f $bytes)
    let args := value.getAppArgs
    let type ← if value.isAppOfArity ``Prog.cons 6 then
        pure (Prog.quoteType args[0]! args[1]! args[3]!)
      else if value.isAppOfArity ``Prog.nil 2 then
        pure (Prog.quoteType args[0]! args[1]! args[1]!)
      else throwError "entry quotation has no typed program root"
    let fullName := (← getCurrNamespace) ++ n.getId
    liftCoreM <| addDecl <| .defnDecl {
      name := fullName, levelParams := [], type, value,
      hints := .abbrev, safety := .safe }

def yes := entry_return[Probe, "f", (wordBytes 1).map UInt8.toNat]
def no := entry_return[Probe, "f", (wordBytes 0).map UInt8.toNat]
def malformed := entry_return[Probe, "f", (wordBytes 2).map UInt8.toNat]

def start : State Probe [] := { State.init Probe with
  tx := { selfAddress := PrimTy.ofIntD .uint 7 } }

/-- Observe the actual typed output object and a typed storage observation in
one execution, at the unchanged native allowance. -/
def snapshot {C : Contract} {Γ : Ctx} (σ : State C []) (read : Storage C → Int)
    (P : Prog C [] (.mem bytesR :: Γ)) : Option (List Nat × Int) := do
  let o ← (P.runF 1000 σ).toOption
  let bytes ← (Tools.Upstream.ABI.readBytes o.st .here).toOption
  pure (bytes, read o.st.storage)

def counter (storage : Storage Probe) : Int :=
  ((⟨.uint, SRef.ofRoot "executions" rfl, .nil⟩ : Ref Probe).read storage).val

def summary {Γ : Ctx} (P : Prog Probe [] (.mem bytesR :: Γ)) : Option (List Nat × Int) :=
  snapshot start counter P

def observe {Γ : Ctx} (P : Prog Probe [] (.mem bytesR :: Γ)) : Option (List Nat) :=
  (summary P).map Prod.fst

def count {Γ : Ctx} (P : Prog Probe [] (.mem bytesR :: Γ)) : Option Int :=
  (summary P).map Prod.snd

def expected (x y : Nat) (text : List UInt8) : List Nat :=
  (wordBytes x ++ wordBytes y ++ wordBytes 96 ++ wordBytes text.length ++
    pad32 text).map UInt8.toNat

/-- Exact success bytes and once-only source effects, checked together. -/
theorem success_summary : summary yes = some (expected 1 2 [111, 107], 1) := by decide +kernel

/-- Exact actual caught reason and once-only effects, checked together. -/
theorem caught_summary : summary no = some (expected 0 0 [110, 111], 1) := by decide +kernel

/-- Source effects happen once, also when the self-call selects a catch. -/
theorem once_success : count yes = some 1 := by rw [count, success_summary]; rfl
/-- A caught failure does not replay the source entry. -/
theorem once_caught : count no = some 1 := by rw [count, caught_summary]; rfl

/-- Actual success binds both primitives and the actual memory string in order. -/
theorem success_bytes : observe yes = some (expected 1 2 [111, 107]) := by
  rw [observe, success_summary]; rfl

/-- Actual self Error bytes bind the reason, not an oracle or expected byte list. -/
theorem caught_bytes : observe no = some (expected 0 0 [110, 111]) := by
  rw [observe, caught_summary]; rfl

/-- A malformed bool word fails before source execution. -/
theorem malformed_input : (malformed.runF 1000 start).halt? = some .revert := by decide +kernel

/-- The bridge does not turn a zero-address self try into a caught success. -/
theorem zero_self_refused : (yes.runF 1000 (State.init Probe)).halt? = some .revert := by decide +kernel

/-- A successful typed snapshot certifies normal completion, not exhaustion. -/
theorem snapshot_normal {C : Contract} {Γ : Ctx} (σ : State C []) (read : Storage C → Int)
    (P : Prog C [] (.mem bytesR :: Γ)) (v : List Nat × Int)
    (h : snapshot σ read P = some v) : (P.runF 1000 σ).halt? = none := by
  cases hr : P.runF 1000 σ with
  | error e =>
    simp only [snapshot, hr, Except.toOption] at h
    cases h
  | ok o => rfl

theorem summary_normal {Γ : Ctx} (P : Prog Probe [] (.mem bytesR :: Γ))
    (v : List Nat × Int) (h : summary P = some v) : (P.runF 1000 start).halt? = none :=
  snapshot_normal start counter P v h

/-- Normal success is within the unchanged native allowance. -/
theorem success_normal : (yes.runF 1000 start).halt? = none := summary_normal yes _ success_summary
/-- The selected catch/serializer is within the unchanged native allowance. -/
theorem caught_normal : (no.runF 1000 start).halt? = none := summary_normal no _ caught_summary
/-- Bounded success agrees with the unchanged ordinary semantics. -/
theorem success_ordinary : yes.runR start = yes.runF 1000 start :=
  Solidity.EntryReturn.bounded_exact yes start 1000 success_normal
/-- Bounded catch agrees with the unchanged ordinary semantics. -/
theorem caught_ordinary : no.runR start = no.runF 1000 start :=
  Solidity.EntryReturn.bounded_exact no start 1000 caught_normal

/-- Wrong reference shape is not admitted as bytes/string. -/
theorem wrong_reference_refused : Tools.EntryReturn.admitted Probe "f"
    { params := [], body := [], rets := [("x", .prim .uint), ("r", .ref (.array (.prim .int)))],
      retMem := true } = false := by decide +kernel

/-- Two reference results are outside this one-reference bridge. -/
theorem wrong_tuple_refused : Tools.EntryReturn.admitted Probe "f"
    { params := [], body := [], rets := [("x", .ref bytesR), ("r", .ref bytesR)],
      retMem := true } = false := by decide +kernel

/-- Storage aliases never become copied memory results through this bridge. -/
theorem storage_refused : Tools.EntryReturn.admitted Probe "f"
    { params := [], body := [], rets := [("x", .prim .uint), ("r", .ref bytesR)],
      retMem := true, retStorage := true } = false := by decide +kernel

/- Function-marker parsing remains a runtime frontend control; the typed
Boolean refusal implication is Tools.EntryReturn.function_marker_refused. -/
/-- info: false -/
#guard_msgs in #eval Tools.EntryReturn.admitted Probe "f"
    { params := [], body := [], rets := [("x", .prim .uint), ("r", .ref bytesR)],
      retMem := true, widths := [("x#function", 1), ("r[]", 8), ("r[]#bytes", 1)] }

/-- uint[] shares bytesR intrinsically, but lacks the source byte marker. -/
theorem unsigned_array_refused : Tools.EntryReturn.admitted Probe "f"
    { params := [], body := [], rets := [("x", .prim .uint), ("r", .ref bytesR)],
      retMem := true } = false := by decide +kernel

/- Runtime source-marker checks complement the typed admitted_result theorem. -/
/-- info: false -/
#guard_msgs in #eval Tools.EntryReturn.admitted Probe "f"
    { params := [], body := [], rets := [("x", .prim .uint), ("r", .ref bytesR)],
      retMem := true, widths := [("r[]", 8)] }
/-- info: false -/
#guard_msgs in #eval Tools.EntryReturn.admitted Probe "f"
    { params := [], body := [], rets := [("x", .prim .uint), ("r", .ref bytesR)],
      retMem := true, widths := [("r[]", 16), ("r[]#bytes", 1)] }

/-- An unresolved name never supplies an alternative entry declaration. -/
theorem absent_declaration_refused :
    ((Tools.EntryReturn.prepare Probe "absent").runFrom' { funs := Probe.funs } ([], 1)).isOk = false := by
  decide +kernel

end Solidity.Examples.Tactics.EntryReturn
