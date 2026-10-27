import Solidity.Tools.Upstream

open Solidity Solidity.Frontend Solidity.Tools Solidity.Tools.Upstream Lean
solc_import "NamedErrorControls.legacy.ast.json" hash 0xef45d8a68f518351 as Group10.Legacy.NamedErrorControls testing
solc_import "NamedErrorControls.viaIR.ast.json" hash 0xf1882faf316259ba as Group10.IR.NamedErrorControls testing

solc_import "NamedErrorControls.override.ast.json" hash 0x3d0ede005dca6d0c as Group10.Override.NamedErrorControls testing evalOrder EvalOrder.viaIR
def NamedLegacy : Contract := Group10.Legacy.NamedErrorControls
def NamedIR : Contract := Group10.IR.NamedErrorControls
example : Group10.Legacy.NamedErrorControls.report.all (·.status == .elaborated) = true := by decide +kernel
example : Group10.IR.NamedErrorControls.report.all (·.status == .elaborated) = true := by decide +kernel
namespace FiveControls
/-- Repeated bounded multiplication, the arithmetic carried by the lowering. -/
def steps (M a : Nat) : Nat → Nat → Option Nat
  | 0, r => some r
  | k+1, r => if r*a < M then steps M a k (r*a) else none
/-- Checked multiplication returns exactly the mathematical power when it fits. -/
theorem steps_eq (M a k : Nat) (ha : 1 ≤ a) (r : Nat) (hr : r < M) :
    steps M a k r = if r*a^k < M then some (r*a^k) else none := by
  induction k generalizing r with
  | zero => simp only [steps, Nat.pow_zero, Nat.mul_one, if_pos hr]
  | succ k ih =>
    simp only [steps]
    by_cases h : r*a < M
    · rw [if_pos h, ih (r*a) h]
      simp only [Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm a]
    · rw [if_neg h]
      have hp : 1 ≤ a^k := Nat.one_le_pow k a (by omega)
      have hm : r*a ≤ r*a*a^k := Nat.le_mul_of_pos_right (r*a) (by omega)
      have he : r*a*a^k = r*a^(k+1) := by simp only [Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm a]
      rw [he] at hm
      rw [if_neg (by omega)]
/-- The cutoff cannot reject a representable unsigned power. -/
theorem cutoff (a b : Nat) (ha : 2 ≤ a) (hb : 256 ≤ b) : 2^256 ≤ a^b := by
  exact Nat.le_trans (Nat.pow_le_pow_left ha 256) (Nat.pow_le_pow_right (by omega) hb)
/-- Width masking is in range and involutive at its actual nominal width. -/
theorem complement (M a : Nat) (ha : a < M) :
    M-1-a < M ∧ M-1-(M-1-a) = a := by omega


/-- The nominal complement lowering has the same typed wrapped-word result. -/
theorem complement_word (M a : Nat) (ha : a < M) (hM : M ≤ 2^256) :
    (((M : Int)-1-(a : Int)) % Semantics.uintBound) = ((M-1-a : Nat) : Int) := by
  have heq : (M : Int)-1-(a : Int) = ((M-1-a : Nat) : Int) := by omega
  rw [heq]
  apply Int.emod_eq_of_lt
  · omega
  · unfold Semantics.uintBound
    omega

/-- Existing uint subtraction realizes the compact-byte complement equation. -/
theorem complement_eval (M a : Nat) (ha : a < M) (hM : M ≤ 2^256) :
    BinOp.evalNum .uint rfl ((M : Int)-1) (a : Int) .subW rfl =
      PrimTy.uint.ofInt? ((M-1-a : Nat) : Int) := by
  simp only [BinOp.evalNum, BinOp.arithInt, Option.bind_some]
  rw [complement_word M a ha hM]

/-- The zero/one shortcuts preserve mathematical power, including0**0. -/
theorem power_zero (b : Nat) : 0^b = if b = 0 then 1 else 0 := by
  cases b with
  | zero => simp only [Nat.pow_zero, ite_true]
  | succ b => simp only [Nat.pow_succ, Nat.mul_zero, if_neg (Nat.succ_ne_zero b)]
/-- Any executed lowering loop uses fewer than the original1000 iterations. -/
theorem power_fuel (b : Nat) (h : b < 256) : b < 1000 := by omega

private def words (xs : List Nat) := (xs.flatMap Semantics.wordBytes).map UInt8.toNat
private def selector (s : String) := (Semantics.selectorBytes (Semantics.customSelector s)).map UInt8.toNat
private def failure (sig : String) (args : List String) (bs : List Nat) := Json.mkObj [
  ("signature",toJson sig),("args",toJson args),("failure",toJson true),
  ("expected",toJson ([] : List String)),("revertBytes",toJson bs)]
private def success (sig : String) (args values : List String) := Json.mkObj [
  ("signature",toJson sig),("args",toJson args),("failure",toJson false),("expected",toJson values)]
private def rows : List ImportRow := ["named()","signed()","dynamicData()","compete()",
  "get()","small(uint8,uint8)","uncheckedPower(uint256,uint256)","unsignedNot(uint8)","literal1()","literal16()","literal25()","literal32()","nested()","complement(bytes25)","size()","storageNamed()","storageReverse()","power(uint256,uint256)","powerBase()","powerExponent()","powerCompete()","modular(uint256)"].map fun sig =>
  {name := (sig.splitOn "(").head!,sourceSignature := sig,tag := .diamond,params := [],status := .elaborated,reason := ""}
private def check (C : Contract) (vectors : List Json) (expected : String) : IO Unit := do
  let out := replay C rows (Json.mkObj [("vectors",toJson vectors)])
  unless (out.getObjValAs? String "status").toOption == some expected do
    throw (IO.userError out.pretty)

-- Full signed words and dynamic offsets are expected independently of the
-- lowered capture names. Every failed call is followed by a rollback read.
#eval (do
  for (C,ir) in [(NamedLegacy,false),(NamedIR,true),(Group10.Override.NamedErrorControls,true)] do
    let back := success "get()" [] ["0"]
    let pair := selector "E(uint256,uint256)" ++ words (if ir then [12,1] else [2,21])
    let stored := selector "Stored(bytes,uint256)" ++ words [64,7,0]
    for sig in ["storageNamed()","storageReverse()"] do
      check C [failure sig [] stored,success "size()" [] ["1"],back] "working"
      check C [failure sig [] (selector "Stored(bytes,uint256)" ++ words [64,7,1] ++
        [97] ++ List.replicate 31 0),back] "broken"
    let signed := selector "S(int8,int16)" ++ words [2^256-1,2^256-257]
    let padded (bs : List Nat) := bs ++ List.replicate (32-bs.length) 0
    let dyn := selector "D(string,bytes,uint256)" ++ words [96,160,300,3] ++
      padded [97,98,99] ++ words [4] ++ padded [222,173,190,239]
    for (sig,bytes) in [("named()",pair),("signed()",signed),("dynamicData()",dyn)] do
      check C [failure sig [] bytes,back] "working"
      for wrong in [[],bytes.drop 1,bytes.take (bytes.length-1),bytes++[0],
          [0]++bytes.drop 1] do
        check C [failure sig [] wrong,back] "broken"
    check C [failure "named()" [] (selector "E(uint256,uint256)" ++
      words (if ir then [1,12] else [21,2])),back] "broken"
    check C [failure "signed()" [] (selector "S(int8,int16)" ++ words [255,65279]),back] "broken"
    let panic code := (Semantics.encodePanic code).map UInt8.toNat
    for (sig,args,code) in [("compete()",[],if ir then 1 else 18),
        ("powerBase()",[],1),("powerExponent()",[],18),
        ("powerCompete()",[],if ir then 1 else 18),
        ("modular(uint256)",["0"],if ir then 1 else 18)] do
      check C [failure sig args (panic code),back] "working"
      check C [failure sig args (panic 17),back] "broken"
      check C [failure sig args [],back] "broken"
    for (a,b,v) in [("0","0","1"),("0","10000","0"),("1","10000","1"),
        ("2","255",toString (2^255 : Nat))] do
      check C [success "power(uint256,uint256)" [a,b] [v]] "working"
    check C [success "small(uint8,uint8)" ["2","7"] ["128"]] "working"
    check C [failure "small(uint8,uint8)" ["2","8"] (panic 17),back] "working"
    check C [success "unsignedNot(uint8)" ["0"] ["255"],
      success "unsignedNot(uint8)" ["255"] ["0"]] "working"
    check C [success "uncheckedPower(uint256,uint256)" ["255","131"]
      [toString ((255^131 : Nat) % 2^256)]] "working"
    for args in [["2","256"],["255","131"],["258","131"]] do
      check C [failure "power(uint256,uint256)" args (panic 17),back] "working"
      check C [failure "power(uint256,uint256)" args [],back] "broken"
    -- Nominal byte widths, literal padding, variable operands and nested casts.
    let raw sig inputs outputs data expected := Json.mkObj [
      ("signature",toJson sig),("inputTypes",toJson (inputs : List String)),
      ("outputTypes",toJson (outputs : List String)),("calldata",toJson (data : List Nat)),
      ("failure",toJson false),("expectedBytes",toJson (expected : List Nat))]
    let fixed (sig : String) (n : Nat) (expected : List Nat) :=
      raw sig [] [s!"bytes{n}"] [] (expected ++ List.replicate (32-n) 0)
    for v in [fixed "literal1()" 1 [0], fixed "literal16()" 16 (List.replicate 16 255),
        fixed "literal25()" 25 (((List.replicate 12 [0,255]).flatten)++[0]),
        fixed "literal32()" 32 (0::List.replicate 31 255),
        fixed "nested()" 32 ([237,203]++List.replicate 14 255++List.replicate 16 0)] do
      check C [v] "working"
    for input in [List.replicate 25 0,List.replicate 25 255] do
      let expected := input.map (255-·) ++ List.replicate 7 0
      check C [raw "complement(bytes25)" ["bytes25"] ["bytes25"]
        (input ++ List.replicate 7 0) expected] "working"
  : IO Unit)

-- Original sender/value and failed-call storage survive source capture lowering.
#eval (do
  for C in [NamedLegacy,NamedIR] do
    let tx : TTx := {msgSender := ⟨37,rfl⟩,msgValue := ⟨5,rfl⟩}
    let ss := [← IO.ofExcept (runStmt C "context" [])]
    let ⟨_,Q⟩ ← IO.ofExcept (entryProg C ss)
    let .ok out := Q.runF 1000 (State.deploy C tx) | throw (IO.userError "context failed")
    let ordinary ← IO.ofExcept (elabProgS C [← IO.ofExcept (runStmt C "power" [.num 255,.num 131])])
    unless (match ordinary.2.runF 1000 (State.deploy C tx) with | .error .revert => true | _ => false) do
      throw (IO.userError "ordinary power reading changed")
    let values := localVals (Q.outNames []) out.st.env
    unless Semantics.lookupBy (Var.ofName retLocal) values == some (.uint (PrimTy.ofIntD .uint 42)) do
      throw (IO.userError "named capture changed caller/value")
  : IO Unit)

-- The previous primitive failure is real overflow, and complement masking is
-- ordinary wrapped subtraction at the original nominal width.
example : BinOp.evalNum .uint rfl 255 131 .pow rfl = none := by decide +kernel
example : BinOp.evalNum .uint rfl 2 8 .pow rfl =
    some (PrimTy.ofIntD .uint 256) := by decide +kernel
#print axioms steps_eq
#print axioms cutoff
#print axioms complement
#print axioms complement_eval
#print axioms power_zero
-- Malformed metadata is a reader rejection, never a successful source vector.
#eval (do
  let cases ← IO.ofExcept (Json.parse (← IO.FS.readFile "tests/upstream/NamedErrorControls.negative.json"))
  let cases ← IO.ofExcept cases.getArr?
  for c in cases do
    let ast ← IO.ofExcept (c.getObjVal? "ast")
    let C ← IO.ofExcept ((Frontend.readContract ast "NamedErrorControls" [] true).mapError toString)
    let some f := C.funs.find? (·.name == "named") | throw (IO.userError "missing boundary control")
    let .error _ := f.body | throw (IO.userError "malformed error identity/names admitted")
  : IO Unit)
end FiveControls
