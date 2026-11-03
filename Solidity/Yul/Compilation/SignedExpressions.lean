import Solidity.Yul.Compilation.BitExpressions
/-! Actual original-AST signed-operation compilation. Two's-complement
conversion, zero divisors and MIN divided by minus one wrapping use the existing source/target
word definitions; no signed source semantics, AST or state is duplicated. -/
namespace Solidity.Yul.Compilation.SignedExpressions
open Backend Scalar
open Solidity.Yul.Closed ProducerExpressions WordExpressions BitExpressions

private theorem cast_power : ((2^256 : Nat) : Int) = 2^256 := Int.natCast_pow 2 256

theorem signed_word (a : Scalar.Word) : Solidity.Yul.signed a.toFin = a.toInt := by
  change (if a.toNat < 2^255 then (a.toNat : Int) else (a.toNat : Int)-2^256) = a.toInt
  rw [BitVec.toInt_eq_toNat_cond]
  have power : 2^256 = 2*2^255 := (Nat.pow_succ 2 255).trans (Nat.mul_comm _ _)
  have threshold : a.toNat < 2^255 ↔ 2*a.toNat < 2^256 := by rw [power]; omega
  by_cases small : a.toNat < 2^255
  · rw [if_pos small,if_pos (threshold.mp small)]
  · rw [if_neg small,if_neg (fun h => small (threshold.mpr h))]
    rw [cast_power]

theorem int_word (value : Int) : (BitVec.ofInt 256 value).toFin = iword value := by
  apply Fin.ext
  have bound := (BitVec.ofInt 256 value).isLt
  rw [BitVec.toNat_ofInt,cast_power] at bound
  change (BitVec.ofInt 256 value).toNat = ((value % (2^256)).toNat) % 2^256
  rw [BitVec.toNat_ofInt,cast_power,Nat.mod_eq_of_lt bound]

def selectSdiv : BinarySelection := ⟨.SDIV,(Scalar.binary .SDIV).getD (fun _ _ => 0),fun _ _ _ => rfl⟩
def selectSmod : BinarySelection := ⟨.SMOD,(Scalar.binary .SMOD).getD (fun _ _ => 0),fun _ _ _ => rfl⟩
def selectSlt : BinarySelection := ⟨.SLT,(Scalar.binary .SLT).getD (fun _ _ => 0),fun _ _ _ => rfl⟩
def selectSgt : BinarySelection := ⟨.SGT,(Scalar.binary .SGT).getD (fun _ _ => 0),fun _ _ _ => rfl⟩
def selectSar : BinarySelection := ⟨.SAR,(Scalar.binary .SAR).getD (fun _ _ => 0),fun _ _ _ => rfl⟩

def sdivBridge : BinaryBridge .sdiv := ⟨selectSdiv,by
  intro a b
  change (if b == 0 then (0 : Scalar.Word) else BitVec.ofInt 256 (a.toInt.tdiv b.toInt)).toFin =
    (if b.toNat = 0 then word 0 else iword ((Solidity.Yul.signed a.toFin).tdiv (Solidity.Yul.signed b.toFin)))
  by_cases zero : b = 0
  · subst b
    rfl
  · have nonzero : b.toNat ≠ 0 := fun h => zero (BitVec.eq_of_toNat_eq h)
    rw [beq_eq_false_iff_ne.mpr zero,if_neg nonzero,signed_word,signed_word]
    exact int_word _⟩

def smodBridge : BinaryBridge .smod := ⟨selectSmod,by
  intro a b
  change (if b == 0 then (0 : Scalar.Word) else BitVec.ofInt 256 (a.toInt.tmod b.toInt)).toFin =
    (if b.toNat = 0 then word 0 else iword ((Solidity.Yul.signed a.toFin).tmod (Solidity.Yul.signed b.toFin)))
  by_cases zero : b = 0
  · subst b
    rfl
  · have nonzero : b.toNat ≠ 0 := fun h => zero (BitVec.eq_of_toNat_eq h)
    rw [beq_eq_false_iff_ne.mpr zero,if_neg nonzero,signed_word,signed_word]
    exact int_word _⟩

def sltBridge : BinaryBridge .slt := ⟨selectSlt,by
  intro a b
  change (flag (a.toInt < b.toInt)).toFin = truth (Solidity.Yul.signed a.toFin < Solidity.Yul.signed b.toFin)
  rw [signed_word,signed_word]
  cases decide (a.toInt < b.toInt) <;> rfl⟩
def sgtBridge : BinaryBridge .sgt := ⟨selectSgt,by
  intro a b
  change (flag (b.toInt < a.toInt)).toFin = truth (Solidity.Yul.signed b.toFin < Solidity.Yul.signed a.toFin)
  rw [signed_word,signed_word]
  cases decide (b.toInt < a.toInt) <;> rfl⟩

def sarBridge : BinaryBridge .sar := ⟨selectSar,by
  intro a b
  change (if a.toNat < 256 then BitVec.ofInt 256 (b.toInt / (2^a.toNat : Int))
    else if b.toInt < 0 then BitVec.ofInt 256 (-1) else (0 : Scalar.Word)).toFin =
    (if a.toNat ≥ 256 then (if Solidity.Yul.signed b.toFin < 0 then word (2^256-1) else word 0)
    else iword (Solidity.Yul.signed b.toFin >>> a.toNat))
  rw [signed_word]
  by_cases small : a.toNat < 256
  · rw [if_pos small,if_neg (by omega),Int.shiftRight_eq_div_pow,Int.natCast_pow]
    exact int_word _
  · have large : a.toNat ≥ 256 := by omega
    rw [if_neg small,if_pos large]
    by_cases negative : b.toInt < 0
    · rw [if_pos negative,if_pos negative]
      decide +kernel
    · rw [if_neg negative,if_neg negative]
      rfl⟩

/-- Actual recursive compiler certificates at the SAME source horizon. -/
def compile {n r : Nat} (fuel : Nat) (expr : Expr [] [] n r) : Option (Compiled fuel expr) :=
  match fuel with
  | 0 => none
  | fuel+1 => by
      apply Expr.casesOn (motive := fun r expr => Option (Compiled (fuel+1) expr)) expr
      case literal => intro w; exact some (literal fuel w)
      case «local» => intro i; exact some (localExpr fuel i)
      case external => intro ref; cases ref.index
      case call => intro sig f args; cases f
      case builtin =>
        intro a r builtin args
        cases builtin with
        | pure op =>
            cases op with
            | add => exact do
                let left ← compile fuel (args 0)
                let right ← compile fuel (args 1)
                pure (ProducerExpressions.binary addBridge left right)
            | sub => exact do
                let left ← compile fuel (args 0)
                let right ← compile fuel (args 1)
                pure (ProducerExpressions.binary subBridge left right)
            | mul => exact do
                let left ← compile fuel (args 0)
                let right ← compile fuel (args 1)
                pure (ProducerExpressions.binary mulBridge left right)
            | «div» => exact do
                let left ← compile fuel (args 0)
                let right ← compile fuel (args 1)
                pure (ProducerExpressions.binary QuotientExpressions.divBridge left right)
            | «mod» => exact do
                let left ← compile fuel (args 0)
                let right ← compile fuel (args 1)
                pure (ProducerExpressions.binary QuotientExpressions.modBridge left right)
            | lt => exact do
                let left ← compile fuel (args 0)
                let right ← compile fuel (args 1)
                pure (ProducerExpressions.binary ltBridge left right)
            | gt => exact do
                let left ← compile fuel (args 0)
                let right ← compile fuel (args 1)
                pure (ProducerExpressions.binary gtBridge left right)
            | eq => exact do
                let left ← compile fuel (args 0)
                let right ← compile fuel (args 1)
                pure (ProducerExpressions.binary eqBridge left right)
            | iszero => exact do
                let arg ← compile fuel (args 0)
                pure (WordExpressions.unary iszeroBridge arg)
            | «not» => exact do
                let arg ← compile fuel (args 0)
                pure (WordExpressions.unary notBridge arg)
            | «and» => exact do
                let left ← compile fuel (args 0)
                let right ← compile fuel (args 1)
                pure (ProducerExpressions.binary andBridge left right)
            | «or» => exact do
                let left ← compile fuel (args 0)
                let right ← compile fuel (args 1)
                pure (ProducerExpressions.binary orBridge left right)
            | «xor» => exact do
                let left ← compile fuel (args 0)
                let right ← compile fuel (args 1)
                pure (ProducerExpressions.binary xorBridge left right)
            | «shl» => exact do
                let left ← compile fuel (args 0)
                let right ← compile fuel (args 1)
                pure (ProducerExpressions.binary shlBridge left right)
            | «shr» => exact do
                let left ← compile fuel (args 0)
                let right ← compile fuel (args 1)
                pure (ProducerExpressions.binary shrBridge left right)
            | sdiv => exact do
                let left ← compile fuel (args 0)
                let right ← compile fuel (args 1)
                pure (ProducerExpressions.binary sdivBridge left right)
            | smod => exact do
                let left ← compile fuel (args 0)
                let right ← compile fuel (args 1)
                pure (ProducerExpressions.binary smodBridge left right)
            | slt => exact do
                let left ← compile fuel (args 0)
                let right ← compile fuel (args 1)
                pure (ProducerExpressions.binary sltBridge left right)
            | sgt => exact do
                let left ← compile fuel (args 0)
                let right ← compile fuel (args 1)
                pure (ProducerExpressions.binary sgtBridge left right)
            | sar => exact do
                let left ← compile fuel (args 0)
                let right ← compile fuel (args 1)
                pure (ProducerExpressions.binary sarBridge left right)
            | _ => exact none
        | _ => exact none
termination_by structural fuel

/-- Single-target assignment uses the existing real statement certificate. -/
def assignment {fuel n : Nat} {c : Control} (targets : Fin 1 → Target [] n) (expr : Expr [] [] n 1) :
    Option (ProducerStatements.Compiled (fuel+1) (Stmt.assign (c := c) targets expr)) :=
  (compile fuel expr).map (ProducerStatements.assignTargets targets)

#print axioms signed_word
#print axioms int_word
#print axioms sdivBridge
#print axioms smodBridge
#print axioms sltBridge
#print axioms sgtBridge
#print axioms sarBridge
#print axioms compile
end Solidity.Yul.Compilation.SignedExpressions
