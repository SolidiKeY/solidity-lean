import SolidityBridge.RoadmapV15.P10.UnsignedDivisionConsumer
import Solidity.Yul.Compilation.PureExpressions
import Solidity.Backend.Scalar.Heights
/-! Compiler-origin local DIV/MOD sites with the real charged P10 producers.
This module handles the arithmetic site. ChargedQuotientPrefix composes the
actual charged read prefix; final source/G24 adequacy remains OPEN.
No gas/PC/source observation or admission decision is added. -/
namespace SolidityBridge.Yul.ChargedQuotients
open Solidity Solidity.Yul Solidity.Yul.Closed Solidity.Yul.Compilation
open Backend Scalar Solidity.Evm.External EvmYul
open SolidityBridge.RoadmapV15

def divExpr : Expr [] [] 2 1 :=
  .builtin (.pure .div) (Fin.cases (.local 0) (fun _ => .local 1))
def modExpr : Expr [] [] 2 1 :=
  .builtin (.pure .mod) (Fin.cases (.local 0) (fun _ => .local 1))
def divCompiled := (PureExpressions.compile 2 divExpr).get (by rfl)
def modCompiled := (PureExpressions.compile 2 modExpr).get (by rfl)
def reads : Backend.Program := [.op (.DUP 1),.op (.DUP 1)]
def divProgram : Backend.Program := reads ++ [.op .DIV]
def modProgram : Backend.Program := reads ++ [.op .MOD]

def divSite (seed : EVM.State) : P10.Site .DIV where
  seed := seed
  before := reads
  after := []
  pcFits := by decide +kernel

def modSite (seed : EVM.State) : P10.Site .MOD where
  seed := seed
  before := reads
  after := []
  pcFits := by decide +kernel

def packet (a b : Scalar.Word) (caller : Scalar.Stack) : Scalar.Stack := a::b::a::b::caller
def divInput (seed : EVM.State) (a b : Scalar.Word) (caller : Scalar.Stack) : P10.Site .DIV :=
  P10.modularSite (divSite seed) (packet a b caller)
def modInput (seed : EVM.State) (a b : Scalar.Word) (caller : Scalar.Stack) : P10.Site .MOD :=
  P10.modularSite (modSite seed) (packet a b caller)

/-- Concrete P10 body, not an unproved interface. Its real pre-arithmetic
capacity/gas/horizon premises remain visible in the generated signature. -/
abbrev divAgreement (seed : EVM.State) (a b : Scalar.Word) (caller : Scalar.Stack)
    (room : (a::b::caller).length+2 ≤ 1024) (gas : 5 ≤ seed.gasAvailable.toNat) (fuel : Nat) :=
  P10.div_agreement (divSite seed) a b (a::b::caller) room gas fuel
abbrev modAgreement (seed : EVM.State) (a b : Scalar.Word) (caller : Scalar.Stack)
    (room : (a::b::caller).length+2 ≤ 1024) (gas : 5 ≤ seed.gasAvailable.toNat) (fuel : Nat) :=
  P10.mod_agreement (modSite seed) a b (a::b::caller) room gas fuel

/-- Exact gate including exceptional halting, for the live four-word operand
packet. Initial capacity (callerLength≤1020) is stricter than this opcode's
output capacity (callerLength≤1021); no initial validity follows from a pass. -/
theorem gate (input : EVM.State) (op : Operation .EVM)
    (allowed : op = .DIV ∨ op = .MOD) (callerLength : Nat)
    (arity : input.stack.length = callerLength+4) (valid : Array UInt256) :
    Assembly.driverGate valid input op =
      if input.gasAvailable.toNat < 5 then .error .OutOfGass
      else if callerLength ≤ 1021 then .ok (input,5) else .error .StackOverflow := by
  have expansion : EVM.memoryExpansionCost input op = 0 := by
    rcases allowed with rfl|rfl <;>
      simp only [EVM.memoryExpansionCost,EVM.memoryExpansionCost.μᵢ',Nat.sub_self]
  have cost : EVM.C' input op = 5 := by rcases allowed with rfl|rfl <;> rfl
  have delta : EVM.δ op = some 2 := by rcases allowed with rfl|rfl <;> rfl
  have alpha : EVM.α op = some 1 := by rcases allowed with rfl|rfl <;> rfl
  have charge : input.gasAvailable-UInt256.ofNat 0 = input.gasAvailable := by
    change UInt256.mk (input.gasAvailable.val-0) = input.gasAvailable
    rw [sub_zero]
  have enough : ¬ input.stack.length < 2 := by omega
  simp only [Assembly.driverGate]
  rw [expansion,charge]
  simp only [cost,delta,alpha,Option.getD_some,if_neg (Nat.not_lt_zero _)]
  by_cases low : input.gasAvailable.toNat < 5
  · simp only [if_pos low]
    rfl
  · rw [if_neg low]
    by_cases room : callerLength ≤ 1021
    · have capacity : ¬ input.stack.length-2+1 > 1024 := by omega
      simp only [if_neg low,if_pos room,if_neg enough,if_neg capacity]
      rcases allowed with rfl|rfl <;> cases input.executionEnv.perm <;> rfl
    · have capacity : input.stack.length-2+1 > 1024 := by omega
      simp only [if_neg low,if_neg room,if_neg enough,if_pos capacity]
      rcases allowed with rfl|rfl <;> rfl

#print axioms gate
#print axioms divAgreement
#print axioms modAgreement
end SolidityBridge.Yul.ChargedQuotients
