import Solidity.Source.WellFormed
import Solidity.Semantics.ContractWorld

/-!
# Callable payment metadata and actual typed frame guards

Read the published declaration flags, including receiveOK's refusal, and attach
only the payment flag to a supplied typed entry. This does not resolve entries,
certify visibility/placement/body selection or admit a source program. In
particular readsValue for an internal/private function is NOT payability.
Ordinary-entry payment guards do not reject an internal call's ambient msg.value;
visibility, readonly effects and body selection still require their owners.
-/
namespace Solidity.Lowering.V08.PayableMetadata
open Solidity
open ContractWorld

/-- Payment metadata only; unsupported declarations and malformed receives do
not manufacture an entry. Other Source.WellFormed clauses stay prerequisites. -/
def payableOf? (declaration : Source.Decl) : Option Bool :=
  if declaration.receiveOK then
    match declaration.kind, declaration.top, declaration.node with
    | .function, _, .function _ _ _ mutability _ _ _ _ _ => some (mutability == some .payable)
    | .fallback, _, .fallback _ _ mutability _ _ _ _ => some (mutability == some .payable)
    | .receive, _, .receive _ _ _ _ _ _ => some true
    | _, _, _ => none
  else none

/-- Retain the actual supplied body, typed locals and decoder, changing only
the source payment flag; source exposure/body linkage remains separate. -/
def attach? {C : Contract} {α : Type} (declaration : Source.Decl) (entry : Entry C α) :
    Option (Entry C α) :=
  (payableOf? declaration).map fun payable => { entry with payable }

/-- Accepted source metadata determines the actual target flag. -/
theorem attach_of_flag {C : Contract} {α : Type} (declaration : Source.Decl)
    (entry : Entry C α) (payable : Bool) (flag : payableOf? declaration = some payable) :
    attach? declaration entry = some { entry with payable } := by
  simp only [attach?, flag, Option.map_some]

/-- A refused metadata lookup never supplies a target callable. -/
theorem attach_none {C : Contract} {α : Type} (declaration : Source.Decl)
    (entry : Entry C α) (refused : payableOf? declaration = none) :
    attach? declaration entry = none := by
  simp only [attach?, refused, Option.map_none]

/-- The existing nonpayable frame guard rejects every nonzero payment,
regardless of whether an earlier funding guard also rejects it. -/
theorem nonpayable_enter {K : Type} {contracts : K → Contract}
    (world : World contracts) {k : K} (self : Address) (context : Context)
    (storage : Storage (contracts k)) (nonzero : context.value.1 ≠ 0) :
    world.enter self context storage false = .error .revert := by
  unfold World.enter
  split
  · rfl
  · have guard : ((!false || context.isStatic) && (context.value.1 != 0)) = true := by
      simp only [Bool.not_false, Bool.true_or, Bool.true_and, bne_iff_ne]
      exact nonzero
    rw [guard]
    rfl

/-- Payable entry succeeds under the actual funded, ordinary and bounded
receiver-sum checks. These numeric premises are not an execution equation. -/
theorem payable_enter_success {K : Type} {contracts : K → Contract}
    (world : World contracts) {k : K} (self : Address) (context : Context)
    (storage : Storage (contracts k))
    (funded : context.value.1 ≤ (world.funds context.sender).1)
    (ordinary : context.isStatic = false)
    (receiverBound : (world.funds self).1 + (if context.sender = self then 0 else context.value.1) <
      ((2 ^ 256 : Nat) : Int)) :
    (world.enter self context storage true).isOk = true := by
  have receiverNonnegative := (world.funds self).2
  have paymentNonnegative := context.value.2
  simp only [PrimTy.inRange, decide_eq_true_eq] at receiverNonnegative paymentNonnegative
  have totalNonnegative : 0 ≤ (world.funds self).1 +
      (if context.sender = self then 0 else context.value.1) := by split <;> omega
  have valid : PrimTy.uint.inRange ((world.funds self).1 +
      (if context.sender = self then 0 else context.value.1)) = true := by
    simp only [PrimTy.inRange, decide_eq_true_eq]
    exact ⟨totalNonnegative, receiverBound⟩
  have notOver : ¬ context.value.1 > (world.funds context.sender).1 := by omega
  simp only [World.enter, notOver, if_false, Bool.not_true, ordinary, Bool.false_or,
    Bool.false_and, Bool.false_eq_true, PrimTy.ofInt?, valid, dif_pos, TRes.ofOpt,
    bind, Except.bind, Except.isOk]
  rfl

/-- A source nonpayable flag transports its exact rejection through attach?. -/
theorem source_nonpayable_rejected {K : Type} {contracts : K → Contract} {α : Type}
    (world : World contracts) {k : K} (self : Address) (context : Context)
    (storage : Storage (contracts k)) (declaration : Source.Decl) (entry : Entry (contracts k) α)
    (flag : payableOf? declaration = some false) (nonzero : context.value.1 ≠ 0) :
    (attach? declaration entry).map (fun attached => world.enter self context storage attached.payable) =
      some (.error .revert) := by
  rw [attach_of_flag declaration entry false flag]
  exact congrArg some (nonpayable_enter world self context storage nonzero)

/-- A source payable flag transports success of the actual numeric frame guards. -/
theorem source_payable_entered {K : Type} {contracts : K → Contract} {α : Type}
    (world : World contracts) {k : K} (self : Address) (context : Context)
    (storage : Storage (contracts k)) (declaration : Source.Decl) (entry : Entry (contracts k) α)
    (flag : payableOf? declaration = some true)
    (funded : context.value.1 ≤ (world.funds context.sender).1) (ordinary : context.isStatic = false)
    (receiverBound : (world.funds self).1 + (if context.sender = self then 0 else context.value.1) <
      ((2 ^ 256 : Nat) : Int)) :
    (attach? declaration entry).map (fun attached => (world.enter self context storage attached.payable).isOk) =
      some true := by
  rw [attach_of_flag declaration entry true flag]
  exact congrArg some (payable_enter_success world self context storage funded ordinary receiverBound)

#print axioms attach_of_flag
#print axioms attach_none
#print axioms nonpayable_enter
#print axioms payable_enter_success
#print axioms source_nonpayable_rejected
#print axioms source_payable_entered
end Solidity.Lowering.V08.PayableMetadata
