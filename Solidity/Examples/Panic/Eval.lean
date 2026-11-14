import Solidity.Semantics.Panic.Eval

namespace Solidity.Examples.Panic.Eval
open Solidity.Panic Solidity.Semantics.Panic

/-- Observe the emitted code, without deciding equality of stored proof witnesses. -/
def code? {α : Type} : EvalResult α → Option Nat
  | .error (.intrinsic code _) => some code.code
  | _ => none

def zero : PrimTy.uint.Denote := ⟨0, by decide⟩
def one : PrimTy.uint.Denote := ⟨1, by decide⟩

example : code? (evalProducer (.assertion false)) = some 1 := rfl
example : code? (binary .div rfl one zero) = some 0x12 := by decide
example : code? (binary .mod rfl one zero) = some 0x12 := by decide
example : code? (binary .sub rfl zero one) = some 0x11 := by decide +kernel
example : code? (modular .addmod one one zero) = some 0x12 := by decide
example : code? (evalProducer (.enumConversion 1 one)) = some 0x21 := by decide
example : code? (evalProducer (.storageEncoding one)) = some 0x22 := by decide
example : code? (evalProducer (.internalFunction zero)) = some 0x51 := by decide
example : code? (evalProducer (.allocation ⟨[], 2^64 - 1⟩ 0 1)) = some 0x41 := by decide
example : code? (binary .add rfl zero one) = none := by decide

/-- The false branch skips a division by zero; selecting it retains code 0x12. -/
def choose {C : Contract} {Γ : Ctx} (b : Bool) : Val C Γ .uint :=
  .ternary (.simple (.bool b))
    (.binop .div rfl rfl (.simple (.lit 1 (by decide))) (.simple (.lit 0 (by decide))))
    (.simple (.lit 1 (by decide)))

example {C : Contract} {Γ : Ctx} (σ : State C Γ) : value σ (choose false) = .ok one :=
  value_of_ok σ (choose false) one rfl
example {C : Contract} {Γ : Ctx} (σ : State C Γ) :
    code? (value σ (choose true)) = some 0x12 := rfl
example {C : Contract} {Γ : Ctx} (σ : State C Γ) :
    erase (value σ (choose true)) = .error .revert := by
  rw [value_erase]
  rfl

/-- Signed minimum negation and nonzero division overflow both use 0x11. -/
example : code? (unary (p := .int) .neg rfl (⟨-(2^255), by decide +kernel⟩ : PrimTy.int.Denote)) =
    some 0x11 := by decide +kernel
example : code? (binary (p := .int) .div rfl (⟨-(2^255), by decide +kernel⟩ : PrimTy.int.Denote)
    ⟨-1, by decide⟩) = some 0x11 := by decide +kernel

example {C : Contract} {E : Ty} (st : Storage C) (keep : Bool)
    (ref : SRef C (.ref (.array E))) (v : SVal (.ref (.array E)))
    (found : st.find ref = some v) (empty : v.view.elems.toList.isEmpty = true) :
    code? (evalProducer (.pop st keep ref)) = some 0x31 := by
  rw [evalProducer_origin _ _ (pop_origin st keep ref v found empty)]
  rfl

example {H : HTy} {R : RefTy} {E : Ty} (hp : Heap H) (ref : HRef H R)
    (array : ArrTy R E) (i : PrimTy.uint.Denote) (failed : hp.index ref array i = none) :
    code? (memoryRead hp (.index ref array i)) = some 0x32 := by
  rw [memoryRead, evalProducer_origin _ _ (index_origin hp ref array i failed)]
  rfl

/- Exported contract checks: these names must remain available to the Run and
source-association steps. Kernel boundary controls above test their evaluation. -/
#check siteCode_code
#check evalProducer_origin
#check evalProducer_success
#check evalProducer_unclassified
#check assertion_project
#check Solidity.Semantics.Panic.binary_success
#check source_erase
#check msource_erase
#check pop_erase
#check allocation_project
#check Raised.ofOrigin_site

end Solidity.Examples.Panic.Eval
