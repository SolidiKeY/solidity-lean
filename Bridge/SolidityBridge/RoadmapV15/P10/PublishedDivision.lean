import SolidityBridge.RoadmapV15.P10.SignedDivisionConsumer
import Solidity.Backend.PrimitivePackets.SignedDiv.Origin
import Solidity.Backend.Scalar.SignedDivision

/-! Source-local division to a constructed native SDIV body. Ordinary and both
exceptional branches stay distinct; physical loads and compiler guards remain open. -/
namespace SolidityBridge.RoadmapV15.P10.PublishedDivision
open Solidity Solidity.Backend EvmYul Solidity.Evm.External
open Solidity.Backend.PrimitivePackets.SignedDiv

theorem quotient_scalar (a b : PrimTy.int.Denote) (nonzero : b.val ≠ 0)
    (ordinary : ¬(a.val=-((2^255:Nat):Int) ∧ b.val = -1)) :
    (if Scalar.encodeValue .int b == 0 then (0 : Scalar.Word)
     else BitVec.ofInt 256 ((Scalar.encodeValue .int a).toInt.tdiv (Scalar.encodeValue .int b).toInt)) =
      Scalar.encodeValue .int (quotient a b nonzero ordinary) := by
  have nz : (Scalar.encodeValue .int b == 0)=false := by
    rw [Scalar.int_word_zero]
    exact decide_eq_false nonzero
  rw [nz]
  simp only [Bool.false_eq_true,if_false,Scalar.encode_int_toInt]
  rfl

theorem quotient_word (a b : PrimTy.int.Denote) (nonzero : b.val ≠ 0)
    (ordinary : ¬(a.val=-((2^255:Nat):Int) ∧ b.val = -1)) :
    UInt256.sdiv ⟨(Scalar.encodeValue .int a).toFin⟩ ⟨(Scalar.encodeValue .int b).toFin⟩ =
      ⟨(Scalar.encodeValue .int (quotient a b nonzero ordinary)).toFin⟩ := by
  rw [signed_div_word,quotient_scalar a b nonzero ordinary]

theorem ordinary_fetched {E : Source.Env} {Γ : Source.RCtx}
    (G : Source.Glob E) (F : Source.Fr) (sfuel : Nat) (s : Source.EMState E Γ)
    (left right : Source.Idx Γ (.int T)) (a b : PrimTy.int.Denote)
    (readLeft : s.1.get left=sourceValue a) (readRight : s.1.get right=sourceValue b)
    (nonzero : b.val ≠ 0) (ordinary : ¬(a.val=-((2^255:Nat):Int) ∧ b.val = -1))
    (site : Site .SDIV) (tail : Scalar.Stack) (room : tail.length+2≤1024)
    (gas : 5≤site.seed.gasAvailable.toNat) (nfuel : Nat) :
    let input := (modularSite site (Scalar.encodeValue .int a::Scalar.encodeValue .int b::tail)).state
    let next := (Assembly.chargedPrepare input 5).replaceStackAndIncrPC
      ((Scalar.encodeValue .int (quotient a b nonzero ordinary)::tail).map (fun w => UInt256.mk w.toFin))
    (Source.evalE G F (sfuel+3) (.binary .div (.local left) (.local right))).run s=
      (.ok (.val (sourceValue (quotient a b nonzero ordinary))),s) ∧
    Assembly.driverSteps 1 (nfuel+2) #[] input=.ok next ∧
    EVM.X (nfuel+2) #[] input=EVM.X (nfuel+1) #[] next ∧
    next.toState=input.toState ∧ next.memory=input.memory ∧
    next.returnData=input.returnData ∧ next.H_return=input.H_return := by
  have source := locals_origin G F sfuel s left right a b readLeft readRight
  rw [source_ordinary F.checked a b nonzero ordinary] at source
  have native := sdiv_agreement site (Scalar.encodeValue .int a) (Scalar.encodeValue .int b) tail room gas nfuel
  dsimp only at native
  rw [quotient_scalar a b nonzero ordinary] at native
  exact ⟨source,native.2.1,native.2.2,rfl,rfl,rfl,rfl⟩

theorem zero_boundary {E : Source.Env} {Γ : Source.RCtx}
    (G : Source.Glob E) (F : Source.Fr) (sfuel : Nat) (s : Source.EMState E Γ)
    (left right : Source.Idx Γ (.int T)) (a b : PrimTy.int.Denote)
    (readLeft : s.1.get left=sourceValue a) (readRight : s.1.get right=sourceValue b)
    (zero : b.val=0) (site : Site .SDIV) (tail : Scalar.Stack) (room : tail.length+2≤1024)
    (gas : 5≤site.seed.gasAvailable.toNat) (nfuel : Nat) :
    let input := (modularSite site (Scalar.encodeValue .int a::Scalar.encodeValue .int b::tail)).state
    let next := (Assembly.chargedPrepare input 5).replaceStackAndIncrPC ((0::tail).map (fun (w : Scalar.Word) => UInt256.mk w.toFin))
    (Source.evalE G F (sfuel+3) (.binary .div (.local left) (.local right))).run s=
      (.error (.revert (Source.panicData .divZero)),s) ∧
    Assembly.driverSteps 1 (nfuel+2) #[] input=.ok next ∧
    EVM.X (nfuel+2) #[] input=EVM.X (nfuel+1) #[] next := by
  have source := locals_origin G F sfuel s left right a b readLeft readRight
  rw [source_zero F.checked a b zero] at source
  have native := sdiv_agreement site (Scalar.encodeValue .int a) (Scalar.encodeValue .int b) tail room gas nfuel
  dsimp only at native
  have z : Scalar.encodeValue .int b=0 := by change BitVec.ofInt 256 b.val=0;rw [zero];rfl
  rw [z] at native
  rw [z]
  exact ⟨source,native.2.1,native.2.2⟩

theorem overflow_scalar (a b : PrimTy.int.Denote)
    (minimum : a.val=-((2^255:Nat):Int)) (minusOne : b.val = -1) :
    (if Scalar.encodeValue .int b == 0 then (0 : Scalar.Word)
     else BitVec.ofInt 256 ((Scalar.encodeValue .int a).toInt.tdiv (Scalar.encodeValue .int b).toInt)) =
      Scalar.encodeValue .int Scalar.minimumInt := by
  rw [Scalar.int_word_zero,Scalar.encode_int_toInt,Scalar.encode_int_toInt,minimum,minusOne]
  decide
theorem overflow_boundary {E : Source.Env} {Γ : Source.RCtx}
    (G : Source.Glob E) (F : Source.Fr) (sfuel : Nat) (s : Source.EMState E Γ)
    (left right : Source.Idx Γ (.int T)) (a b : PrimTy.int.Denote)
    (readLeft : s.1.get left=sourceValue a) (readRight : s.1.get right=sourceValue b)
    (minimum : a.val=-((2^255:Nat):Int)) (minusOne : b.val = -1)
    (site : Site .SDIV) (tail : Scalar.Stack) (room : tail.length+2≤1024)
    (gas : 5≤site.seed.gasAvailable.toNat) (nfuel : Nat) :
    let input := (modularSite site (Scalar.encodeValue .int a::Scalar.encodeValue .int b::tail)).state
    let next := (Assembly.chargedPrepare input 5).replaceStackAndIncrPC
      ((Scalar.encodeValue .int Scalar.minimumInt::tail).map (fun w => UInt256.mk w.toFin))
    (Source.evalE G {F with checked:=true} (sfuel+3) (.binary .div (.local left) (.local right))).run s=
      (.error (.revert (Source.panicData .arithmetic)),s) ∧
    (Source.evalE G {F with checked:=false} (sfuel+3) (.binary .div (.local left) (.local right))).run s=
      (.ok (.val (sourceValue Scalar.minimumInt)),s) ∧
    Assembly.driverSteps 1 (nfuel+2) #[] input=.ok next ∧
    EVM.X (nfuel+2) #[] input=EVM.X (nfuel+1) #[] next ∧
    next.toState=input.toState ∧ next.memory=input.memory ∧
    next.returnData=input.returnData ∧ next.H_return=input.H_return := by
  have checked := locals_origin G {F with checked:=true} sfuel s left right a b readLeft readRight
  rw [source_overflow a b minimum minusOne] at checked
  have unchecked := locals_origin G {F with checked:=false} sfuel s left right a b readLeft readRight
  rw [source_unchecked_overflow a b minimum minusOne] at unchecked
  have native := sdiv_agreement site (Scalar.encodeValue .int a) (Scalar.encodeValue .int b) tail room gas nfuel
  dsimp only at native
  rw [overflow_scalar a b minimum minusOne] at native
  exact ⟨checked,unchecked,native.2.1,native.2.2,rfl,rfl,rfl,rfl⟩

#print axioms quotient_scalar
#print axioms quotient_word
#print axioms ordinary_fetched
#print axioms zero_boundary
#print axioms overflow_scalar
#print axioms overflow_boundary
end SolidityBridge.RoadmapV15.P10.PublishedDivision
