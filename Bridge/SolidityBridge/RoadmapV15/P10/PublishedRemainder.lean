import SolidityBridge.RoadmapV15.P10.SignedDivisionConsumer
import Solidity.Backend.PrimitivePackets.SignedMod.Source
import Solidity.Backend.Scalar.SignedDivision
/-! Pure Source-local signed remainder to the actual constructed native SMOD
body. Initial local reads and numeric resources are explicit. Physical operand
loading, selected whole-code origin and checked zero-guard execution stay open. -/
namespace SolidityBridge.RoadmapV15.P10
open Solidity Solidity.Backend EvmYul Solidity.Evm.External
namespace PublishedRemainder
open Solidity.Backend.PrimitivePackets.SignedMod
theorem source_remainder_scalar (x y : Int) (hx : Range x) (hy : Range y) (nonzero : y ≠ 0) :
    (if Scalar.encodeValue .int (lower y hy) == 0 then (0 : Scalar.Word)
     else BitVec.ofInt 256 ((Scalar.encodeValue .int (lower x hx)).toInt.tmod
       (Scalar.encodeValue .int (lower y hy)).toInt)) =
    Scalar.encodeValue .int (lower (x.tmod y) (remainder_range x y hy nonzero)) := by
  have divisor : (Scalar.encodeValue .int (lower y hy) == 0) = false := by
    rw [Scalar.int_word_zero]
    change decide (y=0)=false
    exact decide_eq_false nonzero
  rw [divisor]
  simp only [Bool.false_eq_true,if_false,Scalar.encode_int_toInt]
  rfl
theorem source_remainder_word (x y : Int) (hx : Range x) (hy : Range y) (nonzero : y ≠ 0) :
    UInt256.smod ⟨(Scalar.encodeValue .int (lower x hx)).toFin⟩ ⟨(Scalar.encodeValue .int (lower y hy)).toFin⟩ =
      ⟨(Scalar.encodeValue .int (lower (x.tmod y) (remainder_range x y hy nonzero))).toFin⟩ := by
  rw [signed_mod_word,source_remainder_scalar x y hx hy nonzero]

theorem source_fetched {E : Source.Env} {Γ : Source.RCtx}
    (G : Source.Glob E) (F : Source.Fr) (sfuel : Nat) (s : Source.EMState E Γ)
    (left right : Source.Idx Γ (.int ty)) (x y : Int) (hx : Range x) (hy : Range y)
    (readLeft : s.1.get left = .int x hx) (readRight : s.1.get right = .int y hy)
    (nonzero : y ≠ 0) (site : Site .SMOD) (tail : Scalar.Stack)
    (room : tail.length+2 ≤ 1024) (gas : 5 ≤ site.seed.gasAvailable.toNat) (nfuel : Nat) :
    let input := (modularSite site (Scalar.encodeValue .int (lower x hx)::Scalar.encodeValue .int (lower y hy)::tail)).state
    let next := (Assembly.chargedPrepare input 5).replaceStackAndIncrPC
      ((Scalar.encodeValue .int (lower (x.tmod y) (remainder_range x y hy nonzero))::tail).map (fun w => UInt256.mk w.toFin))
    (Source.evalE G F (sfuel+3) (.binary .mod (.local left) (.local right))).run s =
      (.ok (.val (.int (x.tmod y) (remainder_range x y hy nonzero))),s) ∧
    Assembly.driverSteps 1 (nfuel+2) #[] input = .ok next ∧
    EVM.X (nfuel+2) #[] input = EVM.X (nfuel+1) #[] next ∧
    next.toState = input.toState ∧ next.memory = input.memory ∧
    next.returnData = input.returnData ∧ next.H_return = input.H_return := by
  have native := smod_agreement site (Scalar.encodeValue .int (lower x hx))
    (Scalar.encodeValue .int (lower y hy)) tail room gas nfuel
  dsimp only at native
  rw [source_remainder_scalar x y hx hy nonzero] at native
  exact ⟨source_locals_nonzero G F sfuel s left right x y hx hy readLeft readRight nonzero,
    native.2.1,native.2.2,rfl,rfl,rfl,rfl⟩

theorem zero_boundary {E : Source.Env} {Γ : Source.RCtx}
    (G : Source.Glob E) (F : Source.Fr) (sfuel : Nat) (s : Source.EMState E Γ)
    (left right : Source.Idx Γ (.int ty)) (x : Int) (hx : Range x) (hz : Range 0)
    (readLeft : s.1.get left = .int x hx) (readRight : s.1.get right = .int 0 hz)
    (site : Site .SMOD) (tail : Scalar.Stack) (room : tail.length+2 ≤ 1024)
    (gas : 5 ≤ site.seed.gasAvailable.toNat) (nfuel : Nat) :
    let input := (modularSite site (Scalar.encodeValue .int (lower x hx)::Scalar.encodeValue .int (lower 0 hz)::tail)).state
    let next := (Assembly.chargedPrepare input 5).replaceStackAndIncrPC
      ((0::tail).map (fun (w : Scalar.Word) => UInt256.mk w.toFin))
    (Source.evalE G F (sfuel+3) (.binary .mod (.local left) (.local right))).run s =
      (.error (.revert (Source.panicData .divZero)),s) ∧
    Assembly.driverSteps 1 (nfuel+2) #[] input = .ok next ∧
    EVM.X (nfuel+2) #[] input = EVM.X (nfuel+1) #[] next := by
  have native := smod_agreement site (Scalar.encodeValue .int (lower x hx))
    (Scalar.encodeValue .int (lower 0 hz)) tail room gas nfuel
  exact ⟨source_locals_zero G F sfuel s left right x hx hz readLeft readRight,native.2.1,native.2.2⟩

#print axioms source_remainder_scalar
#print axioms source_remainder_word
#print axioms source_fetched
#print axioms zero_boundary
end PublishedRemainder
end SolidityBridge.RoadmapV15.P10
