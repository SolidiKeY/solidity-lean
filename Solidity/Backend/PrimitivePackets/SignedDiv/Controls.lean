import Solidity.Backend.PrimitivePackets.SignedDiv.Contract
import Solidity.Evm.MemoryCompileExamples
import Solidity.Source.SemanticsExamples

namespace Solidity.Backend.PrimitivePackets.SignedDiv.Controls
open Evm Evm.Memory
open Source.SemanticsExamples
abbrev P := Evm.Memory.CompileExamples.C
abbrev Γ : Ctx := .val .int :: .val .int :: Evm.Memory.CompileExamples.Γ
def F : Frag Γ := ((Frag.init Evm.Memory.CompileExamples.Γ).push (.val .int) .ok).push (.val .int) .ok

def target (a b : PrimTy.int.Denote) : State P Γ :=
 ((Evm.Memory.CompileExamples.σ).push (t:=.val .int) b).push (t:=.val .int) a
def machine (a b : PrimTy.int.Denote) :=
 writeMachine (writeMachine Evm.Memory.CompileExamples.machine 4 (.val (sword b.val))) 5 (.val (sword a.val))
def source (a b : PrimTy.int.Denote) : Source.EMState E0 [.int T,.int T] :=
 (.cons (sourceValue a) (.cons (sourceValue b) .nil),s0)

theorem word_repr (v : PrimTy.int.Denote) : ReprV .int v (.val (sword v.val)) := by
 first | (solve | rfl) | (solve | decide) | (solve | omega) | skip
 have h := Backend.Scalar.int_range v
 refine ⟨sword v.val,rfl,?_⟩
 rw [sword_val (by change -((2^256:Nat):Int)≤v.val;omega) (by change v.val<((2^256:Nat):Int);omega)]
 exact (sgn_toWord h.1 h.2).symm

theorem word_unique (v : PrimTy.int.Denote) (w : Word) (rep : ReprV .int v w) :
 w=.val (sword v.val) := by
 first | (solve | rfl) | (solve | decide) | (solve | omega) | skip
 obtain ⟨a,rfl,same⟩ := rep
 apply congrArg Word.val
 apply Fin.ext
 rw [sword_val (by have h:=Backend.Scalar.int_range v;change -((2^256:Nat):Int)≤v.val;omega)
  (by have h:=Backend.Scalar.int_range v;change v.val<((2^256:Nat):Int);omega),same,toWord_sgn a.isLt]

theorem initial (a b : PrimTy.int.Denote) :
 StateRepr 1 0 6 F (target a b) Evm.Memory.CompileExamples.base (machine a b) :=
 (Evm.Memory.CompileExamples.fixture_six_cells.consVal b _ (word_repr b) (by decide)).consVal a _ (word_repr a) (by decide)

def n (x : Int) (h : PrimTy.int.inRange x=true) : PrimTy.int.Denote := ⟨x,h⟩
def negSeven := n (-7) (by decide)
def two := n 2 (by decide)
def zero := n 0 (by decide)
def minus := n (-1) (by decide)

theorem zero_both (p : Roadmap.Pipeline) (checked : Bool) (fuel : Nat) (tail : List Word) :
 (Source.evalE (G0 p) {F0 with checked:=checked} (fuel+3)
  (.binary .div (.local .here) (.local (.there .here)))).run (source negSeven zero)=
 (.error (.revert (Source.panicData .divZero)),source negSeven zero) ∧
 run (selected (C:=P) 0 F checked (.here : Idx Γ (.val .int)) (.there .here)).code
  {machine negSeven zero with stack:=tail}=.revert :=
 zero_execution (G0 p) {F0 with checked:=checked} fuel (source negSeven zero) (target negSeven zero)
 .here (.there .here) .here (.there .here) negSeven zero rfl rfl rfl rfl rfl (initial _ _) tail

theorem overflow_both (p : Roadmap.Pipeline) (fuel : Nat) (tail : List Word) :
 (Source.evalE (G0 p) {F0 with checked:=true} (fuel+3)
  (.binary .div (.local .here) (.local (.there .here)))).run (source Backend.Scalar.minimumInt minus)=
 (.error (.revert (Source.panicData .arithmetic)),source Backend.Scalar.minimumInt minus) ∧
 run (selected (C:=P) 0 F true (.here : Idx Γ (.val .int)) (.there .here)).code
  {machine Backend.Scalar.minimumInt minus with stack:=tail}=.revert ∧
 (Source.evalE (G0 p) {F0 with checked:=false} (fuel+3)
  (.binary .div (.local .here) (.local (.there .here)))).run (source Backend.Scalar.minimumInt minus)=
 (.ok (.val (sourceValue Backend.Scalar.minimumInt)),source Backend.Scalar.minimumInt minus) ∧
 run (selected (C:=P) 0 F false (.here : Idx Γ (.val .int)) (.there .here)).code
  {machine Backend.Scalar.minimumInt minus with stack:=tail}=
 .ok ({machine Backend.Scalar.minimumInt minus with stack:=tail}.push (.val (sword Backend.Scalar.minimumInt.val))) 0 := by
 obtain ⟨src,failed,wrap,w,rep,run⟩ := overflow_execution (G0 p) F0 fuel
  (source Backend.Scalar.minimumInt minus) (target Backend.Scalar.minimumInt minus)
  .here (.there .here) .here (.there .here) Backend.Scalar.minimumInt minus
  rfl rfl rfl rfl rfl rfl (initial _ _) tail
 rw [word_unique _ w rep] at run
 exact ⟨src,failed,wrap,run⟩

theorem truncation_both (p : Roadmap.Pipeline) (checked : Bool) (fuel : Nat) (tail : List Word) :
 (Source.evalE (G0 p) {F0 with checked:=checked} (fuel+3)
  (.binary .div (.local .here) (.local (.there .here)))).run (source negSeven two)=
 (.ok (.val (sourceValue (n (-3) (by decide)))),source negSeven two) ∧
 run (selected (C:=P) 0 F checked (.here : Idx Γ (.val .int)) (.there .here)).code
  {machine negSeven two with stack:=tail}=
 .ok ({machine negSeven two with stack:=tail}.push (.val (sword (-3)))) 0 := by
 obtain ⟨src,w,rep,run⟩ := ordinary_execution (G0 p) {F0 with checked:=checked} fuel
  (source negSeven two) (target negSeven two) .here (.there .here) .here (.there .here)
  negSeven two rfl rfl rfl rfl (by decide) (by decide) (initial _ _) tail
 have same := word_unique _ w rep
 rw [same] at run
 exact ⟨src,run⟩

theorem panic_classes_differ : Source.panicData .divZero≠Source.panicData .arithmetic := by decide +kernel

theorem no_floor_rounding (p : Roadmap.Pipeline) (checked : Bool) (tail : List Word) :
 run (selected (C:=P) 0 F checked (.here : Idx Γ (.val .int)) (.there .here)).code
 {machine negSeven two with stack:=tail}≠
 .ok ({machine negSeven two with stack:=tail}.push (.val (sword (-4)))) 0 := by
 first | (solve | rfl) | (solve | decide) | (solve | omega) | skip
 rw [(truncation_both p checked 0 tail).2]
 intro wrong
 have stacks := congrArg Machine.stack (Evm.Out.ok.inj wrong).1
 have same := (List.cons.inj stacks).1
 exact (by decide : Word.val (sword (-3))≠Word.val (sword (-4))) same

theorem checked_not_wrap (p : Roadmap.Pipeline) (tail : List Word) :
 run (selected (C:=P) 0 F true (.here : Idx Γ (.val .int)) (.there .here)).code
 {machine Backend.Scalar.minimumInt minus with stack:=tail}≠
 .ok ({machine Backend.Scalar.minimumInt minus with stack:=tail}.push (.val (sword Backend.Scalar.minimumInt.val))) 0 := by
 rw [(overflow_both p 0 tail).2.1]
 intro wrong
 cases wrong

theorem capacity_witness :
 Backend.Scalar.stackBound (Backend.Scalar.zeroTest ⟨1,by decide⟩) (4:Int)=true ∧
 Backend.Scalar.stackBound Backend.Scalar.signedDivOverflowTest (4:Int)=true ∧
 Backend.Scalar.stackBound [.op .SDIV] (4:Int)=true := by decide +kernel

/-- info: 'Solidity.Backend.PrimitivePackets.SignedDiv.checked_contract' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms checked_contract
/-- info: 'Solidity.Backend.PrimitivePackets.SignedDiv.Controls.capacity_witness' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms capacity_witness
/-- info: 'Solidity.Backend.PrimitivePackets.SignedDiv.locals_origin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms locals_origin
/-- info: 'Solidity.Backend.PrimitivePackets.SignedDiv.public_selection' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms public_selection
/-- info: 'Solidity.Backend.PrimitivePackets.SignedDiv.ordinary_execution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ordinary_execution
/-- info: 'Solidity.Backend.PrimitivePackets.SignedDiv.zero_execution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms zero_execution
/-- info: 'Solidity.Backend.PrimitivePackets.SignedDiv.overflow_execution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms overflow_execution
/-- info: 'Solidity.Backend.PrimitivePackets.SignedDiv.Controls.initial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms initial
/-- info: 'Solidity.Backend.PrimitivePackets.SignedDiv.Controls.truncation_both' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms truncation_both
/-- info: 'Solidity.Backend.PrimitivePackets.SignedDiv.Controls.zero_both' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms zero_both
/-- info: 'Solidity.Backend.PrimitivePackets.SignedDiv.Controls.overflow_both' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms overflow_both
/-- info: 'Solidity.Backend.PrimitivePackets.SignedDiv.Controls.no_floor_rounding' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms no_floor_rounding
/-- info: 'Solidity.Backend.PrimitivePackets.SignedDiv.Controls.checked_not_wrap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms checked_not_wrap
end Solidity.Backend.PrimitivePackets.SignedDiv.Controls
