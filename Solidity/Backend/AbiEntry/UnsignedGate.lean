import Solidity.Backend.AbiEntry.UnsignedGateInterface

/-! Range validation reads the preserved input local and writes only the
continuation/result local. Unbounded unsigned bounds are not word-truncated. -/
namespace Solidity.Backend.AbiEntry.UnsignedGate
open Solidity.Evm
open Interface (RouteCtx unsignedGateOutcome)

def condition (C : Contract) (bound : Fin W) : Val C RouteCtx .bool :=
  .binop .lt rfl rfl (.simple (.local (.there .here)))
    (.simple (.lit (bound.val : Int) (PrimTy.inRange_uint_of_lt bound.isLt)))
def program (C : Contract) (bound : Nat) (label : Fin W) : Prog C RouteCtx RouteCtx :=
  if fits : bound<W then .cons (.require (condition C ⟨bound,fits⟩)) (SelectorRoutes.writeLabel C label)
  else SelectorRoutes.writeLabel C label

theorem admitted (C : Contract) (bound : Nat) (label : Fin W) :
    inFragP (Frag.init RouteCtx) (program C bound label)=some (Frag.init RouteCtx) := by
  unfold program
  split <;> exact SelectorRoutes.write_core C label _

def compiled (C : Contract) (base bound : Nat) (label : Fin W) :
    Compiler.Compilation base (Frag.init RouteCtx) (program C bound label) :=
  .core (Frag.init RouteCtx) (admitted C bound label)

theorem selected (C : Contract) (base bound : Nat) (label : Fin W) :
    Compiler.compile base (Frag.init RouteCtx) (program C bound label)=some (compiled C base bound label) :=
  ValueGateBody.body_selected base _ _ _ (admitted C bound label)

/-- Comparison adapter for typed validator composition. -/
theorem condition_code (C : Contract) (base : Nat) (bound : Fin W) :
    compileVal base (condition C bound)=[.mload base,.push (.val bound),.gt] := by
  simp only [condition,compileVal,compileSimple]
  have literal : wmod (toWord (bound.val : Int))=bound := by
    simp only [toWord,Int.natCast_nonneg,if_true,Int.toNat_natCast]
    exact Fin.ext (Nat.mod_eq_of_lt bound.isLt)
  rw [literal]
  rfl

private theorem bounded_code (C : Contract) (base : Nat) (bound label : Fin W) :
    compileProg base (.cons (.require (condition C bound)) (SelectorRoutes.writeLabel C label))=
      [.mload base,.push (.val bound),.gt,.jumpi 1,.revert,.push (.val label),.mstore (base+1)] := by
  simp only [compileProg,compileStmt,condition,compileVal,compileSimple]
  rw [SelectorRoutes.write_code]
  have literal : wmod (toWord (bound.val : Int))=bound := by
    simp only [toWord,Int.natCast_nonneg,if_true,Int.toNat_natCast]
    exact Fin.ext (Nat.mod_eq_of_lt bound.isLt)
  rw [literal]
  rfl

private theorem bounded_run (base : Nat) (bound label word : Fin W) (machine : Machine)
    (initial : machine.mem base=.val word) :
    run [.mload base,.push (.val bound),.gt,.jumpi 1,.revert,.push (.val label),.mstore (base+1)] machine=
      if word.val<bound.val then .ok {machine with mem := upd machine.mem (base+1) (.val label)} 0 else .revert := by
  by_cases valid : word.val<bound.val
  · simp only [run,exec_cons_zero,Instr.step,Machine.next,Out.bind,initial,valid,
      decide_true,bword,if_true,Nat.one_ne_zero]
    rfl
  · simp only [run,exec_cons_zero,Instr.step,Machine.next,Out.bind,initial,valid,decide_false,bword,Bool.false_eq_true,if_false,if_true]

theorem run_program (C : Contract) (base bound : Nat) (label : Fin W) (machine : Machine)
    (word : Fin W) (initial : machine.mem base=.val word) :
    run (compileProg base (program C bound label)) machine=unsignedGateOutcome base bound label word machine := by
  by_cases fits : bound<W
  · simp only [program,dif_pos fits]
    rw [bounded_code,bounded_run base _ label word machine initial]
    rfl
  · have valid : word.val<bound := Nat.lt_of_lt_of_le word.isLt (Nat.le_of_not_gt fits)
    simp only [program,dif_neg fits,unsignedGateOutcome,if_pos valid]
    rw [SelectorRoutes.write_code]
    rfl

theorem executed (C : Contract) (base bound : Nat) (label : Fin W)
    (result : Compiler.Compilation base (Frag.init RouteCtx) (program C bound label))
    (found : Compiler.compile base (Frag.init RouteCtx) (program C bound label)=some result)
    (machine : Machine) (word : Fin W) (initial : machine.mem base=.val word) :
    run result.code machine=unsignedGateOutcome base bound label word machine := by
  have same : result=compiled C base bound label := Option.some.inj (found.symm.trans (selected C base bound label))
  rw [same]
  exact run_program C base bound label machine word initial

theorem rejected_iff (C : Contract) (base bound : Nat) (label : Fin W)
    (result : Compiler.Compilation base (Frag.init RouteCtx) (program C bound label))
    (found : Compiler.compile base (Frag.init RouteCtx) (program C bound label)=some result)
    (machine : Machine) (word : Fin W) (initial : machine.mem base=.val word) :
    (run result.code machine=.revert ↔ ¬word.val<bound) := by
  rw [executed C base bound label result found machine word initial]
  by_cases valid : word.val<bound
  · simp only [unsignedGateOutcome,if_pos valid]
    constructor
    · intro impossible; cases impossible
    · intro impossible; exact False.elim (impossible valid)
  · simp only [unsignedGateOutcome,if_neg valid]
    exact ⟨fun _ => valid,fun _ => True.intro⟩

/-- Raw-word failure transport to the existing lazy ABI scalar decoder. The
caller is still responsible for all surrounding span/head checks. -/
theorem enum_rejection (C : Contract) (base members : Nat) (label : Fin W)
    (result : Compiler.Compilation base (Frag.init RouteCtx) (program C members label))
    (found : Compiler.compile base (Frag.init RouteCtx) (program C members label)=some result)
    (machine : Machine) (word : Fin W) (initial : machine.mem base=.val word)
    (input : Solidity.AbiEntry.Input) (offset fuel len : Nat)
    (loaded : word.val=Solidity.AbiEntry.load input.data offset) (rejected : run result.code machine=.revert) :
    Solidity.AbiEntry.cval input (fuel+1) (.word (.enumBelow members)) offset len=.error .revert := by
  have invalid := (rejected_iff C base members label result found machine word initial).mp rejected
  rw [loaded] at invalid
  simp only [Solidity.AbiEntry.cval,Solidity.AbiEntry.Kind.valid,decide_eq_false invalid,Bool.false_eq_true,dite_false]

theorem uint_rejection (C : Contract) (base bits : Nat) (label : Fin W)
    (result : Compiler.Compilation base (Frag.init RouteCtx) (program C (2^bits) label))
    (found : Compiler.compile base (Frag.init RouteCtx) (program C (2^bits) label)=some result)
    (machine : Machine) (word : Fin W) (initial : machine.mem base=.val word)
    (input : Solidity.AbiEntry.Input) (offset fuel len : Nat)
    (loaded : word.val=Solidity.AbiEntry.load input.data offset) (rejected : run result.code machine=.revert) :
    Solidity.AbiEntry.cval input (fuel+1) (.word (.uint bits)) offset len=.error .revert := by
  have invalid := (rejected_iff C base (2^bits) label result found machine word initial).mp rejected
  rw [loaded] at invalid
  simp only [Solidity.AbiEntry.cval,Solidity.AbiEntry.Kind.valid,decide_eq_false invalid,Bool.false_eq_true,dite_false]

theorem bool_rejection (C : Contract) (base : Nat) (label : Fin W)
    (result : Compiler.Compilation base (Frag.init RouteCtx) (program C 2 label))
    (found : Compiler.compile base (Frag.init RouteCtx) (program C 2 label)=some result)
    (machine : Machine) (word : Fin W) (initial : machine.mem base=.val word)
    (input : Solidity.AbiEntry.Input) (offset fuel len : Nat)
    (loaded : word.val=Solidity.AbiEntry.load input.data offset) (rejected : run result.code machine=.revert) :
    Solidity.AbiEntry.cval input (fuel+1) (.word .bool) offset len=.error .revert := by
  have invalid := (rejected_iff C base 2 label result found machine word initial).mp rejected
  rw [loaded] at invalid
  simp only [Solidity.AbiEntry.cval,Solidity.AbiEntry.Kind.valid,decide_eq_false invalid,Bool.false_eq_true,dite_false]

theorem enum_correspondence (C : Contract) (base members : Nat) (label : Fin W)
    (result : Compiler.Compilation base (Frag.init RouteCtx) (program C members label))
    (found : Compiler.compile base (Frag.init RouteCtx) (program C members label)=some result)
    (machine : Machine) (word : Fin W) (initial : machine.mem base=.val word)
    (input : Solidity.AbiEntry.Input) (offset fuel len : Nat)
    (loaded : word.val=Solidity.AbiEntry.load input.data offset) :
    (run result.code machine=.revert ↔
      Solidity.AbiEntry.cval input (fuel+1) (.word (.enumBelow members)) offset len=.error .revert) := by
  rw [rejected_iff C base members label result found machine word initial,loaded]
  by_cases valid : Solidity.AbiEntry.load input.data offset<members
  · simp only [Solidity.AbiEntry.cval,Solidity.AbiEntry.Kind.valid,decide_eq_true valid,dite_true]
    constructor
    · intro impossible;exact False.elim (impossible valid)
    · intro impossible;cases impossible
  · simp only [Solidity.AbiEntry.cval,Solidity.AbiEntry.Kind.valid,decide_eq_false valid,Bool.false_eq_true,dite_false]
    exact ⟨fun _ => True.intro,fun _ => valid⟩

theorem uint_correspondence (C : Contract) (base bits : Nat) (label : Fin W)
    (result : Compiler.Compilation base (Frag.init RouteCtx) (program C (2^bits) label))
    (found : Compiler.compile base (Frag.init RouteCtx) (program C (2^bits) label)=some result)
    (machine : Machine) (word : Fin W) (initial : machine.mem base=.val word)
    (input : Solidity.AbiEntry.Input) (offset fuel len : Nat)
    (loaded : word.val=Solidity.AbiEntry.load input.data offset) :
    (run result.code machine=.revert ↔
      Solidity.AbiEntry.cval input (fuel+1) (.word (.uint bits)) offset len=.error .revert) := by
  rw [rejected_iff C base (2^bits) label result found machine word initial,loaded]
  by_cases valid : Solidity.AbiEntry.load input.data offset<(2^bits)
  · simp only [Solidity.AbiEntry.cval,Solidity.AbiEntry.Kind.valid,decide_eq_true valid,dite_true]
    constructor
    · intro impossible;exact False.elim (impossible valid)
    · intro impossible;cases impossible
  · simp only [Solidity.AbiEntry.cval,Solidity.AbiEntry.Kind.valid,decide_eq_false valid,Bool.false_eq_true,dite_false]
    exact ⟨fun _ => True.intro,fun _ => valid⟩

theorem bool_correspondence (C : Contract) (base : Nat) (label : Fin W)
    (result : Compiler.Compilation base (Frag.init RouteCtx) (program C 2 label))
    (found : Compiler.compile base (Frag.init RouteCtx) (program C 2 label)=some result)
    (machine : Machine) (word : Fin W) (initial : machine.mem base=.val word)
    (input : Solidity.AbiEntry.Input) (offset fuel len : Nat)
    (loaded : word.val=Solidity.AbiEntry.load input.data offset) :
    (run result.code machine=.revert ↔
      Solidity.AbiEntry.cval input (fuel+1) (.word .bool) offset len=.error .revert) := by
  rw [rejected_iff C base 2 label result found machine word initial,loaded]
  by_cases valid : Solidity.AbiEntry.load input.data offset<2
  · simp only [Solidity.AbiEntry.cval,Solidity.AbiEntry.Kind.valid,decide_eq_true valid,dite_true]
    constructor
    · intro impossible;exact False.elim (impossible valid)
    · intro impossible;cases impossible
  · simp only [Solidity.AbiEntry.cval,Solidity.AbiEntry.Kind.valid,decide_eq_false valid,Bool.false_eq_true,dite_false]
    exact ⟨fun _ => True.intro,fun _ => valid⟩

def certificate : Interface.UnsignedGateCertificate program where
  selected := fun C base bound label => ⟨compiled C base bound label,selected C base bound label⟩
  executed := executed
/-- info: 'Solidity.Backend.AbiEntry.UnsignedGate.admitted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms admitted
/-- info: 'Solidity.Backend.AbiEntry.UnsignedGate.selected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms selected
/-- info: 'Solidity.Backend.AbiEntry.UnsignedGate.run_program' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms run_program
/-- info: 'Solidity.Backend.AbiEntry.UnsignedGate.executed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms executed
/-- info: 'Solidity.Backend.AbiEntry.UnsignedGate.rejected_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms rejected_iff
/-- info: 'Solidity.Backend.AbiEntry.UnsignedGate.enum_rejection' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms enum_rejection
/-- info: 'Solidity.Backend.AbiEntry.UnsignedGate.uint_rejection' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms uint_rejection
/-- info: 'Solidity.Backend.AbiEntry.UnsignedGate.bool_rejection' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms bool_rejection
/-- info: 'Solidity.Backend.AbiEntry.UnsignedGate.certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms certificate
/-- info: 'Solidity.Backend.AbiEntry.UnsignedGate.enum_correspondence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms enum_correspondence
/-- info: 'Solidity.Backend.AbiEntry.UnsignedGate.uint_correspondence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms uint_correspondence
/-- info: 'Solidity.Backend.AbiEntry.UnsignedGate.bool_correspondence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms bool_correspondence
/-- info: 'Solidity.Backend.AbiEntry.UnsignedGate.condition_code' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms condition_code
end Solidity.Backend.AbiEntry.UnsignedGate
