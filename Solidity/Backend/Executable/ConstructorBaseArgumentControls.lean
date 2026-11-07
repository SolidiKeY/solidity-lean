import Solidity.Backend.Executable.ConstructorBaseArguments
import Solidity.Source.Upstream

/-! Native inherited-argument clients with declaration-derived constructor
contexts. This checks the Source constructor stage, not deployment/account
installation, admitted-program compilation or EVM execution. -/
namespace Solidity.Backend.Executable.ConstructorBaseArgumentControls
open Solidity Source Solidity.Backend.Executable.ConstructorBaseArguments

def signed16 : IntTy := ⟨true,16,by decide⟩
def u8Syntax : Syn .typeName := .elem (.int false 8 (by decide))
def i16Syntax : Syn .typeName := .elem (.int true 16 (by decide))
def baseParams : Syn (.list .param) :=
  .cons (.param u8Syntax none (some "left"))
    (.cons (.param i16Syntax none (some "right")) .nil)
def derivedParams : Syn (.list .param) :=
  .cons (.param (.elem .bytes) (some .memory) (some "old0"))
    (.cons (.param (.elem .bytes) (some .memory) (some "old1"))
      (.cons (.param i16Syntax none (some "right"))
        (.cons (.param u8Syntax none (some "left")) .nil)))
def invocation : Syn .modInv := .modInv ⟨"Base",[]⟩
  (.some (.positional (.cons (.ident "left") (.cons (.ident "right") .nil))))
def unit : Syn .unit := .unit
  (.cons (.contract false "Base" .none .nil
    (.cons (.constructor baseParams .nil false none (.block .nil)) .nil))
    (.cons (.contract false "Derived" .none (.cons (.inherit ⟨"Base",[]⟩ .none) .nil)
      (.cons (.constructor derivedParams (.cons invocation .nil) false none (.block .nil)) .nil)) .nil))
def E : Env := unit.env
def contexts (name : String) : RCtx := tysOf (E.ctorFrameLocals name)
def caller : Locals E.layout (contexts "Derived") :=
  .cons (.int 255 (by decide)) (.cons (.int (-7) (by decide))
    (.cons (.memRef rfl 0) (.cons (.memRef rfl 0) .nil)))
def baseFrame : Locals E.layout (contexts "Base") :=
  .cons (.int (-7) (by decide)) (.cons (.int 255 (by decide)) .nil)
def supplied : RBaseArg E (contexts "Derived") :=
  ⟨"Base",[.int IntTy.u8,.int signed16],
    localArgs _ _ .here (.there .here) (by decide) (by decide)⟩
def baseBody : RBody E :=
  ⟨[.int IntTy.u8,.int signed16],[],false,contexts "Base",contexts "Base",.nil,[]⟩
def derivedBody : RBody E :=
  ⟨[.bytes .memory,.bytes .memory,.int signed16,.int IntTy.u8],[],false,
    contexts "Derived",contexts "Derived",.nil,[]⟩
def program : Program E where
  body _ := none
  consts _ := none
  inits _ := []
  ctor name := if name = "Base" then some baseBody else if name = "Derived" then some derivedBody else none
  ctorLocals := contexts
  baseArgs name := if h : name = "Derived" then h.symm ▸ [supplied] else []
  contracts := E.contracts

def fixed : Roadmap.Fixed where
  evm := { keccak := fun _ => 0, keccak_lt := fun _ => by decide,
           precompile := fun _ _ => none, precompileGas := fun _ _ => 0 }
  ledger := fun balance _ address => balance address
  regionLen := 1
  rootSlots := 1
def global (p : Roadmap.Pipeline) : Glob E :=
  ⟨program,p,fixed,fun _ => ⟨0,by decide⟩,fun _ _ => false,
    fun _ => .answer (.success []),⟨0,by decide⟩⟩
def frame : Fr :=
  { this := ⟨1,by decide⟩, sender := ⟨2,by decide⟩,
    value := ⟨0,by decide⟩, static := false, contract := "Derived" }
def state : St E :=
  { St.init E with heap := ((Heap.empty.alloc ⟨.bytes .memory,.bytes [170,187]⟩).1.alloc
      ⟨.bytes .memory,.bytes [204]⟩).1 }
def initial (p : Roadmap.Pipeline) : CtorLocals (global p) := [⟨"Derived",caller⟩]
def reached (p : Roadmap.Pipeline) : CtorLocals (global p) :=
  initial p ++ [⟨"Base",baseFrame⟩]
/-- Deliberately uncertified arity metadata, used only to check the existing
structural refusal and priority order, not as an admitted Source program. -/
def badArity : RBaseArg E (contexts "Derived") := ⟨"Base",[],.nil⟩

/-- Actual constructor-stage executions; only contexts, not the whole Program, are declaration-derived. -/
theorem executions :
∀ p : Roadmap.Pipeline,
 unit.rejections = [] ∧
 contexts "Base" =
  [.int signed16,.int Source.IntTy.u8] ∧
 (Source.giveArgs (global p)
  frame 3 "Derived"
  caller
  [supplied]
  (initial p)).run
  (Source.L0 E,
   state) =
 (.ok (reached p),
  (Source.L0 E,
   state)) ∧
 (Source.ctorLocalsOf (Γ := []) (global p)
  (reached p) "Base").run
  (Source.L0 E,
   state) =
 (.ok baseFrame,
  (Source.L0 E,
   state)) ∧
 (Source.construct (global p)
  frame 3 "Derived"
  caller).run
  (Source.L0 E,
   state) =
 (.ok (), (Source.L0 E,
   state)) := by
  intro p
  cases p <;> exact ⟨rfl,rfl,rfl,rfl,rfl⟩

/-- Exact budget/priority/structural-refusal and populated-state controls. The bad arity is deliberately uncertified. -/
theorem failure_order :
∀ p : Roadmap.Pipeline,
 (Source.giveArgs (global p)
  frame 0 "Derived"
  caller
  [supplied]
  (initial p)).run
  (Source.L0 E,
   state) =
 (.error .timeout,(Source.L0 E,
   state)) ∧
 (Source.giveArgs (global p)
  frame 0 "Derived"
  caller
  [badArity]
  (reached p)).run
  (Source.L0 E,
   state) =
 (.ok (reached p),
  (Source.L0 E,
   state)) ∧
 (Source.giveArgs (global p)
  frame 3 "Derived"
  caller
  [badArity]
  (initial p)).run
  (Source.L0 E,
   state) =
 (.error (.stuck "base constructor arguments"),
  (Source.L0 E,
   state)) ∧
 state.heap.get 0 =
 some ⟨.bytes .memory,.bytes [170,187]⟩ ∧
 caller.get (.there (.there .here)) =
 caller.get (.there (.there (.there .here))) ∧
 [ (baseFrame.get .here).key,
   (baseFrame.get (.there .here)).key ] ≠
 [some 255,some (-7)] := by
  intro p
  cases p <;> exact ⟨rfl,rfl,rfl,rfl,rfl,by decide⟩

end Solidity.Backend.Executable.ConstructorBaseArgumentControls
