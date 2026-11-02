import Solidity.Source.Preservation.MemberPacking
import Solidity.Source.Preservation.Encoding
import Solidity.Source.Preservation.FrameControls
import Solidity.Source.Elaborate

/-! Actual typed constructor/ABI allocation and count/type refusal controls.
These source-only observations use the existing evaluator and arbitrary fixed
parameters. They assert neither compiler refinement nor universal coverage.
-/
namespace Solidity.Source.Preservation.AllocationControls
open EM

def unit : Syn .unit := .unit (.cons (.contract false "C" .none .nil
  (.cons (.struct "P" (.structMember (.elem .bool) "a")
    (.cons (.structMember (.elem .bool) "b") .nil)) .nil)) .nil)
def E : Env := unit.env
def dn : DeclName := ⟨some "C", "P"⟩
def ctx : Ctx := {env := E, scope := some "C", locals := [("caller", .bool)]}
def syn : Syn .expr := .call (.ident "P") (.positional
  (.cons (.lit (.bool true)) (.cons (.lit (.bool false)) .nil)))
def typed : Typed ctx syn (.struct .memory dn) :=
  .structNew rfl rfl (.cons (.bool true) (.cons (.bool false) .nil)) rfl
def constructor : RExpr E [.bool] (.struct .memory dn) := typed.toR
def structData : Data E.layout (.struct .memory dn) :=
  .struct (.cons (.val (.bool true)) (.cons (.val (.bool false)) .nil))
def glob (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) : Glob E :=
  ⟨Source.progOf E, p, fixed, fun _ => ⟨0, by decide⟩, fun _ _ => true,
    fun _ => .answer (.success []), ⟨0, by decide⟩⟩
def frame : Fr := {this := ⟨0, by decide⟩, sender := ⟨1, by decide⟩, value := ⟨0, by decide⟩, static := false, contract := "C"}

theorem constructor_run (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) :
    (evalE (glob p fixed) frame 10 constructor).run (.cons (.bool false) .nil, St.init E) =
    (.ok (.val (.memRef rfl 0)), (.cons (.bool false) .nil,
      {St.init E with heap := (Heap.empty.alloc ⟨_, structData⟩).1})) := by
  cases p <;> rfl

def encoder : RExpr E [.bool] (.bytes .memory) := .abiEncode .encode (.cons (.bool true) .nil)
def encoded : Roadmap.Bytes := wordBytes ⟨1, by decide⟩

theorem encoder_run (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) :
    (evalE (glob p fixed) frame 10 encoder).run (.cons (.bool false) .nil, St.init E) =
    (.ok (.val (.memRef rfl 0)), (.cons (.bool false) .nil,
      {St.init E with heap := (Heap.empty.alloc ⟨.bytes .memory, .bytes encoded⟩).1})) := by
  cases p <;> rfl

theorem wrong_count (s : St E) :
    ((fieldsOf (.nil : Vals E.layout []) [.bool, .bool] : EM E [] _).run (.nil, s)).1 =
      .error (.stuck "member count") := rfl

theorem wrong_type (s : St E) :
    ((fieldsOf (D := E.layout) (.cons (.bool true) .nil) [.int IntTy.u8] : EM E [] _).run (.nil, s)).1 =
      .error (.stuck "member type") := rfl

theorem initial_mem : MemOK E (Heap.empty : Heap E.layout).ty
    (.cons (.bool false) .nil, St.init E) := FrameControls.inhabited

def args : RConvArgs E [.bool] [.bool, .bool] :=
  .cons (.bool true) rfl (.cons (.bool false) rfl .nil)
theorem constructor_eq : constructor = .structNew (by rfl) args := rfl

theorem args_eq (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) :
    evalConvArgs (glob p fixed) frame 9 args =
      pure (.cons (.bool true) (.cons (.bool false) .nil)) := by cases p <;> rfl

theorem constructor_mem (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) (H : HeapTy) :
    Hoare (MemOK E H) (evalE (glob p fixed) frame 10 constructor)
      (fun v y => MemOK E H y ∧ RValOK E y.2.heap.ty v) (fun _ y => MemOK E H y) := by
  rw [constructor_eq]
  apply evalE_structNew_mem
  rw [args_eq]
  exact Hoare.pure' fun _ h => ⟨h, ⟨trivial, ⟨trivial, trivial⟩⟩⟩

theorem encoder_args_eq (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) :
    evalArgs (glob p fixed) frame 9 (.cons (.bool true) .nil : RArgs E [.bool] [.bool]) =
      pure (.cons (.val (.bool true)) .nil) := by cases p <;> rfl

theorem encoder_mem (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) (H : HeapTy) :
    Hoare (MemOK E H) (evalE (glob p fixed) frame 10 encoder)
      (fun v y => MemOK E H y ∧ RValOK E y.2.heap.ty v) (fun _ y => MemOK E H y) := by
  unfold encoder
  apply evalE_abiEncode_mem
  rw [encoder_args_eq]
  exact Hoare.pure' fun _ h => h

#print axioms constructor_mem
#print axioms encoder_mem
#print axioms constructor_run
#print axioms encoder_run
#print axioms wrong_count
#print axioms wrong_type
end Solidity.Source.Preservation.AllocationControls
