import Solidity.Source.Progress.StructParents
import Solidity.Lowering.P9.InferenceCuts

/-! Struct-parent progress with old and freshly allocated reference fields.
The struct declaration environment is elaborated; constructor nodes are built
directly. Both pipelines retain allocation/alias, panic and packing boundaries. -/
namespace Solidity.Source.Progress.StructParentControls
open EM

def unit : Syn .unit := .unit (.cons (.contract false "C" .none .nil
  (.cons (.struct "Pair" (.structMember (.elem .bytes) "old")
    (.cons (.structMember (.elem .bytes) "fresh") .nil)) .nil)) .nil)
def resolution := Source.resolveUnit {pipeline:=.legacy} unit
abbrev E := resolution.env
def dn : DeclName := ⟨some "C","Pair"⟩
abbrev Bty : STy := .bytes .memory
abbrev Γ : RCtx := [.int .u256,Bty]
theorem typed : (E.structFields dn .memory).map (·.map Prod.snd) = some [Bty,Bty] := rfl

def frame : Fr := {this:=⟨17,by decide⟩,sender:=⟨19,by decide⟩,value:=⟨0,by decide⟩,static:=false,contract:="C"}
def globals (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) : Glob E :=
  ⟨Source.progOf E,p,fixed,fun _=>⟨0,by decide⟩,fun _ _=>true,
    fun _=>.answer (.success []),⟨0,by decide⟩⟩
theorem base_arguments : (Source.elabBaseArgs E "C").isSome = true :=
  Solidity.Lowering.P9.InferenceCuts.base_some E "C"
    (by rw [show E.inheritOf "C" = .nil from rfl, Syn.inheritList]) rfl
theorem env_elaborates : Source.elaborates E = true := by
  change ((Source.elabBaseArgs E "C").isSome && true) = true
  rw [base_arguments]
  rfl
theorem elaborated : (Source.elaborate resolution).isSome = true := by
  simp only [Source.elaborate,env_elaborates,↓reduceIte,Option.isSome_some]
theorem value_checked (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) :
    Solidity.Lowering.P9.WholeProgram.check resolution (globals p fixed) "C" [] = true := rfl

def seed : Heap E.layout := (Heap.empty.alloc ⟨Bty,.bytes [42,77]⟩).1
def initial : St E :=
  {ex:=⟨⟨fun _=>Account.empty _⟩,Transient.empty,[]⟩,heap:=seed,events:=[],
   logs:=[(⟨17,by decide⟩,[9])],fnLocals:=⟨[.bool],.cons (.bool false) .nil⟩}
def small : Locals E.layout Γ := .cons (.int 2 (by decide)) (.cons (.memRef rfl 0) .nil)
def huge : Locals E.layout Γ := .cons (.int (2^64) (by decide)) (.cons (.memRef rfl 0) .nil)
def childHeap : Heap E.layout := (seed.alloc ⟨Bty,.bytes [0,0]⟩).1
def fields : Data E.layout (.struct .memory dn) :=
  .struct (.cons (.val (.memRef rfl 0)) (.cons (.val (.memRef rfl 1)) .nil))
def allocated : St E := {initial with heap:=(childHeap.alloc ⟨_,fields⟩).1}
def partialState : St E := {initial with heap:=childHeap}

theorem initial_mem : MemOK E seed.ty (small,initial) ∧ MemOK E seed.ty (huge,initial) := by
  have heap : HeapOK (E:=E) seed := HeapOK.empty.alloc (.bytes [42,77])
  have shape : HeapShaped seed := HeapShaped.empty.alloc trivial
  have inner : HeapInner seed := HeapInner.empty.alloc trivial
  exact ⟨⟨⟨⟨heap,HeapTy.Le.refl _⟩,⟨trivial,⟨⟨Bty,rfl,rfl⟩,trivial⟩⟩⟩,shape,inner⟩,
    ⟨⟨⟨heap,HeapTy.Le.refl _⟩,⟨trivial,⟨⟨Bty,rfl,rfl⟩,trivial⟩⟩⟩,shape,inner⟩⟩

def fresh : RExpr E Γ Bty := .newArray rfl (.local .here) rfl
def args : RConvArgs E Γ [Bty,Bty] :=
  .cons (.local (.there .here)) rfl (.cons fresh rfl .nil)
def expression : RExpr E Γ (.struct .memory dn) := .structNew typed args

theorem ready {A : Decl → Prop} : ReadyArgs A args :=
  .cons rfl (.inr rfl) (.local _) (.cons rfl (.inr rfl) (.newArray .bytes rfl (.local _)) .nil)

theorem checked (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) :
    NS (evalE (globals p fixed) frame 10 expression) ∧
    Hoare (MemOK E seed.ty) (evalE (globals p fixed) frame 10 expression)
      (fun v y=>MemOK E seed.ty y ∧ RValOK E y.2.heap.ty v) (fun _ y=>MemOK E seed.ty y) :=
  struct_parent_from_elaborate resolution elaborated (globals p fixed) rfl "C" []
    (value_checked p fixed) frame rfl 10 typed args ready seed.ty

theorem run (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) :
    (evalE (globals p fixed) frame 10 expression).run (small,initial) =
      (.ok (.val (.memRef rfl 2)),(small,allocated)) := rfl

theorem early_panic (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) :
    (evalE (globals p fixed) frame 10 expression).run (huge,initial) =
      (.error (.revert (panicData .alloc)),(huge,initial)) := rfl

theorem preserved (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) :
    NS (evalE (globals p fixed) frame 10 expression) ∧
    MemOK E seed.ty (small,allocated) ∧
    RValOK E allocated.heap.ty (.val (.memRef rfl 2) : RVal E.layout (.struct .memory dn)) ∧
    MemOK E seed.ty (huge,initial) := by
  have success := (checked p fixed).2 (small,initial) initial_mem.1
  have panic := (checked p fixed).2 (huge,initial) initial_mem.2
  rw [run] at success
  rw [early_panic] at panic
  exact ⟨(checked p fixed).1,success.1,success.2,panic⟩

theorem heap_observations :
    allocated.heap.get 0 = seed.get 0 ∧
    allocated.heap.get 1 = some ⟨Bty,.bytes [0,0]⟩ ∧
    allocated.heap.get 2 = some ⟨.struct .memory dn,fields⟩ ∧
    allocated.heap.next = 3 ∧ allocated.logs = initial.logs ∧ allocated.fnLocals = initial.fnLocals :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩

def statement : RStmt E [] false .body Γ Γ := .expr expression

theorem statement_checked (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) :
    NS (execS (globals p fixed) frame 11 0 none statement small) ∧
    Hoare (fun y=>MemOK E seed.ty y ∧ LocalsOK E y.2.heap.ty small)
      (execS (globals p fixed) frame 11 0 none statement small)
      (fun out y=>MemOK E seed.ty y ∧ Preservation.OutRefsOK (E:=E) y.2.heap.ty out)
      (fun _ y=>MemOK E seed.ty y) :=
  struct_statement_progress_and_memory
    (Solidity.Lowering.P9.WholeProgram.from_elaborate resolution elaborated
      (globals p fixed) rfl "C" [] (value_checked p fixed))
    frame rfl 11 typed args ready 0 none small seed.ty

theorem statement_run (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) :
    (execS (globals p fixed) frame 11 0 none statement small).run (L0 E,initial) =
      (.ok (.normal small),(L0 E,allocated)) := rfl

theorem statement_preserved (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) :
    NS (execS (globals p fixed) frame 11 0 none statement small) ∧
    MemOK E seed.ty (L0 E,allocated) ∧
    Preservation.OutRefsOK (E:=E) allocated.heap.ty (.normal small : Out E.layout Γ Γ) := by
  have entry : MemOK E seed.ty (L0 E,initial) := Preservation.relocalize initial_mem.1 (L0 E) trivial
  have actual := (statement_checked p fixed).2 (L0 E,initial) ⟨entry,initial_mem.1.1.2⟩
  rw [statement_run] at actual
  exact ⟨(statement_checked p fixed).1,actual⟩

theorem exact_boundary (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) :
    (evalE (globals p fixed) frame 5 expression).run (small,initial) =
      (.ok (.val (.memRef rfl 2)),(small,allocated)) ∧
    (evalE (globals p fixed) frame 4 expression).run (small,initial) =
      (.error .timeout,(small,initial)) := ⟨rfl,rfl⟩

abbrev LateΓ : RCtx := [.int .u256,.int .u256,Bty]
def lateLocals : Locals E.layout LateΓ :=
  .cons (.int 2 (by decide)) (.cons (.int (2^64) (by decide)) (.cons (.memRef rfl 0) .nil))
def lateArgs : RConvArgs E LateΓ [Bty,Bty] :=
  .cons (.newArray (τ:=Bty) rfl (.local .here) rfl) rfl
    (.cons (.newArray (τ:=Bty) rfl (.local (.there .here)) rfl) rfl .nil)
def lateParent : RExpr E LateΓ (.struct .memory dn) := .structNew typed lateArgs
theorem late_ready {A : Decl → Prop} : ReadyArgs A lateArgs :=
  .cons rfl (.inr rfl) (.newArray .bytes rfl (.local _))
    (.cons rfl (.inr rfl) (.newArray .bytes rfl (.local _)) .nil)

theorem late_run (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) :
    (evalE (globals p fixed) frame 10 lateParent).run (lateLocals,initial) =
      (.error (.revert (panicData .alloc)),(lateLocals,partialState)) := rfl

theorem late_preserved (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) :
    NS (evalE (globals p fixed) frame 10 lateParent) ∧ MemOK E seed.ty (lateLocals,partialState) := by
  have joint : NS (evalE (globals p fixed) frame 10 lateParent) ∧
      Hoare (MemOK E seed.ty) (evalE (globals p fixed) frame 10 lateParent)
        (fun v y=>MemOK E seed.ty y ∧ RValOK E y.2.heap.ty v) (fun _ y=>MemOK E seed.ty y) :=
    struct_parent_from_elaborate resolution elaborated (globals p fixed) rfl "C" []
      (value_checked p fixed) frame rfl 10 typed lateArgs late_ready seed.ty
  have input : MemOK E seed.ty (lateLocals,initial) := Preservation.relocalize initial_mem.1
    lateLocals ⟨trivial,⟨trivial,⟨⟨Bty,rfl,rfl⟩,trivial⟩⟩⟩
  have actual := joint.2 (lateLocals,initial) input
  rw [late_run] at actual
  exact ⟨joint.1,actual⟩

theorem low_horizon (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) :
    (evalE (globals p fixed) frame 0 expression).run (small,initial) =
      (.error .timeout,(small,initial)) := rfl

theorem wrong_count (state : St E) :
    ((fieldsOf (E:=E) (.nil : Vals E.layout []) [Bty] : EM E [] _).run (L0 E,state)).1 =
      .error (.stuck "member count") := rfl
theorem wrong_type (state : St E) :
    ((fieldsOf (E:=E) (D:=E.layout) (.cons (.bool true) .nil) [.int .u8] : EM E [] _).run (L0 E,state)).1 =
      .error (.stuck "member type") := rfl
theorem wrong_type_not_ns :
    ¬NS (fieldsOf (E:=E) (D:=E.layout) (Γ:=[]) (.cons (.bool true) .nil) [.int .u8]) := by
  intro progress
  exact progress (L0 E,initial) "member type" rfl

theorem old_ready_refused : ¬ReadyExpr (fun _=>False) expression := by
  intro admitted
  cases admitted with
  | value fragment _ => exact fragment

#print axioms typed
#print axioms base_arguments
#print axioms env_elaborates
#print axioms elaborated
#print axioms value_checked
#print axioms initial_mem
#print axioms ready
#print axioms checked
#print axioms run
#print axioms early_panic
#print axioms preserved
#print axioms heap_observations
#print axioms statement_checked
#print axioms statement_run
#print axioms statement_preserved
#print axioms exact_boundary
#print axioms late_ready
#print axioms late_run
#print axioms late_preserved
#print axioms low_horizon
#print axioms wrong_count
#print axioms wrong_type
#print axioms wrong_type_not_ns
#print axioms old_ready_refused
end Solidity.Source.Progress.StructParentControls
