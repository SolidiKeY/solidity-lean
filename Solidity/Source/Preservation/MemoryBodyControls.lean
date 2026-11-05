import Solidity.Source.Preservation.MemoryBodyCalls
import Solidity.Roadmap.Controls

/-! An inhabited intrinsic memory-call body: mutate through alias a, rebind a
to a fresh allocation, and return alias b. The caller keeps both old locals.
The matching signature/runtime program is built directly, not elaborated. -/
namespace Solidity.Source.Preservation.MemoryBodyControls
open EM

def E : Env := ⟨[]⟩
abbrev U : STy := .int .u256
abbrev Aty : STy := .array .memory U none
abbrev ps : List STy := [Aty,Aty,U]
abbrev rs : List STy := [Aty]
abbrev Δ : RCtx := [Aty,U,Aty,Aty]
def aIndex : Idx Δ Aty := .there (.there (.there .here))
def bIndex : Idx Δ Aty := .there (.there .here)
def valueIndex : Idx Δ U := .there .here

def write : RExpr E Δ U := .assign
  (.indexArray (.local aIndex) (by decide) (.const (Q.ofInt 0)) (by decide +kernel)) (.local valueIndex)
def rebind : RExpr E Δ Aty := .assign (.local aIndex)
  (.newArray rfl (.const (Q.ofInt 2)) (by decide +kernel))
def results : RConvArgs E Δ rs := .cons (.local bIndex) (by decide +kernel) .nil

def body : RBody E where
  ps := ps; rs := rs; inModifier := false; locals := Δ; out := Δ
  items := .stmt (.expr write) (.stmt (.expr rebind) (.stmt (.retTuple results) .nil))

def uintType : Syn .typeName := .elem (.int false 256 (by decide))
def arrayType : Syn .typeName := .array uintType .none
def d : Decl := ⟨.function,"mutate",none,true,
  .function (.ident "mutate")
    (.cons (.param arrayType (some .memory) (some "a"))
      (.cons (.param arrayType (some .memory) (some "b"))
        (.cons (.param uintType none (some "v")) .nil))) none none .nil false none
    (.cons (.param arrayType (some .memory) none) .nil) .none⟩
def program : Program E := ⟨fun _ => some body,fun _ => none,fun _ => [],fun _ => none,fun _ => [],fun _ => [],[]⟩
def glob (p : Roadmap.Pipeline) : Glob E :=
  ⟨program,p,Roadmap.Controls.toyFixed,fun _ => ⟨0,by decide⟩,fun _ _ => false,
    fun _ => .answer (.success []),⟨0,by decide⟩⟩
def frame : Fr := {this := ⟨41,by decide⟩,sender := ⟨37,by decide⟩,value := ⟨0,by decide⟩,static := false,contract := "Memory"}

def original : Data E.layout Aty := .array 1 (fun _ h => nomatch h)
  (fun _ => .val (.int 7 (by decide)))
def empty : Data E.layout Aty := .array 0 (fun _ h => nomatch h) (fun i => i.elim0)
def fresh : Data E.layout Aty := .array 2 (fun _ h => nomatch h)
  (fun _ => .val (.int 0 (by decide)))
def modified : Data E.layout Aty := .array 1 (fun _ h => nomatch h)
  (fun j => if j.val = 0 then .val (.int 42 (by decide)) else .val (.int 7 (by decide)))
def seed : Heap E.layout := (Heap.empty.alloc ⟨Aty,original⟩).1
def defaulted : Heap E.layout := (seed.alloc ⟨Aty,empty⟩).1
def mutated : Heap E.layout := defaulted.write 0 modified rfl

def initial : St E where
  ex := ⟨⟨fun _ => Account.empty _⟩,Transient.empty,[]⟩
  heap := seed
  events := []
  logs := [(⟨17,by decide⟩,[9])]
  fnLocals := ⟨[.bool],.cons (.bool true) .nil⟩
def after : St E := {initial with heap := (mutated.alloc ⟨Aty,fresh⟩).1}
def parameters : Vals E.layout ps :=
  .cons (.memRef rfl 0) (.cons (.memRef rfl 0) (.cons (.int 42 (by decide)) .nil))
abbrev Γ : RCtx := [Aty,Aty,U,.bool]
def caller : Locals E.layout Γ := .cons (.memRef rfl 0)
  (.cons (.memRef rfl 0) (.cons (.int 42 (by decide)) (.cons (.bool false) .nil)))
def args : RConvArgs E Γ ps := .cons (.local .here) (by decide +kernel)
  (.cons (.local (.there .here)) (by decide +kernel)
    (.cons (.local (.there (.there .here))) (by decide +kernel) .nil))
theorem signature : d.fnSig E = some (ps,rs) := rfl
def expression : RExpr E Γ Aty := .call d signature args

theorem body_admitted : MemoryItems (fun _ => False) rs false body.items :=
  .stmt (.expr (.arrayWrite _ rfl (.local _) (.value trivial trivial) (.local _)))
    (.stmt (.expr (.rebind _ (.newArray rfl _ (.value trivial trivial))))
      (.stmt (.returns (.cons _ (.local _) .nil)) .nil))
theorem calls (p : Roadmap.Pipeline) : CallsOK (fun _ => False) (glob p) frame.contract := by
  intro d ps rs signature impossible
  cases impossible

theorem run (p : Roadmap.Pipeline) :
    (callInternal (glob p) frame 20 d parameters rs).run (.nil,initial) =
      (.ok (.val (.memRef rfl 0)),(.nil,after)) := rfl

theorem expression_run (p : Roadmap.Pipeline) :
    (evalE (glob p) frame 22 expression).run (caller,initial) =
      (.ok (.val (.memRef rfl 0)),(caller,after)) := rfl

theorem initial_mem : MemOK E seed.ty (caller,initial) := by
  have heap : HeapOK (E := E) seed := HeapOK.empty.alloc
    (.array (fun _ => .val (Val.refOK_of_loc rfl _)))
  have shape : HeapShaped seed := HeapShaped.empty.alloc trivial
  have inner : HeapInner seed := HeapInner.empty.alloc (fun _ => ⟨_,rfl⟩)
  have ref : (Val.memRef (D := E.layout) (τ := Aty) rfl 0).RefOK E seed.ty := ⟨Aty,rfl,rfl⟩
  exact ⟨⟨⟨heap,HeapTy.Le.refl _⟩,ref,ref,trivial,trivial,trivial⟩,shape,inner⟩

theorem preserved (p : Roadmap.Pipeline) :
    MemOK E seed.ty (caller,after) ∧ RValOK E after.heap.ty (.val (τ := Aty) (.memRef rfl 0)) := by
  have actual := eval_memory_call_mem (calls p) frame rfl d ps rs signature body rfl rfl rfl rfl rfl
    body_admitted args (.cons _ (.local _) (.cons _ (.local _) (.cons _ (.local _) .nil))) seed.ty 21
    (caller,initial) initial_mem
  have observed : (evalE (glob p) frame (21+1) (.call d signature args)).run (caller,initial) =
      (.ok (.val (.memRef rfl 0)),(caller,after)) := expression_run p
  rw [observed] at actual
  exact actual

theorem alias_read :
    (readLoc frame (.mem (τ := U) 0 0) : EM E [] _).run (.nil,after) =
      (.ok (.int 42 (by decide)),(.nil,after)) := rfl

theorem fresh_distinct : after.heap.next = 3 ∧ after.heap.get 2 = some ⟨Aty,fresh⟩ ∧
    caller.get .here = .memRef rfl 0 ∧ caller.get (.there .here) = .memRef rfl 0 := ⟨rfl,rfl,rfl,rfl⟩

theorem timeout (p : Roadmap.Pipeline) :
    (callInternal (glob p) frame 0 d parameters rs).run (.nil,initial) =
      (.error .timeout,(.nil,initial)) := rfl


def emptySeed : Heap E.layout := (Heap.empty.alloc ⟨Aty,empty⟩).1
def emptyInitial : St E := {initial with heap := emptySeed}
def failedAfter : St E := {emptyInitial with heap := (emptySeed.alloc ⟨Aty,empty⟩).1}

theorem bounds_run (p : Roadmap.Pipeline) :
    (evalE (glob p) frame 22 expression).run (caller,emptyInitial) =
      (.error (.revert (panicData .index)),(caller,failedAfter)) := rfl

theorem empty_initial_mem : MemOK E emptySeed.ty (caller,emptyInitial) := by
  have heap : HeapOK (E := E) emptySeed := HeapOK.empty.alloc (.array (fun i => i.elim0))
  have shape : HeapShaped emptySeed := HeapShaped.empty.alloc trivial
  have inner : HeapInner emptySeed := HeapInner.empty.alloc (fun i => i.elim0)
  have ref : (Val.memRef (D := E.layout) (τ := Aty) rfl 0).RefOK E emptySeed.ty := ⟨Aty,rfl,rfl⟩
  exact ⟨⟨⟨heap,HeapTy.Le.refl _⟩,ref,ref,trivial,trivial,trivial⟩,shape,inner⟩

theorem bounds_preserved (p : Roadmap.Pipeline) :
    MemOK E emptySeed.ty (caller,failedAfter) ∧ failedAfter.heap.next = 2 := by
  have actual := eval_memory_call_mem (calls p) frame rfl d ps rs signature body rfl rfl rfl rfl rfl
    body_admitted args (.cons _ (.local _) (.cons _ (.local _) (.cons _ (.local _) .nil))) emptySeed.ty 21
    (caller,emptyInitial) empty_initial_mem
  have observed : (evalE (glob p) frame (21+1) (.call d signature args)).run (caller,emptyInitial) =
      (.error (.revert (panicData .index)),(caller,failedAfter)) := bounds_run p
  rw [observed] at actual
  exact ⟨actual,rfl⟩

def scopedBody : RStmt E [] false .body Γ Γ := .block
  (.stmt (.declVar (.bytes .memory))
    (.stmt (.declInit (τ := Aty) (.newArray (τ := Aty) rfl (.const (Q.ofInt 2)) (by decide +kernel)) (by decide +kernel)) .nil))
def scopeAfter : St E := {initial with heap :=
  ((seed.alloc ⟨.bytes .memory,.bytes []⟩).1.alloc ⟨Aty,fresh⟩).1}

theorem scope_admitted : MemoryStmt (fun _ => False) [] false scopedBody :=
  .block (.stmt (.declVar _) (.stmt (.declInit _ (.base (.newArray rfl _ (.value trivial trivial)))) .nil))

theorem scope_run (p : Roadmap.Pipeline) :
    (execS (glob p) frame 8 0 none scopedBody caller).run (.nil,initial) =
      (.ok (.normal caller),(.nil,scopeAfter)) := rfl

theorem scope_preserved (p : Roadmap.Pipeline) :
    MemOK E seed.ty ((.nil : Locals E.layout []),scopeAfter) ∧
    LocalsOK E scopeAfter.heap.ty caller ∧ scopeAfter.heap.next = 3 := by
  have callerMem : MemOK E seed.ty ((.nil : Locals E.layout []),initial) := relocalize initial_mem .nil trivial
  have actual := (memory_body_at (calls p) 8).stmt frame rfl 0 none scopedBody scope_admitted caller seed.ty
    (.nil,initial) ⟨callerMem,initial_mem.1.2⟩
  rw [scope_run] at actual
  exact ⟨actual.1,actual.2,rfl⟩

#print axioms preserved
#print axioms run
#print axioms expression_run
#print axioms bounds_preserved
#print axioms scope_preserved
end Solidity.Source.Preservation.MemoryBodyControls
