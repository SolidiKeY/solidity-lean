import Solidity.Source.Progress.BoundCatalogue
import Solidity.Source.Progress.ReadyReturns
import Solidity.Lowering.P9.InferenceCuts

/-! A parent argument calls an elaborated bound-parent body through the
catalogue adapter. Frame equations are derived, not supplied; argument,
default and returned allocations are observed separately on inhabited inputs. -/
namespace Solidity.Source.Progress.BoundCatalogueParentControls
open EM Solidity.Lowering.P9

def arrayType : Syn .typeName := .array (.elem .bool) (.some (.lit (.num (.dec 2 0 0))))
def returnSyntax : Syn .expr := .inlineArray (.lit (.bool true)) (.cons (.lit (.bool false)) .nil)
def function : Syn (.part false) := .function (.ident "make")
  (.cons (.param arrayType (some .memory) (some "a")) .nil)
  (some .priv) none .nil false none (.cons (.param arrayType (some .memory) none) .nil)
  (.some (.block
    (.cons (.stmtItem (.simpleStmt (.declVar (.varDecl arrayType (some .memory) "tmp") (.some returnSyntax))))
      (.cons (.stmtItem (.returnStmt (.some (.ident "tmp")))) .nil))))
def unit : Syn .unit := .unit (.cons (.contract false "C" .none .nil (.cons function .nil)) .nil)
def resolution := Source.resolveUnit {pipeline:=.legacy} unit
abbrev E := resolution.env
abbrev Bty : STy := .bytes .memory
abbrev Aty : STy := .array .memory .bool (some 2)
abbrev ps : List STy := [Aty]
def d : Decl := ⟨.function,"make",some "C",false,function⟩
def sourceFrame := (d.frame? E).get (by rfl)
def inferred := (ItemsD.infer (sourceFrame.ctx E d.scope) sourceFrame.locals sourceFrame.body).get (by rfl)
def inferredBody := RBody.ofDerivation sourceFrame inferred.2 []
def bodyFields : RConvArgs E (returnContext ps Aty) [.bool,.bool] :=
  .cons (.bool true) rfl (.cons (.bool false) rfl .nil)
def bodyParent : RExpr E (returnContext ps Aty) Aty := .inlineArray bodyFields rfl
def body : RBody E where
  ps:=ps;rs:=[Aty];inModifier:=false;locals:=returnContext ps Aty;out:=Aty::returnContext ps Aty
  items:=.stmt (.declInit bodyParent rfl) (.stmt (.retVal rfl (.local .here) rfl) .nil)

theorem signature : d.fnSig E = some (ps,[Aty]) := rfl
theorem source_frame : d.frame? E = some sourceFrame := rfl
theorem source_inferred :
    ItemsD.infer (sourceFrame.ctx E d.scope) sourceFrame.locals sourceFrame.body = some inferred := rfl
theorem body_flat : inferredBody = body := rfl
theorem invs : d.modInvs.invList = [] := by
  rw [show d.modInvs = .nil from rfl,Syn.invList]
theorem body_exists : (Source.elabBody E d).isSome = true :=
  InferenceCuts.body_some E d sourceFrame source_frame (by rw [source_inferred];rfl) invs
theorem source_body : (Source.progOf E).body d = some body := by
  have hm : (Source.elabMods E d sourceFrame d.modInvs.invList).map Subtype.val = some [] := by
    rw [invs,Source.elabMods];rfl
  simp only [Source.progOf,Source.elabBody,source_frame,source_inferred]
  cases actual : Source.elabMods E d sourceFrame d.modInvs.invList with
  | none => rw [actual] at hm;cases hm
  | some value =>
    rcases value with ⟨mods,hmods⟩
    simp only [actual,Option.map_some,Option.some.injEq] at hm
    subst mods
    exact congrArg some body_flat
theorem base_arguments : (Source.elabBaseArgs E "C").isSome = true :=
  InferenceCuts.base_some E "C" (by rw [show E.inheritOf "C" = .nil from rfl,Syn.inheritList]) rfl
theorem elaborates : Source.elaborates E = true := by
  change ((((Source.elabBody E d).isSome && true) && true) && ((Source.elabBaseArgs E "C").isSome && true)) = true
  rw [body_exists,base_arguments];rfl
theorem actual_elaboration : (Source.elaborate resolution).isSome = true := by
  simp only [Source.elaborate,elaborates,↓reduceIte,Option.isSome_some]
def globals (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) : Glob E :=
  ⟨Source.progOf E,p,fixed,fun _=>⟨0,by decide⟩,fun _ _=>true,
    fun _=>.answer (.success []),⟨0,by decide⟩⟩
def frame : Fr where
  this := ⟨17,by decide⟩
  sender := ⟨19,by decide⟩
  value := ⟨0,by decide⟩
  static := false
  contract := "C"
theorem local_functions : E.fnIn "C" d.name ps = [d] := rfl
theorem dispatch (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) :
    (globals p fixed).dispatchFn "C" d = d := by
  unfold Glob.dispatchFn
  rw [signature]
  simp only [show E.linearize "C" = some ["C"] from rfl,Option.getD_some]
  change (if true then
    (List.findSome? (fun s=>List.find? (fun d'=>((globals p fixed).prog.body d').isSome)
      (E.fnIn s d.name ps)) ["C"]).getD d else d) = d
  simp only [ite_true,List.findSome?_cons,local_functions,List.find?_cons]
  rw [show (globals p fixed).prog.body d = some body from source_body]
  rfl
theorem checked (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) :
    WholeProgram.check resolution (globals p fixed) "C" [] = true := rfl
theorem declared : d ∈ WholeProgram.functions resolution := by
  change d ∈ [d];exact List.mem_cons_self

theorem shape : FiniteDefault E Aty := .fixed 2 (.ready (.value rfl))
theorem admitted_body {A : Decl → Prop} : BoundParentItems A body.rs body.inModifier body.items :=
  .initialized rfl (.inr rfl)
    (.inline rfl (.cons rfl (.inl rfl) (.value trivial trivial)
      (.cons rfl (.inl rfl) (.value trivial trivial) .nil)))
    (.ready (.stmt (.returnValue rfl rfl (.inr rfl) (.local _)) .nil))

theorem catalogue (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) :
    BoundMemoryCatalogue (fun d=>d ∈ ([] : List Decl)) (globals p fixed) "C" [d] := by
  intro called member
  rcases List.mem_singleton.mp member with rfl
  refine ⟨by decide +kernel,ps,[Aty],ps,body,signature,?_,?_,rfl,?_,admitted_body⟩
  · rw [dispatch];exact signature
  · rw [dispatch];exact source_body
  · intro τ member
    rcases List.mem_singleton.mp member with rfl
    exact shape

abbrev Γ : RCtx := [Bty,.bool]
def fields : RConvArgs E Γ [.bool,.bool] :=
  .cons (.bool true) rfl (.cons (.bool false) rfl .nil)
def parent : RExpr E Γ Aty := .inlineArray fields rfl
def args : RConvArgs E Γ ps := .cons parent rfl .nil
theorem ready_parent {A : Decl → Prop} : AllocationParent A parent :=
  .inline rfl (.cons rfl (.inl rfl) (.value trivial trivial)
    (.cons rfl (.inl rfl) (.value trivial trivial) .nil))
theorem admitted {A : Decl → Prop} : ParentArgs A args :=
  .cons rfl (.inr rfl) (.parent ready_parent) .nil

def seed : Heap E.layout := (Heap.empty.alloc ⟨Bty,.bytes [42,77]⟩).1
def initial : St E :=
  {ex:=⟨⟨fun _=>Account.empty _⟩,Transient.empty,[]⟩,heap:=seed,events:=[],
   logs:=[(⟨17,by decide⟩,[9])],fnLocals:=⟨[.bool],.cons (.bool false) .nil⟩}
def caller : Locals E.layout Γ := .cons (.memRef rfl 0) (.cons (.bool true) .nil)
def argumentData : Data E.layout Aty := inlineData (.cons (.bool true) (.cons (.bool false) .nil))
def argumentReached : St E := {initial with heap:=(seed.alloc ⟨Aty,argumentData⟩).1}
def parameters : Vals E.layout ps := .cons (.memRef rfl 1) .nil
def defaultData : Data E.layout Aty :=
  .array 2 (fun _ h=>by cases h;rfl) (fun _=>.val (.bool false))
def defaulted : St E := {initial with heap:=(argumentReached.heap.alloc ⟨Aty,defaultData⟩).1}
def reached : St E := {initial with heap:=(defaulted.heap.alloc ⟨Aty,argumentData⟩).1}

theorem entry_mem : MemOK E seed.ty (L0 E,initial) := by
  have heap : HeapOK (E:=E) seed := HeapOK.empty.alloc (.bytes [42,77])
  have shaped : HeapShaped seed := HeapShaped.empty.alloc trivial
  have inner : HeapInner seed := HeapInner.empty.alloc trivial
  exact ⟨⟨⟨heap,HeapTy.Le.refl _⟩,trivial⟩,shaped,inner⟩
theorem caller_mem : MemOK E seed.ty (caller,initial) :=
  Preservation.relocalize entry_mem caller ⟨⟨Bty,rfl,rfl⟩,⟨trivial,trivial⟩⟩

theorem checked_expression (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) :
    NS (evalE (globals p fixed) frame 22 (.call d signature args)) ∧
    Hoare (MemOK E seed.ty) (evalE (globals p fixed) frame 22 (.call d signature args))
      (fun v y=>MemOK E seed.ty y ∧ RValOK E y.2.heap.ty v) (fun _ y=>MemOK E seed.ty y) :=
  bound_memory_parent_expr_from_elaborate resolution actual_elaboration (globals p fixed) rfl "C" [] [d]
    (checked p fixed) (catalogue p fixed) frame rfl d signature List.mem_cons_self
    args admitted seed.ty 21

def zeroElements : Fin 2 → Data E.layout .bool :=
  finCons (.val (.bool false)) (finCons (.val (.bool false)) Fin.elim0)
theorem zero_elements : zeroElements = (fun _=>.val (.bool false)) := by
  funext i
  rcases i with ⟨i,h⟩
  cases i with
  | zero => rfl
  | succ i =>
    cases i with
    | zero => rfl
    | succ i => omega
theorem default_run (n : Nat) :
    (zeroVals (E:=E) (Γ:=[]) (n+8) [Aty]).run (L0 E,argumentReached) =
      (.ok (.cons (.memRef rfl 2) .nil),(L0 E,defaulted)) := by
  change ((Except.ok (Vals.cons (Val.memRef (τ:=Aty) rfl 2) .nil) : Except Halt (Vals E.layout [Aty])),
    (L0 E,{initial with heap:=(argumentReached.heap.alloc
      ⟨Aty,.array 2 (fun _ h=>by cases h;rfl) zeroElements⟩).1})) = _
  rw [zero_elements]
  rfl
theorem arguments_run (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) :
    (evalConvArgs (globals p fixed) frame 21 args).run (caller,initial) =
      (.ok parameters,(caller,argumentReached)) := rfl
theorem caller_run (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) :
    (evalE (globals p fixed) frame 22 (.call d signature args)).run (caller,initial) =
      (.ok (.val (.memRef rfl 3)),(caller,reached)) := by
  rw [evalE,Hoare.run_bind,arguments_run]
  dsimp only
  rw [Hoare.run_bind]
  have inner : callInternal (globals p fixed) frame 21 d parameters [Aty] (L0 E,argumentReached) =
      (.ok (.val (.memRef rfl 3)),(L0 E,reached)) := by
    change (callInternal (globals p fixed) frame 21 d parameters [Aty]).run (L0 E,argumentReached) = _
    have hb : (globals p fixed).prog.body d = some body := source_body
    rw [callInternal,show frame.contract = "C" from rfl,dispatch,hb,Hoare.run_bind,default_run 12]
    cases p <;> rfl
  simp only [EM.sub,ExceptT.run,ExceptT.mk,inner]
  rfl
theorem caller_preserved (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) :
    NS (evalE (globals p fixed) frame 22 (.call d signature args)) ∧
    MemOK E seed.ty (caller,reached) ∧
    RValOK E reached.heap.ty (.val (.memRef rfl 3) : RVal E.layout Aty) := by
  have actual := (checked_expression p fixed).2 (caller,initial) caller_mem
  rw [caller_run] at actual
  exact ⟨(checked_expression p fixed).1,actual⟩
theorem heap_and_frame :
    reached.heap.get 0 = seed.get 0 ∧ reached.heap.get 1 = some ⟨Aty,argumentData⟩ ∧
    reached.heap.get 2 = some ⟨Aty,defaultData⟩ ∧
    reached.heap.get 3 = some ⟨Aty,argumentData⟩ ∧ reached.heap.next = 4 ∧
    reached.fnLocals = initial.fnLocals ∧ reached.logs = initial.logs := ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
theorem old_args_refused : ¬ReadyArgs (fun _=>False) args := by
  intro ready
  cases ready with
  | cons _ _ head tail =>
    cases head with
    | value fragment _ => exact fragment
theorem zero_horizon (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) :
    (evalE (globals p fixed) frame 0 (.call d signature args)).run (caller,initial) =
      (.error .timeout,(caller,initial)) := rfl


#print axioms signature
#print axioms source_frame
#print axioms source_inferred
#print axioms body_flat
#print axioms invs
#print axioms body_exists
#print axioms source_body
#print axioms base_arguments
#print axioms elaborates
#print axioms actual_elaboration
#print axioms local_functions
#print axioms dispatch
#print axioms checked
#print axioms declared
#print axioms shape
#print axioms admitted_body
#print axioms catalogue
#print axioms ready_parent
#print axioms admitted
#print axioms entry_mem
#print axioms caller_mem
#print axioms checked_expression
#print axioms zero_elements
#print axioms default_run
#print axioms arguments_run
#print axioms caller_run
#print axioms caller_preserved
#print axioms heap_and_frame
#print axioms old_args_refused
#print axioms zero_horizon
end Solidity.Source.Progress.BoundCatalogueParentControls
