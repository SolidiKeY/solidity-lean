import Solidity.Source.Progress.ForwardingReturns
import Solidity.Source.Progress.ReadyReturnControls
import Solidity.Lowering.P9.InferenceCuts
import Solidity.Roadmap.Controls

/-! A real source relay with primitive arguments and a memory return. Its body
calls a ready allocating function, so body-level forwarding is exercised without
function-value reference-argument elaboration. Both evaluator pipelines retain
the actual caller and reached heap on success and allocation failure. -/
namespace Solidity.Source.Progress.ForwardingControls
open EM Solidity.Lowering.P9
open ReadyFreshReturnControls (uintType arrayType)

def leafFunction := ReadyFreshReturnControls.function
def relayFunction : Syn (.part true) := .function (.ident "relay")
  (.cons (.param uintType none (some "n")) .nil) none none .nil false none
  (.cons (.param arrayType (some .memory) none) .nil)
  (.some (.block (.cons (.stmtItem (.returnStmt (.some
    (.call (.ident "fresh") (.positional (.cons (.ident "n") .nil)))))) .nil)))
def unit : Syn .unit := .unit (.cons (.topPart leafFunction) (.cons (.topPart relayFunction) .nil))
def resolution := Source.resolveUnit {pipeline := .legacy} unit
abbrev E := resolution.env
abbrev U : STy := .int .u256
abbrev Aty : STy := .array .memory U none
def leafDecl : Decl := ⟨.function,"fresh",none,true,leafFunction⟩
def relayDecl : Decl := ⟨.function,"relay",none,true,relayFunction⟩
def leafFrame := (leafDecl.frame? E).get (by rfl)
def leafInferred := (ItemsD.infer (leafFrame.ctx E leafDecl.scope) leafFrame.locals leafFrame.body).get (by rfl)
def leafBody := RBody.ofDerivation leafFrame leafInferred.2 []
def relayFrame := (relayDecl.frame? E).get (by rfl)
def relayInferred := (ItemsD.infer (relayFrame.ctx E relayDecl.scope) relayFrame.locals relayFrame.body).get (by rfl)
def relayBody := RBody.ofDerivation relayFrame relayInferred.2 []

theorem leaf_frame : leafDecl.frame? E = some leafFrame := rfl
theorem leaf_inferred : ItemsD.infer (leafFrame.ctx E leafDecl.scope) leafFrame.locals leafFrame.body = some leafInferred := rfl
theorem leaf_invs : leafDecl.modInvs.invList = [] := by rw [show leafDecl.modInvs = .nil from rfl,Syn.invList]
theorem leaf_exists : (Source.elabBody E leafDecl).isSome = true :=
  InferenceCuts.body_some _ _ _ leaf_frame (by rw [leaf_inferred]; rfl) leaf_invs

theorem relay_frame : relayDecl.frame? E = some relayFrame := rfl
theorem relay_inferred : ItemsD.infer (relayFrame.ctx E relayDecl.scope) relayFrame.locals relayFrame.body = some relayInferred := rfl
theorem relay_invs : relayDecl.modInvs.invList = [] := by rw [show relayDecl.modInvs = .nil from rfl,Syn.invList]
theorem relay_exists : (Source.elabBody E relayDecl).isSome = true :=
  InferenceCuts.body_some _ _ _ relay_frame (by rw [relay_inferred]; rfl) relay_invs

theorem leaf_body : (Source.progOf E).body leafDecl = some leafBody := by
  have hm : (Source.elabMods E leafDecl leafFrame leafDecl.modInvs.invList).map Subtype.val = some [] := by
    rw [leaf_invs,Source.elabMods]; rfl
  simp only [Source.progOf,Source.elabBody,leaf_frame,leaf_inferred]
  cases actual : Source.elabMods E leafDecl leafFrame leafDecl.modInvs.invList with
  | none => rw [actual] at hm; cases hm
  | some value =>
    rcases value with ⟨ms,hms⟩
    simp only [actual,Option.map_some,Option.some.injEq] at hm
    subst ms
    rfl

theorem relay_body : (Source.progOf E).body relayDecl = some relayBody := by
  have hm : (Source.elabMods E relayDecl relayFrame relayDecl.modInvs.invList).map Subtype.val = some [] := by
    rw [relay_invs,Source.elabMods]; rfl
  simp only [Source.progOf,Source.elabBody,relay_frame,relay_inferred]
  cases actual : Source.elabMods E relayDecl relayFrame relayDecl.modInvs.invList with
  | none => rw [actual] at hm; cases hm
  | some value =>
    rcases value with ⟨ms,hms⟩
    simp only [actual,Option.map_some,Option.some.injEq] at hm
    subst ms
    rfl

theorem leaf_signature : leafDecl.fnSig E = some ([U],[Aty]) := rfl
theorem relay_signature : relayDecl.fnSig E = some ([U],[Aty]) := rfl

def same : Aty.implicit E.isBase E.mapFree Aty = true := by decide +kernel
def leafExpr : RExpr E (returnContext [U] Aty) Aty := .newArray rfl (.local (.there .here)) rfl
def relayExpr : RExpr E (returnContext [U] Aty) Aty :=
  .call leafDecl leaf_signature (.cons (.local (.there .here)) (by decide +kernel) .nil)
def flatLeaf := singleReturningBody [U] Aty leafExpr same
def flatRelay := singleReturningBody [U] Aty relayExpr same
theorem leaf_flat : leafBody = flatLeaf := rfl
theorem relay_flat : relayBody = flatRelay := rfl

theorem elaborates : Source.elaborates E = true := by
  change (((((true && ((Source.elabBody E leafDecl).isSome &&
    ((Source.elabBody E relayDecl).isSome && true))) && true) && true))) = true
  rw [leaf_exists,relay_exists]
  rfl
theorem actual_elaboration : (Source.elaborate resolution).isSome = true := by
  simp only [Source.elaborate,elaborates,↓reduceIte,Option.isSome_some]

def glob (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) : Glob E :=
  ⟨Source.progOf E,p,fixed,fun _ => ⟨0,by decide⟩,fun _ _ => true,
    fun _ => .answer (.success []),⟨0,by decide⟩⟩
def frame : Fr where
  this := ⟨17,by decide⟩
  sender := ⟨19,by decide⟩
  value := ⟨0,by decide⟩
  static := false
  contract := "Memory"

theorem leaf_dispatch (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) :
    (glob p fixed).dispatchFn "Memory" leafDecl = leafDecl := by
  unfold Glob.dispatchFn
  rw [leaf_signature]
  rfl
theorem relay_dispatch (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) :
    (glob p fixed).dispatchFn "Memory" relayDecl = relayDecl := by
  unfold Glob.dispatchFn
  rw [relay_signature]
  rfl

theorem value_check (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) :
    WholeProgram.check resolution (glob p fixed) "Memory" [] = true := rfl
theorem leaf_catalogue (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) :
    ReadyMemoryCatalogue (fun d => d ∈ ([] : List Decl)) (glob p fixed) "Memory" [leafDecl] := by
  intro called member
  rcases List.mem_singleton.mp member with rfl
  refine ⟨by decide +kernel,[U],[Aty],[U],flatLeaf,leaf_signature,?_,?_,rfl,?_,?_⟩
  · rw [leaf_dispatch]; exact leaf_signature
  · rw [leaf_dispatch]; exact leaf_body.trans (congrArg some leaf_flat)
  · intro τ member
    rcases List.mem_singleton.mp member with rfl
    exact .memory (.array _)
  · exact .stmt (.returnValue rfl same (.inr rfl) (.newArray (.array U rfl rfl) rfl (.local _))) .nil

theorem relay_ready :
    ComposedExpr (fun d => d ∈ ([] : List Decl)) (fun d => d ∈ [leafDecl]) relayExpr :=
  .call leaf_signature (by decide +kernel) (.cons _ (.inl rfl) (.base (.local _)) .nil)
theorem distinct : relayDecl ∉ [leafDecl] := by decide +kernel

theorem relay_checked (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed)
    (vs : Vals E.layout [U]) (H : HeapTy) (n : Nat) :
    NS (callInternal (glob p fixed) frame n relayDecl vs [Aty]) ∧
    Hoare (fun y => MemOK E H y ∧ RValsOK E y.2.heap.ty vs.toR)
      (callInternal (glob p fixed) frame n relayDecl vs [Aty])
      (fun v y => MemOK E H y ∧ RValOK E y.2.heap.ty v) (fun _ y => MemOK E H y) :=
  forwarding_from_elaborate resolution actual_elaboration (glob p fixed) rfl "Memory" [] [leafDecl]
    (value_check p fixed) (leaf_catalogue p fixed) frame rfl [U] Aty
    ⟨relayDecl,by decide +kernel,relay_signature⟩ relayExpr same (.inr rfl) relay_ready (.memory (.array _))
    (by rw [show frame.contract = "Memory" from rfl,relay_dispatch]; exact relay_body.trans (congrArg some relay_flat))
    vs H n

def original : Data E.layout Aty := .array 1 (fun _ h => nomatch h) (fun _ => .val (.int 7 (by decide)))
def empty : Data E.layout Aty := .array 0 (fun _ h => nomatch h) (fun i => i.elim0)
def fresh : Data E.layout Aty := .array 2 (fun _ h => nomatch h) (fun _ => .val (.int 0 (by decide)))
def seed : Heap E.layout := (Heap.empty.alloc ⟨Aty,original⟩).1
def initial : St E where
  ex := ⟨⟨fun _ => Account.empty _⟩,Transient.empty,[]⟩
  heap := seed
  events := []
  logs := [(⟨17,by decide⟩,[9])]
  fnLocals := ⟨[.bool],.cons (.bool true) .nil⟩
def stopped : St E := {initial with heap := ((seed.alloc ⟨Aty,empty⟩).1.alloc ⟨Aty,empty⟩).1}
def after : St E := {initial with heap := (stopped.heap.alloc ⟨Aty,fresh⟩).1}
def arguments : Vals E.layout [U] := .cons (.int 2 (by decide)) .nil
def huge : Vals E.layout [U] := .cons (.int (2^64) (by decide)) .nil

theorem initial_mem : MemOK E seed.ty ((.nil : Locals E.layout []),initial) := by
  have heap : HeapOK (E := E) seed := HeapOK.empty.alloc (.array (fun _ => .val trivial))
  have shape : HeapShaped seed := HeapShaped.empty.alloc trivial
  have inner : HeapInner seed := HeapInner.empty.alloc (fun _ => ⟨_,rfl⟩)
  exact ⟨⟨⟨heap,HeapTy.Le.refl _⟩,trivial⟩,shape,inner⟩

def cachedGlob (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) : Glob E :=
  {glob p fixed with prog := {(glob p fixed).prog with body := fun called => if called = leafDecl then some flatLeaf else if called = relayDecl then some flatRelay else (glob p fixed).prog.body called}}

theorem cachedGlob_eq (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) : cachedGlob p fixed = glob p fixed := by
  have leaf : (glob p fixed).prog.body leafDecl = some flatLeaf := leaf_body.trans (congrArg some leaf_flat)
  have relay : (glob p fixed).prog.body relayDecl = some flatRelay := relay_body.trans (congrArg some relay_flat)
  have bodies : (fun called => if called = leafDecl then some flatLeaf else if called = relayDecl then some flatRelay
      else (glob p fixed).prog.body called) = (glob p fixed).prog.body := by
    funext called
    split
    next same => subst called; exact leaf.symm
    next different =>
      split
      next same => subst called; exact relay.symm
      next different => rfl
  exact congrArg (fun body => {glob p fixed with prog := {(glob p fixed).prog with body := body}}) bodies

theorem success_run (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) :
    (callInternal (glob p fixed) frame 20 relayDecl arguments [Aty]).run (.nil,initial) =
      (.ok (.val (.memRef rfl 3)),(.nil,after)) := by
  rw [←cachedGlob_eq p fixed]
  cases p <;> rfl

theorem huge_normalized : huge = (.cons (.int 18446744073709551616 (by decide)) .nil : Vals E.layout [U]) := rfl

theorem panic_run (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) :
    (callInternal (glob p fixed) frame 20 relayDecl huge [Aty]).run (.nil,initial) =
      (.error (.revert (panicData .alloc)),(.nil,stopped)) := by
  rw [huge_normalized,←cachedGlob_eq p fixed]
  cases p <;> rfl

theorem inhabited (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) :
    NS (callInternal (glob p fixed) frame 20 relayDecl arguments [Aty]) ∧
    MemOK E seed.ty ((.nil : Locals E.layout []),after) ∧
    RValOK E after.heap.ty (.val (.memRef rfl 3) : RVal E.layout Aty) := by
  have joint := relay_checked p fixed arguments seed.ty 20
  have actual := joint.2 (.nil,initial) ⟨initial_mem,trivial,trivial⟩
  rw [success_run] at actual
  exact ⟨joint.1,actual⟩

theorem reverted_mem (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) :
    NS (callInternal (glob p fixed) frame 20 relayDecl huge [Aty]) ∧
    MemOK E seed.ty ((.nil : Locals E.layout []),stopped) := by
  have joint := relay_checked p fixed huge seed.ty 20
  have actual := joint.2 (.nil,initial) ⟨initial_mem,trivial,trivial⟩
  rw [panic_run] at actual
  exact ⟨joint.1,actual⟩

theorem calls (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) :
    ReadyMemoryCalls (glob p fixed) "Memory" [relayDecl,leafDecl] :=
  extend_forwarding_calls
    (WholeProgram.from_elaborate resolution actual_elaboration (glob p fixed) rfl "Memory" [] (value_check p fixed))
    (ready_memory_from_elaborate resolution actual_elaboration (glob p fixed) rfl "Memory" [] [leafDecl]
      (value_check p fixed) (leaf_catalogue p fixed))
    relayDecl [U] Aty relay_signature relayExpr same (.inr rfl) relay_ready (.memory (.array _))
    (by rw [relay_dispatch]; exact relay_body.trans (congrArg some relay_flat))

def caller : Locals E.layout [U,Aty] := .cons (.int 2 (by decide)) (.cons (.memRef rfl 0) .nil)
def callArgs : RConvArgs E [U,Aty] [U] := .cons (.local .here) (by decide +kernel) .nil
def expression : RExpr E [U,Aty] Aty := .call relayDecl relay_signature callArgs

theorem caller_mem : MemOK E seed.ty (caller,initial) :=
  Preservation.relocalize initial_mem caller ⟨trivial,⟨Aty,rfl,rfl⟩,trivial⟩

theorem expression_ready :
    ComposedExpr (fun d => d ∈ ([] : List Decl)) (fun d => d ∈ [relayDecl,leafDecl]) expression :=
  .call relay_signature (by decide +kernel) (.cons _ (.inl rfl) (.base (.local _)) .nil)

theorem expression_run (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) :
    (evalE (glob p fixed) frame 20 expression).run (caller,initial) =
      (.ok (.val (.memRef rfl 3)),(caller,after)) := by
  rw [←cachedGlob_eq p fixed]
  cases p <;> rfl

theorem caller_restored (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) :
    NS (evalE (glob p fixed) frame 20 expression) ∧
    MemOK E seed.ty (caller,after) ∧ RValOK E after.heap.ty (.val (.memRef rfl 3) : RVal E.layout Aty) := by
  have admitted := composition_at
    (WholeProgram.from_elaborate resolution actual_elaboration (glob p fixed) rfl "Memory" [] (value_check p fixed))
    (calls p fixed) 20
  have joint := admitted.expr frame rfl expression expression_ready seed.ty
  have actual := joint.2 (caller,initial) caller_mem
  rw [expression_run] at actual
  exact ⟨joint.1,actual⟩

def hugeCaller : Locals E.layout [U,Aty] :=
  .cons (.int (2^64) (by decide)) (.cons (.memRef rfl 0) .nil)
theorem huge_caller_mem : MemOK E seed.ty (hugeCaller,initial) :=
  Preservation.relocalize initial_mem hugeCaller ⟨trivial,⟨Aty,rfl,rfl⟩,trivial⟩
theorem huge_caller_normalized : hugeCaller =
    (.cons (.int 18446744073709551616 (by decide)) (.cons (.memRef rfl 0) .nil) : Locals E.layout [U,Aty]) := rfl

theorem caller_panic_run (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) :
    (evalE (glob p fixed) frame 20 expression).run (hugeCaller,initial) =
      (.error (.revert (panicData .alloc)),(hugeCaller,stopped)) := by
  rw [huge_caller_normalized,←cachedGlob_eq p fixed]
  cases p <;> rfl

theorem caller_panic_preserved (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) :
    MemOK E seed.ty (hugeCaller,stopped) := by
  have admitted := composition_at
    (WholeProgram.from_elaborate resolution actual_elaboration (glob p fixed) rfl "Memory" [] (value_check p fixed))
    (calls p fixed) 20
  have actual := (admitted.expr frame rfl expression expression_ready seed.ty).2 (hugeCaller,initial) huge_caller_mem
  rw [caller_panic_run] at actual
  exact actual

theorem wrong_signature_refused : relayDecl.fnSig E ≠ some ([],[Aty]) := by decide +kernel

#print axioms caller_panic_run
#print axioms caller_panic_preserved
#print axioms wrong_signature_refused

#print axioms calls
#print axioms expression_run
#print axioms caller_restored

#print axioms actual_elaboration
#print axioms relay_checked
#print axioms success_run
#print axioms panic_run
#print axioms inhabited
#print axioms reverted_mem
end Solidity.Source.Progress.ForwardingControls
