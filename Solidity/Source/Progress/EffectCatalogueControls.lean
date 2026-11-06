import Solidity.Source.Progress.EffectCatalogue
import Solidity.Lowering.P9.InferenceCuts

/-! Actual elaborated source functions with an emit in the leaf, a require
that calls the leaf, and an assert-failing callee. The complete finite
catalogue is inhabited; observations execute both source pipelines. -/
namespace Solidity.Source.Progress.EffectCatalogueControls
open EM Solidity.Lowering.P9

def retTrue : Syn (.stmt .body) := .returnStmt (.some (.lit (.bool true)))
def fn (name : String) (body : Syn (.list (.item .body))) : Syn (.part true) :=
  .function (.ident name) .nil none none .nil false none
    (.cons (.param (.elem .bool) none none) .nil) (.some (.block body))
def flag : Syn (.part true) := .event "Flag" (.cons (.eventParam (.elem .bool) false none) .nil) false
def leafFunction := fn "leaf" (.cons (.stmtItem (.emit (.ident "Flag")
  (.positional (.cons (.lit (.bool true)) .nil)))) (.cons (.stmtItem retTrue) .nil))
def leafCall : Syn .expr := .call (.ident "leaf") (.positional .nil)
def entryFunction := fn "entry" (.cons (.stmtItem (.simpleStmt (.exprStmt
  (.call (.ident "require") (.positional (.cons leafCall .nil)))))) (.cons (.stmtItem retTrue) .nil))
def failureFunction := fn "failure" (.cons (.stmtItem (.simpleStmt (.exprStmt
  (.call (.ident "assert") (.positional (.cons (.lit (.bool false)) .nil)))))) (.cons (.stmtItem retTrue) .nil))
def unit : Syn .unit := .unit (.cons (.topPart flag) (.cons (.topPart leafFunction)
  (.cons (.topPart entryFunction) (.cons (.topPart failureFunction) .nil))))
def resolution := Source.resolveUnit {pipeline := .legacy} unit
abbrev E := resolution.env
def eventDecl : Decl := ⟨.event,"Flag",none,true,flag⟩
def leafDecl : Decl := ⟨.function,"leaf",none,true,leafFunction⟩
def leafFrame := (leafDecl.frame? E).get (by rfl)
def leafInferred := (ItemsD.infer (leafFrame.ctx E leafDecl.scope) leafFrame.locals leafFrame.body).get (by rfl)
theorem leaf_frame : leafDecl.frame? E = some leafFrame := rfl
theorem leaf_inferred : ItemsD.infer (leafFrame.ctx E leafDecl.scope) leafFrame.locals leafFrame.body = some leafInferred := rfl
theorem leaf_invs : leafDecl.modInvs.invList = [] := by rw [show leafDecl.modInvs = .nil from rfl,Syn.invList]
theorem leaf_exists : (Source.elabBody E leafDecl).isSome = true :=
  InferenceCuts.body_some _ _ _ leaf_frame (by rw [leaf_inferred]; rfl) leaf_invs
def leafBody := RBody.ofDerivation leafFrame leafInferred.2 []
theorem leaf_body : (Source.progOf E).body leafDecl = some leafBody := by
  have hm : (Source.elabMods E leafDecl leafFrame leafDecl.modInvs.invList).map Subtype.val = some [] := by
    rw [leaf_invs,Source.elabMods]; rfl
  simp only [Source.progOf,Source.elabBody,leaf_frame,leaf_inferred]
  cases actual : Source.elabMods E leafDecl leafFrame leafDecl.modInvs.invList with
  | none => rw [actual] at hm; cases hm
  | some v =>
    rcases v with ⟨ms,hms⟩
    simp only [actual,Option.map_some,Option.some.injEq] at hm
    subst ms
    rfl
theorem leaf_signature : leafDecl.fnSig E = some ([],[.bool]) := rfl
def entryDecl : Decl := ⟨.function,"entry",none,true,entryFunction⟩
def entryFrame := (entryDecl.frame? E).get (by rfl)
def entryInferred := (ItemsD.infer (entryFrame.ctx E entryDecl.scope) entryFrame.locals entryFrame.body).get (by rfl)
theorem entry_frame : entryDecl.frame? E = some entryFrame := rfl
theorem entry_inferred : ItemsD.infer (entryFrame.ctx E entryDecl.scope) entryFrame.locals entryFrame.body = some entryInferred := rfl
theorem entry_invs : entryDecl.modInvs.invList = [] := by rw [show entryDecl.modInvs = .nil from rfl,Syn.invList]
theorem entry_exists : (Source.elabBody E entryDecl).isSome = true :=
  InferenceCuts.body_some _ _ _ entry_frame (by rw [entry_inferred]; rfl) entry_invs
def entryBody := RBody.ofDerivation entryFrame entryInferred.2 []
theorem entry_body : (Source.progOf E).body entryDecl = some entryBody := by
  have hm : (Source.elabMods E entryDecl entryFrame entryDecl.modInvs.invList).map Subtype.val = some [] := by
    rw [entry_invs,Source.elabMods]; rfl
  simp only [Source.progOf,Source.elabBody,entry_frame,entry_inferred]
  cases actual : Source.elabMods E entryDecl entryFrame entryDecl.modInvs.invList with
  | none => rw [actual] at hm; cases hm
  | some v =>
    rcases v with ⟨ms,hms⟩
    simp only [actual,Option.map_some,Option.some.injEq] at hm
    subst ms
    rfl
theorem entry_signature : entryDecl.fnSig E = some ([],[.bool]) := rfl
def failureDecl : Decl := ⟨.function,"failure",none,true,failureFunction⟩
def failureFrame := (failureDecl.frame? E).get (by rfl)
def failureInferred := (ItemsD.infer (failureFrame.ctx E failureDecl.scope) failureFrame.locals failureFrame.body).get (by rfl)
theorem failure_frame : failureDecl.frame? E = some failureFrame := rfl
theorem failure_inferred : ItemsD.infer (failureFrame.ctx E failureDecl.scope) failureFrame.locals failureFrame.body = some failureInferred := rfl
theorem failure_invs : failureDecl.modInvs.invList = [] := by rw [show failureDecl.modInvs = .nil from rfl,Syn.invList]
theorem failure_exists : (Source.elabBody E failureDecl).isSome = true :=
  InferenceCuts.body_some _ _ _ failure_frame (by rw [failure_inferred]; rfl) failure_invs
def failureBody := RBody.ofDerivation failureFrame failureInferred.2 []
theorem failure_body : (Source.progOf E).body failureDecl = some failureBody := by
  have hm : (Source.elabMods E failureDecl failureFrame failureDecl.modInvs.invList).map Subtype.val = some [] := by
    rw [failure_invs,Source.elabMods]; rfl
  simp only [Source.progOf,Source.elabBody,failure_frame,failure_inferred]
  cases actual : Source.elabMods E failureDecl failureFrame failureDecl.modInvs.invList with
  | none => rw [actual] at hm; cases hm
  | some v =>
    rcases v with ⟨ms,hms⟩
    simp only [actual,Option.map_some,Option.some.injEq] at hm
    subst ms
    rfl
theorem failure_signature : failureDecl.fnSig E = some ([],[.bool]) := rfl

theorem elaborates : Source.elaborates E = true := by
  change (((((true && ((Source.elabBody E leafDecl).isSome &&
    ((Source.elabBody E entryDecl).isSome && ((Source.elabBody E failureDecl).isSome && true))))
    && true) && true))) = true
  rw [leaf_exists,entry_exists,failure_exists]
  rfl

theorem actual_elaboration : (Source.elaborate resolution).isSome = true := by
  simp only [Source.elaborate,elaborates,↓reduceIte,Option.isSome_some]

def glob (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) : Glob E :=
  ⟨Source.progOf E,p,fixed,fun _ => ⟨0,by decide⟩,fun _ _ => true,
    fun _ => .answer (.success []),⟨0,by decide⟩⟩
def frame : Fr where
  this := ⟨17,by decide⟩
  sender := ⟨23,by decide⟩
  value := ⟨0,by decide⟩
  static := false
  contract := "Effects"

def flatLeaf : RBody E where
  ps := []; rs := [.bool]; inModifier := false; locals := [.bool]; out := [.bool]
  items := .stmt (.emit eventDecl rfl (.cons (.bool true) rfl .nil))
    (.stmt (.retVal rfl (.bool true) rfl) .nil)
def flatEntry : RBody E where
  ps := []; rs := [.bool]; inModifier := false; locals := [.bool]; out := [.bool]
  items := .stmt (.expr (.builtin .require (.cons (.call leafDecl leaf_signature .nil) .nil) rfl))
    (.stmt (.retVal rfl (.bool true) rfl) .nil)
def flatFailure : RBody E where
  ps := []; rs := [.bool]; inModifier := false; locals := [.bool]; out := [.bool]
  items := .stmt (.expr (.builtin .assert (.cons (.bool false) .nil) rfl))
    (.stmt (.retVal rfl (.bool true) rfl) .nil)
theorem leaf_flat : leafBody = flatLeaf := rfl
theorem entry_flat : entryBody = flatEntry := rfl
theorem failure_flat : failureBody = flatFailure := rfl
theorem leaf_dispatch (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) :
    (glob p fixed).dispatchFn "Effects" leafDecl = leafDecl := by
  unfold Glob.dispatchFn
  rw [leaf_signature]
  rfl
theorem entry_dispatch (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) :
    (glob p fixed).dispatchFn "Effects" entryDecl = entryDecl := by
  unfold Glob.dispatchFn
  rw [entry_signature]
  rfl
theorem failure_dispatch (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) :
    (glob p fixed).dispatchFn "Effects" failureDecl = failureDecl := by
  unfold Glob.dispatchFn
  rw [failure_signature]
  rfl

theorem leaf_fragment : EffectItems (fun d => d ∈ ([] : List Decl)) flatLeaf.items :=
  .emit rfl ⟨trivial,rfl,.inl rfl,trivial⟩ ⟨trivial,trivial⟩
    (.value ⟨⟨trivial,rfl,.inl rfl⟩,trivial⟩ ⟨trivial,trivial⟩)
theorem failure_fragment : EffectItems (fun d => d ∈ [leafDecl]) flatFailure.items :=
  .builtin (.assert _ (.cons (.checked _ trivial trivial) .nil))
    (.value ⟨⟨trivial,rfl,.inl rfl⟩,trivial⟩ ⟨trivial,trivial⟩)
theorem entry_fragment : EffectItems (fun d => d ∈ [failureDecl,leafDecl]) flatEntry.items :=
  .builtin (.require _ (.cons (.checked _ ⟨List.mem_cons_of_mem _ (List.mem_singleton.mpr rfl),trivial⟩ trivial) .nil))
    (.value ⟨⟨trivial,rfl,.inl rfl⟩,trivial⟩ ⟨trivial,trivial⟩)

def declarations : List Decl := [entryDecl,failureDecl,leafDecl]

theorem certificate (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) :
    EffectCatalogue (glob p fixed) "Effects" declarations := by
  have leaf : EffectCatalogue (glob p fixed) "Effects" [leafDecl] := by
    refine .cons (targetPs := []) (b := flatLeaf) .nil (by decide +kernel) leaf_signature ?_ ?_ rfl ?_ ?_
    · rw [leaf_dispatch]; exact leaf_signature
    · rw [leaf_dispatch]; exact leaf_body.trans (congrArg some leaf_flat)
    · intro t ht; simp only [List.mem_singleton] at ht; subst t; rfl
    · exact leaf_fragment
  have failure : EffectCatalogue (glob p fixed) "Effects" [failureDecl,leafDecl] := by
    refine .cons (targetPs := []) (b := flatFailure) leaf (by decide +kernel) failure_signature ?_ ?_ rfl ?_ ?_
    · rw [failure_dispatch]; exact failure_signature
    · rw [failure_dispatch]; exact failure_body.trans (congrArg some failure_flat)
    · intro t ht; simp only [List.mem_singleton] at ht; subst t; rfl
    · exact failure_fragment
  refine .cons (targetPs := []) (b := flatEntry) failure (by decide +kernel) entry_signature ?_ ?_ rfl ?_ ?_
  · rw [entry_dispatch]; exact entry_signature
  · rw [entry_dispatch]; exact entry_body.trans (congrArg some entry_flat)
  · intro t ht; simp only [List.mem_singleton] at ht; subst t; rfl
  · exact entry_fragment

theorem coverage : (WholeProgram.functions resolution).all (fun d => decide (d ∈ declarations)) = true := by decide +kernel

theorem derived_progress (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) (n : Nat) :
    NS (callInternal (glob p fixed) frame n entryDecl .nil [.bool]) :=
  checked_effect_call resolution actual_elaboration (glob p fixed) rfl rfl "Effects"
    declarations (certificate p fixed) coverage frame rfl n entryDecl entry_signature (by decide +kernel) .nil


/-- Exact body sharing for reduction only: proved equal to the actual program. -/
def replayBody (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) (d : Decl) : Option (RBody E) :=
  if d = leafDecl then some flatLeaf
  else if d = entryDecl then some flatEntry
  else if d = failureDecl then some flatFailure
  else (glob p fixed).prog.body d

def replayGlob (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) : Glob E :=
  {glob p fixed with prog := {(glob p fixed).prog with body := replayBody p fixed}}

theorem replay_eq (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) : replayGlob p fixed = glob p fixed := by
  have bodyEq : replayBody p fixed = (glob p fixed).prog.body := by
    funext d
    unfold replayBody
    split
    next h => subst d; exact (leaf_body.trans (congrArg some leaf_flat)).symm
    next h =>
      split
      next h => subst d; exact (entry_body.trans (congrArg some entry_flat)).symm
      next h =>
        split
        next h => subst d; exact (failure_body.trans (congrArg some failure_flat)).symm
        next h => rfl
  unfold replayGlob
  rw [bodyEq]

def initial : St E where
  ex := ⟨⟨fun _ => Account.empty _⟩,Transient.empty,[]⟩
  heap := (Heap.empty.alloc ⟨.bytes .memory,.bytes [42,77]⟩).1
  events := []
  logs := [(⟨31,by decide⟩,[0xa1])]
  fnLocals := ⟨[.bool],.cons (.bool false) .nil⟩
def emitted (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) : St E :=
  {initial with logs := (frame.this,(glob p fixed).selector (sigOf E.layout "Flag" [.bool]) ++
    wordBytes ⟨1,by decide⟩) :: initial.logs}

theorem source_success (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) :
    (callInternal (glob p fixed) frame 16 entryDecl .nil [.bool]).run (.nil,initial) =
      (.ok (.val (.bool true)),(.nil,emitted p fixed)) := by
  rw [← replay_eq p fixed]
  cases p <;> rfl

theorem source_static (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) :
    (callInternal (glob p fixed) {frame with static := true} 16 entryDecl .nil [.bool]).run (.nil,initial) =
      (.error (.revert []),(.nil,initial)) := by
  rw [← replay_eq p fixed]
  cases p <;> rfl

theorem source_assert (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) :
    (callInternal (glob p fixed) frame 16 failureDecl .nil [.bool]).run (.nil,initial) =
      (.error (.revert (panicData .assert)),(.nil,initial)) := by
  rw [← replay_eq p fixed]
  cases p <;> rfl

def caller : Locals E.layout [.bytes .memory,.bool] := .cons (.memRef rfl 0) (.cons (.bool false) .nil)
def expression : RExpr E [.bytes .memory,.bool] .bool := .call entryDecl entry_signature .nil

theorem source_expression (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) :
    (evalE (glob p fixed) frame 18 expression).run (caller,initial) =
      (.ok (.val (.bool true)),(caller,emitted p fixed)) := by
  rw [← replay_eq p fixed]
  cases p <;> rfl

theorem incomplete_coverage :
    (WholeProgram.functions resolution).all (fun d => decide (d ∈ [leafDecl])) = false := by decide +kernel

theorem old_checker_refuses (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) :
    WholeProgram.checkFunctions resolution (glob p fixed) "Effects" = false := by
  rw [← replay_eq p fixed]
  rfl

theorem timeout_retained (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) :
    (callInternal (glob p fixed) frame 0 entryDecl .nil [.bool]).run (.nil,initial) =
      (.error .timeout,(.nil,initial)) := rfl

theorem success_not_false (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) :
    (callInternal (glob p fixed) frame 16 entryDecl .nil [.bool]).run (.nil,initial) ≠
      (.ok (.val (.bool false)),(.nil,emitted p fixed)) := by
  rw [source_success]
  intro wrong
  cases wrong

#print axioms actual_elaboration
#print axioms certificate
#print axioms derived_progress
#print axioms source_success
#print axioms source_assert
#print axioms source_static
#print axioms source_expression
end Solidity.Source.Progress.EffectCatalogueControls
