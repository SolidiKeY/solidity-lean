import Solidity.Calculus.ProvesDerive

/-! Kernel-checked decomposition of the original 1024-step walk. Native proposals
only choose candidate empty/none results and callback order; every equation is
checked by the kernel. Each declaration retains the default proof limits.
Residual leaves are refused. This helper changes no source formula or rule. -/
namespace Solidity.Seq
variable {C : Contract} {α : Type}
def memoryReplayLayer (R : RuleSet)
    (leaf : {Γ : Ctx} → Hyps C [] Γ → Fml C Γ → Option (List α))
    (rf : {Γ : Ctx} → Hyps C [] Γ → Fml C Γ → Bool)
    (next : {Γ : Ctx} → Hyps C [] Γ → Nat → Fml C Γ → Nat → Option (List α × Nat))
    {Γ : Ctx} (H : Hyps C [] Γ) (k : Nat) (φ : Fml C Γ) (budget : Nat) : Option (List α × Nat) :=
  Nat.casesOn budget none fun b =>
    Fml.casesOn (motive := fun Γ _ => Hyps C [] Γ → Option (List α × Nat)) φ
      (tt := fun H => cond H.boxOnly (some ([], b)) ((leaf H .tt).map (·, b)))
      (eq := fun t u H => (leaf H (.eq t u)).map (·, b))
      (wellFormed := fun s H => (leaf H (.wellFormed s)).map (·, b))
      (not := fun ψ H => (leaf H (.not ψ)).map (·, b))
      (and := fun ψ χ H => cond (Fml.and ψ χ).modalFree ((leaf H (.and ψ χ)).map (·, b))
        (both (next H k ψ) (next H k χ) b))
      (imp := fun a ψ H => match a.negModal? with
        | some X => match next H k X b with
          | some (ls, b') => cond ls.isEmpty (some ([], b')) (next H k ψ b)
          | none => next H k ψ b
        | none => next (H.pre a) (max k a.maxIdx) ψ b)
      (upd := fun m U ψ H => next (H.upd m U) (max k U.maxIdx) ψ b)
      (modal := fun m P κ ψ H =>
        modal R (fun H k φ b => next H k φ b) rf m H k P κ ψ b)
      (havoc := fun ψ H => (leaf H (.havoc ψ)).map (·, b))
      (all := fun x p ψ H => next (H.all x p) (max k x.idx) ψ b)
      (bind := fun m x t ψ H => next (H.bind m x t) (max k x.idx) ψ b)
      (anon := fun xs ψ H => (leaf H (.anon xs ψ)).map (·, b))
      (allocAll := fun x A ψ H => next (H.allocAll x A) (max k x.idx) ψ b)
      (grow := fun ψ H => (leaf H (.grow ψ)).map (·, b)) H


theorem runK_memoryReplayLayer (R : RuleSet)
    (leaf : {Γ : Ctx} → Hyps C [] Γ → Fml C Γ → Option (List α))
    (rf : {Γ : Ctx} → Hyps C [] Γ → Fml C Γ → Bool) (n : Nat)
    {Γ : Ctx} (H : Hyps C [] Γ) (k : Nat) (φ : Fml C Γ) (b : Nat) :
    runK R leaf rf (n + 1) H k φ b =
      memoryReplayLayer R leaf rf (runK R leaf rf n) H k φ b := by
  cases b with
  | zero => rfl
  | succ b => rw [runK]; rfl
end Solidity.Seq
namespace Solidity.Seq.MemoryReplay
open Lean Meta Elab Tactic Command Term
structure Visit (C : Contract) where
  n : Nat
  Γ : Ctx
  H : Hyps C [] Γ
  k : Nat
  φ : Fml C Γ
  b : Nat
  result : Option (List (SLeaf C) × Nat)
  children : Array Nat
instance {C : Contract} : Inhabited (Visit C) := ⟨⟨0,[],.nil,0,.tt,0,none,#[]⟩⟩
unsafe def gather {C : Contract} (ref : IO.Ref (Array (Visit C))) (R : RuleSet)
    (n : Nat) {Γ : Ctx} (H : Hyps C [] Γ) (k : Nat) (φ : Fml C Γ) (b : Nat) :
    Option (List (SLeaf C) × Nat) := unsafeBaseIO do
  let children ← IO.mkRef #[]
  let next : {Δ : Ctx} → Hyps C [] Δ → Nat → Fml C Δ → Nat → Option (List (SLeaf C) × Nat) :=
    fun {_} h fresh f budget => unsafeBaseIO do
      let result := gather ref R (n-1) h fresh f budget
      children.modify (·.push ((← ref.get).size-1))
      return result
  let result := if n==0 then none else memoryReplayLayer R leafS refuteLanded next H k φ b
  ref.modify (·.push ⟨n,Γ,H,k,φ,b,result,← children.get⟩)
  return result
unsafe def propose {C : Contract} (R : RuleSet) (n : Nat) (φ : Fml C []) : Array (Visit C) := unsafeBaseIO do
  let ref ← IO.mkRef #[]
  let result := gather ref R n .nil 0 φ n
  if result.isNone then return #[]
  return ← ref.get
structure Input where
  n : Nat
  args : Array Expr
  value : Expr
  layer : Option Expr := none
  proof : Option Expr := none
structure Hint where
  n : Nat
  result : Option Nat
  residual : Bool
  children : Array Nat
  deriving Inhabited
structure Job where
  target : Expr
  C : Expr
  R : Expr
  resultTy : Expr
  hints : Array Hint
  inputs : IO.Ref (Array (Option Input))
  pending : List Nat
  assembled : Nat := 0
structure Snapshot where
  target : Expr
  C : Expr
  R : Expr
  resultTy : Expr
  hints : Array Hint
  inputs : Array (Option Input)
  pending : List Nat
  assembled : Nat
initialize snapshots : SimplePersistentEnvExtension Snapshot (Array Snapshot) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun xs x => xs.push x
    addImportedFn := fun xss => xss.foldl (· ++ ·) #[] }
initialize job : IO.Ref (Option Job) ← IO.mkRef none

def checkEnabled : MetaM Unit := do
  if (← getOptions).getBool `debug.skipKernelTC false then throwError "memory replay requires kernel checking"
def defineChecked (type value : Expr) : MetaM Expr := do
  let name ← mkFreshUserName ((← getEnv).mainModule ++ `_memoryLoopState)
  withOptions (Elab.async.set · false) <| addDecl <| Declaration.defnDecl {
    name, levelParams := [], type, value, hints := .abbrev, safety := .safe }
  return Lean.mkConst name

def expected (j : Job) (id : Nat) : MetaM Expr := do
  if id ≥ j.hints.size then throwError "memory replay: invalid visit"
  if j.hints[id]!.residual then throwError "memory replay: residual-leaf proposal is outside this checker"
  match j.hints[id]!.result with
  | none => return mkApp (Lean.mkConst ``Option.none [0]) j.resultTy
  | some b =>
    let lsTy := mkApp (Lean.mkConst ``List [0]) (mkApp (Lean.mkConst ``SLeaf) j.C)
    let nil := mkApp (Lean.mkConst ``List.nil [0]) (mkApp (Lean.mkConst ``SLeaf) j.C)
    let pair := mkAppN (Lean.mkConst ``Prod.mk [0,0]) #[lsTy,Lean.mkConst ``Nat,nil,toExpr b]
    return mkApp2 (Lean.mkConst ``Option.some [0]) j.resultTy pair

def runExpr (j : Job) (n : Nat) (args : Array Expr) : Expr :=
  mkAppN (Lean.mkConst ``runK)
    (#[j.C,mkApp (Lean.mkConst ``SLeaf) j.C,j.R,mkApp (Lean.mkConst ``leafS) j.C,
      mkApp (Lean.mkConst ``refuteLanded) j.C,toExpr n] ++ args)

def assignInput (j : Job) (id n : Nat) (args : Array Expr) : MetaM Unit := do
  if id ≥ j.hints.size || j.hints[id]!.n != n then throwError "memory replay: wrong child depth"
  unless args.size==5 && !(args.any fun e => e.hasFVar || e.hasMVar || e.hasLooseBVars) do
    throwError "memory replay: open child state"
  if ((← j.inputs.get)[id]!).isSome then throwError "memory replay: repeated visit"
  let value ← expected j id
  j.inputs.modify (·.set! id (some ⟨n,args,value,none,none⟩))

partial def layer (j : Job) (id : Nat) (input : Input) (actual next start e hp : Expr)
    (left : List Nat) (hyps : Array Expr) : MetaM Expr := do
  let ew ← ofExceptKernelException (Kernel.whnf (← getEnv) (← getLCtx) e)
  let ew ← Core.transform ew (pre := fun t =>
    return if !t.hasFVar then .done t
      else if t.isHeadBetaTarget then .visit t.headBeta else .continue)
  let call? := ew.find? fun t => t.getAppFn==next && t.getAppNumArgs==5 && !t.hasLooseBVars
  if let some call := call? then
    let child::rest := left | throwError "memory replay: unproposed callback"
    unless child < id do throwError "memory replay: non-postorder child"
    assignInput j child (input.n-1) call.getAppArgs
    let result ← expected j child
    withLocalDeclD `child (← mkEq call result) fun hyp => do
      if ew==call then
        layer j id input actual next start result (← mkEqTrans hp hyp) rest (hyps.push hyp)
      else
        let body ← kabstract ew call (.pos [1])
        let f := mkLambda `result .default (mkApp (Lean.mkConst ``Option [0]) j.resultTy) body
        let optionTy := mkApp (Lean.mkConst ``Option [0]) j.resultTy
        let hr := mkAppN (Lean.mkConst ``congrArg [1,1]) #[optionTy,optionTy,call,result,f,hyp]
        layer j id input actual next start (mkApp f result) (← mkEqTrans hp hr) rest (hyps.push hyp)
  else
    unless left.isEmpty do throwError "memory replay: unreachable proposed callback"
    let params := #[next] ++ hyps
    let type ← mkForallFVars params (← mkEq start input.value)
    let value ← mkLambdaFVars params hp
    Derive.kernelLemma type value

def discover (j : Job) (id : Nat) : MetaM (List Nat) := do
  let some input := (← j.inputs.get)[id]! | throwError "memory replay: undiscovered input"
  let a := input.args
  let Γ ← defineChecked (Lean.mkConst ``Ctx) a[0]!
  let nilCtx := mkApp (Lean.mkConst ``List.nil [0]) (Lean.mkConst ``LTy)
  let H ← defineChecked (mkApp3 (Lean.mkConst ``Hyps) j.C nilCtx Γ) a[1]!
  let k ← defineChecked (Lean.mkConst ``Nat) a[2]!
  let φ ← defineChecked (mkApp2 (Lean.mkConst ``Fml) j.C Γ) a[3]!
  let b ← defineChecked (Lean.mkConst ``Nat) a[4]!
  let input := {input with args := #[Γ,H,k,φ,b]}
  let mut lemma := none
  let children := j.hints[id]!.children.toList
  if input.n==0 then
    unless children.isEmpty do throwError "memory replay: zero-depth callback"
  else
    let actual := mkAppN (Lean.mkConst ``runK)
      #[j.C,mkApp (Lean.mkConst ``SLeaf) j.C,j.R,mkApp (Lean.mkConst ``leafS) j.C,
        mkApp (Lean.mkConst ``refuteLanded) j.C,toExpr (input.n-1)]
    lemma ← withLocalDeclD `next (← inferType actual) fun next => do
      let start := mkAppN (Lean.mkConst ``memoryReplayLayer)
        (#[j.C,mkApp (Lean.mkConst ``SLeaf) j.C,j.R,mkApp (Lean.mkConst ``leafS) j.C,
          mkApp (Lean.mkConst ``refuteLanded) j.C,next] ++ input.args)
      return some (← layer j id input actual next start start (← mkEqRefl start) children #[])
  j.inputs.modify (·.set! id (some {input with layer:=lemma}))
  return children

def assemble (j : Job) (id : Nat) : MetaM Unit := do
  let some input := (← j.inputs.get)[id]! | throwError "memory replay: no checked layer"
  let original := runExpr j input.n input.args
  let value ← if input.n==0 then mkEqRefl input.value else do
    let some lemma := input.layer | throwError "memory replay: missing layer theorem"
    let actual := mkAppN (Lean.mkConst ``runK)
      #[j.C,mkApp (Lean.mkConst ``SLeaf) j.C,j.R,mkApp (Lean.mkConst ``leafS) j.C,
        mkApp (Lean.mkConst ``refuteLanded) j.C,toExpr (input.n-1)]
    let mut children := #[]
    for child in j.hints[id]!.children do
      let some ci := (← j.inputs.get)[child]! | throwError "memory replay: missing child input"
      let some h := ci.proof | throwError "memory replay: missing child proof"
      children := children.push h
    let hLayer := mkAppN lemma (#[actual] ++ children)
    let hUnfold := mkAppN (Lean.mkConst ``runK_memoryReplayLayer)
      (#[j.C,mkApp (Lean.mkConst ``SLeaf) j.C,j.R,mkApp (Lean.mkConst ``leafS) j.C,
        mkApp (Lean.mkConst ``refuteLanded) j.C,toExpr (input.n-1)] ++ input.args)
    mkEqTrans hUnfold hLayer
  let h ← Derive.kernelLemma (← mkEq original input.value) value
  j.inputs.modify (·.set! id (some {input with proof:=some h}))

elab "prepare_memory_replay " t:term : command => liftTermElabM do
  job.set none
  checkEnabled
  let φ ← elabTerm t none
  let_expr Fml C Γ := (← inferType φ) | throwError "memory replay expects typed formula"
  unless (← whnf Γ).isAppOf ``List.nil do throwError "memory replay expects closed context"
  let R := Lean.mkConst ``RuleSet.all
  let nativeC ← unsafe evalExpr Contract (Lean.mkConst ``Contract) C
  let type := mkApp (Lean.mkConst ``Array [0]) (mkApp (Lean.mkConst ``Visit) C)
  let visits ← unsafe evalExpr (Array (Visit nativeC)) type
    (mkAppN (Lean.mkConst ``propose) #[C,R,toExpr (1024:Nat),← Symex.evaluable φ]) (safety:=.unsafe)
  unless !visits.isEmpty do throwError "memory replay proposal refused"
  let lsTy := mkApp (Lean.mkConst ``List [0]) (mkApp (Lean.mkConst ``SLeaf) C)
  let pairTy := mkApp2 (Lean.mkConst ``Prod [0,0]) lsTy (Lean.mkConst ``Nat)
  let hints := visits.map fun v =>
    match v.result with
    | none => (⟨v.n,none,false,v.children⟩ : Hint)
    | some (ls,b) => ⟨v.n,some b,!ls.isEmpty,v.children⟩
  let inputs ← IO.mkRef (Array.replicate visits.size none)
  let j : Job := ⟨φ,C,R,pairTy,hints,inputs,[visits.size-1],0⟩
  let nil := mkApp (Lean.mkConst ``Hyps.nil) C
  let nilCtx := mkApp (Lean.mkConst ``List.nil [0]) (Lean.mkConst ``LTy)
  let H := mkApp nil nilCtx
  assignInput j (visits.size-1) 1024 #[nilCtx,H,toExpr (0:Nat),φ,toExpr (1024:Nat)]
  job.set (some j)
  logInfo m!"proposed {visits.size} typed visits under original1024 limits"

elab "discover_memory_replay" : command => liftTermElabM do
  let savedEnv ← getEnv
  tryCatchRuntimeEx (do
    checkEnabled
    let some j ← job.get | throwError "memory replay: no job"
    let id::pending := j.pending | throwError "memory replay: discovery already finished"
    let children ← discover j id
    job.set (some {j with pending:=children++pending})
    logInfo m!"checked layer {id}"
  ) fun e => do
    setEnv savedEnv
    job.set none
    throw e

elab "assemble_memory_replay" : command => liftTermElabM do
  let savedEnv ← getEnv
  tryCatchRuntimeEx (do
    checkEnabled
    let some j ← job.get | throwError "memory replay: no job"
    unless j.pending.isEmpty do throwError "memory replay: unchecked layers"
    unless j.assembled<j.hints.size do throwError "memory replay: already assembled"
    assemble j j.assembled
    job.set (some {j with assembled:=j.assembled+1})
    logInfo m!"assembled node {j.assembled}"
  ) fun e => do
    setEnv savedEnv
    job.set none
    throw e

elab "save_memory_replay" : command => liftTermElabM do
  let savedEnv ← getEnv
  tryCatchRuntimeEx (do
    checkEnabled
    if (← Core.getMessageLog).hasErrors then throwError "memory replay: cannot save after errors"
    let some j ← job.get | throwError "memory replay: no checkpoint to save"
    let s : Snapshot := ⟨j.target,j.C,j.R,j.resultTy,j.hints,← j.inputs.get,j.pending,j.assembled⟩
    modifyEnv (snapshots.addEntry · s)
    job.set none
    logInfo m!"saved checked replay checkpoint"
  ) fun e => do
    setEnv savedEnv
    job.set none
    throw e

elab "resume_memory_replay " t:term : command => liftTermElabM do
  job.set none
  checkEnabled
  let target ← elabTerm t none
  let some s := (snapshots.getState (← getEnv)).toList.reverse.find? (fun s => s.target == target)
    | throwError "memory replay: no checked checkpoint for this exact typed target"
  let some root := s.inputs[s.hints.size-1]! | throwError "memory replay: checkpoint has no root"
  unless root.n==1024 do throwError "memory replay: wrong checkpoint bounds"
  let inputs ← IO.mkRef s.inputs
  job.set (some ⟨s.target,s.C,s.R,s.resultTy,s.hints,inputs,s.pending,s.assembled⟩)
  logInfo m!"resumed checked replay checkpoint"

elab "finish_memory_replay" : tactic => withMainContext do
  let savedEnv ← getEnv
  tryCatchRuntimeEx (do
    checkEnabled
    let some j ← job.get | throwError "memory replay: no job"
    unless j.pending.isEmpty && j.assembled==j.hints.size do throwError "memory replay: incomplete proof"
    let some input := (← j.inputs.get)[j.hints.size-1]! | throwError "memory replay: no root"
    let some root := input.proof | throwError "memory replay: unchecked root"
    unless input.n==1024 do throwError "memory replay: wrong root bounds"
    let g ← getMainGoal
    let_expr Proves C R Γ₀ Γ H φ := (← instantiateMVars (← g.getType)) | throwUnsupportedSyntax
    unless (← isDefEq C j.C) && (← isDefEq R j.R) && (← whnf Γ₀).isAppOf ``List.nil do
      throwError "memory replay: wrong contract, rules, or outer context"
    let k := mkAppN (Lean.mkConst ``Hyps.maxIdxH) #[C,Γ₀,Γ,H]
    let targetArgs := #[Γ,H,k,φ,toExpr (1024:Nat)]
    for i in [0:5] do
      unless (← ofExceptKernelException (Kernel.isDefEq (← getEnv) (← getLCtx) input.args[i]! targetArgs[i]!)) do
        throwError "memory replay: wrong root state"
    let lsTy := mkApp (Lean.mkConst ``List [0]) (mkApp (Lean.mkConst ``SLeaf) C)
    let proj := mkLambda `pair .default j.resultTy (mkProj ``Prod 0 (.bvar 0))
    let mapper := mkAppN (Lean.mkConst ``Option.map [0,0]) #[j.resultTy,lsTy,proj]
    let h ← mkCongrArg mapper root
    let nil := mkApp (Lean.mkConst ``List.nil [0]) (mkApp (Lean.mkConst ``SLeaf) C)
    let target := mkApp2 (Lean.mkConst ``Option.some [0]) lsTy nil
    let closed ← Derive.kernelLemma (← mkEq (mkApp mapper input.value) target) (← mkEqRefl target)
    let h ← mkEqTrans h closed
    g.assign (mkAppN (Lean.mkConst ``Proves.of_residueWithin)
      #[C,toExpr (1024:Nat),R,Γ,H,φ,nil,h,mkApp2 (Lean.mkConst ``SLeaf.nil) C R])
    setGoals []
  ) fun e => do
    setEnv savedEnv
    job.set none
    throw e

end Solidity.Seq.MemoryReplay
