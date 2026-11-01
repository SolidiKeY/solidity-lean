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


-- Shared kernel equations keep accumulated hypotheses opaque at deterministic nodes.
section
variable (R : RuleSet)
  (leaf : {Γ : Ctx} → Hyps C [] Γ → Fml C Γ → Option (List α))
  (rf : {Γ : Ctx} → Hyps C [] Γ → Fml C Γ → Bool)
  (next : {Γ : Ctx} → Hyps C [] Γ → Nat → Fml C Γ → Nat → Option (List α × Nat))
theorem memoryReplayUpd {Γ Δ : Ctx} (H : Hyps C [] Γ) (k : Nat)
    (m : Modality) (U : Upd C Γ Δ) (φ : Fml C Δ) (b : Nat) (r : Option (List α × Nat))
    (h : next (H.upd m U) (max k U.maxIdx) φ b = r) :
    memoryReplayLayer R leaf rf next H k (.upd m U φ) (b+1) = r := h
theorem memoryReplayAll {Γ : Ctx} (H : Hyps C [] Γ) (k : Nat)
    (x : Var) (p : PrimTy) (φ : Fml C (.val p :: Γ)) (b : Nat) (r : Option (List α × Nat))
    (h : next (H.all x p) (max k x.idx) φ b = r) :
    memoryReplayLayer R leaf rf next H k (.all x p φ) (b+1) = r := h
theorem memoryReplayBind {Γ : Ctx} (H : Hyps C [] Γ) (k : Nat)
    (m : Modality) (x : Var) (t : LTy) (φ : Fml C (t :: Γ)) (b : Nat) (r : Option (List α × Nat))
    (h : next (H.bind m x t) (max k x.idx) φ b = r) :
    memoryReplayLayer R leaf rf next H k (.bind m x t φ) (b+1) = r := h
theorem memoryReplayAllocAll {Γ : Ctx} (H : Hyps C [] Γ) (k : Nat)
    (x : Var) (A : RefTy) (φ : Fml C (.mem A :: Γ)) (b : Nat) (r : Option (List α × Nat))
    (h : next (H.allocAll x A) (max k x.idx) φ b = r) :
    memoryReplayLayer R leaf rf next H k (.allocAll x A φ) (b+1) = r := h

theorem memoryReplayLayer_congr {Γ : Ctx} (H H' : Hyps C [] Γ) (k k' : Nat)
    (φ φ' : Fml C Γ) (b b' : Nat) (hH : H=H') (hk : k=k') (hφ : φ=φ') (hb : b=b') :
    memoryReplayLayer R leaf rf next H k φ b = memoryReplayLayer R leaf rf next H' k' φ' b' := by
  cases hH; cases hk; cases hφ; cases hb; rfl

theorem memoryReplayModalConsAt {Γ Δ Ξ Ω : Ctx} (H : Hyps C [] Γ) (k : Nat)
    (m : Modality) (s : Stmt C Γ Δ) (ω : Prog C Δ Ξ) (κ : Frames C Ξ Ω)
    (φ : Fml C Ω) (p : Premise C Γ Δ) (b f : Nat)
    (hf : freshK k (.modal m (.cons s ω) κ φ) = f)
    (hs : s.stepIn R f m = some p) :
    memoryReplayLayer R leaf rf next H k (.modal m (.cons s ω) κ φ) (b+1) =
      premise next rf H k m ω κ φ p b := by
  change (match s.stepIn R (freshK k (.modal m (.cons s ω) κ φ)) m with
    | some q => premise next rf H k m ω κ φ q b | none => none) = _
  rw [hf, hs]
end



section
variable (rf : {Γ : Ctx} → Hyps C [] Γ → Fml C Γ → Bool)
  (next : {Γ : Ctx} → Hyps C [] Γ → Nat → Fml C Γ → Nat → Option (List α × Nat))
  {Γ Ξ Ω Γ₁ Γ₂ : Ctx} (H : Hyps C [] Γ) (k : Nat) (m : Modality)
  (ω : Prog C Γ Ξ) (κ : Frames C Ξ Ω) (φ : Fml C Ω)
  (bk : BlockKind) (c c' : Fml C Γ) (P : Prog C Γ Γ₁) (Q : Prog C Γ Γ₂) (b : Nat)
theorem memoryReplaySplitLeft (h : rf H c = true) :
    premise next rf H k m ω κ φ (.split bk c c' P Q) b =
      next (H.pre c') (max k c'.maxIdx) (.modalK m Q (.pop bk Q.ext (.seq ω κ)) φ) b := by
  simp only [premise, h, cond_true]
theorem memoryReplaySplitRight (h : rf H c = false) (h' : rf H c' = true) :
    premise next rf H k m ω κ φ (.split bk c c' P Q) b =
      next (H.pre c) (max k c.maxIdx) (.modalK m P (.pop bk P.ext (.seq ω κ)) φ) b := by
  simp only [premise, h, h', cond_false, cond_true]
theorem memoryReplaySplitBoth (h : rf H c = false) (h' : rf H c' = false) :
    premise next rf H k m ω κ φ (.split bk c c' P Q) b =
      both (next (H.pre c) (max k c.maxIdx) (.modalK m P (.pop bk P.ext (.seq ω κ)) φ))
        (next (H.pre c') (max k c'.maxIdx) (.modalK m Q (.pop bk Q.ext (.seq ω κ)) φ)) b := by
  simp only [premise, h, h', cond_false]
end


-- Typed evaluator closures; no source syntax or operational bound changes.
def memoryReplayRigidNil (C : Contract) (c : Fml C []) : Option (Fml C []) :=
  cond (decide (c.tmSize ≤ Hyps.rigidSize)) (some c) none

def memoryReplayRigidUpd {Γ Δ : Ctx} (g : Fml C Γ → Option (Fml C []))
    (U : Upd C Γ Δ) (c : Fml C Δ) : Option (Fml C []) :=
  cond (decide (c.tmSize ≤ Hyps.rigidSize)) ((Fml.substU U c) >>= g) none

def memoryReplayRigidThin {Γ : Ctx} (g : Fml C Γ → Option (Fml C []))
    (t : LTy) (c : Fml C (t::Γ)) : Option (Fml C []) :=
  (Fml.thinFO? (.drop .refl) c) >>= g

theorem memoryReplayRigidNilEq : (Hyps.nil (C := C) (Γ₀ := [])).rigid = memoryReplayRigidNil C := rfl

theorem memoryReplayRigidPreEq {Γ : Ctx} (H : Hyps C [] Γ) (a : Fml C Γ)
    (g : Fml C Γ → Option (Fml C [])) (h : H.rigid = g) : (H.pre a).rigid = g := h

theorem memoryReplayRigidUpdEq {Γ Δ : Ctx} (H : Hyps C [] Γ) (m : Modality) (U : Upd C Γ Δ)
    (g : Fml C Γ → Option (Fml C [])) (hu : decide (U.tmSize ≤ Hyps.rigidSize) = true)
    (h : H.rigid = g) : (H.upd m U).rigid = memoryReplayRigidUpd g U := by
  funext c
  change (cond (decide (c.tmSize ≤ Hyps.rigidSize) && decide (U.tmSize ≤ Hyps.rigidSize))
    ((Fml.substU U c) >>= H.rigid) none) =
    cond (decide (c.tmSize ≤ Hyps.rigidSize)) ((Fml.substU U c) >>= g) none
  rw [hu, Bool.and_true, h]

theorem memoryReplayRigidAllEq {Γ : Ctx} (H : Hyps C [] Γ) (x : Var) (p : PrimTy)
    (g : Fml C Γ → Option (Fml C [])) (h : H.rigid = g) :
    (H.all x p).rigid = memoryReplayRigidThin g (.val p) := by
  funext c
  change ((Fml.thinFO? (.drop .refl) c) >>= H.rigid) = _
  rw [h]
  rfl

theorem memoryReplayRigidBindEq {Γ : Ctx} (H : Hyps C [] Γ) (m : Modality) (x : Var) (t : LTy)
    (g : Fml C Γ → Option (Fml C [])) (h : H.rigid = g) :
    (H.bind m x t).rigid = memoryReplayRigidThin g t := by
  funext c
  change ((Fml.thinFO? (.drop .refl) c) >>= H.rigid) = _
  rw [h]
  rfl

-- These equations retain the actual upstream projection and evaluator relations.
-- A checked false right operand makes the left conjunction operand irrelevant.
theorem memoryReplayGuardFalse {Γ : Ctx} (H : Hyps C [] Γ) (c : Fml C Γ) (q : Fml C [])
    (hg : H.groundS c = true) (hr : H.rigid (.not c) = some q)
    (hq : (Solidity.Seq.checkCore q).getD false = false) : refuteLanded H c = false := by
  simp only [refuteLanded, hg, cond_true, hr, hq, Bool.and_false]
theorem memoryReplayGuardTrue {Γ : Ctx} (H : Hyps C [] Γ) (c : Fml C Γ) (q : Fml C []) (b : Bool)
    (hg : H.groundS c = true) (hr : H.rigid (.not c) = some q)
    (hq : (Solidity.Seq.checkCore q).getD false = true)
    (hm : ((H.pre c).wrap .ff).modalFree = b) : refuteLanded H c = b := by
  simp only [refuteLanded, hg, cond_true, hr, hq, Bool.and_true, hm]

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
  guards : Array Bool
  guardHints : Array (Option (Fml C [] × Bool))
instance {C : Contract} : Inhabited (Visit C) := ⟨⟨0,[],.nil,0,.tt,0,none,#[],#[],#[]⟩⟩
unsafe def gather {C : Contract} (ref : IO.Ref (Array (Visit C))) (R : RuleSet)
    (n : Nat) {Γ : Ctx} (H : Hyps C [] Γ) (k : Nat) (φ : Fml C Γ) (b : Nat) :
    Option (List (SLeaf C) × Nat) := unsafeBaseIO do
  let children ← IO.mkRef #[]
  let next : {Δ : Ctx} → Hyps C [] Δ → Nat → Fml C Δ → Nat → Option (List (SLeaf C) × Nat) :=
    fun {_} h fresh f budget => unsafeBaseIO do
      let result := gather ref R (n-1) h fresh f budget
      children.modify (·.push ((← ref.get).size-1))
      return result
  let guards ← IO.mkRef #[]
  let guardHints ← IO.mkRef #[]
  let rf : {Δ : Ctx} → Hyps C [] Δ → Fml C Δ → Bool := fun {_} h c => unsafeBaseIO do
    let value := refuteLanded h c
    guards.modify (·.push value)
    let hint := if h.groundS c then (h.rigid (.not c)).map fun q => (q,(Solidity.Seq.checkCore q).getD false) else none
    guardHints.modify (·.push hint)
    return value
  let result := if n==0 then none else memoryReplayLayer R leafS rf next H k φ b
  ref.modify (·.push ⟨n,Γ,H,k,φ,b,result,← children.get,← guards.get,← guardHints.get⟩)
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
  fresh : Nat
  guards : Array Bool
  guardHints : Array (Option (Expr × Bool))
  formula : Expr
  inputK : Nat
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

def requireKernelChecking (disabled : Bool) : MetaM Unit := do
  if disabled then throwError "memory replay requires kernel checking"

def checkEnabled : MetaM Unit := do
  requireKernelChecking ((← getOptions).getBool `debug.skipKernelTC false)
initialize aliasCache : IO.Ref (Std.HashMap (Expr × Expr) Expr) ← IO.mkRef {}

-- Reuse checked values rather than building chains of transparent aliases.
-- Normalize only scalar metadata; the kernel still checks every node equation.
partial def canonicalContext (value : Expr) : MetaM Expr := do
  let e ← ofExceptKernelException (Kernel.whnf (← getEnv) (← getLCtx) value)
  if e.isAppOf ``List.nil then return e
  unless e.isAppOf ``List.cons do throwError "memory replay: nonclosed context spine"
  let args := e.getAppArgs
  let head ← ofExceptKernelException (Kernel.whnf (← getEnv) (← getLCtx) args[1]!)
  let tail ← canonicalContext args[2]!
  return mkAppN e.getAppFn #[args[0]!,head,tail]

-- Pending proof terms are NOT accepted layer certificates. Every component
-- is kernel checked together before any checkpoint or concrete assembly use.
structure LayerCandidate where
  type : Expr
  value : Expr
  deriving Inhabited
initialize pendingLayers : IO.Ref (Array (Nat × LayerCandidate)) ← IO.mkRef #[]

partial def layerConjunction (cs : Array LayerCandidate) (lo hi : Nat) : MetaM (Expr × Expr) := do
  unless lo<hi do throwError "memory replay: empty conjunction interval"
  if hi==lo+1 then return (cs[lo]!.type,cs[lo]!.value)
  let mid := lo+(hi-lo)/2
  let (a,ha) ← layerConjunction cs lo mid
  let (b,hb) ← layerConjunction cs mid hi
  return (mkApp2 (Lean.mkConst ``And) a b,
    mkAppN (Lean.mkConst ``And.intro) #[a,b,ha,hb])

partial def layerComponent (type proof : Expr) (lo hi id : Nat) : MetaM Expr := do
  unless lo≤id ∧ id<hi do throwError "memory replay: component outside conjunction"
  if hi==lo+1 then return proof
  let_expr And a b := type | throwError "memory replay: malformed checked conjunction"
  let mid := lo+(hi-lo)/2
  if id<mid then
    layerComponent a (mkProj ``And 0 proof) lo mid id
  else layerComponent b (mkProj ``And 1 proof) mid hi id

def checkLayerConjunction (cs : Array LayerCandidate) : MetaM (Array Expr) := do
  checkEnabled
  if cs.isEmpty then return #[]
  let (type,value) ← layerConjunction cs 0 cs.size
  -- This is the same kernel checker, checking ALL component proofs. No
  -- heartbeat reset/increase, native proof result or unchecked axiom is used.
  let checked ← Derive.kernelLemma type value
  (Array.range cs.size).mapM (layerComponent type checked 0 cs.size)

initialize finePerf : IO.Ref (Std.HashMap String Nat) ← IO.mkRef {}
def timedMeta {β : Type} (label : String) (action : MetaM β) : MetaM β := do
  let start ← IO.monoNanosNow
  let value ← action
  let stop ← IO.monoNanosNow
  finePerf.modify fun times => times.insert label ((times[label]?.getD 0)+stop-start)
  return value

partial def defineChecked (type value : Expr) : MetaM Expr := do
  let originalKey := (type,value)
  if let some cached := (← aliasCache.get)[originalKey]? then
    if (← getEnv).contains cached.constName! then return cached
  let value ← if type.isConstOf ``Ctx then canonicalContext value else pure value
  let value ← if type.isConstOf ``Nat then
    ofExceptKernelException (Kernel.whnf (← getEnv) (← getLCtx) value)
    else pure value
  if value.isConst || value.isLit then return value
  let value ← if type.isAppOf ``Fml then do
    let e ← ofExceptKernelException (Kernel.whnf (← getEnv) (← getLCtx) value)
    if e.isAppOf ``Fml.modal then
      let mut args := e.getAppArgs
      -- Share the indexed context spines before checking child data aliases.
      -- Every reconstructed constructor is still checked by addDecl below.
      for i in [1:4] do
        let context ← defineChecked (Lean.mkConst ``Ctx) args[i]!
        args := args.set! i context
      for i in [5:8] do
        let child := args[i]!
        let childTy := if i==5 then mkApp3 (Lean.mkConst ``Prog) args[0]! args[1]! args[2]!
          else if i==6 then mkApp3 (Lean.mkConst ``Frames) args[0]! args[2]! args[3]!
          else mkApp2 (Lean.mkConst ``Fml) args[0]! args[3]!
        let shared ← defineChecked childTy child
        args := args.set! i shared
      pure (mkAppN e.getAppFn args)
    else pure value
    else pure value
  let key := (type, value)
  if let some cached := (← aliasCache.get)[key]? then
    if (← getEnv).contains cached.constName! then return cached
  let name ← mkFreshUserName ((← getEnv).mainModule ++ `_memoryLoopState)
  let hints := ReducibilityHints.regular (getMaxHeight (← getEnv) value + 1)
  timedMeta ("aliasDecl-"++(if type.getAppFn.isConst then type.getAppFn.constName!.toString else "function")) <| withOptions (Elab.async.set · false) <| addDecl <| Declaration.defnDecl {
    name, levelParams := [], type, value, hints, safety := .safe }
  let result := Lean.mkConst name
  aliasCache.modify (fun cache => (cache.insert key result).insert originalKey result)
  return result

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

-- The chosen callback is an exact subtree: avoid definitional matching over
-- every unrelated subtree. Track binder depth and replace exactly one occurrence.
partial def abstractFirstExact (e target : Expr) (depth : Nat := 0) (used : Bool := false) : Expr × Bool :=
  if used || !e.hasFVar then (e,used) else
  if e==target then (.bvar depth,true) else
  match e with
  | .app f a =>
    let (f,used) := abstractFirstExact f target depth used
    let (a,used) := abstractFirstExact a target depth used
    (.app f a,used)
  | .lam n t b info =>
    let (t,used) := abstractFirstExact t target depth used
    let (b,used) := abstractFirstExact b target (depth+1) used
    (.lam n t b info,used)
  | .forallE n t b info =>
    let (t,used) := abstractFirstExact t target depth used
    let (b,used) := abstractFirstExact b target (depth+1) used
    (.forallE n t b info,used)
  | .letE n t v b nondep =>
    let (t,used) := abstractFirstExact t target depth used
    let (v,used) := abstractFirstExact v target depth used
    let (b,used) := abstractFirstExact b target (depth+1) used
    (.letE n t v b nondep,used)
  | .mdata data a =>
    let (a,used) := abstractFirstExact a target depth used
    (.mdata data a,used)
  | .proj n i a =>
    let (a,used) := abstractFirstExact a target depth used
    (.proj n i a,used)
  | _ => (e,used)

def knownEq (type a b : Expr) : Expr := mkAppN (Lean.mkConst ``Eq [1]) #[type,a,b]
def knownRefl (type a : Expr) : Expr := mkAppN (Lean.mkConst ``Eq.refl [1]) #[type,a]

-- Construct transitivity with already tracked endpoints. The same kernel check
-- validates both premises; avoid repeatedly inferring the growing proof term.
def layerTrans (j : Job) (a b c h₁ h₂ : Expr) : Expr :=
  mkAppN (Lean.mkConst ``Eq.trans [1])
    #[mkApp (Lean.mkConst ``Option [0]) j.resultTy,a,b,c,h₁,h₂]

initialize rigidFunctions : SimplePersistentEnvExtension (Expr × Expr × Expr) (Std.HashMap Expr (Expr × Expr)) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun cache (key,run,proof) => cache.insert key (run,proof)
    addImportedFn := fun arrays => arrays.foldl (fun cache entries =>
      entries.foldl (fun cache (key,run,proof) => cache.insert key (run,proof)) cache) {} }

def instantiateCertificateType (name : Lean.Name) (args : Array Expr) : MetaM Expr := do
  let info ← getConstInfo name
  unless info.levelParams.isEmpty do throwError "memory replay: unexpected certificate universe"
  let mut type := info.type
  for arg in args do
    let .forallE _ _ body _ := type | throwError "memory replay: function certificate arity"
    type := body.instantiate1 arg
  return type

partial def checkedRigidFunction (C Γ H : Expr) : MetaM (Expr × Expr) := do
  checkEnabled
  let original := mkAppN (Lean.mkConst ``Hyps.rigid) #[C,Γ,H]
  if original.hasFVar || original.hasMVar || original.hasLooseBVars then
    throwError "memory replay: open rigid function cache key"
  if let some (run,proof) := (rigidFunctions.getState (← getEnv))[original]? then
    if run.isConst && proof.isConst && (← getEnv).contains run.constName! && (← getEnv).contains proof.constName! then
      return (run,proof)
  let nilCtx := mkApp (Lean.mkConst ``List.nil [0]) (Lean.mkConst ``LTy)
  let inputTy := mkApp2 (Lean.mkConst ``Fml) C Γ
  let resultTy := mkApp (Lean.mkConst ``Option [0]) (mkApp2 (Lean.mkConst ``Fml) C nilCtx)
  let type ← mkArrow inputTy resultTy
  let e ← ofExceptKernelException (Kernel.whnf (← getEnv) (← getLCtx) H)
  let a := e.getAppArgs
  let (run,proof) ← if e.isAppOf ``Hyps.nil then do
      let run ← defineChecked type (mkApp (Lean.mkConst ``memoryReplayRigidNil) C)
      pure (run,mkApp (Lean.mkConst ``memoryReplayRigidNilEq) C)
    else if e.isAppOf ``Hyps.pre then do
      let (run,previous) ← checkedRigidFunction C a[2]! a[3]!
      pure (run,mkAppN (Lean.mkConst ``memoryReplayRigidPreEq) #[C,a[2]!,a[3]!,a[4]!,run,previous])
    else if e.isAppOf ``Hyps.upd then do
      let (parent,previous) ← checkedRigidFunction C a[2]! a[4]!
      let args := #[C,a[2]!,a[3]!,a[4]!,a[5]!,a[6]!,parent]
      let certificateType ← instantiateCertificateType ``memoryReplayRigidUpdEq args
      let .forallE _ cap _ _ := certificateType | throwError "memory replay: missing original update cap"
      let capProof ← Derive.kernelLemma cap (knownRefl (Lean.mkConst ``Bool) (toExpr true))
      let run ← defineChecked type (mkAppN (Lean.mkConst ``memoryReplayRigidUpd) #[C,a[2]!,a[3]!,parent,a[6]!])
      pure (run,mkAppN (Lean.mkConst ``memoryReplayRigidUpdEq) (args ++ #[capProof,previous]))
    else if e.isAppOf ``Hyps.all then do
      let (parent,previous) ← checkedRigidFunction C a[2]! a[3]!
      let t := mkApp (Lean.mkConst ``LTy.val) a[5]!
      let run ← defineChecked type (mkAppN (Lean.mkConst ``memoryReplayRigidThin) #[C,a[2]!,parent,t])
      pure (run,mkAppN (Lean.mkConst ``memoryReplayRigidAllEq) #[C,a[2]!,a[3]!,a[4]!,a[5]!,parent,previous])
    else if e.isAppOf ``Hyps.bind then do
      let (parent,previous) ← checkedRigidFunction C a[2]! a[3]!
      let run ← defineChecked type (mkAppN (Lean.mkConst ``memoryReplayRigidThin) #[C,a[2]!,parent,a[6]!])
      pure (run,mkAppN (Lean.mkConst ``memoryReplayRigidBindEq) #[C,a[2]!,a[3]!,a[4]!,a[5]!,a[6]!,parent,previous])
    else throwError "memory replay: unsupported rigid function prefix"
  let proof ← Derive.kernelLemma (knownEq type original run) proof
  modifyEnv (rigidFunctions.addEntry · (original,run,proof))
  return (run,proof)

-- Check both ORIGINAL sibling projections in one kernel call so their
-- common typed substitution reductions can share the kernel's local cache.
def checkedRigidPair (j : Job) (id : Nat) (Γ H c c' : Expr) : MetaM (Array Expr) := do
  checkEnabled
  let hints := j.hints[id]!.guardHints
  let some (q,_) := hints[0]?.join | return #[]
  let some (q',_) := hints[1]?.join | return #[]
  let (run,correct) ← checkedRigidFunction j.C Γ H
  let nilCtx := mkApp (Lean.mkConst ``List.nil [0]) (Lean.mkConst ``LTy)
  let fmlTy := mkApp2 (Lean.mkConst ``Fml) j.C nilCtx
  let optionTy := mkApp (Lean.mkConst ``Option [0]) fmlTy
  let inputTy := mkApp2 (Lean.mkConst ``Fml) j.C Γ
  let family := mkLambda `condition .default inputTy optionTy
  let original := mkAppN (Lean.mkConst ``Hyps.rigid) #[j.C,Γ,H]
  let mut components := #[]
  for (condition,result) in [(c,q),(c',q')] do
    let notc := mkAppN (Lean.mkConst ``Fml.not) #[j.C,Γ,condition]
    let value := mkApp run notc
    let result := mkApp2 (Lean.mkConst ``Option.some [0]) fmlTy result
    let call := mkApp original notc
    let atProof := mkAppN (Lean.mkConst ``congrFun [1,1]) #[inputTy,family,original,run,correct,notc]
    let proof := mkAppN (Lean.mkConst ``Eq.trans [1])
      #[optionTy,call,value,result,atProof,knownRefl optionTy result]
    components := components.push (⟨knownEq optionTy call result,proof⟩ : LayerCandidate)
  timedMeta "rigidPairKernel" <| checkLayerConjunction components

-- All proposed intermediate values are checked against the ORIGINAL
-- evaluator expressions before the final original guard equation is accepted.
def checkedGuard (j : Job) (id index : Nat) (Γ H c : Expr) (wanted : Bool) (rigid : Option Expr := none) : MetaM Expr := do
  checkEnabled
  let boolTy := Lean.mkConst ``Bool
  let choice := toExpr wanted
  let call := mkAppN (Lean.mkConst ``refuteLanded) #[j.C,Γ,H,c]
  let goal := knownEq boolTy call choice
  let hints := j.hints[id]!.guardHints
  if let some (q,core) := hints[index]?.join then
    let name := if core then ``memoryReplayGuardTrue else ``memoryReplayGuardFalse
    let args := #[j.C,Γ,H,c,q] ++ (if core then #[choice] else #[])
    let mut type := (← getConstInfo name).type
    let mut proof := Lean.mkConst name
    for arg in args do
      let .forallE _ _ body _ := type | throwError "guard lemma arity"
      type := body.instantiate1 arg
      proof := mkApp proof arg
    for step in [:if core then 4 else 3] do
      let .forallE _ premise body _ := type | throwError "guard relation arity"
      unless premise.isAppOf ``Eq && premise.getAppNumArgs==3 do throwError "guard relation is not equality"
      let eqArgs := premise.getAppArgs
      let fact ← timedMeta ("guardRelation-"++toString step) do
        if step==1 && rigid.isSome then
          Derive.kernelLemma premise rigid.get!
        else if step==1 then
          let (run,correct) ← timedMeta "rigidFunctionBuild" <| checkedRigidFunction j.C Γ H
          let notc := mkAppN (Lean.mkConst ``Fml.not) #[j.C,Γ,c]
          let value := mkApp run notc
          let reduced ← timedMeta "rigidFunctionEval" <| Derive.kernelLemma
            (knownEq eqArgs[0]! value eqArgs[2]!) (knownRefl eqArgs[0]! eqArgs[2]!)
          let inputTy := mkApp2 (Lean.mkConst ``Fml) j.C Γ
          let family := mkLambda `condition .default inputTy eqArgs[0]!
          let original := mkAppN (Lean.mkConst ``Hyps.rigid) #[j.C,Γ,H]
          let atProof := mkAppN (Lean.mkConst ``congrFun [1,1]) #[inputTy,family,original,run,correct,notc]
          let proof := mkAppN (Lean.mkConst ``Eq.trans [1]) #[eqArgs[0]!,eqArgs[1]!,value,eqArgs[2]!,atProof,reduced]
          Derive.kernelLemma premise proof
        else Derive.kernelLemma premise (knownRefl eqArgs[0]! eqArgs[2]!)
      proof := mkApp proof fact
      type := body.instantiate1 fact
    return ← Derive.kernelLemma goal proof
  Derive.kernelLemma goal (knownRefl boolTy choice)

partial def layer (j : Job) (id : Nat) (input : Input) (actual next start e hp : Expr)
    (left : List Nat) (hyps : Array Expr) : MetaM LayerCandidate := do
  let ew ← timedMeta "layerWHNF" do
    let env ← getEnv
    let lctx ← getLCtx
    ofExceptKernelException (Kernel.whnf env lctx e)
  let ew ← timedMeta "betaTransform" <| Core.transform ew (pre := fun t =>
    return if !t.hasFVar then .done t
      else if t.isHeadBetaTarget then .visit t.headBeta else .continue)
  let call? := ew.findExt? fun t =>
    if !t.hasFVar then .done
    else if t.getAppFn==next && t.getAppNumArgs==5 && !t.hasLooseBVars then .found
    else .visit
  if let some call := call? then
    let child::rest := left | throwError "memory replay: unproposed callback"
    unless child < id do throwError "memory replay: non-postorder child"
    assignInput j child (input.n-1) call.getAppArgs
    let result ← expected j child
    withLocalDeclD `child (knownEq (mkApp (Lean.mkConst ``Option [0]) j.resultTy) call result) fun hyp => do
      if ew==call then
        layer j id input actual next start result (layerTrans j start e result hp hyp) rest (hyps.push hyp)
      else
        let (body,found) := abstractFirstExact ew call
        unless found do throwError "memory replay: exact callback absent"
        let f := mkLambda `result .default (mkApp (Lean.mkConst ``Option [0]) j.resultTy) body
        let optionTy := mkApp (Lean.mkConst ``Option [0]) j.resultTy
        let hr := mkAppN (Lean.mkConst ``congrArg [1,1]) #[optionTy,optionTy,call,result,f,hyp]
        layer j id input actual next start (mkApp f result) (layerTrans j start e (mkApp f result) hp hr) rest (hyps.push hyp)
  else
    unless left.isEmpty do throwError "memory replay: unreachable proposed callback"
    let params := #[next] ++ hyps
    let type ← timedMeta "closeType" <| mkForallFVars params (knownEq (mkApp (Lean.mkConst ``Option [0]) j.resultTy) start input.value)
    let value ← timedMeta "closeValue" <| mkLambdaFVars params hp
    pure (⟨type,value⟩ : LayerCandidate)

initialize perf : IO.Ref (Nat × Nat) ← IO.mkRef (0,0)
initialize heads : IO.Ref (Std.HashMap Lean.Name Nat) ← IO.mkRef {}

def discover (j : Job) (id : Nat) : MetaM (List Nat) := do
  let t0 ← IO.monoNanosNow
  let some input := (← j.inputs.get)[id]! | throwError "memory replay: undiscovered input"
  let original := input
  let a := input.args
  let Γ ← timedMeta "alias-Γ" <| defineChecked (Lean.mkConst ``Ctx) a[0]!
  let nilCtx := mkApp (Lean.mkConst ``List.nil [0]) (Lean.mkConst ``LTy)
  let H ← timedMeta "alias-H" <| defineChecked (mkApp3 (Lean.mkConst ``Hyps) j.C nilCtx Γ) a[1]!
  let k ← timedMeta "alias-k" <| defineChecked (Lean.mkConst ``Nat) (toExpr j.hints[id]!.inputK)
  -- Flat constructor quotations remain proposals: memoryReplayLayer_congr
  -- retains the ORIGINAL equality premises, checked in the layer conjunction.
  let φ ← timedMeta "alias-φ" <| defineChecked (mkApp2 (Lean.mkConst ``Fml) j.C Γ) j.hints[id]!.formula
  let b ← timedMeta "alias-b" <| defineChecked (Lean.mkConst ``Nat) a[4]!
  let input := {input with args := #[a[0]!,H,k,φ,b]}
  let t1 ← IO.monoNanosNow
  let mut lemma := none
  let children := j.hints[id]!.children.toList
  if input.n==0 then
    unless children.isEmpty do throwError "memory replay: zero-depth callback"
  else
    let actual := mkAppN (Lean.mkConst ``runK)
      #[j.C,mkApp (Lean.mkConst ``SLeaf) j.C,j.R,mkApp (Lean.mkConst ``leafS) j.C,
        mkApp (Lean.mkConst ``refuteLanded) j.C,toExpr (input.n-1)]
    lemma ← withLocalDeclD `next (← timedMeta "nextType" <| inferType actual) fun next => do
      let start := mkAppN (Lean.mkConst ``memoryReplayLayer)
        (#[j.C,mkApp (Lean.mkConst ``SLeaf) j.C,j.R,mkApp (Lean.mkConst ``leafS) j.C,
          mkApp (Lean.mkConst ``refuteLanded) j.C,next] ++ input.args)
      let rawStart := mkAppN (Lean.mkConst ``memoryReplayLayer)
        (#[j.C,mkApp (Lean.mkConst ``SLeaf) j.C,j.R,mkApp (Lean.mkConst ``leafS) j.C,
          mkApp (Lean.mkConst ``refuteLanded) j.C,next] ++ original.args)
      let common := #[j.C,mkApp (Lean.mkConst ``SLeaf) j.C,j.R,
        mkApp (Lean.mkConst ``leafS) j.C,mkApp (Lean.mkConst ``refuteLanded) j.C,next]
      let hc := mkAppN (Lean.mkConst ``memoryReplayLayer_congr) (common ++
        #[original.args[0]!,original.args[1]!,input.args[1]!,original.args[2]!,input.args[2]!,
          original.args[3]!,input.args[3]!,original.args[4]!,input.args[4]!,
          knownRefl (mkApp3 (Lean.mkConst ``Hyps) j.C nilCtx original.args[0]!) original.args[1]!,
          knownRefl (Lean.mkConst ``Nat) original.args[2]!,
          knownRefl (mkApp2 (Lean.mkConst ``Fml) j.C original.args[0]!) original.args[3]!,
          knownRefl (Lean.mkConst ``Nat) original.args[4]!])
      let φ ← timedMeta "formulaWHNF" do
        let env ← getEnv
        let lctx ← getLCtx
        ofExceptKernelException (Kernel.whnf env lctx input.args[3]!)
      heads.modify fun hs => hs.insert φ.getAppFn.constName! ((hs[φ.getAppFn.constName!]?.getD 0)+1)
      if φ.isAppOf ``Fml.modal then
        let fa := φ.getAppArgs
        let P ← timedMeta "programWHNF" do
          let env ← getEnv
          let lctx ← getLCtx
          ofExceptKernelException (Kernel.whnf env lctx fa[5]!)
        if P.isAppOf ``Prog.cons then
          let ps := P.getAppArgs
          let Γ := ps[1]!
          let Δ := ps[2]!
          let Ξ := ps[3]!
          let Ω := fa[3]!
          let fullPhi := mkAppN (Lean.mkConst ``Fml.modal) #[j.C,Γ,Ξ,Ω,fa[4]!,P,fa[6]!,fa[7]!]
          let fresh := mkAppN (Lean.mkConst ``freshK) #[j.C,Γ,input.args[2]!,fullPhi]
          let symbolicStep := mkAppN (Lean.mkConst ``Stmt.stepIn) #[j.C,j.R,fresh,fa[4]!,Γ,Δ,ps[4]!]
          let symbolic ← timedMeta "stepWHNF" do
            let env ← getEnv
            let lctx ← getLCtx
            ofExceptKernelException (Kernel.whnf env lctx symbolicStep)
          if symbolic.isAppOf ``Option.some then
            let pv ← timedMeta "premiseWHNF" do
              let env ← getEnv
              let lctx ← getLCtx
              ofExceptKernelException (Kernel.whnf env lctx symbolic.getAppArgs[1]!)
            -- This only chooses a proof-construction path. Every chosen
            -- fresh literal and every original symbolic step is kernel checked.
            -- Do not search recursively inside earlier freshK computations.
            let literalCandidate ← timedMeta "literalScan" do
              let _ ← getFVarLocalDecl next
              return (pv.findExt? fun e =>
                if e==fresh then .found
                else if e.isAppOf ``freshK then .done
                else .visit).isSome
            if pv.isAppOf ``Premise.split && !literalCandidate then
              let some budget := (← ofExceptKernelException (Kernel.whnf (← getEnv) (← getLCtx) input.args[4]!)).rawNatLit? | throwError "nonliteral budget"
              if budget>0 then
                let pa := pv.getAppArgs
                let guards := j.hints[id]!.guards
                unless guards.size>0 do throwError "missing split guard"
                let rf := mkApp (Lean.mkConst ``refuteLanded) j.C
                let call := mkAppN rf #[Γ,input.args[1]!,pa[5]!]
                let choice := toExpr guards[0]!
                let pair ← if guards.size==2 && !guards[0]! then
                    checkedRigidPair j id Γ input.args[1]! pa[5]! pa[6]!
                  else pure #[]
                let h ← timedMeta "guardKernel" <| checkedGuard j id 0 Γ input.args[1]! pa[5]! guards[0]! pair[0]?
                let mut proofs := #[h]
                let name ← if guards[0]! then do
                    unless guards.size==1 do throwError "extra split guard"
                    pure ``memoryReplaySplitLeft
                  else do
                    unless guards.size==2 do throwError "missing second split guard"
                    let call := mkAppN rf #[Γ,input.args[1]!,pa[6]!]
                    let choice := toExpr guards[1]!
                    let h ← timedMeta "guardKernel" <| checkedGuard j id 1 Γ input.args[1]! pa[6]! guards[1]! pair[1]?
                    proofs := proofs.push h
                    pure (if guards[1]! then ``memoryReplaySplitRight else ``memoryReplaySplitBoth)
                let b := toExpr (budget-1)
                let hm := mkAppN (Lean.mkConst ``memoryReplayModalConsAt) (common ++
                  #[Γ,Δ,Ξ,Ω,input.args[1]!,input.args[2]!,fa[4]!,ps[4]!,ps[5]!,fa[6]!,fa[7]!,pv,b,fresh,
                    ← mkEqRefl fresh,← mkEqRefl symbolic])
                let select := mkAppN (Lean.mkConst name)
                  (#[j.C,mkApp (Lean.mkConst ``SLeaf) j.C,rf,next,Γ,Ξ,Ω,pa[2]!,pa[3]!,
                    input.args[1]!,input.args[2]!,fa[4]!,ps[5]!,fa[6]!,fa[7]!,
                    pa[4]!,pa[5]!,pa[6]!,pa[7]!,pa[8]!,b] ++ proofs)
                let selectTy ← timedMeta "splitType" <| inferType select
                let rhs := selectTy.getAppArgs.back!
                return some (← layer j id input actual next rawStart rhs (← mkEqTrans hc (← mkEqTrans hm select)) children #[])
            if literalCandidate then
              logInfo m!"reached literal freshness at node {id}"
              let some budget := (← ofExceptKernelException (Kernel.whnf (← getEnv) (← getLCtx) input.args[4]!)).rawNatLit? | throwError "nonliteral budget"
              if budget>0 then
                let f := toExpr j.hints[id]!.fresh
                let step := mkAppN (Lean.mkConst ``Stmt.stepIn) #[j.C,j.R,f,fa[4]!,Γ,Δ,ps[4]!]
                let sw ← timedMeta "literalStepWHNF" do
                  let env ← getEnv
                  let lctx ← getLCtx
                  ofExceptKernelException (Kernel.whnf env lctx step)
                unless sw.isAppOf ``Option.some do throwError "literal step refused"
                let p ← timedMeta "literalPremiseWHNF" do
                  let env ← getEnv
                  let lctx ← getLCtx
                  ofExceptKernelException (Kernel.whnf env lctx sw.getAppArgs[1]!)
                let b := toExpr (budget-1)
                let hf ← mkEqRefl f
                let hs ← timedMeta "stepReflType" <| mkEqRefl sw
                let hm := mkAppN (Lean.mkConst ``memoryReplayModalConsAt) (common ++
                  #[Γ,Δ,Ξ,Ω,input.args[1]!,input.args[2]!,fa[4]!,ps[4]!,ps[5]!,fa[6]!,fa[7]!,p,b,f,hf,hs])
                let prem := mkAppN (Lean.mkConst ``premise)
                  (#[j.C,mkApp (Lean.mkConst ``SLeaf) j.C,next,mkApp (Lean.mkConst ``refuteLanded) j.C,
                    Γ,Δ,Ξ,Ω,input.args[1]!,input.args[2]!,fa[4]!,ps[5]!,fa[6]!,fa[7]!,p,b])
                return some (← layer j id input actual next rawStart prem (← timedMeta "literalTrans" <| mkEqTrans hc hm) children #[])
            -- Reuse the inspected step through its checked equation instead
            -- of reducing the entire modal layer a second time in Meta.
            let some budget := (← ofExceptKernelException (Kernel.whnf (← getEnv) (← getLCtx) input.args[4]!)).rawNatLit? | throwError "nonliteral budget"
            if budget>0 then
              let b := toExpr (budget-1)
              let premiseTy := mkApp3 (Lean.mkConst ``Premise) j.C Γ Δ
              let optionPremise := mkApp (Lean.mkConst ``Option [0]) premiseTy
              let hm := mkAppN (Lean.mkConst ``memoryReplayModalConsAt) (common ++
                #[Γ,Δ,Ξ,Ω,input.args[1]!,input.args[2]!,fa[4]!,ps[4]!,ps[5]!,fa[6]!,fa[7]!,pv,b,fresh,
                  knownRefl (Lean.mkConst ``Nat) fresh,knownRefl optionPremise symbolic])
              let prem := mkAppN (Lean.mkConst ``premise)
                (#[j.C,mkApp (Lean.mkConst ``SLeaf) j.C,next,mkApp (Lean.mkConst ``refuteLanded) j.C,
                  Γ,Δ,Ξ,Ω,input.args[1]!,input.args[2]!,fa[4]!,ps[5]!,fa[6]!,fa[7]!,pv,b])
              return some (← layer j id input actual next rawStart prem (layerTrans j rawStart start prem hc hm) children #[])
      let generic := if φ.isAppOf ``Fml.upd then some (``memoryReplayUpd, 3)
        else if φ.isAppOf ``Fml.all then some (``memoryReplayAll, 2)
        else if φ.isAppOf ``Fml.bind then some (``memoryReplayBind, 2)
        else if φ.isAppOf ``Fml.allocAll then some (``memoryReplayAllocAll, 2)
        else none
      if let some (lemmaName, skip) := generic then
        if let [child] := children then
          let ew ← timedMeta "deterministicWHNF" do
            let env ← getEnv
            let lctx ← getLCtx
            ofExceptKernelException (Kernel.whnf env lctx start)
          let some budget := (← ofExceptKernelException (Kernel.whnf (← getEnv) (← getLCtx) input.args[4]!)).rawNatLit?
            | throwError "memory replay: noncanonical checked budget"
          if budget>0 && ew.getAppFn==next && ew.getAppNumArgs==5 then
            assignInput j child (input.n-1) ew.getAppArgs
            let r ← expected j child
            unless r==input.value do throwError "memory replay: deterministic result mismatch"
            return some (← withLocalDeclD `child (knownEq (mkApp (Lean.mkConst ``Option [0]) j.resultTy) ew r) fun h => do
              let args := #[j.C,mkApp (Lean.mkConst ``SLeaf) j.C,j.R,
                mkApp (Lean.mkConst ``leafS) j.C,mkApp (Lean.mkConst ``refuteLanded) j.C,next] ++
                φ.getAppArgs.extract 1 skip ++ #[input.args[1]!,input.args[2]!] ++
                φ.getAppArgs.extract skip φ.getAppNumArgs ++ #[toExpr (budget-1),r,h]
              let proof := mkAppN (Lean.mkConst lemmaName) args
              let ty ← mkForallFVars #[next,h] (knownEq (mkApp (Lean.mkConst ``Option [0]) j.resultTy) rawStart r)
              let value ← mkLambdaFVars #[next,h] (layerTrans j rawStart start r hc proof)
              pure (⟨ty,value⟩ : LayerCandidate))
      return some (← layer j id input actual next rawStart start hc children #[])
  let t2 ← IO.monoNanosNow
  perf.modify fun (a,b) => (a+(t1-t0),b+(t2-t1))
  if let some candidate := lemma then pendingLayers.modify (·.push (id,candidate))
  j.inputs.modify (·.set! id (some {original with layer:=none}))
  return children

def flushLayers (j : Job) : MetaM Unit := do
  checkEnabled
  let pending ← pendingLayers.get
  if pending.isEmpty then return
  let checked ← timedMeta "batchKernel" <| checkLayerConjunction (pending.map (·.2))
  for i in [:pending.size] do
    let id := pending[i]!.1
    let some input := (← j.inputs.get)[id]! | throwError "memory replay: missing pending node"
    unless input.layer.isNone do throwError "memory replay: duplicate checked layer"
    j.inputs.modify (·.set! id (some {input with layer:=some checked[i]!}))
  pendingLayers.set #[]
  logInfo m!"kernel checked every equation in layer conjunction ({pending.size} components)"

def assemble (j : Job) (id : Nat) : MetaM Unit := do
  flushLayers j
  let some input := (← j.inputs.get)[id]! | throwError "memory replay: no checked layer"
  let original := runExpr j input.n input.args
  let optionTy := mkApp (Lean.mkConst ``Option [0]) j.resultTy
  let value ← if input.n==0 then pure (knownRefl optionTy input.value) else do
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
    let middle := mkAppN (Lean.mkConst ``memoryReplayLayer)
      (#[j.C,mkApp (Lean.mkConst ``SLeaf) j.C,j.R,mkApp (Lean.mkConst ``leafS) j.C,
        mkApp (Lean.mkConst ``refuteLanded) j.C,actual] ++ input.args)
    pure (layerTrans j original middle input.value hUnfold hLayer)
  let h ← timedMeta "assemblyKernel" <| Derive.kernelLemma (knownEq optionTy original input.value) value
  j.inputs.modify (·.set! id (some {input with proof:=some h}))

elab "prepare_memory_replay " t:term : command => liftTermElabM do
  job.set none
  pendingLayers.set #[]
  checkEnabled
  let φ ← elabTerm t none
  synthesizeSyntheticMVarsNoPostponing
  let φ ← instantiateMVars φ
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
    | none => (⟨v.n,none,false,v.children,freshK v.k v.φ,v.guards,v.guardHints.map (·.map fun (q,b) => (Fml.quote C q,b)),Fml.quote C v.φ,v.k⟩ : Hint)
    | some (ls,b) => ⟨v.n,some b,!ls.isEmpty,v.children,freshK v.k v.φ,v.guards,v.guardHints.map (·.map fun (q,b) => (Fml.quote C q,b)),Fml.quote C v.φ,v.k⟩
  let inputs ← IO.mkRef (Array.replicate visits.size none)
  let j : Job := ⟨φ,C,R,pairTy,hints,inputs,[visits.size-1],0⟩
  let nil := mkApp (Lean.mkConst ``Hyps.nil) C
  let nilCtx := mkApp (Lean.mkConst ``List.nil [0]) (Lean.mkConst ``LTy)
  let H := mkApp nil nilCtx
  assignInput j (visits.size-1) 1024 #[nilCtx,H,toExpr (0:Nat),φ,toExpr (1024:Nat)]
  job.set (some j)
  logInfo m!"proposed {visits.size} typed visits under original1024 limits"

def discoverNext : MetaM Unit := do
  let savedEnv ← getEnv
  tryCatchRuntimeEx (do
    checkEnabled
    let some j ← job.get | throwError "memory replay: no job"
    let id::pending := j.pending | throwError "memory replay: discovery already finished"
    let children ← discover j id
    job.set (some {j with pending:=children++pending})
    logInfo m!"prepared layer {id}; concrete node checked during assembly"
  ) fun e => do
    setEnv savedEnv
    job.set none
    pendingLayers.set #[]
    throw e

elab "discover_memory_replay" : command => liftTermElabM do
  discoverNext

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
    pendingLayers.set #[]
    throw e

def saveCheckpoint : MetaM Unit := do
  let savedEnv ← getEnv
  tryCatchRuntimeEx (do
    checkEnabled
    if (← Core.getMessageLog).hasErrors then throwError "memory replay: cannot save after errors"
    let some j ← job.get | throwError "memory replay: no checkpoint to save"
    flushLayers j
    let s : Snapshot := ⟨j.target,j.C,j.R,j.resultTy,j.hints,← j.inputs.get,j.pending,j.assembled⟩
    modifyEnv (snapshots.addEntry · s)
    job.set none
    pendingLayers.set #[]
    logInfo m!"saved replay checkpoint; alias/layer ns {← perf.get}; heads {repr (← heads.get).toList}; fine ns {repr (← finePerf.get).toList}"
  ) fun e => do
    setEnv savedEnv
    job.set none
    pendingLayers.set #[]
    throw e

elab "save_memory_replay" : command => liftTermElabM do
  saveCheckpoint

elab "resume_memory_replay " t:term : command => liftTermElabM do
  job.set none
  pendingLayers.set #[]
  checkEnabled
  let target ← elabTerm t none
  synthesizeSyntheticMVarsNoPostponing
  let target ← instantiateMVars target
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
    flushLayers j
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
    pendingLayers.set #[]
    throw e

end Solidity.Seq.MemoryReplay
