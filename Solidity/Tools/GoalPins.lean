import Solidity.Goals.GoalPinsSpec
/-! Executable traversal of the goal-pin reference graph. -/
namespace Solidity.GoalPins
open Lean
open Solidity.Goals.GoalPinSpecV2
/-- Evaluate the finite reference graph with an explicit depth bound. -/
def derive (env : Environment) : Nat → Task → Except Error Tree
  | 0, _ => .error .resource
  | fuel + 1, task => do
      let (label, tasks) ← step env fuel task
      let children ← collect (tasks.map (derive env fuel))
      pure (.node label children)
theorem propResult_mono (env : Environment) (fuel : Nat) :
    ∀ larger ty result, fuel ≤ larger →
      propResult env fuel ty = .ok result → propResult env larger ty = .ok result := by
  induction fuel with
  | zero =>
    intro larger ty result hle h
    simp [propResult] at h
  | succ fuel ih =>
    intro larger ty result hle h
    cases larger with
    | zero => omega
    | succ larger =>
      have hleSmall : fuel ≤ larger := Nat.le_of_succ_le_succ hle
      cases hw : Kernel.whnf env {} ty with
      | error err => simp only [propResult, hw, reduceCtorEq] at h
      | ok value =>
        cases value <;> simp only [propResult, hw] at h ⊢
        all_goals try exact h
        case forallE name domain body info => exact ih larger body result hleSmall h
        case sort level => cases level <;> simpa using h
theorem step_mono (env : Environment) (fuel larger : Nat) (task : Task)
    (result : Label × List Task) (hle : fuel ≤ larger)
    (h : step env fuel task = .ok result) : step env larger task = .ok result := by
  cases hr : raw task.params task.locals.length (erase task.expression) with
  | error err => simp only [step, hr, bind, Except.bind] at h; cases h
  | ok rawValue =>
    cases hi : inferred env task with
    | error err => simp only [step, hr, hi, bind, Except.bind] at h; cases h
    | ok ty =>
      cases hp : propResult env fuel ty with
      | error err => simp only [step, hr, hi, hp, bind, Except.bind] at h; cases h
      | ok family =>
        have hpLarge : propResult env larger ty = .ok family :=
          propResult_mono env fuel larger ty family hle hp
        simp only [step, hr, hi, hp, bind, Except.bind] at h
        simp only [step, hr, hi, hpLarge, bind, Except.bind]
        exact h
theorem collect_mono (f g : Task → Except Error Tree)
    (hm : ∀ task tree, f task = .ok tree → g task = .ok tree) :
    ∀ (tasks : List Task) (trees : List Tree), collect (tasks.map f) = .ok trees →
      collect (tasks.map g) = .ok trees := by
  intro tasks
  induction tasks with
  | nil =>
    intro trees h
    simpa [collect] using h
  | cons task tasks ih =>
    intro trees h
    cases hf : f task with
    | error err => simp [collect, hf] at h
    | ok tree =>
      cases hr : collect (tasks.map f) with
      | error err => simp [collect, hf, hr, Except.map] at h
      | ok rest =>
        have eq : tree :: rest = trees := by simpa [collect, hf, hr, Except.map] using h
        subst trees
        have hg := hm task tree hf
        have hgRest := ih rest hr
        simp [collect, hg, hgRest, Except.map]
theorem derive_mono (env : Environment) (fuel : Nat) :
    ∀ larger task tree, fuel ≤ larger → derive env fuel task = .ok tree →
      derive env larger task = .ok tree := by
  induction fuel with
  | zero =>
    intro larger task tree hle h
    simp [derive] at h
  | succ fuel ih =>
    intro larger task tree hle h
    cases larger with
    | zero => omega
    | succ larger =>
      have hleSmall : fuel ≤ larger := Nat.le_of_succ_le_succ hle
      cases hs : step env fuel task with
      | error err => simp [derive, hs, bind, Except.bind] at h
      | ok pair =>
        rcases pair with ⟨lab, tasks⟩
        cases hc : collect (tasks.map (derive env fuel)) with
        | error err => simp [derive, hs, hc, bind, Except.bind] at h
        | ok trees =>
          have eq : Tree.node lab trees = tree := by
            simpa [derive, hs, hc, bind, Except.bind, Functor.map, Except.map,
              Pure.pure, Except.pure] using h
          subst tree
          have hsLarge := step_mono env fuel larger task (lab, tasks) hleSmall hs
          have hcLarge := collect_mono (derive env fuel) (derive env larger)
            (fun task tree ht => ih larger task tree hleSmall ht) tasks trees hc
          simp [derive, hsLarge, hcLarge, bind, Except.bind, Pure.pure, Except.pure]
/-! The cache is only an optimization. Every entry carries a proof equating it to
`derive`; a hash selects candidates, and `sameTask` must produce an equality proof
before a result is reused. Unsupported equality cases merely miss the cache. -/
def sameLevel : (a b : Level) → Option (PLift (a = b))
  | .zero, .zero => some ⟨rfl⟩
  | .succ a, .succ b => do
    let ⟨h⟩ ← sameLevel a b
    pure ⟨congrArg Level.succ h⟩
  | .max a b, .max c d => do
    let ⟨h⟩ ← sameLevel a c
    let ⟨k⟩ ← sameLevel b d
    pure ⟨(congrArg (fun x => Level.max x b) h).trans (congrArg (Level.max c) k)⟩
  | .imax a b, .imax c d => do
    let ⟨h⟩ ← sameLevel a c
    let ⟨k⟩ ← sameLevel b d
    pure ⟨(congrArg (fun x => Level.imax x b) h).trans (congrArg (Level.imax c) k)⟩
  | .param a, .param b => if h : a = b then some ⟨congrArg Level.param h⟩ else none
  | _, _ => none
def sameLevels : (a b : List Level) → Option (PLift (a = b))
  | [], [] => some ⟨rfl⟩
  | a :: as, b :: bs => do
    let ⟨h⟩ ← sameLevel a b
    let ⟨k⟩ ← sameLevels as bs
    pure ⟨(congrArg (fun x => x :: as) h).trans (congrArg (List.cons b) k)⟩
  | _, _ => none
def sameBinder (a b : BinderInfo) : Option (PLift (a = b)) := by
  cases a <;> cases b <;> first | exact some ⟨rfl⟩ | exact none
def sameLiteral : (a b : Literal) → Option (PLift (a = b))
  | .natVal a, .natVal b => if h : a = b then some ⟨congrArg Literal.natVal h⟩ else none
  | .strVal a, .strVal b => if h : a = b then some ⟨congrArg Literal.strVal h⟩ else none
  | _, _ => none
def sameExpr : (a b : Expr) → Option (PLift (a = b))
  | .bvar a, .bvar b => if h : a = b then some ⟨congrArg Expr.bvar h⟩ else none
  | .sort a, .sort b => do
    let ⟨h⟩ ← sameLevel a b
    pure ⟨congrArg Expr.sort h⟩
  | .const a us, .const b vs => do
    if h : a = b then
      let ⟨k⟩ ← sameLevels us vs
      pure ⟨by cases h; cases k; rfl⟩
    else none
  | .app a b, .app c d => do
    let ⟨h⟩ ← sameExpr a c
    let ⟨k⟩ ← sameExpr b d
    pure ⟨by cases h; cases k; rfl⟩
  | .lam n t b i, .lam m u c j => do
    if hn : n = m then
      let ⟨ht⟩ ← sameExpr t u
      let ⟨hb⟩ ← sameExpr b c
      let ⟨hi⟩ ← sameBinder i j
      pure ⟨by cases hn; cases ht; cases hb; cases hi; rfl⟩
    else none
  | .forallE n t b i, .forallE m u c j => do
    if hn : n = m then
      let ⟨ht⟩ ← sameExpr t u
      let ⟨hb⟩ ← sameExpr b c
      let ⟨hi⟩ ← sameBinder i j
      pure ⟨by cases hn; cases ht; cases hb; cases hi; rfl⟩
    else none
  | .letE n t v b d, .letE m u w c e => do
    if hn : n = m then
      if hd : d = e then
        let ⟨ht⟩ ← sameExpr t u
        let ⟨hv⟩ ← sameExpr v w
        let ⟨hb⟩ ← sameExpr b c
        pure ⟨by cases hn; cases ht; cases hv; cases hb; cases hd; rfl⟩
      else none
    else none
  | .lit a, .lit b => do
    let ⟨h⟩ ← sameLiteral a b
    pure ⟨congrArg Expr.lit h⟩
  | .proj n i a, .proj m j b => do
    if hn : n = m then
      if hi : i = j then
        let ⟨h⟩ ← sameExpr a b
        pure ⟨by cases hn; cases hi; cases h; rfl⟩
      else none
    else none
  | _, _ => none
open Solidity.Goals.GoalPinSpecV2
def sameLocal : (a b : Local) → Option (PLift (a = b))
  | ⟨t, i⟩, ⟨u, j⟩ => do
    let ⟨ht⟩ ← sameExpr t u
    let ⟨hi⟩ ← sameBinder i j
    pure ⟨by cases ht; cases hi; rfl⟩
def sameLocals : (a b : List Local) → Option (PLift (a = b))
  | [], [] => some ⟨rfl⟩
  | a :: as, b :: bs => do
    let ⟨ha⟩ ← sameLocal a b
    let ⟨ht⟩ ← sameLocals as bs
    pure ⟨by cases ha; cases ht; rfl⟩
  | _, _ => none
def sameTask : (a b : Task) → Option (PLift (a = b))
  | ⟨ps, ls, active, e⟩, ⟨qs, ms, running, f⟩ => do
    if hp : ps = qs then
      if ha : active = running then
        let ⟨hl⟩ ← sameLocals ls ms
        let ⟨he⟩ ← sameExpr e f
        pure ⟨by cases hp; cases hl; cases ha; cases he; rfl⟩
      else none
    else none
structure CacheEntry (env : Environment) where
  fuel : Nat
  task : Task
  result : Except Error Tree
  proof : derive env fuel task = result
abbrev Cache (env : Environment) := Std.HashMap UInt64 (List (CacheEntry env))
abbrev Certified (env : Environment) (fuel : Nat) (task : Task) :=
  { result : Except Error Tree // derive env fuel task = result }

def taskHash (task : Task) : UInt64 :=
  let localsHash := task.locals.foldl
    (fun h l => mixHash h (mixHash (hash l.type) (hash l.info))) (hash task.params)
  mixHash (hash task.expression) (mixHash (hash task.active) localsHash)

def findEntry (env : Environment) (fuel : Nat) (task : Task) :
    List (CacheEntry env) → Option (Certified env fuel task)
  | [] => none
  | entry :: rest =>
    match sameTask task entry.task with
    | none => findEntry env fuel task rest
    | some ⟨ht⟩ =>
      if hf : fuel = entry.fuel then
        some ⟨entry.result, by cases hf; cases ht; exact entry.proof⟩
      else if hle : entry.fuel ≤ fuel then
        match hr : entry.result with
        | .error _ => findEntry env fuel task rest
        | .ok tree =>
          have old : derive env entry.fuel task = .ok tree := by
            rw [ht]
            exact entry.proof.trans hr
          some ⟨.ok tree, derive_mono env entry.fuel fuel task tree hle old⟩
      else findEntry env fuel task rest

def lookup (env : Environment) (fuel : Nat) (task : Task) (cache : Cache env) :
    Option (Certified env fuel task) :=
  findEntry env fuel task (cache.getD (taskHash task) [])

def save (env : Environment) (fuel : Nat) (task : Task) (value : Certified env fuel task)
    (cache : Cache env) : Cache env :=
  let key := taskHash task
  let entry : CacheEntry env := ⟨fuel, task, value.val, value.property⟩
  cache.insert key (entry :: cache.getD key [])

def deriveMemo (env : Environment) : (fuel : Nat) → (task : Task) →
    StateM (Cache env) (Certified env fuel task)
  | 0, task => pure ⟨.error .resource, rfl⟩
  | fuel + 1, task => do
    let cache ← get
    if let some value := lookup env (fuel + 1) task cache then
      return value
    let value ← match h : step env fuel task with
      | .error err =>
        pure ⟨.error err, by simp [derive, h, bind, Except.bind]⟩
      | .ok (lab, tasks) => do
        let rec children (tasks : List Task) : StateM (Cache env)
            { output : Except Error (List Tree) //
              collect (tasks.map (derive env fuel)) = output } := do
          match tasks with
          | [] => return ⟨.ok [], rfl⟩
          | t :: ts =>
            let a ← deriveMemo env fuel t
            match ha : a.val with
            | .error err =>
              return ⟨.error err, by simp [List.map_cons, a.property, ha, collect]⟩
            | .ok tree =>
              let b ← children ts
              return ⟨b.val.map (tree :: ·), by
                simp [List.map_cons, a.property, ha, collect, b.property]⟩
        let output ← children tasks
        let result := output.val.map (fun trees => Tree.node lab trees)
        pure ⟨result, by
          cases hc : output.val <;>
            simp [derive, h, output.property, result, bind, Except.bind, Except.map,
              Pure.pure, Except.pure, hc]⟩
    modify (save env (fuel + 1) task value)
    return value


/-- Inspect the actual goal declaration before traversing its statement. -/
def recompute (env : Environment) (fuel : Nat) (name : Lean.Name) : Except Error Tree := do
  let (label, task) ← root env name
  let certified := ((deriveMemo env fuel task).run {}).1
  let body ← certified.val
  pure (.node label [body])

/-- Digest the canonical graph; malformed encodings fail closed. -/
def digest (env : Environment) (fuel : Nat) (name : Lean.Name) : Except Error (List Nat) := do
  let tree ← recompute env fuel name
  let some bytes := EncodingV2.encode tree | throw .unsupported
  pure (Solidity.Hashes.sha256 bytes)

/-- The executable traversal produces a derivation in the reference graph. -/
theorem derive_sound (env : Environment) (fuel : Nat) :
    ∀ task, Derives env fuel task (derive env fuel task) := by
  induction fuel with
  | zero =>
    intro task
    exact .exhausted
  | succ fuel ih =>
    intro task
    cases h : step env fuel task with
    | error err =>
      simpa [derive, h] using (Derives.failed h)
    | ok pair =>
      rcases pair with ⟨lab, tasks⟩
      have children : DerivesList env fuel tasks (tasks.map (derive env fuel)) := by
        clear h
        induction tasks with
        | nil => exact .nil
        | cons t ts hts => exact .cons (ih t) hts
      cases hc : collect (tasks.map (derive env fuel)) with
      | error err =>
        simpa [derive, h, hc, Except.bind, Except.map, bind, Functor.map] using
          (Derives.childFailed h children hc)
      | ok trees =>
        simpa [derive, h, hc, Except.bind, Except.map, bind, Functor.map] using
          (Derives.node h children hc)

/-- Every reference derivation agrees with the executable traversal. -/
theorem derive_complete (env : Environment) (fuel : Nat) :
    ∀ {task output}, Derives env fuel task output → derive env fuel task = output := by
  induction fuel with
  | zero =>
    intro task output h
    cases h
    rfl
  | succ fuel ih =>
    have list_complete : ∀ {tasks outputs}, DerivesList env fuel tasks outputs →
        tasks.map (derive env fuel) = outputs := by
      intro tasks outputs h
      induction tasks generalizing outputs with
      | nil => cases h; rfl
      | cons t ts tail =>
        cases h with
        | cons first rest => simp only [List.map_cons, ih first, tail rest]
    intro task output h
    cases h with
    | failed hs => simp [derive, hs, bind, Except.bind]
    | node hs children hc =>
      have he := list_complete children
      simp [derive, hs, he, hc, Except.bind, bind, Pure.pure, Except.pure]
    | childFailed hs children hc =>
      have he := list_complete children
      simp [derive, hs, he, hc, Except.bind, bind]

/-- Root recomputation agrees exactly with the reference graph. -/
theorem recompute_exact (env : Environment) (fuel : Nat) (name : Lean.Name)
    (output : Except Error Tree) : recompute env fuel name = output ↔ RootGraph env fuel name output := by
  unfold RootGraph
  cases h : root env name with
  | error err => simp [recompute, h, bind, Except.bind, eq_comm]
  | ok pair =>
    rcases pair with ⟨lab, task⟩
    have memoEq : ((deriveMemo env fuel task).run {}).1.val = derive env fuel task :=
      ((deriveMemo env fuel task).run {}).1.property.symm
    constructor
    · intro he
      refine ⟨derive env fuel task, derive_sound env fuel task, ?_⟩
      simpa [recompute, h, memoEq, bind, Functor.map, Except.bind, Except.map,
        Pure.pure, Except.pure] using he.symm
    · rintro ⟨body, hd, he⟩
      have eq := derive_complete env fuel hd
      simpa [recompute, h, memoEq, eq, bind, Functor.map, Except.bind, Except.map,
        Pure.pure, Except.pure] using he.symm

/-- The reference traversal has at most one result for fixed fuel. -/
theorem graph_deterministic (env : Environment) (fuel : Nat) (name : Lean.Name)
    (a b : Except Error Tree) (ha : RootGraph env fuel name a)
    (hb : RootGraph env fuel name b) : a = b :=
  ((recompute_exact env fuel name a).2 ha).symm.trans
    ((recompute_exact env fuel name b).2 hb)

/-- Pointwise reference computations have unique output lists. -/
theorem graph_outputs_unique (env : Environment) (fuel : Nat)
    (pins : List Solidity.Goals.GoalPinSpec.Pin) (xs ys : List (Except Error Tree))
    (hx : Pointwise (fun p => RootGraph env fuel p.goal) pins xs)
    (hy : Pointwise (fun p => RootGraph env fuel p.goal) pins ys) : xs = ys := by
  induction hx generalizing ys with
  | nil => cases hy; rfl
  | cons h tail ih =>
    cases hy with
    | cons h' tail' =>
      have he := graph_deterministic env fuel _ _ _ h h'
      cases he
      rw [ih _ tail']

/-- A successful reference graph remains valid at every larger fuel bound. -/
theorem graph_budget_adequate (env : Environment) (name : Lean.Name) (fuel : Nat)
    (tree : Tree) (h : RootGraph env fuel name (.ok tree)) (larger : Nat)
    (hle : fuel ≤ larger) : RootGraph env larger name (.ok tree) := by
  unfold RootGraph at h ⊢
  cases hr : root env name with
  | error err => simp [hr] at h
  | ok pair =>
    rcases pair with ⟨lab, task⟩
    simp only [hr] at h ⊢
    obtain ⟨body, hd, he⟩ := h
    cases body with
    | error err => simp [Except.map] at he
    | ok bodyTree =>
      have old : derive env fuel task = .ok bodyTree := derive_complete env fuel hd
      have new := derive_mono env fuel larger task bodyTree hle old
      refine ⟨.ok bodyTree, ?_, he⟩
      rw [← new]
      exact derive_sound env larger task

/-- Every supported root has a bound after which recomputation succeeds. -/
theorem supported_complete (env : Environment) (name : Lean.Name)
    (h : Supported env name) :
    ∃ bound tree, ∀ fuel, bound ≤ fuel → recompute env fuel name = .ok tree := by
  obtain ⟨bound, tree, graph⟩ := h
  refine ⟨bound, tree, fun fuel hle => ?_⟩
  exact (recompute_exact env fuel name (.ok tree)).2
    (graph_budget_adequate env name bound tree graph fuel hle)

/-- Equal digests identify input bytes only under the stated collision boundary. -/
theorem collision_boundary (a b : List Nat)
    (h : Solidity.Goals.GoalPinSpec.CollisionFreeOn a b)
    (digestEq : Solidity.Hashes.sha256 a = Solidity.Hashes.sha256 b) : a = b :=
  h digestEq

open Lean Elab Command

/-- Report the failure class without treating an incomplete traversal as a digest. -/
def errorLabel : Error → String
  | .definition _ => "definition"
  | .notProposition => "notProposition"
  | .invalidUniverse => "invalidUniverse"
  | .freeVariable => "freeVariable"
  | .metavariable => "metavariable"
  | .illScoped => "illScoped"
  | .illTyped => "illTyped"
  | .unsupported => "unsupported"
  | .resource => "resource"
  | .recursion => "recursion"
  | .interrupted => "interrupted"
  | .coverage _ => "coverage"
  | .duplicatePin => "duplicatePin"
  | .malformedPin => "malformedPin"
  | .malformedManifest => "malformedManifest"
  | .unknownGoal => "unknownGoal"
  | .missingPin => "missingPin"
  | .missingDecision => "missingDecision"
  | .decisionMismatch => "decisionMismatch"
  | .digestMismatch => "digestMismatch"

/-- Checked rows are retained so the complete registry can be checked outward. -/
structure CheckedPin where
  goal : Lean.Name
  decision : String
  digest : List Nat
  deriving Inhabited

initialize pinExt : SimplePersistentEnvExtension CheckedPin (Array CheckedPin) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := Array.push
    addImportedFn := fun arrays => arrays.foldl (· ++ ·) #[] }

/-- Print a digest for a registered goal, for preparing a reviewed pin. -/
elab "#goal_pin_digest " id:ident " gp_fuel " fuel:num : command => do
  let name ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
  let env ← getEnv
  unless (Solidity.Goal.goalExt.getState env).any (·.decl == name) do
    throwError "goal pin: {name} is not a registered goal"
  match digest env fuel.getNat name with
  | .error err => throwError "goal pin: recomputation failed for {name}: {errorLabel err}"
  | .ok bytes => logInfo m!"{name}: {bytes}"

/-- Check one explicit goal/digest/decision triple against the current environment. -/
elab "#goal_pin " id:ident decision:str " gp_bytes " bytes:num+ " end " " gp_fuel " budget:num : command => do
  let name ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
  let env ← getEnv
  unless (Solidity.Goal.goalExt.getState env).any (·.decl == name) do
    throwError "goal pin: {name} is not a registered goal"
  let decisionId := decision.getString
  let some number := (String.mk (decisionId.toList.drop 1)).toNat?
    | throwError "goal pin: malformed decision identifier"
  unless decisionId == "H" ++ toString number do
    throwError "goal pin: malformed decision identifier"
  let expected := bytes.toList.map (·.getNat)
  unless expected.length == 32 && expected.all (· < 256) do
    throwError "goal pin: digest must contain 32 bytes"
  match digest env budget.getNat name with
  | .error err => throwError "goal pin: recomputation failed for {name}: {errorLabel err}"
  | .ok actual =>
    unless actual == expected do
      throwError "goal pin: digest mismatch for {name}"
    if (pinExt.getState env).any (·.goal == name) then
      throwError "goal pin: duplicate entry for {name}"
    modifyEnv (pinExt.addEntry · ⟨name, decisionId, expected⟩)

/-- Fail if any finish-line component or proved roadmap goal is missing. -/
elab "#goal_pins_complete" : command => do
  let required ← liftTermElabM Solidity.Goals.GoalPinSpec.required
  let .ok names := required | throwError "goal pin: could not determine required coverage"
  let pins := pinExt.getState (← getEnv)
  let pinnedNames := pins.toList.map (·.goal)
  unless pinnedNames.eraseDups.length == pinnedNames.length do
    throwError "goal pin: duplicate entries in imported pin tables"
  for name in names do
    unless pins.any (·.goal == name) do
      throwError "goal pin: missing required entry for {name}"

end Solidity.GoalPins
