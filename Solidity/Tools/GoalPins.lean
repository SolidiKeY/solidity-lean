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

/-- Structural failures are incompatible with a clean issue list. -/
theorem first_issue_not_clean (issues : List (Error × Prop)) (err : Error)
    (h : FirstIssue issues err) : ¬ (∀ issue ∈ issues, ¬ issue.2) := by
  induction h with
  | here condition =>
    intro clean
    exact clean _ (List.mem_cons_self) condition
  | later _ rest ih =>
    intro clean
    apply ih
    intro issue member
    exact clean issue (by simp [member])

/-- The first structural issue is uniquely determined. -/
theorem first_issue_unique (issues : List (Error × Prop)) (a b : Error)
    (ha : FirstIssue issues a) (hb : FirstIssue issues b) : a = b := by
  induction ha generalizing b with
  | here condition =>
    cases hb with
    | here _ => rfl
    | later notCondition _ => exact False.elim (notCondition condition)
  | later notCondition rest ih =>
    cases hb with
    | here condition => exact False.elim (notCondition condition)
    | later _ other => exact ih _ other

/-- Matching pin digests requires an encoding for every corresponding tree. -/
theorem matches_encodable (pins : List Solidity.Goals.GoalPinSpec.Pin) (trees : List Tree)
    (h : Matches pins trees) : Encodable trees := by
  intro tree member
  induction h with
  | nil => simp at member
  | cons first rest ih =>
    simp only [List.mem_cons] at member
    rcases member with rfl | member
    · obtain ⟨bytes, encoded, _⟩ := first
      exact ⟨bytes, encoded⟩
    · exact ih member

/-- A named relation exposes the environment and budget for output comparison. -/
def GraphOutputs (env : Environment) (fuel : Nat)
    (pins : List Solidity.Goals.GoalPinSpec.Pin) (outputs : List (Except Error Tree)) : Prop :=
  Pointwise (fun p => RootGraph env fuel p.goal) pins outputs

theorem graphOutputs_def (env : Environment) (fuel : Nat)
    (pins : List Solidity.Goals.GoalPinSpec.Pin) (outputs : List (Except Error Tree)) :
    GraphOutputs env fuel pins outputs ↔
      Pointwise (fun p => RootGraph env fuel p.goal) pins outputs := Iff.rfl

theorem graphOutputs_unique (env : Environment) (fuel : Nat)
    (pins : List Solidity.Goals.GoalPinSpec.Pin) (xs ys : List (Except Error Tree))
    (hx : GraphOutputs env fuel pins xs) (hy : GraphOutputs env fuel pins ys) : xs = ys :=
  graph_outputs_unique env fuel pins xs ys hx hy

local grind_pattern graphOutputs_unique => GraphOutputs env fuel pins xs, GraphOutputs env fuel pins ys

/-- The reference checker has a unique result for a fixed snapshot and budget. -/
theorem check_graph_deterministic (s : Snapshot) (m : Manifest)
    (pins : List Solidity.Goals.GoalPinSpec.Pin) (fuel : Nat) (a b : Except Error Unit)
    (ha : CheckGraph s m pins fuel a) (hb : CheckGraph s m pins fuel b) : a = b := by
  cases ha <;> cases hb <;> simp_all <;>
    simp only [← graphOutputs_def] at * <;>
    grind [first_issue_unique, first_issue_not_clean, matches_encodable, Clean]

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

open Lean Solidity.Goals.GoalPinSpec Solidity.Goals.GoalPinSpecV2 Solidity.GoalPins

namespace Draft
/-- Parse the decimal suffix of a decision identifier without accepting empty or non-digit text. -/
def parseDecision (text : String) : Option Nat :=
  match text.toList with
  | 'H' :: digits =>
    if digits.isEmpty || !(digits.all Char.isDigit) then none
    else some (digits.foldl (fun n c => n * 10 + (c.toNat - '0'.toNat)) 0)
  | _ => none

instance (p : Pin) : Decidable p.WellFormed := by
  unfold Pin.WellFormed
  infer_instance
instance (pins : List Pin) : Decidable (Unique pins) := by
  unfold Unique
  infer_instance
instance (required : List Lean.Name) (pins : List Pin) : Decidable (Covers required pins) := by
  unfold Covers
  infer_instance
instance (m : Manifest) : Decidable m.WellFormed := by
  unfold Manifest.WellFormed
  infer_instance
instance (m : Manifest) (pins : List Pin) : Decidable (AuthorizedTriples m pins) := by
  unfold AuthorizedTriples
  infer_instance

def structural (s : Snapshot) (m : Manifest) (pins : List Pin) : Except Error Unit :=
  if ¬ Unique pins then .error .duplicatePin
  else if ∃ p ∈ pins, ¬ p.WellFormed then .error .malformedPin
  else if ¬ m.WellFormed then .error .malformedManifest
  else if ∃ p ∈ pins, p.goal ∉ registryNames s then .error .unknownGoal
  else if ¬ Covers s.requiredNames pins then .error .missingPin
  else if ∃ p ∈ pins, ¬ ∃ a ∈ m.records, a.pin.goal = p.goal then .error .missingDecision
  else if ¬ AuthorizedTriples m pins then .error .decisionMismatch
  else .ok ()

theorem structural_ok (s : Snapshot) (m : Manifest) (pins : List Pin) :
    structural s m pins = .ok () ↔ Clean s m pins := by
  unfold structural
  repeat' (split <;> simp_all [Clean, issues])
  all_goals grind

theorem firstIssue_cons_iff (label : Error) (p : Prop) (rest : List (Error × Prop)) (err : Error) :
    FirstIssue ((label, p) :: rest) err ↔ (label = err ∧ p) ∨ (¬p ∧ FirstIssue rest err) := by
  constructor
  · intro h
    cases h with
    | here hp => exact Or.inl ⟨rfl, hp⟩
    | later hn ht => exact Or.inr ⟨hn, ht⟩
  · rintro (⟨rfl, hp⟩ | ⟨hn, ht⟩)
    · exact .here hp
    · exact .later hn ht

theorem structural_error_sound (s : Snapshot) (m : Manifest) (pins : List Pin)
    (err : Error) (h : structural s m pins = .error err) :
    FirstIssue (issues s m pins) err := by
  unfold structural at h
  unfold issues
  simp only [firstIssue_cons_iff]
  repeat' (split at h <;> simp_all)
  all_goals grind

theorem firstIssue_unique {xs : List (Error × Prop)} {a b : Error}
    (ha : FirstIssue xs a) (hb : FirstIssue xs b) : a = b := by
  induction ha generalizing b with
  | here condition =>
    cases hb with
    | here _ => rfl
    | later notCondition _ => exact False.elim (notCondition condition)
  | later notCondition _ ih =>
    cases hb with
    | here condition => exact False.elim (notCondition condition)
    | later _ other => exact ih other

theorem firstIssue_not_clean {xs : List (Error × Prop)} {err : Error}
    (h : FirstIssue xs err) (clean : ∀ issue ∈ xs, ¬issue.2) : False := by
  induction h with
  | @here condition err rest proof => exact clean (err, condition) (by simp) proof
  | later _ _ ih =>
    apply ih
    intro issue member
    exact clean issue (by simp [member])

theorem structural_error_exact (s : Snapshot) (m : Manifest) (pins : List Pin)
    (err : Error) : structural s m pins = .error err ↔ FirstIssue (issues s m pins) err := by
  constructor
  · exact structural_error_sound s m pins err
  · intro h
    cases hs : structural s m pins with
    | error actual =>
      have actualIssue := structural_error_sound s m pins actual hs
      have eq := firstIssue_unique actualIssue h
      cases eq
      rfl
    | ok value =>
      cases value
      have clean := (structural_ok s m pins).1 hs
      exact False.elim (firstIssue_not_clean h clean)

/-- Encoding remains a separate pass so its failures precede digest mismatches. -/
def encodeAll : List Tree → Except Error (List (List Nat))
  | [] => .ok []
  | tree :: trees => do
    let some bytes := EncodingV2.encode tree | throw .unsupported
    let rest ← encodeAll trees
    pure (bytes :: rest)

theorem encodeAll_sound : ∀ trees bytes,
    encodeAll trees = .ok bytes → Pointwise (fun tree bs => EncodingV2.encode tree = some bs) trees bytes := by
  intro trees
  induction trees with
  | nil =>
    intro bytes h
    simp [encodeAll] at h
    subst bytes
    exact .nil
  | cons tree trees ih =>
    intro bytes h
    cases he : EncodingV2.encode tree with
    | none => simp [encodeAll, he] at h
    | some bs =>
      cases hr : encodeAll trees with
      | error err => simp [encodeAll, he, hr, bind, Except.bind] at h
      | ok rest =>
        have eq : bs :: rest = bytes := by simpa [encodeAll, he, hr, bind, Except.bind, Pure.pure, Except.pure] using h
        subst bytes
        exact .cons he (ih rest hr)

theorem encodeAll_complete : ∀ {trees bytes},
    Pointwise (fun tree bs => EncodingV2.encode tree = some bs) trees bytes →
    encodeAll trees = .ok bytes := by
  intro trees bytes h
  induction h with
  | nil => rfl
  | cons he _ ih => simp [encodeAll, he, ih, bind, Except.bind, Pure.pure, Except.pure]

theorem encoded_encodable {trees : List Tree} {bytes : List (List Nat)}
    (h : Pointwise (fun tree bs => EncodingV2.encode tree = some bs) trees bytes) : Encodable trees := by
  intro tree ht
  induction h with
  | nil => simp at ht
  | @cons first bytes tail rest he _ ih =>
    simp only [List.mem_cons] at ht
    rcases ht with rfl | ht
    · exact ⟨bytes, he⟩
    · exact ih ht

theorem encodable_encoded (trees : List Tree) (h : Encodable trees) :
    ∃ bytes, Pointwise (fun tree bs => EncodingV2.encode tree = some bs) trees bytes := by
  induction trees with
  | nil => exact ⟨[], .nil⟩
  | cons tree trees ih =>
    have first := h tree (by simp)
    obtain ⟨bytes, he⟩ := first
    have tail : Encodable trees := by
      intro t ht
      exact h t (by simp [ht])
    obtain ⟨rest, hr⟩ := ih tail
    exact ⟨bytes :: rest, .cons he hr⟩

theorem encodeAll_error_kind (trees : List Tree) (err : Error)
    (h : encodeAll trees = .error err) : err = .unsupported := by
  induction trees with
  | nil => simp [encodeAll] at h
  | cons tree trees ih =>
    cases he : EncodingV2.encode tree with
    | none =>
      simp only [encodeAll, he] at h
      change Except.error Error.unsupported = Except.error err at h
      cases h
      rfl
    | some bytes =>
      cases hr : encodeAll trees with
      | error e =>
        have eq : e = err := by simpa [encodeAll, he, hr, bind, Except.bind] using h
        subst err
        exact ih hr
      | ok rest => simp [encodeAll, he, hr, bind, Except.bind, Pure.pure, Except.pure] at h

def matchBytes : List Pin → List (List Nat) → Bool
  | [], [] => true
  | p :: ps, bytes :: rest => (p.digest == Solidity.Hashes.sha256 bytes) && matchBytes ps rest
  | _, _ => false

theorem matchBytes_exact {trees : List Tree} {bytes : List (List Nat)}
    (h : Pointwise (fun tree bs => EncodingV2.encode tree = some bs) trees bytes) :
    ∀ pins, matchBytes pins bytes = true ↔ Matches pins trees := by
  induction h with
  | nil =>
    intro pins
    cases pins with
    | nil =>
      constructor
      · intro _; exact .nil
      · intro _; rfl
    | cons p ps =>
      constructor
      · intro h; contradiction
      · intro h; cases h
  | @cons tree bs trees rest he tail ih =>
    intro pins
    cases pins with
    | nil =>
      constructor
      · intro h; contradiction
      · intro h; cases h
    | cons p ps =>
      simp only [matchBytes, Bool.and_eq_true, beq_iff_eq]
      constructor
      · rintro ⟨equal, remaining⟩
        exact .cons ⟨bs, he, equal⟩ ((ih ps).1 remaining)
      · intro matched
        cases matched with
        | cons first remaining =>
          obtain ⟨other, ho, eq⟩ := first
          have same : other = bs := Option.some.inj (ho.symm.trans he)
          subst other
          exact ⟨eq, (ih ps).2 remaining⟩

/-- Check all reference trees before encoding, and all encodings before comparing. -/
def check (s : Snapshot) (fuel : Nat) (m : Manifest) (pins : List Pin) : Except Error Unit := do
  structural s m pins
  let trees ← collect (pins.map (fun p => recompute s.env fuel p.goal))
  let bytes ← encodeAll trees
  if matchBytes pins bytes then
    pure ()
  else
    throw .digestMismatch

theorem recompute_pointwise (s : Snapshot) (fuel : Nat) (pins : List Pin) :
    Pointwise (fun p => RootGraph s.env fuel p.goal) pins
      (pins.map fun p => recompute s.env fuel p.goal) := by
  induction pins with
  | nil => exact .nil
  | cons p ps ih =>
    exact .cons ((recompute_exact s.env fuel p.goal _).1 rfl) ih

theorem check_sound (s : Snapshot) (fuel : Nat) (m : Manifest) (pins : List Pin) :
    CheckGraph s m pins fuel (check s fuel m pins) := by
  let outputs := pins.map fun p => recompute s.env fuel p.goal
  have graphs : Pointwise (fun p => RootGraph s.env fuel p.goal) pins outputs :=
    recompute_pointwise s fuel pins
  cases hs : structural s m pins with
  | error err =>
    have issue := (structural_error_exact s m pins err).1 hs
    simpa [check, hs, bind, Except.bind] using (CheckGraph.structural issue)
  | ok value =>
    cases value
    have clean := (structural_ok s m pins).1 hs
    cases hc : collect outputs with
    | error err =>
      simp only [outputs] at hc
      simpa [check, hs, hc, bind, Except.bind] using
        (CheckGraph.computation clean graphs hc)
    | ok trees =>
      simp only [outputs] at hc
      cases he : encodeAll trees with
      | error err =>
        have eq := encodeAll_error_kind trees err he
        subst err
        have notEncodable : ¬ Encodable trees := by
          intro valid
          obtain ⟨bytes, encoded⟩ := encodable_encoded trees valid
          have good := encodeAll_complete encoded
          rw [he] at good
          cases good
        simpa [check, hs, hc, he, bind, Except.bind] using
          (CheckGraph.encoding clean graphs hc notEncodable)
      | ok bytes =>
        have encoded := encodeAll_sound trees bytes he
        have encodable := encoded_encodable encoded
        cases hm : matchBytes pins bytes with
        | false =>
          have notMatched : ¬ Matches pins trees := by
            intro matched
            have good := (matchBytes_exact encoded pins).2 matched
            rw [hm] at good
            cases good
          simpa [check, hs, hc, he, hm, bind, Except.bind] using
            (CheckGraph.mismatch clean graphs hc encodable notMatched)
        | true =>
          have matched := (matchBytes_exact encoded pins).1 hm
          simpa [check, hs, hc, he, hm, bind, Except.bind, Pure.pure, Except.pure] using
            (CheckGraph.success clean graphs hc matched)

theorem check_exact (s : Snapshot) (fuel : Nat) (m : Manifest) (pins : List Pin)
    (output : Except Error Unit) :
    check s fuel m pins = output ↔ CheckGraph s m pins fuel output := by
  constructor
  · intro h
    rw [← h]
    exact check_sound s fuel m pins
  · intro h
    exact check_graph_deterministic s m pins fuel _ _ (check_sound s fuel m pins) h

theorem witnesses_bound (s : Snapshot) (pins : List Pin)
    (witnesses : ∀ p ∈ pins, ∃ fuel tree bytes,
      RootGraph s.env fuel p.goal (.ok tree) ∧ EncodingV2.encode tree = some bytes ∧
        p.digest = Solidity.Hashes.sha256 bytes) :
    ∃ bound trees, Matches pins trees ∧ ∀ fuel, bound ≤ fuel →
      Pointwise (fun p tree => RootGraph s.env fuel p.goal (.ok tree)) pins trees := by
  induction pins with
  | nil =>
    exact ⟨0, [], .nil, fun _ _ => .nil⟩
  | cons p pins ih =>
    obtain ⟨firstFuel, tree, bytes, graph, encoding, digest⟩ := witnesses p (by simp)
    have restWitnesses : ∀ q ∈ pins, ∃ fuel tree bytes,
        RootGraph s.env fuel q.goal (.ok tree) ∧ EncodingV2.encode tree = some bytes ∧
          q.digest = Solidity.Hashes.sha256 bytes := by
      intro q hq
      exact witnesses q (by simp [hq])
    obtain ⟨restFuel, trees, matched, restGraphs⟩ := ih restWitnesses
    refine ⟨max firstFuel restFuel, tree :: trees, .cons ⟨bytes, encoding, digest⟩ matched, ?_⟩
    intro fuel hf
    have firstLe : firstFuel ≤ fuel := Nat.le_trans (Nat.le_max_left ..) hf
    have restLe : restFuel ≤ fuel := Nat.le_trans (Nat.le_max_right ..) hf
    exact .cons (graph_budget_adequate s.env p.goal firstFuel tree graph fuel firstLe)
      (restGraphs fuel restLe)

theorem lifted_graphs (s : Snapshot) (fuel : Nat) {pins : List Pin} {trees : List Tree}
    (graphs : Pointwise (fun p tree => RootGraph s.env fuel p.goal (.ok tree)) pins trees) :
    Pointwise (fun p => RootGraph s.env fuel p.goal) pins (trees.map Except.ok) := by
  induction graphs with
  | nil => exact .nil
  | cons first _ ih => exact .cons first ih

theorem collect_oks (trees : List Tree) : collect (trees.map Except.ok) = .ok trees := by
  induction trees with
  | nil => rfl
  | cons tree trees ih => simp [collect, ih, Except.map]

theorem correct_pins_complete (s : Snapshot) (m : Manifest) (pins : List Pin)
    (correct : CorrectPins s m pins) :
    ∃ bound, ∀ fuel, bound ≤ fuel → check s fuel m pins = .ok () := by
  obtain ⟨clean, witnesses⟩ := correct
  obtain ⟨bound, trees, matched, graphs⟩ := witnesses_bound s pins witnesses
  refine ⟨bound, fun fuel hf => ?_⟩
  exact (check_exact s fuel m pins (.ok ())).2
    (.success clean (lifted_graphs s fuel (graphs fuel hf)) (collect_oks trees) matched)

/-- Draft row decoder; completeness against every canonical decision remains to be proved. -/
def decodeRow (row : RawPin) : Except Error Pin := do
  let some number := parseDecision row.decisionId
    | throw .malformedPin
  let pin : Pin := ⟨row.goal, row.digest, number⟩
  if row.decisionId = pin.decisionId ∧ pin.WellFormed then pure pin
  else throw .malformedPin

def decode : List RawPin → Except Error (List Pin)
  | [] => .ok []
  | row :: rows => do
    let pin ← decodeRow row
    let rest ← decode rows
    pure (pin :: rest)

theorem decodeRow_sound (row : RawPin) (pin : Pin)
    (h : decodeRow row = .ok pin) : RowOf row pin := by
  cases hs : parseDecision row.decisionId with
  | none =>
    simp only [decodeRow, hs] at h
    change Except.error Error.malformedPin = Except.ok pin at h
    cases h
  | some number =>
    simp only [decodeRow, hs] at h
    split at h
    · rename_i valid
      have eq : (⟨row.goal, row.digest, number⟩ : Pin) = pin := by
        simpa [Pure.pure, Except.pure] using h
      subst pin
      exact ⟨rfl, rfl, valid.1, valid.2⟩
    · change Except.error Error.malformedPin = Except.ok pin at h
      cases h

theorem decode_sound : ∀ rows pins,
    decode rows = .ok pins → Pointwise RowOf rows pins := by
  intro rows
  induction rows with
  | nil =>
    intro pins h
    simp [decode] at h
    subst pins
    exact .nil
  | cons row rows ih =>
    intro pins h
    cases hr : decodeRow row with
    | error err => simp [decode, hr, bind, Except.bind] at h
    | ok pin =>
      cases hs : decode rows with
      | error err => simp [decode, hr, hs, bind, Except.bind] at h
      | ok rest =>
        have eq : pin :: rest = pins := by
          simpa [decode, hr, hs, bind, Except.bind, Pure.pure, Except.pure] using h
        subst pins
        exact .cons (decodeRow_sound row pin hr) (ih rest hs)

/-- Upstream decimal parser property required to finish decoder completeness. -/
def DecisionRoundTrip : Prop := ∀ number : Nat,
  parseDecision ("H" ++ toString number) = some number

theorem decodeRow_complete (roundtrip : DecisionRoundTrip) {row : RawPin} {pin : Pin}
    (h : RowOf row pin) : decodeRow row = .ok pin := by
  cases row with
  | mk goal digest decisionId =>
    cases pin with
    | mk pinGoal pinDigest number =>
      simp only [RowOf] at h
      obtain ⟨hgoal, hdigest, hid, hwell⟩ := h
      cases hgoal
      cases hdigest
      cases hid
      simp [decodeRow, Pin.decisionId, roundtrip number, hwell, Pure.pure, Except.pure]


end Draft

open Lean Solidity.Goals.GoalPinSpec Solidity.Goals

namespace Draft

theorem level_encodable (params : List Lean.Name) (level : Lean.Level)
    (h : validLevel params level = true) : ∃ bytes, Encoding.level level = some bytes := by
  induction level with
  | zero => exact ⟨_, rfl⟩
  | succ level ih =>
    obtain ⟨bytes, hb⟩ := ih h
    exact ⟨[2] ++ bytes, by simp [Encoding.level, hb]⟩
  | max a b ihA ihB =>
    simp only [validLevel, Bool.and_eq_true] at h
    obtain ⟨aBytes, ha⟩ := ihA h.1
    obtain ⟨bBytes, hb⟩ := ihB h.2
    exact ⟨[3] ++ aBytes ++ bBytes, by simp [Encoding.level, ha, hb]⟩
  | imax a b ihA ihB =>
    simp only [validLevel, Bool.and_eq_true] at h
    obtain ⟨aBytes, ha⟩ := ihA h.1
    obtain ⟨bBytes, hb⟩ := ihB h.2
    exact ⟨[4] ++ aBytes ++ bBytes, by simp [Encoding.level, ha, hb]⟩
  | param _ => exact ⟨_, rfl⟩
  | mvar _ => simp [validLevel] at h

theorem levels_encodable (params : List Lean.Name) (levels : List Lean.Level)
    (h : levels.all (validLevel params) = true) : ∃ bytes, Encoding.levels levels = some bytes := by
  induction levels with
  | nil => exact ⟨_, rfl⟩
  | cons level levels ih =>
    simp only [List.all_cons, Bool.and_eq_true] at h
    obtain ⟨a, ha⟩ := level_encodable params level h.1
    obtain ⟨b, hb⟩ := ih h.2
    exact ⟨[1] ++ a ++ b, by simp [Encoding.levels, ha, hb]⟩

theorem term_encodable (params : List Lean.Name) (term : Canonical) :
    ∀ depth, term.sourceScoped params depth = true → ∃ bytes, Encoding.term depth term = some bytes := by
  induction term with
  | bvar index =>
    intro depth h
    simp only [Canonical.sourceScoped, decide_eq_true_eq] at h
    exact ⟨[1] ++ Encoding.number index, by simp [Encoding.term, h]⟩
  | sort level =>
    intro depth h
    obtain ⟨bytes, hb⟩ := level_encodable params level h
    exact ⟨[2] ++ bytes, by simp [Encoding.term, hb]⟩
  | const name levels =>
    intro depth h
    obtain ⟨bytes, hb⟩ := levels_encodable params levels h
    exact ⟨[3] ++ Encoding.name name ++ bytes, by simp [Encoding.term, hb]⟩
  | app f a ihF ihA =>
    intro depth h
    simp only [Canonical.sourceScoped, Bool.and_eq_true] at h
    obtain ⟨fBytes, hf⟩ := ihF depth h.1
    obtain ⟨aBytes, ha⟩ := ihA depth h.2
    exact ⟨[4] ++ fBytes ++ aBytes, by simp [Encoding.term, hf, ha]⟩
  | lam ty body info ihT ihB =>
    intro depth h
    simp only [Canonical.sourceScoped, Bool.and_eq_true] at h
    obtain ⟨tBytes, ht⟩ := ihT depth h.1
    obtain ⟨bBytes, hb⟩ := ihB (depth+1) h.2
    exact ⟨[5, Encoding.binder info] ++ tBytes ++ bBytes, by simp [Encoding.term, ht, hb]⟩
  | forallE ty body info ihT ihB =>
    intro depth h
    simp only [Canonical.sourceScoped, Bool.and_eq_true] at h
    obtain ⟨tBytes, ht⟩ := ihT depth h.1
    obtain ⟨bBytes, hb⟩ := ihB (depth+1) h.2
    exact ⟨[6, Encoding.binder info] ++ tBytes ++ bBytes, by simp [Encoding.term, ht, hb]⟩
  | letE ty value body nondep ihT ihV ihB =>
    intro depth h
    simp only [Canonical.sourceScoped, Bool.and_eq_true] at h
    obtain ⟨tBytes, ht⟩ := ihT depth h.1.1
    obtain ⟨vBytes, hv⟩ := ihV depth h.1.2
    obtain ⟨bBytes, hb⟩ := ihB (depth+1) h.2
    exact ⟨[7, if nondep then 1 else 0] ++ tBytes ++ vBytes ++ bBytes,
      by simp [Encoding.term, ht, hv, hb]⟩
  | natLit n => intro depth h; exact ⟨_, rfl⟩
  | strLit text => intro depth h; exact ⟨_, rfl⟩
  | proj name index target ih =>
    intro depth h
    obtain ⟨bytes, hb⟩ := ih depth h
    exact ⟨[10] ++ Encoding.name name ++ Encoding.number index ++ bytes,
      by simp [Encoding.term, hb]⟩
  | unfolded source spine body ihS ihP ihB =>
    intro depth h
    simp [Canonical.sourceScoped] at h

/-- A successful raw observation is scoped at its recorded local depth. -/
theorem raw_scoped (params : List Lean.Name) (depth : Nat) (expression : Expr)
    (term : Canonical) (h : GoalPinSpecV2.raw params depth expression = .ok term) :
    term.sourceScoped params depth = true := by
  cases hf : expression.hasFVar with
  | true => simp [GoalPinSpecV2.raw, hf, bind, Except.bind] at h
  | false =>
    cases hm : expression.hasMVar with
    | true => simp [GoalPinSpecV2.raw, hf, hm, bind, Except.bind, Pure.pure, Except.pure] at h
    | false =>
      cases hr : reify expression with
      | none => simp [GoalPinSpecV2.raw, hf, hm, hr, bind, Except.bind, Pure.pure, Except.pure] at h
      | some candidate =>
        cases hu : GoalPinSpecV2.universesValid params candidate with
        | false => simp [GoalPinSpecV2.raw, hf, hm, hr, hu, bind, Except.bind, Pure.pure, Except.pure] at h
        | true =>
          cases hs : candidate.sourceScoped params depth with
          | false => simp [GoalPinSpecV2.raw, hf, hm, hr, hu, hs, bind, Except.bind, Pure.pure, Except.pure] at h
          | true =>
            have eq : candidate = term := by
              simpa [GoalPinSpecV2.raw, hf, hm, hr, hu, hs, bind, Except.bind,
                Pure.pure, Except.pure] using h
            subst candidate
            exact hs

theorem scoped_mono (params : List Lean.Name) (term : Canonical) :
    ∀ small large, small ≤ large → term.sourceScoped params small = true →
      term.sourceScoped params large = true := by
  induction term with
  | bvar index =>
    intro small large hle h
    simp only [Canonical.sourceScoped, decide_eq_true_eq] at h ⊢
    omega
  | sort level => intro small large hle h; exact h
  | const name levels => intro small large hle h; exact h
  | app f a ihF ihA =>
    intro small large hle h
    simp only [Canonical.sourceScoped, Bool.and_eq_true] at h ⊢
    exact ⟨ihF small large hle h.1, ihA small large hle h.2⟩
  | lam ty body info ihT ihB =>
    intro small large hle h
    simp only [Canonical.sourceScoped, Bool.and_eq_true] at h ⊢
    exact ⟨ihT small large hle h.1, ihB (small+1) (large+1) (by omega) h.2⟩
  | forallE ty body info ihT ihB =>
    intro small large hle h
    simp only [Canonical.sourceScoped, Bool.and_eq_true] at h ⊢
    exact ⟨ihT small large hle h.1, ihB (small+1) (large+1) (by omega) h.2⟩
  | letE ty value body nondep ihT ihV ihB =>
    intro small large hle h
    simp only [Canonical.sourceScoped, Bool.and_eq_true] at h ⊢
    exact ⟨⟨ihT small large hle h.1.1, ihV small large hle h.1.2⟩,
      ihB (small+1) (large+1) (by omega) h.2⟩
  | natLit n => intro small large hle h; rfl
  | strLit text => intro small large hle h; rfl
  | proj name index target ih => intro small large hle h; exact ih small large hle h
  | unfolded source spine body ihS ihP ihB =>
    intro small large hle h
    simp [Canonical.sourceScoped] at h

/-- A raw observation remains encodable under any larger binder depth. -/
theorem raw_encodable (params : List Lean.Name) (small large : Nat) (expression : Expr)
    (term : Canonical) (hle : small ≤ large)
    (h : GoalPinSpecV2.raw params small expression = .ok term) :
    ∃ bytes, Encoding.term large term = some bytes :=
  term_encodable params term large (scoped_mono params term small large hle
    (raw_scoped params small expression term h))

theorem listOf_encodable {A : Type} (encode : A → Option (List Nat)) (items : List A)
    (h : ∀ item ∈ items, ∃ bytes, encode item = some bytes) :
    ∃ bytes, GoalPinSpecV2.EncodingV2.listOf encode items = some bytes := by
  induction items with
  | nil => exact ⟨[0], rfl⟩
  | cons item items ih =>
    obtain ⟨first, hf⟩ := h item (by simp)
    have tail : ∀ item ∈ items, ∃ bytes, encode item = some bytes := by
      intro item hm
      exact h item (by simp [hm])
    obtain ⟨rest, hr⟩ := ih tail
    exact ⟨[1] ++ Encoding.number first.length ++ first ++ rest,
      by simp [GoalPinSpecV2.EncodingV2.listOf, hf, hr]⟩

theorem label_encodable (lab : GoalPinSpecV2.Label)
    (h : ∀ term ∈ lab.rawSyntax,
      ∃ bytes, Encoding.term ((lab.numbers[1]?).getD 0) term = some bytes) :
    ∃ bytes, GoalPinSpecV2.EncodingV2.labelBytes lab = some bytes := by
  obtain ⟨names, hn⟩ := listOf_encodable (fun n => some (Encoding.name n)) lab.names
    (by intro n hm; exact ⟨_, rfl⟩)
  obtain ⟨numbers, hi⟩ := listOf_encodable (fun n => some (Encoding.number n)) lab.numbers
    (by intro n hm; exact ⟨_, rfl⟩)
  obtain ⟨terms, ht⟩ := listOf_encodable (Encoding.term ((lab.numbers[1]?).getD 0)) lab.rawSyntax h
  exact ⟨Encoding.number lab.tag ++ names ++ numbers ++ terms,
    by simp [GoalPinSpecV2.EncodingV2.labelBytes, hn, hi, ht]⟩

def AllLabels (tree : GoalPinSpecV2.Tree) : Prop :=
  ∀ lab children, GoalPinSpecV2.Subtree (.node lab children) tree →
    ∃ bytes, GoalPinSpecV2.EncodingV2.labelBytes lab = some bytes

theorem tree_bytes_from_labels (tree : GoalPinSpecV2.Tree) (good : AllLabels tree) :
    ∃ bytes, GoalPinSpecV2.EncodingV2.treeBytes tree = some bytes := by
  apply GoalPinSpecV2.Tree.rec
    (motive_1 := fun tree => AllLabels tree →
      ∃ bytes, GoalPinSpecV2.EncodingV2.treeBytes tree = some bytes)
    (motive_2 := fun trees => (∀ tree ∈ trees, AllLabels tree) →
      ∃ bytes, GoalPinSpecV2.EncodingV2.forestBytes trees = some bytes)
    ?_ ?_ ?_ tree good
  · intro lab children ih all
    obtain ⟨first, hf⟩ := all lab children .root
    have childGood : ∀ tree ∈ children, AllLabels tree := by
      intro child member inner descendants subtree
      exact all inner descendants (.descend member subtree)
    obtain ⟨rest, hr⟩ := ih childGood
    exact ⟨Encoding.number first.length ++ first ++ rest,
      by simp [GoalPinSpecV2.EncodingV2.treeBytes, hf, hr]⟩
  · intro _
    exact ⟨[0], rfl⟩
  · intro head tail ihHead ihTail all
    have headGood := all head (by simp)
    have tailGood : ∀ tree ∈ tail, AllLabels tree := by
      intro tree member
      exact all tree (by simp [member])
    obtain ⟨first, hf⟩ := ihHead headGood
    obtain ⟨rest, hr⟩ := ihTail tailGood
    exact ⟨[1] ++ Encoding.number first.length ++ first ++ rest,
      by simp [GoalPinSpecV2.EncodingV2.forestBytes, hf, hr]⟩

theorem encode_from_labels (tree : GoalPinSpecV2.Tree) (good : AllLabels tree) :
    ∃ bytes, GoalPinSpecV2.EncodingV2.encode tree = some bytes := by
  obtain ⟨bytes, hb⟩ := tree_bytes_from_labels tree good
  exact ⟨[71, 80, 2, 0] ++ bytes, by simp [GoalPinSpecV2.EncodingV2.encode, hb]⟩

theorem label_good (t : GoalPinSpecV2.Task) (tag : Nat) (names : List Lean.Name)
    (numbers : List Nat) (extras : List Canonical) (lab : GoalPinSpecV2.Label)
    (extraGood : ∀ term ∈ extras, ∃ bytes, Encoding.term t.locals.length term = some bytes)
    (h : GoalPinSpecV2.label t tag names numbers extras = .ok lab) :
    ∃ bytes, GoalPinSpecV2.EncodingV2.labelBytes lab = some bytes := by
  cases hr : GoalPinSpecV2.raw t.params t.locals.length (GoalPinSpecV2.erase t.expression) with
  | error err => simp [GoalPinSpecV2.label, hr, bind, Except.bind] at h
  | ok source =>
    have eq : (⟨tag, t.params ++ names, t.params.length :: t.locals.length :: numbers,
        source :: extras⟩ : GoalPinSpecV2.Label) = lab := by
      simpa [GoalPinSpecV2.label, hr, bind, Except.bind, Pure.pure, Except.pure] using h
    subst lab
    apply label_encodable
    intro term member
    simp only [List.mem_cons] at member
    rcases member with rfl | member
    · simpa using raw_encodable t.params t.locals.length t.locals.length
        (GoalPinSpecV2.erase t.expression) term (Nat.le_refl _) hr
    · simpa using extraGood term member

theorem folded_good (t : GoalPinSpecV2.Task) (ci : ConstantInfo)
    (args : List GoalPinSpecV2.Task) (lab : GoalPinSpecV2.Label)
    (tasks : List GoalPinSpecV2.Task)
    (h : GoalPinSpecV2.folded t ci args = .ok (lab, tasks)) :
    ∃ bytes, GoalPinSpecV2.EncodingV2.labelBytes lab = some bytes := by
  cases hr : GoalPinSpecV2.raw ci.levelParams 0 ci.type with
  | error err => simp [GoalPinSpecV2.folded, hr, bind, Except.bind] at h
  | ok ty =>
    cases hl : GoalPinSpecV2.label t 1 (ci.name :: ci.levelParams) [ci.levelParams.length] [ty] with
    | error err => simp [GoalPinSpecV2.folded, hr, hl, bind, Except.bind] at h
    | ok found =>
      have pair : found = lab ∧ (args ++ if t.active.contains ci.name then [] else
          [GoalPinSpecV2.template t ci ci.type]) = tasks := by
        simpa [GoalPinSpecV2.folded, hr, hl, bind, Except.bind, Pure.pure, Except.pure] using h
      have eq : found = lab := pair.1
      subst found
      apply label_good t 1 (ci.name :: ci.levelParams) [ci.levelParams.length] [ty] lab
      · intro term member
        simp only [List.mem_singleton] at member
        subst term
        exact raw_encodable ci.levelParams 0 t.locals.length ci.type ty (Nat.zero_le _) hr
      · exact hl

theorem mapM_raw_good (params : List Lean.Name) (depth : Nat) :
    ∀ (expressions : List Expr) (terms : List Canonical),
      expressions.mapM (GoalPinSpecV2.raw params depth) = .ok terms →
      ∀ term ∈ terms, ∃ bytes, Encoding.term depth term = some bytes := by
  intro expressions
  induction expressions with
  | nil =>
    intro terms h term member
    simp [Pure.pure, Except.pure] at h
    subst terms
    simp at member
  | cons expression expressions ih =>
    intro terms h term member
    cases hr : GoalPinSpecV2.raw params depth expression with
    | error err => simp [List.mapM_cons, hr, bind, Except.bind] at h
    | ok first =>
      cases hs : expressions.mapM (GoalPinSpecV2.raw params depth) with
      | error err => simp [List.mapM_cons, hr, hs, bind, Except.bind] at h
      | ok rest =>
        have eq : first :: rest = terms := by
          simpa [List.mapM_cons, hr, hs, bind, Except.bind, Pure.pure, Except.pure] using h
        subst terms
        simp only [List.mem_cons] at member
        rcases member with rfl | member
        · exact raw_encodable params depth depth expression term (Nat.le_refl _) hr
        · exact ih rest hs term member

theorem signature_good (env : Environment) (t : GoalPinSpecV2.Task) (owner : InductiveVal)
    (levels : List Level) (args : List Expr) (name : Lean.Name) (sig : GoalPinSpecV2.Signature)
    (h : GoalPinSpecV2.signature env t owner levels args name = .ok sig) :
    (∃ bytes, Encoding.term t.locals.length sig.source = some bytes) ∧
    (∀ term ∈ sig.requestedIndices, ∃ bytes, Encoding.term t.locals.length term = some bytes) := by
  simp only [GoalPinSpecV2.signature, bind, Except.bind, Pure.pure, Except.pure] at h
  cases hc : env.toKernelEnv.find? name with
  | none =>
    simp [hc] at h
  | some ci =>
    simp only [hc] at h
    cases hu : ci.isUnsafe with
    | true => simp [hu] at h
    | false =>
      simp only [hu, Bool.false_eq_true, ↓reduceIte] at h
      cases hl : (ci.levelParams.length != levels.length) with
      | true => simp [hl] at h
      | false =>
        simp only [hl, Bool.false_eq_true, ↓reduceIte] at h
        cases hr : GoalPinSpecV2.raw ci.levelParams 0 ci.type with
        | error err => simp [hr] at h
        | ok source =>
          simp only [hr] at h
          cases hi : (args.drop owner.numParams |>.take owner.numIndices).mapM
              (GoalPinSpecV2.raw t.params t.locals.length) with
          | error err => simp [hi] at h
          | ok indices =>
            simp only [hi, Except.ok.injEq] at h
            cases h
            constructor
            · exact raw_encodable ci.levelParams 0 t.locals.length ci.type source (Nat.zero_le _) hr
            · exact mapM_raw_good t.params t.locals.length _ indices hi

theorem signatures_good (env : Environment) (t : GoalPinSpecV2.Task) (owner : InductiveVal)
    (levels : List Level) (args : List Expr) : ∀ (names : List Lean.Name) (sigs : List GoalPinSpecV2.Signature),
    names.mapM (GoalPinSpecV2.signature env t owner levels args) = .ok sigs →
    ∀ sig ∈ sigs,
      (∃ bytes, Encoding.term t.locals.length sig.source = some bytes) ∧
      (∀ term ∈ sig.requestedIndices, ∃ bytes, Encoding.term t.locals.length term = some bytes) := by
  intro names
  induction names with
  | nil =>
    intro sigs h sig member
    simp [Pure.pure, Except.pure] at h
    subst sigs
    simp at member
  | cons name names ih =>
    intro sigs h sig member
    cases hr : GoalPinSpecV2.signature env t owner levels args name with
    | error err => simp [List.mapM_cons, hr, bind, Except.bind] at h
    | ok first =>
      cases hs : names.mapM (GoalPinSpecV2.signature env t owner levels args) with
      | error err => simp [List.mapM_cons, hr, hs, bind, Except.bind] at h
      | ok rest =>
        have eq : first :: rest = sigs := by
          simpa [List.mapM_cons, hr, hs, bind, Except.bind, Pure.pure, Except.pure] using h
        subst sigs
        simp only [List.mem_cons] at member
        rcases member with rfl | member
        · exact signature_good env t owner levels args name sig hr
        · exact ih rest hs sig member

theorem signature_extras_good (t : GoalPinSpecV2.Task) (sigs : List GoalPinSpecV2.Signature)
    (good : ∀ sig ∈ sigs,
      (∃ bytes, Encoding.term t.locals.length sig.source = some bytes) ∧
      (∀ term ∈ sig.requestedIndices, ∃ bytes, Encoding.term t.locals.length term = some bytes)) :
    ∀ term ∈ sigs.map (·.source) ++ sigs.flatMap (·.requestedIndices),
      ∃ bytes, Encoding.term t.locals.length term = some bytes := by
  intro term member
  simp only [List.mem_append, List.mem_map, List.mem_flatMap] at member
  rcases member with ⟨sig, hm, rfl⟩ | ⟨sig, hm, ht⟩
  · exact (good sig hm).1
  · exact (good sig hm).2 term ht

theorem signature_label_good (t : GoalPinSpecV2.Task) (tag : Nat) (names : List Lean.Name)
    (numbers : List Nat) (params : List Lean.Name) (ty : Expr) (source : Canonical)
    (sigs : List GoalPinSpecV2.Signature) (lab : GoalPinSpecV2.Label)
    (rawType : GoalPinSpecV2.raw params 0 ty = .ok source)
    (good : ∀ sig ∈ sigs,
      (∃ bytes, Encoding.term t.locals.length sig.source = some bytes) ∧
      (∀ term ∈ sig.requestedIndices, ∃ bytes, Encoding.term t.locals.length term = some bytes))
    (h : GoalPinSpecV2.label t tag names numbers
      (source :: sigs.map (·.source) ++ sigs.flatMap (·.requestedIndices)) = .ok lab) :
    ∃ bytes, GoalPinSpecV2.EncodingV2.labelBytes lab = some bytes := by
  apply label_good t tag names numbers
    (source :: sigs.map (·.source) ++ sigs.flatMap (·.requestedIndices)) lab
  · intro term member
    change term ∈ source :: (sigs.map (·.source) ++ sigs.flatMap (·.requestedIndices)) at member
    simp only [List.mem_cons] at member
    rcases member with rfl | member
    · exact raw_encodable params 0 t.locals.length ty term (Nat.zero_le _) rawType
    · exact signature_extras_good t sigs good term member
  · exact h

theorem two_raw_label_good (t : GoalPinSpecV2.Task) (tag : Nat) (names : List Lean.Name)
    (numbers : List Nat) (params : List Lean.Name) (ty value : Expr) (source body : Canonical)
    (lab : GoalPinSpecV2.Label)
    (rawType : GoalPinSpecV2.raw params 0 ty = .ok source)
    (rawValue : GoalPinSpecV2.raw params 0 value = .ok body)
    (h : GoalPinSpecV2.label t tag names numbers [source, body] = .ok lab) :
    ∃ bytes, GoalPinSpecV2.EncodingV2.labelBytes lab = some bytes := by
  apply label_good t tag names numbers [source, body] lab
  · intro term member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact raw_encodable params 0 t.locals.length ty term (Nat.zero_le _) rawType
    · exact raw_encodable params 0 t.locals.length value term (Nat.zero_le _) rawValue
  · exact h

theorem one_raw_label_good (t : GoalPinSpecV2.Task) (tag : Nat) (names : List Lean.Name)
    (numbers : List Nat) (params : List Lean.Name) (ty : Expr) (source : Canonical)
    (lab : GoalPinSpecV2.Label)
    (rawType : GoalPinSpecV2.raw params 0 ty = .ok source)
    (h : GoalPinSpecV2.label t tag names numbers [source] = .ok lab) :
    ∃ bytes, GoalPinSpecV2.EncodingV2.labelBytes lab = some bytes := by
  apply label_good t tag names numbers [source] lab
  · intro term member
    simp only [List.mem_singleton] at member
    subst term
    exact raw_encodable params 0 t.locals.length ty source (Nat.zero_le _) rawType
  · exact h

theorem inspect_scoped (env : Environment) (name : Lean.Name) (d : Definition)
    (h : inspectIn env name = .ok d) :
    d.type.sourceScoped d.levelParams 0 = true ∧ d.value.sourceScoped d.levelParams 0 = true := by
  simp only [inspectIn, bind, Except.bind, Pure.pure, Except.pure] at h
  repeat' (split at h <;> try simp_all)
  all_goals cases h; assumption

theorem root_label_good (env : Environment) (name : Lean.Name)
    (lab : GoalPinSpecV2.Label) (task : GoalPinSpecV2.Task)
    (h : GoalPinSpecV2.root env name = .ok (lab, task)) :
    ∃ bytes, GoalPinSpecV2.EncodingV2.labelBytes lab = some bytes := by
  simp only [GoalPinSpecV2.root, bind, Except.bind, Pure.pure, Except.pure] at h
  cases hi : inspectIn env name with
  | error err => simp [hi, Except.mapError] at h
  | ok d =>
    have scopeProof := inspect_scoped env name d hi
    simp only [hi, Except.mapError] at h
    repeat' (split at h <;> try simp_all)
    obtain ⟨labelEq, _⟩ := h
    subst lab
    apply label_encodable
    intro term member
    change term ∈ [Canonical.const name (d.levelParams.map Level.param), d.type, d.value] at member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with first | second | third
    · subst term
      have paramsValid : (d.levelParams.map Level.param).all (validLevel d.levelParams) = true := by
        simp only [List.all_eq_true, List.mem_map]
        rintro x ⟨n, hn, rfl⟩
        simpa [validLevel] using hn
      exact term_encodable d.levelParams _ 0 paramsValid
    · subst term
      exact term_encodable d.levelParams d.type 0 scopeProof.1
    · subst term
      exact term_encodable d.levelParams d.value 0 scopeProof.2

theorem nonconst_label_good (env : Environment) (fuel : Nat) (t : GoalPinSpecV2.Task)
    (lab : GoalPinSpecV2.Label) (tasks : List GoalPinSpecV2.Task)
    (notConst : ∀ name levels, (GoalPinSpecV2.erase t.expression).getAppFn ≠ .const name levels)
    (h : GoalPinSpecV2.step env fuel t = .ok (lab, tasks)) :
    ∃ bytes, GoalPinSpecV2.EncodingV2.labelBytes lab = some bytes := by
  simp only [GoalPinSpecV2.step, bind, Except.bind, Pure.pure, Except.pure] at h
  repeat' (split at h <;> try simp_all)
  all_goals try (apply label_good t 0 [] [] [] lab <;> simp_all)

theorem const_def_label_good (env : Environment) (fuel : Nat) (t : GoalPinSpecV2.Task)
    (name : Lean.Name) (levels : List Level) (d : DefinitionVal)
    (lab : GoalPinSpecV2.Label) (tasks : List GoalPinSpecV2.Task)
    (head : (GoalPinSpecV2.erase t.expression).getAppFn = .const name levels)
    (found : env.toKernelEnv.find? name = some (.defnInfo d))
    (h : GoalPinSpecV2.step env fuel t = .ok (lab, tasks)) :
    ∃ bytes, GoalPinSpecV2.EncodingV2.labelBytes lab = some bytes := by
  simp only [GoalPinSpecV2.step, bind, Except.bind, Pure.pure, Except.pure, head, found] at h
  repeat' (split at h <;> try simp_all)
  all_goals first
    | solve | apply two_raw_label_good t _ _ _ d.levelParams d.type d.value _ _ lab <;> assumption
    | solve | apply folded_good t (.defnInfo d) _ lab tasks <;> assumption

theorem signatures_append_good (env : Environment) (t : GoalPinSpecV2.Task) (owner : InductiveVal)
    (levels : List Level) (args : List Expr) (first second : List Lean.Name)
    (sigs : List GoalPinSpecV2.Signature)
    (h : (do
      let left ← first.mapM (GoalPinSpecV2.signature env t owner levels args)
      (left ++ ·) <$> second.mapM (GoalPinSpecV2.signature env t owner levels args)) = .ok sigs) :
    ∀ sig ∈ sigs,
      (∃ bytes, Encoding.term t.locals.length sig.source = some bytes) ∧
      (∀ term ∈ sig.requestedIndices, ∃ bytes, Encoding.term t.locals.length term = some bytes) := by
  apply signatures_good env t owner levels args (first ++ second) sigs
  simpa only [List.mapM_append, bind, Except.bind, Functor.map, Except.map, Pure.pure, Except.pure] using h

theorem const_induct_label_good (env : Environment) (fuel : Nat) (t : GoalPinSpecV2.Task)
    (name : Lean.Name) (levels : List Level) (d : InductiveVal)
    (lab : GoalPinSpecV2.Label) (tasks : List GoalPinSpecV2.Task)
    (head : (GoalPinSpecV2.erase t.expression).getAppFn = .const name levels)
    (found : env.toKernelEnv.find? name = some (.inductInfo d))
    (h : GoalPinSpecV2.step env fuel t = .ok (lab, tasks)) :
    ∃ bytes, GoalPinSpecV2.EncodingV2.labelBytes lab = some bytes := by
  simp only [GoalPinSpecV2.step, bind, Except.bind, Pure.pure, Except.pure, head, found] at h
  repeat' (split at h <;> try simp_all)
  all_goals try (first
    | solve | apply one_raw_label_good t _ _ _ d.levelParams d.type _ lab <;> assumption
    | solve | apply folded_good t (.inductInfo d) _ lab tasks <;> assumption)
  all_goals
    refine signature_label_good t ?_ ?_ ?_ d.levelParams d.type ?_ ?_ lab ?_ ?_ ?_
    rotate_left 7
    · assumption
    · assumption
    · refine signatures_append_good env { t with active := name :: t.active } d levels
        (GoalPinSpecV2.erase t.expression).getAppArgs.toList ?_ ?_ _ ?_
      rotate_left 2
      · assumption

theorem const_other_label_good (env : Environment) (fuel : Nat) (t : GoalPinSpecV2.Task)
    (name : Lean.Name) (levels : List Level) (ci : ConstantInfo)
    (lab : GoalPinSpecV2.Label) (tasks : List GoalPinSpecV2.Task)
    (head : (GoalPinSpecV2.erase t.expression).getAppFn = .const name levels)
    (found : env.toKernelEnv.find? name = some ci)
    (notDef : ∀ d, ci ≠ .defnInfo d)
    (notInduct : ∀ d, ci ≠ .inductInfo d)
    (h : GoalPinSpecV2.step env fuel t = .ok (lab, tasks)) :
    ∃ bytes, GoalPinSpecV2.EncodingV2.labelBytes lab = some bytes := by
  cases ci <;> simp_all
  all_goals
    simp only [GoalPinSpecV2.step, bind, Except.bind, Pure.pure, Except.pure, head, found] at h
    repeat' (split at h <;> try simp_all)
    all_goals
      refine folded_good t ?_ ?_ lab tasks ?_
      rotate_left 2
      assumption

theorem step_label_good (env : Environment) (fuel : Nat) (t : GoalPinSpecV2.Task)
    (lab : GoalPinSpecV2.Label) (tasks : List GoalPinSpecV2.Task)
    (h : GoalPinSpecV2.step env fuel t = .ok (lab, tasks)) :
    ∃ bytes, GoalPinSpecV2.EncodingV2.labelBytes lab = some bytes := by
  by_cases isConst : ∃ name levels, (GoalPinSpecV2.erase t.expression).getAppFn = .const name levels
  · obtain ⟨name, levels, head⟩ := isConst
    cases found : env.toKernelEnv.find? name with
    | none =>
      simp only [GoalPinSpecV2.step, bind, Except.bind, head, found] at h
      repeat' (split at h <;> try simp_all)
    | some ci =>
      by_cases isDef : ∃ d, ci = .defnInfo d
      · obtain ⟨d, rfl⟩ := isDef
        exact const_def_label_good env fuel t name levels d lab tasks head found h
      · by_cases isInduct : ∃ d, ci = .inductInfo d
        · obtain ⟨d, rfl⟩ := isInduct
          exact const_induct_label_good env fuel t name levels d lab tasks head found h
        · have notDef : ∀ d, ci ≠ .defnInfo d := by
            intro d eq; exact isDef ⟨d, eq⟩
          have notInduct : ∀ d, ci ≠ .inductInfo d := by
            intro d eq; exact isInduct ⟨d, eq⟩
          exact const_other_label_good env fuel t name levels ci lab tasks head found notDef notInduct h
  · apply nonconst_label_good env fuel t lab tasks
    · intro name levels head
      exact isConst ⟨name, levels, head⟩
    · exact h

theorem collect_mem : ∀ (values : List (Except GoalPinSpecV2.Error GoalPinSpecV2.Tree)) trees,
    GoalPinSpecV2.collect values = .ok trees → ∀ tree ∈ trees, .ok tree ∈ values := by
  intro values
  induction values with
  | nil =>
    intro trees h tree member
    simp [GoalPinSpecV2.collect] at h
    subst trees
    simp at member
  | cons value values ih =>
    intro trees h tree member
    cases value with
    | error err => simp [GoalPinSpecV2.collect] at h
    | ok first =>
      cases hc : GoalPinSpecV2.collect values with
      | error err => simp [GoalPinSpecV2.collect, hc, Except.map] at h
      | ok rest =>
        have eq : first :: rest = trees := by
          simpa [GoalPinSpecV2.collect, hc, Except.map] using h
        subst trees
        simp only [List.mem_cons] at member ⊢
        rcases member with rfl | member
        · exact Or.inl rfl
        · exact Or.inr (ih rest hc tree member)

theorem derive_allLabels (env : Environment) (fuel : Nat) :
    ∀ task tree, Solidity.GoalPins.derive env fuel task = .ok tree → AllLabels tree := by
  induction fuel with
  | zero =>
    intro task tree h
    simp [Solidity.GoalPins.derive] at h
  | succ fuel ih =>
    intro task tree h
    cases hs : GoalPinSpecV2.step env fuel task with
    | error err => simp [Solidity.GoalPins.derive, hs, bind, Except.bind] at h
    | ok pair =>
      rcases pair with ⟨lab, tasks⟩
      cases hc : GoalPinSpecV2.collect (tasks.map (Solidity.GoalPins.derive env fuel)) with
      | error err => simp [Solidity.GoalPins.derive, hs, hc, bind, Except.bind] at h
      | ok trees =>
        have eq : GoalPinSpecV2.Tree.node lab trees = tree := by
          simpa [Solidity.GoalPins.derive, hs, hc, bind, Except.bind, Pure.pure, Except.pure] using h
        subst tree
        intro inner children subtree
        cases subtree with
        | root => exact step_label_good env fuel task lab tasks hs
        | descend member subtree =>
          have present := collect_mem _ _ hc _ member
          obtain ⟨childTask, childMember, childEq⟩ := List.mem_map.mp present
          have good := ih childTask _ childEq
          exact good inner children subtree

theorem success_encodes (env : Environment) (fuel : Nat) (name : Lean.Name)
    (tree : GoalPinSpecV2.Tree) (graph : GoalPinSpecV2.RootGraph env fuel name (.ok tree)) :
    ∃ bytes, GoalPinSpecV2.EncodingV2.encode tree = some bytes := by
  unfold GoalPinSpecV2.RootGraph at graph
  cases hr : GoalPinSpecV2.root env name with
  | error err => simp [hr] at graph
  | ok pair =>
    rcases pair with ⟨lab, task⟩
    simp only [hr] at graph
    obtain ⟨body, derived, result⟩ := graph
    cases body with
    | error err => simp [Except.map] at result
    | ok inner =>
      have eval : Solidity.GoalPins.derive env fuel task = .ok inner :=
        Solidity.GoalPins.derive_complete env fuel derived
      have innerGood := derive_allLabels env fuel task inner eval
      have eq : GoalPinSpecV2.Tree.node lab [inner] = tree := by
        simpa [Except.map] using result.symm
      subst tree
      apply encode_from_labels
      intro subLab children subtree
      cases subtree with
      | root => exact root_label_good env name lab task hr
      | descend member subtree =>
        simp only [List.mem_singleton] at member
        subst inner
        exact innerGood subLab children subtree

end Draft

namespace Draft

theorem digit_properties (n : Nat) (h : n < 10) :
    (Nat.digitChar n).isDigit = true ∧ (Nat.digitChar n).toNat - '0'.toNat = n := by
  have cases : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨
      n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8 ∨ n = 9 := by omega
  rcases cases with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 <;> subst n <;> decide

def digitsValue : List Char → Nat
  | [] => 0
  | c :: cs => (c.toNat - '0'.toNat) * 10 ^ cs.length + digitsValue cs

theorem digitsCore_value : ∀ fuel n digits, n < fuel →
    digitsValue (Nat.toDigitsCore 10 fuel n digits) = n * 10 ^ digits.length + digitsValue digits := by
  intro fuel
  induction fuel with
  | zero =>
    intro n digits h
    omega
  | succ fuel ih =>
    intro n digits h
    have hmod : n % 10 < 10 := Nat.mod_lt _ (by decide)
    have digit := (digit_properties (n % 10) hmod).2
    simp only [Nat.toDigitsCore]
    by_cases hz : n / 10 = 0
    · simp only [hz, ↓reduceIte, digitsValue, digit]
      have hn : n % 10 = n := Nat.mod_eq_of_lt (by omega)
      rw [hn]
    · simp only [hz, ↓reduceIte]
      have hn : n / 10 < fuel := by
        have positive : 0 < n := by omega
        have smaller := Nat.div_lt_self positive (by decide : 1 < 10)
        omega
      rw [ih (n / 10) (Nat.digitChar (n % 10) :: digits) hn]
      simp only [List.length_cons, digitsValue, digit, Nat.pow_succ]
      calc
        n / 10 * (10 ^ digits.length * 10) +
            (n % 10 * 10 ^ digits.length + digitsValue digits) =
          (10 * (n / 10) + n % 10) * 10 ^ digits.length + digitsValue digits := by
            simp [Nat.add_mul, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm, Nat.add_assoc]
        _ = n * 10 ^ digits.length + digitsValue digits := by rw [Nat.div_add_mod]

theorem digitsCore_valid : ∀ fuel n digits, n < fuel →
    (∀ c ∈ digits, c.isDigit = true) →
    ∀ c ∈ Nat.toDigitsCore 10 fuel n digits, c.isDigit = true := by
  intro fuel
  induction fuel with
  | zero =>
    intro n digits h
    omega
  | succ fuel ih =>
    intro n digits h valid
    have digit := (digit_properties (n % 10) (Nat.mod_lt _ (by decide))).1
    simp only [Nat.toDigitsCore]
    by_cases hz : n / 10 = 0
    · simp only [hz, ↓reduceIte, List.mem_cons]
      intro c hc
      rcases hc with rfl | hc
      · exact digit
      · exact valid c hc
    · simp only [hz, ↓reduceIte]
      have hn : n / 10 < fuel := by
        have positive : 0 < n := by omega
        have smaller := Nat.div_lt_self positive (by decide : 1 < 10)
        omega
      apply ih (n / 10) _ hn
      intro c hc
      simp only [List.mem_cons] at hc
      rcases hc with rfl | hc
      · exact digit
      · exact valid c hc

theorem digitsCore_nonempty : ∀ fuel n digits, n < fuel →
    Nat.toDigitsCore 10 fuel n digits ≠ [] := by
  intro fuel
  induction fuel with
  | zero => intro n digits h; omega
  | succ fuel ih =>
    intro n digits h
    simp only [Nat.toDigitsCore]
    by_cases hz : n / 10 = 0
    · simp [hz]
    · simp only [hz, ↓reduceIte]
      have hn : n / 10 < fuel := by
        have positive : 0 < n := by omega
        have smaller := Nat.div_lt_self positive (by decide : 1 < 10)
        omega
      exact ih _ _ hn

theorem digitsValue_fold (digits : List Char) (acc : Nat) :
    digits.foldl (fun n c => n * 10 + (c.toNat - '0'.toNat)) acc =
      acc * 10 ^ digits.length + digitsValue digits := by
  induction digits generalizing acc with
  | nil => simp [digitsValue]
  | cons c rest ih =>
    simp only [List.foldl_cons, ih, List.length_cons, digitsValue, Nat.pow_succ]
    simp [Nat.mul_add, Nat.mul_assoc, Nat.mul_comm, Nat.add_assoc]

theorem decimal_digits_properties (n : Nat) :
    Nat.toDigits 10 n ≠ [] ∧
    (∀ c ∈ Nat.toDigits 10 n, c.isDigit = true) ∧
    (Nat.toDigits 10 n).foldl (fun x c => x * 10 + (c.toNat - '0'.toNat)) 0 = n := by
  constructor
  · exact digitsCore_nonempty (n + 1) n [] (by omega)
  constructor
  · exact digitsCore_valid (n + 1) n [] (by omega) (by simp)
  · rw [digitsValue_fold]
    simp only [Nat.zero_mul, Nat.zero_add]
    have h := digitsCore_value (n + 1) n [] (by omega)
    simpa [Nat.toDigits, digitsValue] using h

/-- Every canonical decision identifier parses to its represented number. -/
theorem decision_roundtrip : DecisionRoundTrip := by
  intro number
  obtain ⟨nonempty, valid, value⟩ := decimal_digits_properties number
  have repr : (toString number).data = Nat.toDigits 10 number := rfl
  simpa [parseDecision, repr, nonempty] using And.intro valid value

/-- Every well-formed reference row is accepted by the executable decoder. -/
theorem decode_complete {rows : List RawPin} {pins : List Pin}
    (h : Pointwise RowOf rows pins) : decode rows = .ok pins := by
  induction h with
  | nil => rfl
  | cons first rest ih =>
    simp [decode, decodeRow_complete decision_roundtrip first, ih,
      bind, Except.bind, Pure.pure, Except.pure]

/-- Each reference row has an associated pin. -/
theorem pointwise_row_exists {rows : List RawPin} {pins : List Pin}
    (h : Pointwise RowOf rows pins) : ∀ row ∈ rows, ∃ pin, RowOf row pin := by
  induction h with
  | nil => simp
  | cons first rest ih =>
    intro row member
    simp only [List.mem_cons] at member
    rcases member with rfl | member
    · exact ⟨_, first⟩
    · exact ih row member

/-- A row decoder error has the single specified error class. -/
theorem decodeRow_error_kind (row : RawPin) (err : Error)
    (h : decodeRow row = .error err) : err = .malformedPin := by
  cases hp : parseDecision row.decisionId with
  | none =>
    simp only [decodeRow, hp] at h
    change Except.error Error.malformedPin = Except.error err at h
    cases h
    rfl
  | some number =>
    simp only [decodeRow, hp, Except.bind, Pure.pure, Except.pure] at h
    split at h
    · cases h
    · change Except.error Error.malformedPin = Except.error err at h
      cases h
      rfl

/-- A failed row decoder identifies a row with no valid reference pin. -/
theorem decodeRow_error_invalid (row : RawPin) (err : Error)
    (h : decodeRow row = .error err) : ¬ ∃ pin, RowOf row pin := by
  rintro ⟨pin, valid⟩
  have accepted := decodeRow_complete decision_roundtrip valid
  rw [h] at accepted
  cases accepted

/-- Every decoder result is a result in the independent decode graph. -/
theorem decode_graph (rows : List RawPin) : DecodeGraph rows (decode rows) := by
  induction rows with
  | nil => exact .success .nil
  | cons row rows ih =>
    cases hr : decodeRow row with
    | error err =>
      have kind := decodeRow_error_kind row err hr
      subst err
      have invalid := decodeRow_error_invalid row .malformedPin hr
      simpa [decode, hr, bind, Except.bind] using
        (DecodeGraph.malformed (rows := row :: rows) ⟨row, by simp, invalid⟩)
    | ok pin =>
      cases ht : decode rows with
      | error err =>
        rw [ht] at ih
        cases ih with
        | malformed invalid =>
          simpa [decode, hr, ht, bind, Except.bind] using
            (DecodeGraph.malformed (rows := row :: rows) (by
              obtain ⟨bad, member, invalid⟩ := invalid
              exact ⟨bad, by simp [member], invalid⟩))
      | ok pins =>
        rw [ht] at ih
        cases ih with
        | success valid =>
          have first := decodeRow_sound row pin hr
          simpa [decode, hr, ht, bind, Except.bind, Pure.pure, Except.pure] using
            (DecodeGraph.success (.cons first valid))

/-- The decoder is exact for both successful rows and malformed input. -/
theorem decode_exact (rows : List RawPin) (output : Except Error (List Pin)) :
    decode rows = output ↔ DecodeGraph rows output := by
  constructor
  · intro h
    rw [← h]
    exact decode_graph rows
  · intro graph
    cases graph with
    | success valid => exact decode_complete valid
    | malformed invalid =>
      have actual := decode_graph rows
      cases h : decode rows with
      | error err =>
        rw [h] at actual
        cases actual
        rfl
      | ok pins =>
        have valid := decode_sound rows pins h
        obtain ⟨row, member, bad⟩ := invalid
        exact False.elim (bad (pointwise_row_exists valid row member))

end Draft

/-- Executable operations use the fixed snapshot route and independent checker. -/
def operations : Operations where
  decode := Draft.decode
  recompute := recompute
  check := Draft.check
  current := fun fuel manifest pins => do
    let snapshot ← readSnapshot
    match snapshot with
    | .error err => pure (.error err)
    | .ok s => pure (Draft.check s fuel manifest pins)
  rawCurrent := fun fuel manifest rows => do
    match Draft.decode rows with
    | .error err => pure (.error err)
    | .ok pins => do
      let snapshot ← readSnapshot
      match snapshot with
      | .error err => pure (.error err)
      | .ok s => pure (Draft.check s fuel manifest pins)

/-- The current law shape would imply that every possible snapshot was observed. -/
theorem laws_force_observed (ops : Operations) (laws : Laws ops) (s : Snapshot) :
    ObservedSnapshot s := by
  classical
  by_cases observed : ObservedSnapshot s
  · exact observed
  · let manifest : Manifest := ⟨"", []⟩
    have first : CheckGraph s manifest [] 1 (.error .malformedPin) :=
      (laws.check_exact s 1 manifest [] (.error .malformedPin)).1
        (fun evidence => False.elim (observed evidence))
    have second : CheckGraph s manifest [] 1 (.ok ()) :=
      (laws.check_exact s 1 manifest [] (.ok ())).1
        (fun evidence => False.elim (observed evidence))
    have contradiction := laws.check_deterministic s manifest [] 1 _ _ first second
    cases contradiction
end Solidity.GoalPins
