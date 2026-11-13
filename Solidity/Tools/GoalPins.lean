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
  let some number := (String.mk (row.decisionId.toList.drop 1)).toNat?
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
  cases hs : (String.mk (row.decisionId.toList.drop 1)).toNat? with
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
  (String.mk (("H" ++ toString number).toList.drop 1)).toNat? = some number

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
      have parsed : (toString number).toNat? = some number := by
        simpa using roundtrip number
      simp [decodeRow, Pin.decisionId, parsed, hwell, Pure.pure, Except.pure]

end Draft

end Solidity.GoalPins
