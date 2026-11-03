import Solidity.Yul.CatalogLaws
import Solidity.Source.Syntax
/-! A separate no-bare-builtin-use judgement. This is not declaration validity,
typing, tier admission or Source provenance. Qualified external paths remain
available; executable calls keep their existing arity/tier checks. -/
namespace Solidity.Yul.BuiltinUse
open Solidity.Source (Syn)

inductive Failure where
  | bareBuiltin (name : String)
  | notYul
  deriving Repr, DecidableEq

/-- Independent condition over intrinsic builtin constructors, not lookup output. -/
def PathD (path : List String) : Prop := ∀ name, path = [name] → NoBuiltin name
def PathsD (paths : List (List String)) : Prop := ∀ path ∈ paths, PathD path

def merge (one two : Option Failure) : Option Failure :=
  match one with | none => two | some reason => some reason

theorem merge_none {one two} : merge one two = none ↔ one = none ∧ two = none := by
  constructor
  · intro same
    cases one with
    | none => exact ⟨rfl,same⟩
    | some reason => cases same
  · rintro ⟨rfl,same⟩
    exact same

def pathFailure : List String → Option Failure
  | [name] => (lookupBuiltin name).map (fun _ => .bareBuiltin name)
  | _ => none

theorem path_failure_iff (path : List String) : pathFailure path = none ↔ PathD path := by
  cases path with
  | nil =>
      constructor
      · intro same name impossible
        cases impossible
      · intro valid
        rfl
  | cons name rest =>
      cases rest with
      | nil =>
          constructor
          · intro same query equal
            have names : name = query := (List.cons.inj equal).1
            cases names
            have absent : lookupBuiltin name = none := by
              cases found : lookupBuiltin name with
              | none => rfl
              | some entry =>
                  simp only [pathFailure,found,Option.map] at same
                  cases same
            exact lookup_none_sound absent
          · intro valid
            have absent := lookup_none_complete (valid name rfl)
            simp only [pathFailure,absent,Option.map]
      | cons next tail =>
          constructor
          · intro same query impossible
            cases impossible
          · intro valid
            rfl

def pathsFailure : List (List String) → Option Failure
  | [] => none
  | first::rest => merge (pathFailure first) (pathsFailure rest)

theorem paths_failure_iff (paths : List (List String)) :
    pathsFailure paths = none ↔ PathsD paths := by
  induction paths with
  | nil =>
      constructor
      · intro same path impossible
        cases impossible
      · intro valid
        rfl
  | cons first rest ih =>
      constructor
      · intro same path present
        have both := merge_none.mp same
        rcases List.mem_cons.mp present with equal | later
        · cases equal
          exact (path_failure_iff first).mp both.1
        · exact ih.mp both.2 path later
      · intro valid
        exact merge_none.mpr ⟨(path_failure_iff first).mpr (valid first List.mem_cons_self),
          ih.mpr (fun path present => valid path (List.mem_cons_of_mem first present))⟩

/-- Only the variable/path-use condition is new. All other static constraints
remain obligations of the existing independent typing/declaration layers. -/
inductive D : {category : Solidity.Source.Cat} → Syn category → Prop where
  | literal (value) : D (.yulLit value)
  | path {name parts} : PathD (name::parts) → D (.yulPath name parts)
  | call {name args} : D args → D (.yulCall name args)
  | nil (category) : D (.nil : Syn (.list category))
  | cons {category} {head : Syn category} {tail : Syn (.list category)} :
      D head → D tail → D (.cons head tail)
  | none (category) : D (.none : Syn (.opt category))
  | some {category} {value : Syn category} : D value → D (.some value)
  | block {body} : D body → D (.yulBlock body)
  | declaration {first rest value} : D value → D (.yulLet first rest value)
  | assignment {first rest value} :
      PathsD (first::rest) → D value → D (.yulAssign first rest value)
  | expression {value} : D value → D (.yulExprStmt value)
  | if_ {condition body} : D condition → D body → D (.yulIf condition body)
  | for_ {pre condition post body} : D pre → D condition → D post → D body →
      D (.yulFor pre condition post body)
  | switch {selector cases fallback} : D selector → D cases → D fallback →
      D (.yulSwitch selector cases fallback)
  | function {name args rets body} : D body → D (.yulFun name args rets body)
  | case_ {value body} : D body → D (.yulCase value body)
  | leave : D .yulLeave
  | break_ : D .yulBreak
  | continue_ : D .yulContinue

structure CheckedPath (path : List String) : Type where
  valid : PathD path
structure CheckedPaths (paths : List (List String)) : Type where
  valid : PathsD paths
structure Checked {category} (tree : Syn category) : Type where
  valid : D tree

def checkPath (path : List String) : Except Failure (CheckedPath path) :=
  match same : pathFailure path with
  | none => .ok ⟨(path_failure_iff path).mp same⟩
  | some reason => .error reason

theorem CheckedPath.complete {path} (checked : CheckedPath path) :
    checkPath path = .ok checked := by
  cases checked with
  | mk valid =>
      unfold checkPath
      split
      · rfl
      · next reason equation =>
          have absent := (path_failure_iff path).mpr valid
          cases equation.symm.trans absent

def checkPaths : (paths : List (List String)) → Except Failure (CheckedPaths paths)
  | [] => .ok ⟨fun path impossible => by cases impossible⟩
  | first::rest => do
      let head ← checkPath first
      let tail ← checkPaths rest
      pure ⟨fun path present => by
        rcases List.mem_cons.mp present with equal | later
        · cases equal; exact head.valid
        · exact tail.valid path later⟩

theorem CheckedPaths.complete {paths} (checked : CheckedPaths paths) :
    checkPaths paths = .ok checked := by
  induction paths with
  | nil =>
      cases checked
      rfl
  | cons first rest ih =>
      have head : CheckedPath first := ⟨checked.valid first List.mem_cons_self⟩
      have tail : CheckedPaths rest := ⟨fun path present =>
        checked.valid path (List.mem_cons_of_mem first present)⟩
      simp only [checkPaths,head.complete,ih tail,bind,Except.bind,pure,Except.pure]

/-- Executable proof-producing category-generalized checker. No indexed
equation-compiler match or noncomputable recursor is used. -/
def check {category} (tree : Syn category) : Except Failure (Checked tree) := by
  apply Syn.casesOn (motive := fun category tree => Except Failure (Checked tree)) tree
  case yulLit => intro value; exact .ok ⟨.literal value⟩
  case yulPath =>
    intro name parts
    exact do let valid ← checkPath (name::parts); pure ⟨.path valid.valid⟩
  case yulCall =>
    intro name args
    exact do let valid ← check args; pure ⟨.call valid.valid⟩
  case nil => intro category; exact .ok ⟨.nil category⟩
  case cons =>
    intro category head tail
    exact do let first ← check head; let rest ← check tail; pure ⟨.cons first.valid rest.valid⟩
  case none => intro category; exact .ok ⟨.none category⟩
  case some =>
    intro category value
    exact do let valid ← check value; pure ⟨.some valid.valid⟩
  case yulBlock =>
    intro body
    exact do let valid ← check body; pure ⟨.block valid.valid⟩
  case yulLet =>
    intro first rest value
    exact do let valid ← check value; pure ⟨.declaration valid.valid⟩
  case yulAssign =>
    intro first rest value
    exact do
      let paths ← checkPaths (first::rest)
      let rhs ← check value
      pure ⟨.assignment paths.valid rhs.valid⟩
  case yulExprStmt =>
    intro value
    exact do let valid ← check value; pure ⟨.expression valid.valid⟩
  case yulIf =>
    intro condition body
    exact do let guard ← check condition; let block ← check body; pure ⟨.if_ guard.valid block.valid⟩
  case yulFor =>
    intro pre condition post body
    exact do
      let first ← check pre
      let guard ← check condition
      let after ← check post
      let block ← check body
      pure ⟨.for_ first.valid guard.valid after.valid block.valid⟩
  case yulSwitch =>
    intro selector cases fallback
    exact do
      let value ← check selector
      let arms ← check cases
      let otherwise ← check fallback
      pure ⟨.switch value.valid arms.valid otherwise.valid⟩
  case yulFun =>
    intro name args rets body
    exact do let valid ← check body; pure ⟨.function valid.valid⟩
  case yulCase =>
    intro value body
    exact do let valid ← check body; pure ⟨.case_ valid.valid⟩
  case yulLeave => exact .ok ⟨.leave⟩
  case yulBreak => exact .ok ⟨.break_⟩
  case yulContinue => exact .ok ⟨.continue_⟩
  all_goals intros; exact .error .notYul
termination_by structural tree

theorem D.complete {category tree} (valid : @D category tree) :
    check tree = .ok ⟨valid⟩ := by
  induction valid with
  | literal value => rfl
  | @path name parts safe =>
      change (do let result ← checkPath (name::parts); pure (Checked.mk (D.path (name := name) (parts := parts) result.valid))) = _
      simp only [(CheckedPath.complete (⟨safe⟩ : CheckedPath (name::parts))),bind,Except.bind,pure,Except.pure]
  | @call name args valid ih =>
      change (do let result ← check args; pure (Checked.mk (D.call (name := name) result.valid))) = _
      simp only [ih,bind,Except.bind,pure,Except.pure]
  | nil category => rfl
  | @cons category head tail validHead validTail ihHead ihTail =>
      change (do let first ← check head; let rest ← check tail; pure (Checked.mk (D.cons first.valid rest.valid))) = _
      simp only [ihHead,ihTail,bind,Except.bind,pure,Except.pure]
  | none category => rfl
  | @some category value valid ih =>
      change (do let result ← check value; pure (Checked.mk (D.some result.valid))) = _
      simp only [ih,bind,Except.bind,pure,Except.pure]
  | @block body valid ih =>
      change (do let result ← check body; pure (Checked.mk (D.block result.valid))) = _
      simp only [ih,bind,Except.bind,pure,Except.pure]
  | @declaration first rest value valid ih =>
      change (do let result ← check value; pure (Checked.mk (D.declaration (first := first) (rest := rest) result.valid))) = _
      simp only [ih,bind,Except.bind,pure,Except.pure]
  | @assignment first rest value paths valid ih =>
      change (do
        let targets ← checkPaths (first::rest)
        let result ← check value
        pure (Checked.mk (D.assignment (first := first) (rest := rest) targets.valid result.valid))) = _
      simp only [(CheckedPaths.complete (⟨paths⟩ : CheckedPaths (first::rest))),
        ih,bind,Except.bind,pure,Except.pure]
  | @expression value valid ih =>
      change (do let result ← check value; pure (Checked.mk (D.expression result.valid))) = _
      simp only [ih,bind,Except.bind,pure,Except.pure]
  | @if_ condition body validCondition validBody ihCondition ihBody =>
      change (do
        let guard ← check condition
        let block ← check body
        pure (Checked.mk (D.if_ guard.valid block.valid))) = _
      simp only [ihCondition,ihBody,bind,Except.bind,pure,Except.pure]
  | @for_ pre condition post body validPre validCondition validPost validBody ihPre ihCondition ihPost ihBody =>
      change (do
        let first ← check pre
        let guard ← check condition
        let after ← check post
        let block ← check body
        pure (Checked.mk (D.for_ first.valid guard.valid after.valid block.valid))) = _
      simp only [ihPre,ihCondition,ihPost,ihBody,bind,Except.bind,pure,Except.pure]
  | @switch selector cases fallback validSelector validCases validFallback ihSelector ihCases ihFallback =>
      change (do
        let value ← check selector
        let arms ← check cases
        let otherwise ← check fallback
        pure (Checked.mk (D.switch value.valid arms.valid otherwise.valid))) = _
      simp only [ihSelector,ihCases,ihFallback,bind,Except.bind,pure,Except.pure]
  | @function name args rets body valid ih =>
      change (do let result ← check body; pure (Checked.mk (D.function (name := name) (args := args) (rets := rets) result.valid))) = _
      simp only [ih,bind,Except.bind,pure,Except.pure]
  | @case_ value body valid ih =>
      change (do let result ← check body; pure (Checked.mk (D.case_ (value := value) result.valid))) = _
      simp only [ih,bind,Except.bind,pure,Except.pure]
  | leave => rfl
  | break_ => rfl
  | continue_ => rfl

theorem Checked.complete {category tree} (checked : @Checked category tree) :
    check tree = .ok checked := by
  cases checked with
  | mk valid => exact valid.complete

theorem check_iff {category} (tree : Syn category) :
    (check tree).isOk = true ↔ D tree := by
  constructor
  · intro accepted
    cases actual : check tree with
    | error reason => rw [actual] at accepted; cases accepted
    | ok checked => exact checked.valid
  · intro valid
    rw [valid.complete]
    rfl

def failure {category} (tree : Syn category) : Option Failure :=
  match check tree with | .ok _ => none | .error reason => some reason

theorem failure_iff {category} (tree : Syn category) : failure tree = none ↔ D tree := by
  constructor
  · intro absent
    cases actual : check tree with
    | error reason =>
        simp only [failure,actual] at absent
        cases absent
    | ok checked => exact checked.valid
  · intro valid
    simp only [failure,valid.complete]

theorem bare_builtin_invalid {a r} (builtin : Builtin a r) :
    ¬ D (.yulPath builtin.name []) := by
  intro valid
  cases valid with
  | path safe => exact safe builtin.name rfl a r builtin rfl

theorem qualified_path (name part : String) (rest : List String) :
    D (.yulPath name (part::rest)) :=
  .path (by intro query impossible; cases impossible)

theorem checkPath_error {path reason} (actual : pathFailure path = some reason) :
    checkPath path = .error reason := by
  unfold checkPath
  split
  · next equation => cases equation.symm.trans actual
  · next found equation =>
      have same := Option.some.inj (equation.symm.trans actual)
      cases same
      rfl

theorem bare_builtin_refused {a r} (builtin : Builtin a r) :
    check (.yulPath builtin.name []) = .error (.bareBuiltin builtin.name) := by
  change (do
    let result ← checkPath [builtin.name]
    pure (Checked.mk (D.path (name := builtin.name) (parts := []) result.valid))) = _
  have reported : pathFailure [builtin.name] = some (.bareBuiltin builtin.name) := by
    simp only [pathFailure,lookup_builtin_name builtin,Option.map]
  simp only [checkPath_error reported,bind,Except.bind]

end Solidity.Yul.BuiltinUse
