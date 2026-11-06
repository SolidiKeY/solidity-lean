import Solidity.Yul.TypingSites
import Solidity.Yul.ScalarLocals

/-! Individual variable/target leaves from actual intrinsic derivations.
These are indexed static certificates over original syntax, not a new program
representation, checker or execution model. JSON-position and metadata
accounting are not established here. -/
namespace Solidity.Yul.TypingLeaves
open Solidity.Source (Syn)
open Solidity.Yul.BlockTyping (Env)
open Solidity.Yul.BlockScope (Scope)

inductive Edge where
  | arguments | first | rest
  deriving DecidableEq, Repr
abbrev Path := List Edge

structure ReadLeaf {F X n} (E : ExprEnv F X n) where
  name : String
  parts : List String
  typed : ExprD E (.yulPath name parts) 1

structure WriteLeaf {X n} (E : TargetEnv X n) where
  name : String
  parts : List String
  target : Target X n
  typed : TargetD E name parts target

abbrev ReadTrace {F X n} (E : ExprEnv F X n) := List (Path × ReadLeaf E)
abbrev WriteTrace {X n} (E : TargetEnv X n) := List (Path × WriteLeaf E)

def All {α : Type} (predicate : Path → α → Prop) (trace : List (Path × α)) : Prop :=
  ∀ entry ∈ trace, predicate entry.1 entry.2

private theorem all_nil {α} (predicate : Path → α → Prop) : All predicate [] ↔ True := by
  constructor
  · intro _; exact True.intro
  · intro _ entry impossible; cases impossible
private theorem all_one {α} (predicate : Path → α → Prop) (path : Path) (leaf : α) :
    All predicate [(path,leaf)] ↔ predicate path leaf := by
  constructor
  · intro all; exact all (path,leaf) List.mem_cons_self
  · intro yes entry present
    rcases List.mem_cons.mp present with same | impossible
    · cases same; exact yes
    · cases impossible
private theorem all_append {α} (predicate : Path → α → Prop) (left right : List (Path × α)) :
    All predicate (left++right) ↔ All predicate left ∧ All predicate right := by
  constructor
  · intro all
    exact ⟨fun entry present => all entry (List.mem_append_left _ present),
      fun entry present => all entry (List.mem_append_right _ present)⟩
  · rintro ⟨one,two⟩ entry present
    rcases List.mem_append.mp present with fromLeft | fromRight
    · exact one entry fromLeft
    · exact two entry fromRight

mutual
def reads {F X n E term arity} (d : @ExprD F X n E term arity) : Path → ReadTrace E := by
  apply ExprD.casesOn (motive_1 := fun _ _ _ => Path → ReadTrace E) d
  case literal => intros; exact []
  case «variable» =>
    intro name index resolved path
    exact [(path,⟨name,[],.«variable» resolved⟩)]
  case external =>
    intro name parts reference priority resolved path
    exact [(path,⟨name,parts,.external priority resolved⟩)]
  case builtin =>
    intro name args a r builtin spelling typed path
    exact arguments typed (path++[.arguments])
  case call =>
    intro name args signature function noBuiltin resolved typed path
    exact arguments typed (path++[.arguments])
termination_by structural d

def arguments {F X n E terms arity} (d : @ArgsD F X n E terms arity) : Path → ReadTrace E := by
  apply ArgsD.casesOn (motive_2 := fun _ _ _ => Path → ReadTrace E) d
  case nil => intro path; exact []
  case cons =>
    intro first rest count head tail path
    exact reads head (path++[.first]) ++ arguments tail (path++[.rest])
termination_by structural d
end

mutual
def everyRead {F X n E term arity} (d : @ExprD F X n E term arity) :
    Path → (Path → ReadLeaf E → Prop) → Prop := by
  apply ExprD.casesOn (motive_1 := fun _ _ _ => Path → (Path → ReadLeaf E → Prop) → Prop) d
  case literal => intros; exact True
  case «variable» =>
    intro name index resolved path predicate
    exact predicate path ⟨name,[],.«variable» resolved⟩
  case external =>
    intro name parts reference priority resolved path predicate
    exact predicate path ⟨name,parts,.external priority resolved⟩
  case builtin =>
    intro name args a r builtin spelling typed path predicate
    exact everyArgument typed (path++[.arguments]) predicate
  case call =>
    intro name args signature function noBuiltin resolved typed path predicate
    exact everyArgument typed (path++[.arguments]) predicate
termination_by structural d

def everyArgument {F X n E terms arity} (d : @ArgsD F X n E terms arity) :
    Path → (Path → ReadLeaf E → Prop) → Prop := by
  apply ArgsD.casesOn (motive_2 := fun _ _ _ => Path → (Path → ReadLeaf E → Prop) → Prop) d
  case nil => intros; exact True
  case cons =>
    intro first rest count head tail path predicate
    exact everyRead head (path++[.first]) predicate ∧ everyArgument tail (path++[.rest]) predicate
termination_by structural d
end

mutual
theorem all_reads {F X n E term arity} (d : @ExprD F X n E term arity)
    (path : Path) (predicate : Path → ReadLeaf E → Prop) :
    All predicate (reads d path) ↔ everyRead d path predicate := by
  revert path
  apply ExprD.casesOn (motive_1 := fun _ _ d => ∀ path,
    All predicate (reads d path) ↔ everyRead d path predicate) d
  case literal => intros; exact all_nil predicate
  case «variable» =>
    intro name index resolved path
    exact all_one predicate path ⟨name,[],.«variable» resolved⟩
  case external =>
    intro name parts reference priority resolved path
    exact all_one predicate path ⟨name,parts,.external priority resolved⟩
  case builtin =>
    intro name args a r builtin spelling typed path
    exact all_arguments typed (path++[.arguments]) predicate
  case call =>
    intro name args signature function noBuiltin resolved typed path
    exact all_arguments typed (path++[.arguments]) predicate
termination_by structural d

theorem all_arguments {F X n E terms arity} (d : @ArgsD F X n E terms arity)
    (path : Path) (predicate : Path → ReadLeaf E → Prop) :
    All predicate (arguments d path) ↔ everyArgument d path predicate := by
  revert path
  apply ArgsD.casesOn (motive_2 := fun _ _ d => ∀ path,
    All predicate (arguments d path) ↔ everyArgument d path predicate) d
  case nil => intros; exact all_nil predicate
  case cons =>
    intro first rest count head tail path
    change All predicate (reads head (path++[.first]) ++ arguments tail (path++[.rest])) ↔
      everyRead head (path++[.first]) predicate ∧ everyArgument tail (path++[.rest]) predicate
    simp only [all_append,all_reads head,all_arguments tail]
termination_by structural d
end

def targetPath {X n E path target} (d : @TargetPathD X n E path target) : WriteLeaf E := by
  apply TargetPathD.casesOn (motive := fun _ _ _ => WriteLeaf E) d
  intro head tail target typed
  exact ⟨head,tail,target,typed⟩

def targets {X n E paths} (d : @TargetsD X n E paths) : Path → WriteTrace E := by
  apply TargetsD.casesOn (motive := fun _ _ => Path → WriteTrace E) d
  case nil => intro path; exact []
  case cons =>
    intro first rest target head tail path
    exact [(path++[.first],targetPath head)] ++ targets tail (path++[.rest])
termination_by structural d

def everyTarget {X n E paths} (d : @TargetsD X n E paths) :
    Path → (Path → WriteLeaf E → Prop) → Prop := by
  apply TargetsD.casesOn (motive := fun _ _ => Path → (Path → WriteLeaf E → Prop) → Prop) d
  case nil => intros; exact True
  case cons =>
    intro first rest target head tail path predicate
    exact predicate (path++[.first]) (targetPath head) ∧ everyTarget tail (path++[.rest]) predicate
termination_by structural d

theorem all_targets {X n E paths} (d : @TargetsD X n E paths)
    (path : Path) (predicate : Path → WriteLeaf E → Prop) :
    All predicate (targets d path) ↔ everyTarget d path predicate := by
  revert path
  apply TargetsD.casesOn (motive := fun _ d => ∀ path,
    All predicate (targets d path) ↔ everyTarget d path predicate) d
  case nil => intros; exact all_nil predicate
  case cons =>
    intro first rest target head tail path
    change All predicate ([(path++[.first],targetPath head)] ++ targets tail (path++[.rest])) ↔
      predicate (path++[.first]) (targetPath head) ∧ everyTarget tail (path++[.rest]) predicate
    simp only [all_append,all_one,all_targets tail]
termination_by structural d

/-- Recover the ACTUAL expression derivation without casting its arity at
runtime. The real fixed-arity equality is exported separately below. -/
def expressionInput {X F n} (scope : Scope X) (E : Env F n) {term count}
    (typed : BlockScope.ExpressionD scope E term count) :
    ((arity : Nat) × ExprD (scope.reads E) term arity) := by
  revert typed
  apply Scope.casesOn (motive := fun X scope =>
    BlockScope.ExpressionD scope E term count →
      ((arity : Nat) × ExprD (scope.reads E) term arity)) scope
  case closed => exact fun typed => ⟨count,typed⟩
  case external =>
    intro root X decls input original typed
    exact ⟨typed.val.arity,typed.val.typed⟩

theorem expressionInput_count {X F n} (scope : Scope X) (E : Env F n) {term count}
    (typed : BlockScope.ExpressionD scope E term count) :
    (expressionInput scope E typed).1 = count := by
  revert typed
  apply Scope.casesOn (motive := fun X scope =>
    (typed : BlockScope.ExpressionD scope E term count) →
      (expressionInput scope E typed).1 = count) scope
  case closed => intro typed; rfl
  case external =>
    intro root X decls input original typed
    exact typed.property

def assignmentReads {X F n} (scope : Scope X) (E : Env F n) {paths rhs}
    (typed : BlockScope.AssignmentD scope E paths rhs) :
    ExprD (scope.reads E) rhs paths.length := by
  revert typed
  apply Scope.casesOn (motive := fun X scope =>
    BlockScope.AssignmentD scope E paths rhs → ExprD (scope.reads E) rhs paths.length) scope
  case closed => exact fun typed => ScopedAssignments.rhsD typed
  case external =>
    intro root X decls input original typed
    exact ScopedAssignments.rhsD typed.typed

def assignmentTargets {X F n} (scope : Scope X) (E : Env F n) {paths rhs}
    (typed : BlockScope.AssignmentD scope E paths rhs) :
    TargetsD (scope.writes E) paths := by
  revert typed
  apply Scope.casesOn (motive := fun X scope =>
    BlockScope.AssignmentD scope E paths rhs → TargetsD (scope.writes E) paths) scope
  case closed => exact fun typed => ScopedAssignments.targetsD typed
  case external =>
    intro root X decls input original typed
    exact ScopedAssignments.targetsD typed.typed

/-- Intrinsic static metadata retains the actual parent site's scope and
environment. The original expression/target derivation remains in each leaf. -/
inductive Leaf where
  | read {X F n} (scope : Scope X) (environment : Env F n)
      (leaf : ReadLeaf (scope.reads environment))
  | write {X F n} (scope : Scope X) (environment : Env F n)
      (leaf : WriteLeaf (scope.writes environment))

inductive Role where
  | read | write
  deriving DecidableEq, Repr
abbrev Position := Role × Path
abbrev Trace := List (Position × Leaf)

def AllLeaves (predicate : Position → Leaf → Prop) (trace : Trace) : Prop :=
  ∀ entry ∈ trace, predicate entry.1 entry.2

theorem allLeaves_append (predicate : Position → Leaf → Prop) (one two : Trace) :
    AllLeaves predicate (one++two) ↔ AllLeaves predicate one ∧ AllLeaves predicate two := by
  constructor
  · intro all
    exact ⟨fun entry present => all entry (List.mem_append_left _ present),
      fun entry present => all entry (List.mem_append_right _ present)⟩
  · rintro ⟨first,second⟩ entry present
    rcases List.mem_append.mp present with left | right
    · exact first entry left
    · exact second entry right

theorem all_mapped {α} (predicate : Position → Leaf → Prop) (role : Role)
    (inject : α → Leaf) (trace : List (Path × α)) :
    AllLeaves predicate (trace.map (fun entry => ((role,entry.1),inject entry.2))) ↔
      All (fun path leaf => predicate (role,path) (inject leaf)) trace := by
  constructor
  · intro all entry present
    exact all ((role,entry.1),inject entry.2) (List.mem_map.mpr ⟨entry,present,rfl⟩)
  · intro all entry present
    obtain ⟨original,member,same⟩ := List.mem_map.mp present
    cases same
    exact all original member

def siteTrace (site : TypingSites.Site) : Trace :=
  match site with
  | .expression scope E _ _ typed =>
      (reads (expressionInput scope E typed).2 []).map
        (fun entry => ((.read,entry.1),.read scope E entry.2))
  | .assignment scope E _ _ typed =>
      (reads (assignmentReads scope E typed) []).map
        (fun entry => ((.read,entry.1),.read scope E entry.2)) ++
      (targets (assignmentTargets scope E typed) []).map
        (fun entry => ((.write,entry.1),.write scope E entry.2))

def everySite (site : TypingSites.Site) (predicate : Position → Leaf → Prop) : Prop :=
  match site with
  | .expression scope E _ _ typed =>
      everyRead (expressionInput scope E typed).2 []
        (fun path leaf => predicate (.read,path) (.read scope E leaf))
  | .assignment scope E _ _ typed =>
      everyRead (assignmentReads scope E typed) []
        (fun path leaf => predicate (.read,path) (.read scope E leaf)) ∧
      everyTarget (assignmentTargets scope E typed) []
        (fun path leaf => predicate (.write,path) (.write scope E leaf))

theorem all_site (site : TypingSites.Site) (predicate : Position → Leaf → Prop) :
    AllLeaves predicate (siteTrace site) ↔ everySite site predicate := by
  cases site with
  | expression scope E tree arity typed =>
      exact (all_mapped predicate .read (Leaf.read scope E) _).trans
        (all_reads (expressionInput scope E typed).2 [] _)
  | assignment scope E paths rhs typed =>
      change AllLeaves predicate (_++_) ↔ _
      rw [allLeaves_append]
      exact and_congr
        ((all_mapped predicate .read (Leaf.read scope E) _).trans
          (all_reads (assignmentReads scope E typed) [] _))
        ((all_mapped predicate .write (Leaf.write scope E) _).trans
          (all_targets (assignmentTargets scope E typed) [] _))

/-- Indexed binding metadata, preserving actual local slots or typed external
references/capabilities. It is not an executable intermediate language. -/
inductive Binding (X : List ExternalType) (n : Nat) (write : Bool) where
  | local (index : Fin n)
  | external (reference : ExternalRef X write)

def readBinding {F X n E term arity} (typed : @ExprD F X n E term arity) :
    Option (Binding X n false) := by
  apply ExprD.casesOn (motive_1 := fun _ _ _ => Option (Binding X n false)) typed
  case literal => intros; exact none
  case «variable» => intro name index resolved; exact some (.local index)
  case external => intro name parts reference priority resolved; exact some (.external reference)
  case builtin => intros; exact none
  case call => intros; exact none

def ReadLeaf.binding {F X n E} (leaf : @ReadLeaf F X n E) : Option (Binding X n false) :=
  readBinding leaf.typed

theorem ReadLeaf.binding_present {F X n E} (leaf : @ReadLeaf F X n E) :
    leaf.binding.isSome = true := by
  cases leaf with
  | mk name parts typed => cases typed <;> rfl

def Binding.expression {F X n} (binding : Binding X n false) : Expr F X n 1 :=
  match binding with
  | .local index => .local index
  | .external reference => .external reference

theorem ReadLeaf.binding_sound {F X n E} (leaf : @ReadLeaf F X n E)
    (binding : Binding X n false) (found : leaf.binding = some binding) :
    leaf.typed.term = binding.expression := by
  cases leaf with
  | mk name parts typed =>
      cases typed with
      | «variable» resolved =>
          cases found
          rfl
      | external priority resolved =>
          cases found
          rfl

def WriteLeaf.binding {X n E} (leaf : @WriteLeaf X n E) : Binding X n true :=
  match leaf.target with
  | .local index => .local index
  | .external reference => .external reference

def Binding.isExternal {X n write} (binding : Binding X n write) : Bool :=
  match binding with
  | .local _ => false
  | .external _ => true
def Binding.position {X n write} (binding : Binding X n write) : Nat :=
  match binding with
  | .local index => index.val
  | .external reference => reference.index.position
def Binding.attribute {X n write} (binding : Binding X n write) : Option Attribute :=
  match binding with
  | .local _ => none
  | .external reference => some reference.attr

structure View where
  name : String
  parts : List String
  write : Bool
  externalBinding : Option Bool
  position : Option Nat
  selectedAttribute : Option Attribute
  locals : List (String × Nat)
  functions : List String
  slots : Nat
  externalTypes : Nat
  externalFunctionScope : Bool
  deriving DecidableEq, Repr

def Leaf.view (leaf : Leaf) : View :=
  match leaf with
  | .read (X := X) (n := n) scope E reference =>
      ⟨reference.name,reference.parts,false,reference.binding.map Binding.isExternal,
        reference.binding.map Binding.position,reference.binding.bind Binding.attribute,
        E.locals.map (fun p => (p.1,p.2.val)),E.functions.map Prod.fst,
        n,X.length,TypingSites.scopeFunction scope⟩
  | .write (X := X) (n := n) scope E reference =>
      ⟨reference.name,reference.parts,true,some reference.binding.isExternal,
        some reference.binding.position,reference.binding.attribute,
        E.locals.map (fun p => (p.1,p.2.val)),E.functions.map Prod.fst,
        n,X.length,TypingSites.scopeFunction scope⟩

abbrev ContextPosition := TypingSites.Path × Position
abbrev ContextTrace := List (ContextPosition × Leaf)

def contextual (trace : TypingSites.Trace) : ContextTrace :=
  trace.flatMap fun entry => (siteTrace entry.2).map fun leaf =>
    ((entry.1,leaf.1),leaf.2)

def AllContexts (predicate : ContextPosition → Leaf → Prop) (trace : ContextTrace) : Prop :=
  ∀ entry ∈ trace, predicate entry.1 entry.2

theorem all_contextual (trace : TypingSites.Trace) (predicate : ContextPosition → Leaf → Prop) :
    AllContexts predicate (contextual trace) ↔
      TypingSites.All (fun context site =>
        everySite site (fun position leaf => predicate (context,position) leaf)) trace := by
  constructor
  · intro all entry present
    apply (all_site entry.2 (fun position leaf => predicate (entry.1,position) leaf)).mp
    intro leaf member
    exact all ((entry.1,leaf.1),leaf.2)
      (List.mem_flatMap.mpr ⟨entry,present,List.mem_map.mpr ⟨leaf,member,rfl⟩⟩)
  · intro all entry present
    obtain ⟨context,member,mapped⟩ := List.mem_flatMap.mp present
    obtain ⟨leaf,leafMember,same⟩ := List.mem_map.mp mapped
    cases same
    exact ((all_site context.2 _).mpr (all context member)) leaf leafMember

def Binding.target {X n} (binding : Binding X n true) : Target X n :=
  match binding with
  | .local index => .local index
  | .external reference => .external reference

theorem WriteLeaf.binding_sound {X n E} (leaf : @WriteLeaf X n E) :
    leaf.target = leaf.binding.target := by
  cases leaf with
  | mk name parts target typed => cases target <;> rfl

theorem ReadLeaf.checked {F X n E} (leaf : @ReadLeaf F X n E) :
    inferExpr E (.yulPath leaf.name leaf.parts) = some ⟨1,leaf.typed⟩ :=
  leaf.typed.complete

theorem WriteLeaf.checked {X n E} (leaf : @WriteLeaf X n E) :
    checkTarget E leaf.name leaf.parts = some ⟨leaf.target,leaf.typed⟩ :=
  leaf.typed.complete

def Leaf.accepted (leaf : Leaf) : Bool :=
  match leaf with
  | .read scope E reference =>
      (inferExpr (scope.reads E) (.yulPath reference.name reference.parts)).isSome
  | .write scope E reference =>
      (checkTarget (scope.writes E) reference.name reference.parts).isSome

theorem Leaf.accepted_true (leaf : Leaf) : leaf.accepted = true := by
  cases leaf with
  | read scope E reference => simp only [Leaf.accepted,reference.checked,Option.isSome_some]
  | write scope E reference => simp only [Leaf.accepted,reference.checked,Option.isSome_some]

end Solidity.Yul.TypingLeaves
