import Solidity.Yul.ExpressionCheck
import Solidity.Source.Syntax

/-!
# Solidity-local occurrence isolation inside Yul functions

Pinned ReferencesResolver.cpp236-313 visits variable identifiers even when they
will resolve to a Yul parameter/return slot; function call names are not such
identifiers. This is a separate component from Yul scope/arity checking.
The supplied names must be the original spellings whose FIRST outside lookup
selects a local Solidity variable. Constructing that set from actual Source/
solc identities is a separate provenance obligation. No lookup/type/policy/
placement/shape or Source admission follows from this component alone.
-/
namespace Solidity.Yul.OccurrenceCheck
open Solidity.Source (Syn Cat)

def suffixes : List String := ["slot", "offset", "length", "address", "selector"]

/-- Membership at full spelling or a supported one-suffix base. This is not
an ordered outside resolver: full-spelling priority/canonical-name coherence
belongs to the actual Source-name provenance obligation. Unsupported/malformed
suffixes are checked elsewhere; no general C++ resolver equivalence is claimed. -/
def SelectsLocal (names : List String) (name : String) (parts : List String) : Prop :=
  externalKey name parts ∈ names ∨
    ∃ suffix, suffix ∈ suffixes ∧ parts = [suffix] ∧ name ∈ names

instance (names : List String) (name : String) (parts : List String) :
    Decidable (SelectsLocal names name parts) := by
  unfold SelectsLocal
  exact inferInstance

def Allowed (names : List String) (inside : Bool) (name : String) (parts : List String) : Prop :=
  inside = false ∨ ¬ SelectsLocal names name parts
instance (names : List String) (inside : Bool) (name : String) (parts : List String) :
    Decidable (Allowed names inside name parts) := by
  unfold Allowed
  exact inferInstance

inductive Error where
  | unsupportedSourceNode
  | localCapture (name : String)
  deriving Repr, DecidableEq

/-- Empty paths contain no identifier occurrence. Their malformed assignment
shape is refused by AssignmentCheck; it is not this component's conclusion. -/
inductive PathsD (names : List String) (inside : Bool) : List (List String) → Type where
  | nil : PathsD names inside []
  | empty {rest} : PathsD names inside rest → PathsD names inside ([] :: rest)
  | cons {name parts rest} : Allowed names inside name parts → PathsD names inside rest →
      PathsD names inside ((name :: parts) :: rest)

def checkPaths (names : List String) (inside : Bool) :
    (paths : List (List String)) → Except Error (PathsD names inside paths)
  | [] => .ok .nil
  | [] :: rest => (checkPaths names inside rest).map PathsD.empty
  | (name :: parts) :: rest =>
    if permitted : Allowed names inside name parts then do
      pure (.cons permitted (← checkPaths names inside rest))
    else .error (.localCapture (externalKey name parts))

theorem PathsD.complete {names inside paths} (d : PathsD names inside paths) :
    checkPaths names inside paths = .ok d := by
  induction d with
  | nil => rfl
  | empty tail ih => simp only [checkPaths, ih]; rfl
  | cons permitted tail ih =>
    simp only [checkPaths, dif_pos permitted, ih]
    rfl

/-- Independent occurrence semantics over ORIGINAL indexed syntax. Generic empty
lists/options contain no occurrences; successful occurrence isolation alone does
not assert that an arbitrary Source category is legal Yul syntax. -/
inductive D (names : List String) : Bool → {category : Cat} → Syn category → Type where
  | nil {inside category} : D names inside (.nil (c := category))
  | cons {inside category first rest} : D names inside first → D names inside rest →
      D names inside (.cons (c := category) first rest)
  | none {inside category} : D names inside (.none (c := category))
  | some {inside category body} : D names inside body →
      D names inside (.some (c := category) body)
  | literal {inside literal} : D names inside (.yulLit literal)
  | path {inside name parts} : Allowed names inside name parts →
      D names inside (.yulPath name parts)
  | call {inside name args} : D names inside args → D names inside (.yulCall name args)
  | block {inside body} : D names inside body → D names inside (.yulBlock body)
  | declaration {inside first rest value} : D names inside value →
      D names inside (.yulLet first rest value)
  | assignment {inside first rest value} : PathsD names inside (first :: rest) →
      D names inside value → D names inside (.yulAssign first rest value)
  | expression {inside value} : D names inside value → D names inside (.yulExprStmt value)
  | if_ {inside condition body} : D names inside condition → D names inside body →
      D names inside (.yulIf condition body)
  | for_ {inside pre condition post body} : D names inside pre → D names inside condition →
      D names inside post → D names inside body → D names inside (.yulFor pre condition post body)
  | switch {inside value cases fallback} : D names inside value → D names inside cases →
      D names inside fallback → D names inside (.yulSwitch value cases fallback)
  | case_ {inside literal body} : D names inside body → D names inside (.yulCase literal body)
  | leave {inside} : D names inside .yulLeave
  | break_ {inside} : D names inside .yulBreak
  | continue_ {inside} : D names inside .yulContinue
  | function {inside name args rets body} : D names true body →
      D names inside (.yulFun name args rets body)

/-- Fixed-result, category-generalized recursion. Function bodies change the
inside flag; function headers/callees and unused parameter/return declarations
are not variable occurrences. No new intermediate program is constructed. -/
def check (names : List String) (inside : Bool) {category : Cat} (term : Syn category) :
    Except Error (D names inside term) := by
  apply Syn.casesOn (motive := fun _ term => Except Error (D names inside term)) term
  case nil => intros; exact .ok .nil
  case cons =>
    intro category first rest
    exact do pure (.cons (← check names inside first) (← check names inside rest))
  case none => intros; exact .ok .none
  case some => intro category body; exact (check names inside body).map D.some
  case yulLit => intro literal; exact .ok .literal
  case yulPath =>
    intro name parts
    exact if permitted : Allowed names inside name parts then .ok (.path permitted)
      else .error (.localCapture (externalKey name parts))
  case yulCall => intro name args; exact (check names inside args).map D.call
  case yulBlock => intro body; exact (check names inside body).map D.block
  case yulLet => intro first rest value; exact (check names inside value).map D.declaration
  case yulAssign =>
    intro first rest value
    exact do pure (.assignment (← checkPaths names inside (first :: rest)) (← check names inside value))
  case yulExprStmt => intro value; exact (check names inside value).map D.expression
  case yulIf =>
    intro condition body
    exact do pure (.if_ (← check names inside condition) (← check names inside body))
  case yulFor =>
    intro pre condition post body
    exact do pure (.for_ (← check names inside pre) (← check names inside condition)
      (← check names inside post) (← check names inside body))
  case yulSwitch =>
    intro value cases fallback
    exact do pure (.switch (← check names inside value) (← check names inside cases)
      (← check names inside fallback))
  case yulCase => intro literal body; exact (check names inside body).map D.case_
  case yulLeave => exact .ok .leave
  case yulBreak => exact .ok .break_
  case yulContinue => exact .ok .continue_
  case yulFun => intro name args rets body; exact (check names true body).map D.function
  all_goals intros; exact .error .unsupportedSourceNode
termination_by structural term

theorem D.complete {names inside category term} (d : @D names inside category term) :
    check names inside term = .ok d := by
  induction d with
  | nil => rfl
  | cons head tail ihHead ihTail =>
      change (check names _ _).bind _ = _
      rw [ihHead]
      change (check names _ _).bind _ = _
      rw [ihTail]
      rfl
  | none => rfl
  | some body ih =>
      change (check names _ _).map _ = _
      rw [ih]
      rfl
  | literal => rfl
  | path permitted => exact dif_pos permitted
  | call args ih =>
      change (check names _ _).map _ = _
      rw [ih]
      rfl
  | block body ih =>
      change (check names _ _).map _ = _
      rw [ih]
      rfl
  | declaration value ih =>
      change (check names _ _).map _ = _
      rw [ih]
      rfl
  | assignment paths value ih =>
      change (checkPaths names _ _).bind _ = _
      rw [paths.complete]
      change (check names _ _).bind _ = _
      rw [ih]
      rfl
  | expression value ih =>
      change (check names _ _).map _ = _
      rw [ih]
      rfl
  | if_ condition body ihCondition ihBody =>
      change (check names _ _).bind _ = _
      rw [ihCondition]
      change (check names _ _).bind _ = _
      rw [ihBody]
      rfl
  | for_ pre condition post body ihPre ihCondition ihPost ihBody =>
      change (check names _ _).bind _ = _
      rw [ihPre]
      change (check names _ _).bind _ = _
      rw [ihCondition]
      change (check names _ _).bind _ = _
      rw [ihPost]
      change (check names _ _).bind _ = _
      rw [ihBody]
      rfl
  | switch value cases fallback ihValue ihCases ihFallback =>
      change (check names _ _).bind _ = _
      rw [ihValue]
      change (check names _ _).bind _ = _
      rw [ihCases]
      change (check names _ _).bind _ = _
      rw [ihFallback]
      rfl
  | case_ body ih =>
      change (check names _ _).map _ = _
      rw [ih]
      rfl
  | leave => rfl
  | break_ => rfl
  | continue_ => rfl
  | function body ih =>
      change (check names true _).map _ = _
      rw [ih]
      rfl

theorem check_iff {category} (names : List String) (inside : Bool) (term : Syn category) :
    (check names inside term).isOk = true ↔ Nonempty (D names inside term) := by
  constructor
  · intro h
    cases actual : check names inside term with
    | error reason => rw [actual] at h; cases h
    | ok d => exact ⟨d⟩
  · rintro ⟨d⟩
    rw [d.complete]
    rfl


theorem path_no_capture {names name parts} (d : D names true (.yulPath name parts)) :
    ¬ SelectsLocal names name parts := by
  cases d with
  | path permitted =>
      rcases permitted with impossible | safe
      · cases impossible
      · exact safe

theorem path_capture_refused {names name parts} (selected : SelectsLocal names name parts) :
    check names true (.yulPath name parts) = .error (.localCapture (externalKey name parts)) := by
  have invalid : ¬ Allowed names true name parts := by
    intro permitted
    rcases permitted with impossible | safe
    · cases impossible
    · exact safe selected
  exact dif_neg invalid

theorem function_body {names inside name args rets body}
    (d : D names inside (.yulFun name args rets body)) : Nonempty (D names true body) := by
  cases d with
  | function bodyD => exact ⟨bodyD⟩

end Solidity.Yul.OccurrenceCheck
