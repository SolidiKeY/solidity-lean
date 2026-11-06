
import Solidity.Yul.FunctionScope
import Solidity.Source.Syntax

/-! Direct-block function header collection over existing intrinsic source
grammar. This connects supplied-header hoisting laws to actual block syntax;
function bodies, lexical validity/reserved names and full block typing remain
separate. No second raw AST or body representation is introduced. -/
namespace Solidity.Yul
open Solidity.Source (Syn)

/-- Independent classification of a direct statement's declaration header. -/
inductive HeaderD : Syn .yulStmt → Option (String × Sig) → Prop where
  | block {body} : HeaderD (.yulBlock body) none
  | let_ {first rest value} : HeaderD (.yulLet first rest value) none
  | assign {first rest value} : HeaderD (.yulAssign first rest value) none
  | expression {value} : HeaderD (.yulExprStmt value) none
  | if_ {condition body} : HeaderD (.yulIf condition body) none
  | for_ {pre condition post body} : HeaderD (.yulFor pre condition post body) none
  | switch {value cases fallback} : HeaderD (.yulSwitch value cases fallback) none
  | leave : HeaderD .yulLeave none
  | break_ : HeaderD .yulBreak none
  | continue_ : HeaderD .yulContinue none
  | function {name args rets body} :
      HeaderD (.yulFun name args rets body) (some (name, ⟨args.length, rets.length⟩))

/-- The explicit recursor generalizes the category as required by Gate G0.
Only the function constructor yields a direct header. -/

def headerNode {c : Solidity.Source.Cat} (s : Syn c) : Option (String × Sig) := by
  apply Syn.casesOn (motive := fun _ _ => Option (String × Sig)) s
  case yulFun =>
    intro name args rets body
    exact some (name, ⟨args.length, rets.length⟩)
  all_goals intros; exact none

theorem headerNode_sound (s : Syn .yulStmt) : HeaderD s (headerNode s) := by
  cases s with
  | yulBlock body => exact .block
  | yulLet first rest value => exact .let_
  | yulAssign first rest value => exact .assign
  | yulExprStmt value => exact .expression
  | yulIf condition body => exact .if_
  | yulFor pre condition post body => exact .for_
  | yulSwitch value cases fallback => exact .switch
  | yulLeave => exact .leave
  | yulBreak => exact .break_
  | yulContinue => exact .continue_
  | yulFun name args rets body => exact .function

theorem HeaderD.complete {s h} (d : HeaderD s h) : headerNode s = h := by
  cases d <;> rfl

/-- Collect only direct function declarations, without entering nested blocks,
loops or function bodies. Their declarations belong to different scopes. -/
inductive HeadersD : Syn (.list .yulStmt) → List (String × Sig) → Prop where
  | nil : HeadersD .nil []
  | skip {s rest headers} : HeaderD s none → HeadersD rest headers →
      HeadersD (.cons s rest) headers
  | cons {s rest header headers} : HeaderD s (some header) → HeadersD rest headers →
      HeadersD (.cons s rest) (header :: headers)

/-- This observer traverses list spines only; syntax bodies are never copied
into an intermediate representation. Public callers use the Yul-list category. -/

def collectHeaderNode {c : Solidity.Source.Cat} (s : Syn c) : List (String × Sig) := by
  apply Syn.casesOn (motive := fun _ _ => List (String × Sig)) s
  case cons =>
    intro c stmt rest
    exact match headerNode stmt with
      | none => collectHeaderNode rest
      | some h => h :: collectHeaderNode rest
  all_goals intros; exact []
termination_by structural s

def collectHeaders (s : Syn (.list .yulStmt)) : List (String × Sig) := collectHeaderNode s


/-- Category-generalized proof family keeps the structural recursion index a
variable, as required by G0 for S00's indexed syntax. -/
def HeaderCollectionResult : {c : Solidity.Source.Cat} → Syn c → Prop
  | .list .yulStmt, s => HeadersD s (collectHeaders s)
  | _, _ => True

def collectHeaderProof {c : Solidity.Source.Cat} (s : Syn c) : HeaderCollectionResult s := by
  cases s with
  | @nil c =>
      cases c with
      | yulStmt => exact HeadersD.nil
      | _ => exact True.intro
  | @cons c stmt rest =>
      have hr : HeaderCollectionResult rest := collectHeaderProof rest
      cases c with
      | yulStmt =>
          have hd : HeaderD stmt (headerNode stmt) := headerNode_sound stmt
          cases h : headerNode stmt with
          | none =>
              rw [h] at hd
              change HeadersD (.cons stmt rest) (match headerNode stmt with
                | none => collectHeaderNode rest | some h => h :: collectHeaderNode rest)
              rw [h]
              exact .skip hd hr
          | some header =>
              rw [h] at hd
              change HeadersD (.cons stmt rest) (match headerNode stmt with
                | none => collectHeaderNode rest | some h => h :: collectHeaderNode rest)
              rw [h]
              exact .cons hd hr
      | _ => exact True.intro
  | _ => exact True.intro
termination_by structural s

theorem collectHeaders_sound (s : Syn (.list .yulStmt)) : HeadersD s (collectHeaders s) :=
  collectHeaderProof s

theorem HeadersD.complete {s headers} (d : HeadersD s headers) :
    collectHeaders s = headers := by
  induction d with
  | nil => rfl
  | skip hd _ ih =>
      change (match headerNode _ with | none => collectHeaders _ | some h => h :: collectHeaders _) = _
      rw [hd.complete]
      exact ih
  | cons hd _ ih =>
      change (match headerNode _ with | none => collectHeaders _ | some h => h :: collectHeaders _) = _
      rw [hd.complete, ih]

/-- Actual collection plus freshness against the supplied ENTIRE visible
namespace, including names unavailable for executable capture. The caller must
supply that namespace; this record does not certify its provenance/completeness. -/
structure CheckedHeaders (visible : List String) (s : Syn (.list .yulStmt)) where
  headers : List (String × Sig)
  collected : HeadersD s headers
  fresh : Fresh visible (headers.map Prod.fst)

def checkHeaders (visible : List String) (s : Syn (.list .yulStmt)) :
    Option (CheckedHeaders visible s) :=
  let headers := collectHeaders s
  if h : fresh visible (headers.map Prod.fst) = true then
    some ⟨headers, collectHeaders_sound s, (fresh_iff _ _).mp h⟩
  else none

theorem HeadersD.check_complete {s headers visible} (d : HeadersD s headers)
    (hf : Fresh visible (headers.map Prod.fst)) :
    checkHeaders visible s = some ⟨headers, d, hf⟩ := by
  have he : collectHeaders s = headers := d.complete
  subst headers
  exact dif_pos ((fresh_iff _ _).mpr hf)


theorem checkHeaders_iff (visible : List String) (s : Syn (.list .yulStmt)) :
    (checkHeaders visible s).isSome = true ↔
      ∃ headers, HeadersD s headers ∧ Fresh visible (headers.map Prod.fst) := by
  constructor
  · intro h
    cases hc : checkHeaders visible s with
    | none =>
        simp only [hc, Option.isSome] at h
        cases h
    | some c => exact ⟨c.headers, c.collected, c.fresh⟩
  · rintro ⟨headers, d, hf⟩
    rw [d.check_complete hf]
    rfl

/-- Every direct declaration is available in the hoisted function table with
its exact arity, even before its declaration. Reserved-name legality, expression
callability and body checking remain separate obligations. -/
def CheckedHeaders.hoist {visible s F} (h : CheckedHeaders visible s) (older : FunctionNames F) :
    FunctionNames (h.headers.map Prod.snd ++ F) := hoistNames h.headers older

theorem CheckedHeaders.hoist_new {visible s F} (h : CheckedHeaders visible s)
    (older : FunctionNames F) {sig i name} (d : NamedFunction h.headers (s := sig) i name) :
    resolve (h.hoist older) name = some ⟨sig, i.append F⟩ :=
  hoistNames_new older h.fresh.1 d

end Solidity.Yul
