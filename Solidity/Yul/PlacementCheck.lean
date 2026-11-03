import Solidity.Source.Syntax

/-! Intrinsic source control-placement derivations. This checks placement only:
names, scopes, references, literal ranges, arities and tier admission are separate.
The current loop component resets on nested loops as in pinned AsmParser.cpp;
an ancestor-init blanket prohibition would incorrectly refuse inner loop bodies. -/
namespace Solidity.Yul.Placement
open Solidity.Source (Syn Cat)

inductive Part where
  | outside | init | post | body
  deriving DecidableEq, Repr

structure Context where
  inFunction : Bool
  part : Part
  deriving DecidableEq, Repr

def Context.withPart (ctx : Context) (part : Part) : Context := ⟨ctx.inFunction, part⟩

inductive Error where
  | nonYulStatement
  | leaveOutsideFunction
  | breakOutsideLoop | breakInInit | breakInPost
  | continueOutsideLoop | continueInInit | continueInPost
  | functionInInit
  deriving DecidableEq, Repr

def breakError : Part → Error
  | .init => .breakInInit
  | .post => .breakInPost
  | .outside | .body => .breakOutsideLoop

def continueError : Part → Error
  | .init => .continueInInit
  | .post => .continueInPost
  | .outside | .body => .continueOutsideLoop

/-- Independent placement semantics on the ORIGINAL source grammar. -/
inductive Derivation : Context → {category : Cat} → Syn category → Type where
  | nilStatements {ctx} : Derivation ctx (.nil (c := .yulStmt))
  | consStatements {ctx s rest} : Derivation ctx s → Derivation ctx rest →
      Derivation ctx (.cons (c := .yulStmt) s rest)
  | block {ctx body} : Derivation ctx body → Derivation ctx (.yulBlock body)
  | declaration {ctx first rest value} : Derivation ctx (.yulLet first rest value)
  | assignment {ctx first rest value} : Derivation ctx (.yulAssign first rest value)
  | expression {ctx value} : Derivation ctx (.yulExprStmt value)
  | if_ {ctx condition body} : Derivation ctx body → Derivation ctx (.yulIf condition body)
  | for_ {ctx pre condition post body} :
      Derivation (ctx.withPart .init) pre →
      Derivation (ctx.withPart .post) post →
      Derivation (ctx.withPart .body) body →
      Derivation ctx (.yulFor pre condition post body)
  | switch {ctx value cases fallback} : Derivation ctx cases → Derivation ctx fallback →
      Derivation ctx (.yulSwitch value cases fallback)
  | leave {ctx} : ctx.inFunction = true → Derivation ctx .yulLeave
  | break_ {ctx} : ctx.part = .body → Derivation ctx .yulBreak
  | continue_ {ctx} : ctx.part = .body → Derivation ctx .yulContinue
  | function {ctx name args rets body} : ctx.part ≠ .init →
      Derivation ⟨true, .outside⟩ body →
      Derivation ctx (.yulFun name args rets body)
  | nilCases {ctx} : Derivation ctx (.nil (c := .yulCase))
  | consCases {ctx first rest} : Derivation ctx first → Derivation ctx rest →
      Derivation ctx (.cons (c := .yulCase) first rest)
  | case_ {ctx literal body} : Derivation ctx body → Derivation ctx (.yulCase literal body)
  | noDefault {ctx} : Derivation ctx (.none (c := .list .yulStmt))
  | default_ {ctx body} : Derivation ctx body →
      Derivation ctx (.some (c := .list .yulStmt) body)

private def consCheck (ctx : Context) (category : Cat) (head : Syn category)
    (tail : Syn (.list category)) (firstD : Except Error (Derivation ctx head))
    (restD : Except Error (Derivation ctx tail)) :
    Except Error (Derivation ctx (.cons head tail)) := by
  cases category with
  | yulStmt => exact do pure (.consStatements (← firstD) (← restD))
  | yulCase => exact do pure (.consCases (← firstD) (← restD))
  | _ => exact .error .nonYulStatement

private def someCheck (ctx : Context) (category : Cat) (body : Syn category)
    (bodyD : Except Error (Derivation ctx body)) :
    Except Error (Derivation ctx (.some body)) := by
  cases category with
  | list category =>
    cases category with
    | yulStmt => exact do pure (.default_ (← bodyD))
    | _ => exact .error .nonYulStatement
  | _ => exact .error .nonYulStatement

/-- Category-generalized source observer. Other source categories refuse;
no unrelated Solidity node can become a successful Yul placement derivation. -/
def check (ctx : Context) {category : Cat} (term : Syn category) :
    Except Error (Derivation ctx term) := by
  apply Syn.casesOn (motive := fun _ term => Except Error (Derivation ctx term)) term
  case nil =>
    intro category
    cases category with
    | yulStmt => exact .ok .nilStatements
    | yulCase => exact .ok .nilCases
    | _ => exact .error .nonYulStatement
  case cons =>
    intro category first rest
    exact consCheck ctx category first rest (check ctx first) (check ctx rest)
  case none =>
    intro category
    cases category with
    | list category =>
      cases category with
      | yulStmt => exact .ok .noDefault
      | _ => exact .error .nonYulStatement
    | _ => exact .error .nonYulStatement
  case some =>
    intro category body
    exact someCheck ctx category body (check ctx body)
  case yulBlock => intro body; exact do pure (.block (← check ctx body))
  case yulLet => intros; exact .ok .declaration
  case yulAssign => intros; exact .ok .assignment
  case yulExprStmt => intros; exact .ok .expression
  case yulIf => intro condition body; exact do pure (.if_ (← check ctx body))
  case yulFor =>
    intro pre condition post body
    exact do
      let preD ← check (ctx.withPart .init) pre
      let postD ← check (ctx.withPart .post) post
      let bodyD ← check (ctx.withPart .body) body
      pure (.for_ preD postD bodyD)
  case yulSwitch =>
    intro value cases fallback
    exact do pure (.switch (← check ctx cases) (← check ctx fallback))
  case yulCase => intro literal body; exact do pure (.case_ (← check ctx body))
  case yulLeave =>
    exact if h : ctx.inFunction = true then .ok (.leave h) else .error .leaveOutsideFunction
  case yulBreak =>
    exact if h : ctx.part = .body then .ok (.break_ h) else .error (breakError ctx.part)
  case yulContinue =>
    exact if h : ctx.part = .body then .ok (.continue_ h) else .error (continueError ctx.part)
  case yulFun =>
    intro name args rets body
    exact if h : ctx.part = .init then .error .functionInInit
      else do pure (.function h (← check ⟨true, .outside⟩ body))
  all_goals intros; exact .error .nonYulStatement
termination_by structural term

/-- Every independent placement derivation is reconstructed exactly.
No fuel or assumed checker-success premise is used. -/
theorem Derivation.complete {ctx category term} (d : @Derivation ctx category term) :
    check ctx term = .ok d := by
  induction d with
  | nilStatements => rfl
  | @consStatements ctx first rest df dr ihf ihr =>
    change (do let a ← check ctx first
               let b ← check ctx rest
               pure (Derivation.consStatements a b)) = _
    rw [ihf, ihr]
    rfl
  | @block ctx body d ih =>
    change (check ctx body >>= fun a => pure (Derivation.block a)) = _
    rw [ih]
    rfl
  | declaration => rfl
  | assignment => rfl
  | expression => rfl
  | @if_ ctx condition body d ih =>
    change (check ctx body >>= fun a => pure (@Derivation.if_ ctx condition body a)) = _
    rw [ih]
    rfl
  | @for_ ctx pre condition post body dp dq db ihp ihq ihb =>
    change (do let a ← check (ctx.withPart .init) pre
               let b ← check (ctx.withPart .post) post
               let c ← check (ctx.withPart .body) body
               pure (@Derivation.for_ ctx pre condition post body a b c)) = _
    rw [ihp, ihq, ihb]
    rfl
  | @switch ctx value cases fallback dc df ihc ihf =>
    change (do let a ← check ctx cases
               let b ← check ctx fallback
               pure (@Derivation.switch ctx value cases fallback a b)) = _
    rw [ihc, ihf]
    rfl
  | @leave ctx h =>
    change (if hf : ctx.inFunction = true then Except.ok (@Derivation.leave ctx hf)
      else Except.error Error.leaveOutsideFunction) = _
    rw [dif_pos h]
  | @break_ ctx h =>
    change (if hf : ctx.part = .body then Except.ok (@Derivation.break_ ctx hf)
      else Except.error (breakError ctx.part)) = _
    rw [dif_pos h]
  | @continue_ ctx h =>
    change (if hf : ctx.part = .body then Except.ok (@Derivation.continue_ ctx hf)
      else Except.error (continueError ctx.part)) = _
    rw [dif_pos h]
  | @function ctx name args rets body h d ih =>
    change (if hf : ctx.part = .init then .error .functionInInit
      else (check ⟨true, .outside⟩ body >>= fun a =>
        pure (@Derivation.function ctx name args rets body hf a))) = _
    rw [dif_neg h, ih]
    rfl
  | nilCases => rfl
  | @consCases ctx first rest df dr ihf ihr =>
    change (do let a ← check ctx first
               let b ← check ctx rest
               pure (Derivation.consCases a b)) = _
    rw [ihf, ihr]
    rfl
  | @case_ ctx literal body d ih =>
    change (check ctx body >>= fun a => pure (@Derivation.case_ ctx literal body a)) = _
    rw [ih]
    rfl
  | noDefault => rfl
  | @default_ ctx body d ih =>
    change (check ctx body >>= fun a => pure (Derivation.default_ a)) = _
    rw [ih]
    rfl

theorem check_accepts_iff {category} (ctx : Context) (term : Syn category) :
    (∃ d, check ctx term = .ok d) ↔ Nonempty (Derivation ctx term) :=
  ⟨fun ⟨d, _⟩ => ⟨d⟩, fun ⟨d⟩ => ⟨d, d.complete⟩⟩

/-- Assembly roots have neither a Yul function nor a Yul loop, even when the
surrounding Solidity source is itself a function/loop. -/
def rootContext : Context := ⟨false, .outside⟩

def checkBlock (body : Syn (.list .yulStmt)) :
    Except Error (Derivation rootContext body) := check rootContext body

theorem checkBlock_accepts_iff (body : Syn (.list .yulStmt)) :
    (∃ d, checkBlock body = .ok d) ↔ Nonempty (Derivation rootContext body) :=
  check_accepts_iff rootContext body

end Solidity.Yul.Placement
