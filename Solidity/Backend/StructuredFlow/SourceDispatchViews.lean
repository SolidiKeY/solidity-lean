import Solidity.Source.Value
import Solidity.Source.Resolved

/-!
# Typed structural views for the structured Source dispatcher

Guards accepting an unsupported expression merely because its outer tag looks
like a local assignment. Every view carries equality to the exact existing
Source term. These are extraction certificates, not syntax or semantics of a
second language. Indexed elimination uses generalising recursors via `cases`.
-/
namespace Solidity.Backend.StructuredFlow.SourceDispatch

structure LocalRead {E : Source.Env} {Γ : Source.RCtx} {τ : Source.STy}
    (e : Source.RExpr E Γ τ) where
  index : Source.Idx Γ τ
  exact : e = .local index

def localRead? {E : Source.Env} {Γ : Source.RCtx} {τ : Source.STy}
    (e : Source.RExpr E Γ τ) : Option (LocalRead e) := by
  cases e
  case «local» i => exact some ⟨i,rfl⟩
  all_goals exact none

structure LocalWrite {E : Source.Env} {Γ : Source.RCtx} {τ : Source.STy}
    (e : Source.RExpr E Γ τ) where
  index : Source.Idx Γ τ
  value : Source.RExpr E Γ τ
  exact : e = .assign (.local index) value

def localWrite? {E : Source.Env} {Γ : Source.RCtx} {τ : Source.STy}
    (e : Source.RExpr E Γ τ) : Option (LocalWrite e) := by
  cases e
  case assign l r =>
    cases l
    case «local» i => exact some ⟨i,r,rfl⟩
    all_goals exact none
  all_goals exact none

structure LocalCopy {E : Source.Env} {Γ : Source.RCtx} {τ : Source.STy}
    (e : Source.RExpr E Γ τ) where
  dest : Source.Idx Γ τ
  donor : Source.Idx Γ τ
  exact : e = .assign (.local dest) (.local donor)

def localCopy? {E : Source.Env} {Γ : Source.RCtx} {τ : Source.STy}
    (e : Source.RExpr E Γ τ) : Option (LocalCopy e) := do
  let write ← localWrite? e
  let read ← localRead? write.value
  return ⟨write.index,read.index,write.exact.trans
    (congrArg (fun rhs => Source.RExpr.assign (.local write.index) rhs) read.exact)⟩

inductive Literal {E : Source.Env} {Γ : Source.RCtx} :
    {τ : Source.STy} → Source.RExpr E Γ τ → Type where
  | bool (value : Bool) : Literal (.bool value)

def literal? {E : Source.Env} {Γ : Source.RCtx} {τ : Source.STy}
    (e : Source.RExpr E Γ τ) : Option (Literal e) := by
  cases e
  case bool b => exact some (.bool b)
  all_goals exact none

inductive CopyStatement {E : Source.Env} {R : List Source.STy} {M : Bool} :
    {k : Source.SCtx} → {Γ Δ : Source.RCtx} → Source.RStmt E R M k Γ Δ → Type where
  | copy {k : Source.SCtx} {Γ : Source.RCtx} {τ : Source.STy}
      (dest donor : Source.Idx Γ τ) :
      CopyStatement (.expr (.assign (.local dest) (.local donor)) : Source.RStmt E R M k Γ Γ)

def copyStatement? {E : Source.Env} {R : List Source.STy} {M : Bool}
    {k : Source.SCtx} {Γ Δ : Source.RCtx} (s : Source.RStmt E R M k Γ Δ) :
    Option (CopyStatement s) := by
  cases s
  case expr e =>
    exact do
      let copy ← localCopy? e
      return (by
        cases copy with
        | mk i a eq =>
          cases eq
          exact .copy i a)
  all_goals exact none

inductive BoolCopyStatement {E : Source.Env} {R : List Source.STy} {M : Bool} :
    {k : Source.SCtx} → {Γ Δ : Source.RCtx} → Source.RStmt E R M k Γ Δ → Type where
  | copy {k Γ} (dest donor : Source.Idx Γ .bool) :
      BoolCopyStatement (.expr (.assign (.local dest) (.local donor)) : Source.RStmt E R M k Γ Γ)

def boolCopyStatement? {E : Source.Env} {R : List Source.STy} {M : Bool}
    {k : Source.SCtx} {Γ Δ : Source.RCtx} (s : Source.RStmt E R M k Γ Δ) :
    Option (BoolCopyStatement s) := by
  cases h : copyStatement? s with
  | none => exact none
  | some copy =>
    cases copy with
    | @copy τ i a =>
      if ht : τ = .bool then
        cases ht
        exact some (.copy i a)
      else exact none

inductive BoolWriteStatement {E : Source.Env} {R : List Source.STy} {M : Bool} :
    {k : Source.SCtx} → {Γ Δ : Source.RCtx} → Source.RStmt E R M k Γ Δ → Type where
  | set {k Γ} (index : Source.Idx Γ .bool) (value : Bool) :
      BoolWriteStatement (.expr (.assign (.local index) (.bool value)) : Source.RStmt E R M k Γ Γ)

def boolWriteStatement? {E : Source.Env} {R : List Source.STy} {M : Bool}
    {k : Source.SCtx} {Γ Δ : Source.RCtx} (s : Source.RStmt E R M k Γ Δ) :
    Option (BoolWriteStatement s) := by
  cases s
  case expr e =>
    exact do
      let write ← localWrite? e
      let lit ← literal? write.value
      return (by
        cases write with
        | mk i value eq =>
          cases lit with
          | bool b =>
            cases eq
            exact .set i b)
  all_goals exact none

inductive BlockStatement {E : Source.Env} {R : List Source.STy} {M : Bool} :
    {k : Source.SCtx} → {Γ Δ : Source.RCtx} → Source.RStmt E R M k Γ Δ → Type where
  | block {k Γ tailΓ} (items : Source.RItems E R M k Γ tailΓ) :
      BlockStatement (.block items)

def blockStatement? {E : Source.Env} {R : List Source.STy} {M : Bool}
    {k : Source.SCtx} {Γ Δ : Source.RCtx} (s : Source.RStmt E R M k Γ Δ) :
    Option (BlockStatement s) := by
  cases s
  case block items => exact some (.block items)
  all_goals exact none

inductive ItemHead {E : Source.Env} {R : List Source.STy} {M : Bool} :
    {k : Source.SCtx} → {Γ Δ : Source.RCtx} → Source.RItems E R M k Γ Δ → Type where
  | stmt {k Γ midΓ Δ} (head : Source.RStmt E R M k Γ midΓ)
      (tail : Source.RItems E R M k midΓ Δ) : ItemHead (.stmt head tail)

def itemHead? {E : Source.Env} {R : List Source.STy} {M : Bool}
    {k : Source.SCtx} {Γ Δ : Source.RCtx} (items : Source.RItems E R M k Γ Δ) :
    Option (ItemHead items) := by
  cases items
  case stmt head tail => exact some (.stmt head tail)
  all_goals exact none

inductive EmptyItems {E : Source.Env} {R : List Source.STy} {M : Bool} :
    {k : Source.SCtx} → {Γ Δ : Source.RCtx} → Source.RItems E R M k Γ Δ → Type where
  | nil {k Γ} : EmptyItems (Source.RItems.nil : Source.RItems E R M k Γ Γ)

def emptyItems? {E : Source.Env} {R : List Source.STy} {M : Bool}
    {k : Source.SCtx} {Γ Δ : Source.RCtx} (items : Source.RItems E R M k Γ Δ) :
    Option (EmptyItems items) := by
  cases items
  case nil => exact some .nil
  all_goals exact none

inductive ReturnStatement {E : Source.Env} {R : List Source.STy} {M : Bool} :
    {k : Source.SCtx} → {Γ Δ : Source.RCtx} → Source.RStmt E R M k Γ Δ → Type where
  | ret {k Γ} (empty : R = []) : ReturnStatement (Source.RStmt.ret (E := E) (M := M) (k := k) (Γ := Γ) empty)

def returnStatement? {E : Source.Env} {R : List Source.STy} {M : Bool}
    {k : Source.SCtx} {Γ Δ : Source.RCtx} (s : Source.RStmt E R M k Γ Δ) :
    Option (ReturnStatement s) := by
  cases s
  case ret h => exact some (.ret h)
  all_goals exact none

inductive BreakStatement {E : Source.Env} {R : List Source.STy} {M : Bool} :
    {k : Source.SCtx} → {Γ Δ : Source.RCtx} → Source.RStmt E R M k Γ Δ → Type where
  | brk {u Γ} : BreakStatement (Source.RStmt.brk (E := E) (R := R) (M := M) (u := u) (Γ := Γ))

def breakStatement? {E : Source.Env} {R : List Source.STy} {M : Bool}
    {k : Source.SCtx} {Γ Δ : Source.RCtx} (s : Source.RStmt E R M k Γ Δ) :
    Option (BreakStatement s) := by
  cases s
  case brk => exact some .brk
  all_goals exact none

inductive ContinueStatement {E : Source.Env} {R : List Source.STy} {M : Bool} :
    {k : Source.SCtx} → {Γ Δ : Source.RCtx} → Source.RStmt E R M k Γ Δ → Type where
  | cont {u Γ} : ContinueStatement (Source.RStmt.cont (E := E) (R := R) (M := M) (u := u) (Γ := Γ))

def continueStatement? {E : Source.Env} {R : List Source.STy} {M : Bool}
    {k : Source.SCtx} {Γ Δ : Source.RCtx} (s : Source.RStmt E R M k Γ Δ) :
    Option (ContinueStatement s) := by
  cases s
  case cont => exact some .cont
  all_goals exact none

inductive SkipStatement {E : Source.Env} {R : List Source.STy} {M : Bool} :
    {k : Source.SCtx} → {Γ Δ : Source.RCtx} → Source.RStmt E R M k Γ Δ → Type where
  | skip {k Γ} : SkipStatement (Source.RStmt.skip (E := E) (R := R) (M := M) (k := k) (Γ := Γ))

def skipStatement? {E : Source.Env} {R : List Source.STy} {M : Bool}
    {k : Source.SCtx} {Γ Δ : Source.RCtx} (s : Source.RStmt E R M k Γ Δ) :
    Option (SkipStatement s) := by
  cases s
  case skip => exact some .skip
  all_goals exact none

@[simp] theorem localRead_local {E : Source.Env} {Γ : Source.RCtx} {τ : Source.STy}
    (i : Source.Idx Γ τ) : localRead? (Source.RExpr.local (E := E) i) = some ⟨i,rfl⟩ := rfl

@[simp] theorem localCopy_copy {E : Source.Env} {Γ : Source.RCtx} {τ : Source.STy}
    (i a : Source.Idx Γ τ) :
    localCopy? (Source.RExpr.assign (E := E) (.local i) (.local a)) = some ⟨i,a,rfl⟩ := rfl

@[simp] theorem copyStatement_copy {E : Source.Env} {R : List Source.STy} {M : Bool}
    {k : Source.SCtx} {Γ : Source.RCtx} {τ : Source.STy} (i a : Source.Idx Γ τ) :
    copyStatement? (Source.RStmt.expr (E := E) (R := R) (M := M) (k := k)
      (.assign (.local i) (.local a))) = some (.copy i a) := rfl

@[simp] theorem boolCopyStatement_copy {E : Source.Env} {R : List Source.STy} {M : Bool}
    {k : Source.SCtx} {Γ : Source.RCtx} (i a : Source.Idx Γ .bool) :
    boolCopyStatement? (Source.RStmt.expr (E := E) (R := R) (M := M) (k := k)
      (.assign (.local i) (.local a))) = some (.copy i a) := rfl

@[simp] theorem boolWriteStatement_set {E : Source.Env} {R : List Source.STy} {M : Bool}
    {k : Source.SCtx} {Γ : Source.RCtx} (i : Source.Idx Γ .bool) (b : Bool) :
    boolWriteStatement? (Source.RStmt.expr (E := E) (R := R) (M := M) (k := k)
      (.assign (.local i) (.bool b))) = some (.set i b) := rfl

end Solidity.Backend.StructuredFlow.SourceDispatch
