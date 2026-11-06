import Solidity.Syntax.Grammar
import Solidity.Syntax.Elab.Context

/-!
# Notices for literal loop bounds

Diagnostics only: neither the raw statements nor the intrinsic program is
rewritten. An invariant (including quantified invariants) or explicit unwind
clause suppresses the notice for that loop, but not for nested loops.
-/

namespace Solidity

private def RawExpr.boundInt? : RawExpr → Option Int
  | .num n => some (Int.ofNat n)
  | .unop .neg a => return -(← a.boundInt?)
  | _ => none

/-- A signed or unsigned integer literal, without evaluating other expressions. -/
def RawExpr.boundLiteral? (e : RawExpr) : Option String := e.boundInt?.map toString

/-- A readable subject for raw-body notices. The stable function/block path
still identifies complex expressions that have no source syntax at this use. -/
def RawExpr.boundSubject : RawExpr → String
  | .name x => x
  | .field a f => s!"{a.boundSubject}.{f}"
  | .index a i => s!"{a.boundSubject}[{i.boundLiteral?.getD i.boundSubject}]"
  | .call f _ => s!"{f}(…)"
  | .binop op a b => s!"({a.boundLiteral?.getD a.boundSubject} {op.sym} {b.boundLiteral?.getD b.boundSubject})"
  | _ => "expression"

/-- A literal comparison in a conjunction bounds the named counter
syntactically. This does not claim termination: the body may fail to advance it.
Disjunctions are not accepted as bounds. -/
def RawExpr.literalBound? : RawExpr → Option String
  | .binop .and a b => a.literalBound? <|> b.literalBound?
  | .binop op a b => do
    unless [.lt, .le, .gt, .ge].contains op do none
    match a.boundLiteral?, b.boundLiteral? with
    | none, some n => return s!"{a.boundSubject} {op.sym} {n}"
    | some n, none => return s!"{n} {op.sym} {b.boundSubject}"
    | _, _ => none
  | _ => none

/-- The loop as written, before lowering introduces break flags. -/
def RawStmt.literalLoop? (s : RawStmt) : Option String := do
  let (kind, spec, cond) ← match s with
    | .whileLoop a c _ => some ("while", a, c)
    | .doWhile a _ c => some ("do/while", a, c)
    | .forLoop a _ (some c) _ _ => some ("for", a, c)
    | .loop a c _ => some ("loop", a, c)
    | _ => none
  if !spec.inv.isEmpty || !spec.qinv.isEmpty || spec.unwind.isSome then none
  else return s!"{kind} ({← cond.literalBound?})"

/-- Stable statement/block paths identify loops whose original source syntax
is not available (a called function, or an imported body). -/
partial def literalLoopPaths (ss : List RawStmt) (pathPrefix : String := "body") : List String :=
  (ss.zipIdx).flatMap fun (s, i) =>
    let path := s!"{pathPrefix}.{i}"
    (s.literalLoop?.toList.map fun label => s!"{path}: {label}") ++
      (s.blocks.zipIdx).flatMap fun (b, j) => literalLoopPaths b s!"{path}/block{j}"

/-- Only reachable callees, once each. An unused function must not cause a
notice when a different program is elaborated. -/
def calledLiteralLoops (C : Contract) (ss : List RawStmt) : List String := Id.run do
  let direct := RawStmt.calleesList ss
  let funs := match C.ctor with
    | some f => ("constructor", f) :: C.funs
    | none => C.funs
  let fromBody := direct ++ direct.flatMap (reachable funs)
  let fromInit := if fromBody.contains "constructor" then
    C.inits.flatMap (fun (_, e) => e.callees) else []
  let names := (fromBody ++ fromInit ++ fromInit.flatMap (reachable funs)).eraseDups
  return names.flatMap fun name =>
    match Semantics.lookupBy name funs with
    | none => []
    | some f =>
      (literalLoopPaths f.body).map (s!"{name}/{·}") ++
        (f.mods.zipIdx).flatMap fun (m, i) =>
          (literalLoopPaths m.body s!"modifier{i}").map (s!"{name}/{·}")

open Lean in
private partial def boundNameSyntax? (e : Syntax) : Option String :=
  match e with
  | `(sol_expr| $x:ident) => some (x.getId.eraseMacroScopes.toString false)
  | `(sol_expr| ($c:sol_expr)) => boundNameSyntax? c
  | _ => none

open Lean in
private partial def boundIntSyntax? (e : Syntax) : Option Int :=
  match e with
  | `(sol_expr| $n:num) => some (Int.ofNat n.getNat)
  | `(sol_expr| -$a:sol_expr) => return -(← boundIntSyntax? a)
  | `(sol_expr| $n:num $u:ident) => do
    let factor ← unitFactor? (u.getId.eraseMacroScopes.toString false)
    return Int.ofNat (n.getNat * factor)
  | `(sol_expr| ($c:sol_expr)) => boundIntSyntax? c
  | _ => none

open Lean in
private def boundLiteralSyntax? (e : Syntax) : Option String :=
  (boundIntSyntax? e).map toString

open Lean in
/-- Literal-bound syntax, retaining its original source span for a notice. -/
partial def literalBoundSyntax? (e : Syntax) : Option String :=
  let subject (x : Syntax) : String :=
    (boundNameSyntax? x).getD ((x.reprint.getD "expression").trim)
  let compare (op : String) (a b : Syntax) : Option String :=
    match boundLiteralSyntax? a, boundLiteralSyntax? b with
    | none, some n => some s!"{subject a} {op} {n}"
    | some n, none => some s!"{n} {op} {subject b}"
    | _, _ => none
  match e with
  | `(sol_expr| $a:sol_expr < $b:sol_expr) => compare "<" a b
  | `(sol_expr| $a:sol_expr <= $b:sol_expr) => compare "<=" a b
  | `(sol_expr| $a:sol_expr > $b:sol_expr) => compare ">" a b
  | `(sol_expr| $a:sol_expr >= $b:sol_expr) => compare ">=" a b
  | `(sol_expr| $a:sol_expr && $b:sol_expr) => literalBoundSyntax? a <|> literalBoundSyntax? b
  | `(sol_expr| ($c:sol_expr)) => literalBoundSyntax? c
  | _ => none

open Lean in
/-- Source locations of unannotated literal loops, including nested bodies.
An annotation suppresses only the immediately annotated loop. -/
partial def literalLoopSyntax (s : Syntax) (stop : Syntax → Bool := fun _ => false) :
    Array (Syntax × String) := Id.run do
  if stop s then return #[]
  let mut cur := s
  let mut annotated := false
  while cur.getKind == ``solLoopSpec do
    let clause := cur[0]
    annotated := annotated || clause.getKind == ``solLoopForall ||
      ["invariant", "unwind"].contains (clause[5].getId.eraseMacroScopes.toString false)
    cur := cur[1]
  let head :=
    if cur.getKind == ``solWhile then some ("while", cur[2])
    else if cur.getKind == ``solDoWhile then some ("do/while", cur[4])
    else if cur.getKind == ``solFor && !cur[4].isNone then some ("for", cur[4][0])
    else none
  let own := if annotated then #[] else
    match head with
    | some (kind, cond) =>
      match literalBoundSyntax? cond with
      | some label => #[(cur, s!"{kind} ({label})")]
      | none => #[]
    | none => #[]
  return cur.getArgs.foldl (fun out child => out ++ literalLoopSyntax child stop) own

open Lean Elab in
/-- Report at the source boundary, once before modality readings or retries. -/
def warnLiteralLoopSyntax [Monad m] [MonadLog m] [AddMessageContext m] [MonadOptions m] (s : Syntax)
    (stop : Syntax → Bool := fun _ => false) : m Unit := do
  for (ref, name) in literalLoopSyntax s stop do
    logWarningAt ref m!"unannotated literal-bounded loop `{name}`; keeping symbolic unrolling"

end Solidity
