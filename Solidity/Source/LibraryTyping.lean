import Solidity.Source.ExpressionTyping

/-! Generic library-call resolution. Guards qualified-name shadowing and
using-target mismatches before typed delegated-call admission. Existing v1
statement typing is unchanged; these helpers alone admit no new statement. -/
namespace Solidity.Source

/-- A library named as a qualifier, respecting local shadowing. -/
def Ctx.libraryQualifier (C : Ctx) (receiver : Syn .expr) : Option String := by
  apply Syn.casesOn (motive := fun {_} _ => Option String) receiver
  case ident =>
    intro name
    exact match C.resolve name with
    | Option.some (.decls [d]) => if d.kind == .library then Option.some d.name else Option.none
    | _ => Option.none
  all_goals (intros; exact Option.none)

/-- Typed `using L for T` targets in a declaration tree. This generalized
elimination reuses the source syntax rather than introducing another AST. -/
def Syn.libraryUsings (E : Env) (scope : Option String) (ty : STy)
    {c : Cat} (s : Syn c) : List IdPath := by
  apply Syn.casesOn (motive := fun {_} _ => List IdPath) s
  case unit => intro xs; exact xs.libraryUsings E scope ty
  case cons => intro _ x xs; exact x.libraryUsings E scope ty ++ xs.libraryUsings E scope ty
  case topPart => intro x; exact x.libraryUsings E scope ty
  case contract => intro _ _ _ _ body; exact body.libraryUsings E scope ty
  case library => intro _ body; exact body.libraryUsings E scope ty
  case usingPart => intro _ u; exact u.libraryUsings E scope ty
  case usingPath =>
    intro lib target _
    cases target with
    | none => exact [lib]
    | some t => exact if (t.ty E scope .storage).any (fun actual => actual.same (ty.withLoc .storage)) then [lib] else []
  all_goals (intros; exact [])
termination_by structural s

/-- Qualified library calls keep their arguments; a `using` call prepends
its receiver exactly once. Overload checking verifies that receiver as well. -/
def Ctx.libraryArgs (C : Ctx) (receiver : Syn .expr) (args : Syn (.list .expr)) : Syn (.list .expr) :=
  if (C.libraryQualifier receiver).isSome then args else .cons receiver args

/-- Public/external library overloads, restricted to the actual qualifier or
the current contract library directives whose target matches the receiver. -/
def Ctx.libraryOverloads (C : Ctx) (receiver : Syn .expr) (f : String) (sigmas : List STy) : List Decl :=
  let libs := match C.libraryQualifier receiver with
    | some name => [name]
    | none => match sigmas with
      | [] => []
      | ty :: _ => (C.env.decls.filter (fun (d : Decl) => Option.some d.name == C.scope &&
          (d.kind == DeclKind.contract || d.kind == DeclKind.library))).flatMap fun (d : Decl) =>
          (d.node.libraryUsings C.env C.scope ty).filterMap fun path =>
            match C.env.lookupPath C.scope path with
            | [lib] => if lib.kind == DeclKind.library then Option.some lib.name else none
            | _ => none
  libs.eraseDups.flatMap fun name => extOverloads C.env C.isBase C.mapFree ⟨none, name⟩ f sigmas

/-- The typed delegated boundary: value or storage-pointer parameters and
value results. Other ABI copies remain an explicit implementation gap. -/
def libraryBoundary (ps rs : List STy) : Bool :=
  ps.all (fun ty => ty.isValue || match ty with
    | .bytes .storage | .string .storage | .array .storage _ _ | .struct .storage _ | .mapping _ _ => true
    | _ => false) && rs.all STy.isValue

end Solidity.Source
