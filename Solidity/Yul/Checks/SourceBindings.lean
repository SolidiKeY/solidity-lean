import Solidity.Yul.SourceBindings
namespace Solidity.Yul.Checks.SourceBindings
open Solidity.Source

def libraryDecl : Decl := ⟨.library, "same", none, true, .library "same" .nil⟩
def ctx : Ctx :=
  {env := ⟨[libraryDecl]⟩, scope := none,
   locals := [("same", .tuple [.bool, .bool]), ("same", .int .u8),
     ("a", .bool), ("b", .bool), ("keccak256", .bytes .memory),
     ("f", .fn true [] [] none), ("ptr", .array .storage (.int .u256) none)]}

def position (ctx : Ctx) (name : String) : Option Nat :=
  (checkSourceLocal ctx name).map fun ⟨ref, _⟩ => ref.index.toNat

example : position ctx "same" = some 0 := by decide
example : position ctx "a" = some 2 := by decide
example : position ctx "b" = some 3 := by decide
example : position ctx "keccak256" = some 4 := by decide
example : position ctx "f" = some 5 := by decide
example : position ctx "ptr" = some 6 := by decide
example : position ctx "missing" = none := by decide
example : position {ctx with locals := []} "same" = none := by decide
example : position {ctx with locals := []} "keccak256" = none := by decide
example : position {ctx with locals := []} "this" = none := by decide

/-- An unsupported assembly type still shadows the otherwise visible library.
Classification MUST happen after this selected occurrence, with no retry. -/
def selectedIsTuple : Bool :=
  (checkSourceLocal ctx "same").any fun ⟨ref, _⟩ =>
    match ref.ty with | .tuple _ => true | _ => false
example : selectedIsTuple = true := by decide

def selectedIsBool (name : String) : Bool :=
  (checkSourceLocal ctx name).any fun ⟨ref, _⟩ =>
    match ref.ty with | .bool => true | _ => false
example : selectedIsBool "a" = true := by decide
example : selectedIsBool "b" = true := by decide
example : selectedIsBool "same" = false := by decide

def selected := (checkSourceLocal ctx "b").get (by decide)
def actualRead : RExpr ctx.env ctx.tys selected.1.ty := selected.2.typed.toR
def actualWrite : RLVal ctx.env ctx.tys selected.1.ty := selected.2.lvalue.toR
example : actualRead = .local selected.1.index := selected.2.typed_toR
example : actualWrite = .local selected.1.index := selected.2.lvalue_toR

/-- Actual original S01 resolution distinguishes equal-typed positions. -/
example : ctx.resolve "a" = some (.loc 2) := rfl
example : ctx.resolve "b" = some (.loc 3) := rfl
example : ({ctx with locals := []} : Ctx).resolve "same" = some (.decls [libraryDecl]) := rfl

def unshadowed : Ctx := {ctx with locals := ctx.locals.tail}
example : position unshadowed "same" = some 0 := by decide
example : (checkSourceLocal ctx "same").isSome = true := by decide
example : (checkSourceLocal unshadowed "same").isSome = true := by decide

end Solidity.Yul.Checks.SourceBindings
