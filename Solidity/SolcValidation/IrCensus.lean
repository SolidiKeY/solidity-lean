import Solidity.SolcValidation.IrParse

/-!
# Census of a parsed IR tree

Function definitions and operation uses read off the intrinsic tree, so each
counted function is a resolved definition in its object scope (not a lexical
match on text). Used by the fixture checks and as the T02 matcher's index of
`fun_<name>_<id>` and helper definitions.
-/
namespace Solidity.SolcValidation.IrSyntax
open Solidity.SolcValidation

mutual
def Expr.ops {F L r} : Expr F L r → List String
  | .lit _ => []
  | .var _ _ => []
  | .op o args => o.name :: args.ops
  | .call _ args => args.ops

def Args.ops {F L k} : Args F L k → List String
  | .nil => []
  | .cons e rest => e.ops ++ rest.ops
end

def initOps {F L} {xs : List String} : Option (Expr F L xs.length) → List String
  | none => []
  | some e => e.ops

mutual
/-- Every function definition (with its signature) and operation use. -/
def Stmt.census {F c L} : Stmt F c L → List FnSig × List String
  | .block b => b.census
  | .discard e => ([], e.ops)
  | .assign _ e => ([], e.ops)
  | .if_ e b => let (f, o) := b.census; (f, e.ops ++ o)
  | .switch e cs => let (f, o) := cs.census; (f, e.ops ++ o)
  | .switchDefault e cs b =>
      let (f, o) := cs.census
      let (g, p) := b.census
      (f ++ g, e.ops ++ o ++ p)
  | .for_ lp => lp.census
  | .leave | .break_ | .continue_ => ([], [])

def Cases.census {F c L} : Cases F c L → List FnSig × List String
  | .nil => ([], [])
  | .cons _ b rest => let (f, o) := b.census; let (g, p) := rest.census; (f ++ g, o ++ p)

def Loop.census {F c L} : Loop F c L → List FnSig × List String
  | .stmt s rest => let (f, o) := s.census; let (g, p) := rest.census; (f ++ g, o ++ p)
  | .let_ _ e rest => let (g, p) := rest.census; (g, initOps e ++ p)
  | .run e post body =>
      let (f, o) := post.census
      let (g, p) := body.census
      (f ++ g, e.ops ++ o ++ p)

def Items.census {F c L g} : Items F c L g → List FnSig × List String
  | .nil => ([], [])
  | .stmt s rest => let (f, o) := s.census; let (g, p) := rest.census; (f ++ g, o ++ p)
  | .let_ _ e rest => let (g, p) := rest.census; (g, initOps e ++ p)
  | .fn _ rest => rest.census

def Block.census {F c L} : Block F c L → List FnSig × List String
  | .mk ss bodies items =>
      let (f, o) := bodies.census
      let (g, p) := items.census
      (ss ++ f ++ g, o ++ p)

def Bodies.census {F ss} : Bodies F ss → List FnSig × List String
  | .nil => ([], [])
  | .cons body rest => let (f, o) := body.census; let (g, p) := rest.census; (f ++ g, o ++ p)
end

mutual
/-- Per object (by its path of names), the functions and operations of its code. -/
def objectCensus (path : List String) : Object Code → List (List String × List FnSig × List String)
  | .object name code children =>
      let (fns, ops) := Block.census code
      (path ++ [name], fns, ops) :: objectsCensus (path ++ [name]) children
  | .data _ _ => []

def objectsCensus (path : List String) : List (Object Code) → List (List String × List FnSig × List String)
  | [] => []
  | o :: os => objectCensus path o ++ objectsCensus path os
end

end Solidity.SolcValidation.IrSyntax
