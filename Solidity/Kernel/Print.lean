import Solidity.Kernel.Syntax

/-!
# Printing kernel terms as Solidity

`Prog.toStr` writes a kernel block back as the Solidity it came from:
`ksol[C]{ … }` and `Prog.toStr` round-trip up to parentheses, spacing, and
the `;` the notation wants after an `if`, which Solidity does not.  An
operator application is parenthesised unless it is the whole expression.
Kernel terms derive nothing (their constructors carry proofs), so this is how
an example shows a term.
-/

namespace Solidity
namespace Kernel

open Semantics

def BinOp.sym : BinOp → String
  | .add => "+" | .sub => "-" | .mul => "*" | .pow => "**" | .div => "/" | .mod => "%"
  | .lt => "<" | .gt => ">" | .le => "<=" | .ge => ">="
  | .eqB => "==" | .neB => "!=" | .and => "&&" | .or => "||"

def UnOp.sym : UnOp → String
  | .neg => "-" | .not => "!"

def tyStr : Ty → String
  | .prim .uint => "uint" | .prim .int => "int" | .prim .bool => "bool"
  | .ref (.struct s) => s
  | .ref (.array T) => tyStr T ++ "[]"
  | .ref (.mapping K V) => s!"mapping({tyStr K} => {tyStr V})"

variable {C : Contract} {Γ : Ctx}

mutual

def SPath.toStr {T : Ty} : SPath C Γ T → String
  | .alias x _ => x
  | .loc l => l.toStr

def Loc.toStr {T : Ty} : Loc C Γ T → String
  | .root r _ _ => r
  | .field b f _ => s!"{b.toStr}.{f}"
  | .mapIndex b i => s!"{b.toStr}[{i.toStr true}]"
  | .arrIndex b i => s!"{b.toStr}[{i.toStr true}]"

/-- `top` is whether the value stands alone, so needs no parentheses. -/
def Val.toStr {p : PrimTy} : Val C Γ p → (top : Bool := false) → String
  | .lit n _, _ => toString n
  | .bool b, _ => toString b
  | .local x _, _ => x
  | .read l, _ => l.toStr
  | .binop op _ a b, top =>
    let s := s!"{a.toStr} {BinOp.sym op} {b.toStr}"
    if top then s else s!"({s})"
  | .unop op _ a, _ => s!"{UnOp.sym op}{a.toStr}"

end

def Src.toStr {T : Ty} : Src C Γ T → String
  | .val v => v.toStr true
  | .copy p _ => p.toStr

mutual

def Stmt.toStr {Γ Γ' : Ctx} : Stmt C Γ Γ' → String
  | .assign l r => s!"{l.toStr} = {r.toStr};"
  | .rebind x _ r => s!"{x} = {r.toStr};"
  | .assignLocal x _ r => s!"{x} = {r.toStr true};"
  | .declLocal p x none => s!"{tyStr (.prim p)} {x};"
  | .declLocal p x (some e) => s!"{tyStr (.prim p)} {x} = {e.toStr true};"
  | .declStorage R x e => s!"{tyStr (.ref R)} storage {x} = {e.toStr};"
  | .declStorageSkip R x => s!"{tyStr (.ref R)} storage {x};"
  | .bindAlias R x e => s!"{tyStr (.ref R)} storage {x} = {e.toStr};"
  | .delete l => s!"delete {l.toStr};"
  | .ite c thn els => s!"if ({c.toStr true}) \{ {thn.toStr} } else \{ {els.toStr} }"
  | .require c => s!"require({c.toStr true});"
  | .assert c => s!"assert({c.toStr true});"
  | .revert => "revert();"

def Prog.toStr {Γ Γ' : Ctx} : Prog C Γ Γ' → String
  | .nil => ""
  | .cons s .nil => s.toStr
  | .cons s P => s!"{s.toStr} {P.toStr}"

end

/-- One statement per line, for display. -/
def Prog.show {Γ Γ' : Ctx} : Prog C Γ Γ' → String
  | .nil => ""
  | .cons s .nil => s.toStr
  | .cons s P => s!"{s.toStr}\n{P.show}"

end Kernel
end Solidity
