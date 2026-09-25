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

def Simple.toStr {p : PrimTy} : Simple C Γ p → String
  | .lit n _ => toString n
  | .bool b => toString b
  | .local x _ => x

mutual

def SPath.toStr {T : Ty} : SPath C Γ T → String
  | .alias x _ => x
  | .loc l => l.toStr

def Loc.toStr {T : Ty} : Loc C Γ T → String
  | .root r _ _ => r
  | .field b f _ => s!"{b.toStr}.{f}"
  | .index _ b i => s!"{b.toStr}[{i.toStr true}]"

/-- `top` is whether the value stands alone, so needs no parentheses. -/
def Val.toStr {p : PrimTy} : Val C Γ p → (top : Bool := false) → String
  | .simple s, _ => s.toStr
  | .read l, _ => l.toStr
  | .binop op _ _ a b, top =>
    let s := s!"{a.toStr} {BinOp.sym op} {b.toStr}"
    if top then s else s!"({s})"
  | .unop op _ _ a, _ => s!"{UnOp.sym op}{a.toStr}"

end

def Src.toStr {T : Ty} : Src C Γ T → String
  | .val v => v.toStr true
  | .copy p _ => p.toStr

def OpLoc.toStr {p : PrimTy} : OpLoc C Γ p → String
  | .local x _ => x
  | .root r _ _ => r
  | .field b f _ => s!"{b.toStr}.{f}"
  | .index _ b i => s!"{b.toStr}[{i.toStr}]"

/-- `x++`, `--x`. -/
def IncDec.show (op : IncDec) (x : String) : String :=
  let t := if op.isIncrement then "++" else "--"
  if op.isPre then t ++ x else x ++ t

mutual

def Stmt.toStr {Γ Γ' : Ctx} : Stmt C Γ Γ' → String
  | .assign l r => s!"{l.toStr} = {r.toStr};"
  | .rebind x _ r => s!"{x} = {r.toStr};"
  | .assignLocal x _ r => s!"{x} = {r.toStr true};"
  | .declLocal p x _ init =>
    match init with
    | none => s!"{tyStr (.prim p)} {x};"
    | some e => s!"{tyStr (.prim p)} {x} = {e.toStr true};"
  | .declStorage _ R x _ e => s!"{tyStr (.ref R)} storage {x} = {e.toStr};"
  | .opAssign op _ _ l r => s!"{l.toStr} {BinOp.sym op}= {r.toStr true};"
  | .incDec op _ l => s!"{IncDec.show op l.toStr};"
  | .assignIncDec x _ op _ l _ => s!"{x} = {IncDec.show op l.toStr};"
  | .delete l => s!"delete {l.toStr};"
  | .ite c thn els => s!"if ({c.toStr}) \{ {thn.toStr} } else \{ {els.toStr} }"
  | .require c => s!"require({c.toStr});"
  | .assert c => s!"assert({c.toStr});"
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
