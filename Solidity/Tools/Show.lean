import Solidity.Semantics
import Solidity.Semantics.Run

/-!
# Printing states as Solidity

The printers the `Tools/` commands share, over the typed state: a value as
Solidity writes it (`SVal.fmt`, a fold over the typed value, its types as
`Ty.toStr` spells them), a storage one state variable per line
(`fmtStorage`) or on one line (`fmtStorageLine`), a transaction as `#run …
with` sets it (`fmtTx`), a typed run's halt (`fmtHalt`).  They are for
people, not for the kernel: nothing is proved about them.

A mapping prints its entries and then its default, `{7: 5, _: 0}`; an array
its live elements, not the `shadow` a `pop` leaves behind.
-/

namespace Solidity.Tools

open Semantics (Value lookupBy)

/-- A word: `5`, `-1`, `true`. -/
def Value.fmt : Value → String
  | .int n => toString n
  | .bool b => toString b

/-- A mapping's key as its type writes it: a `bool` key `true`, any other
the number. -/
def keyFmt (K : Ty) (k : Int) : String :=
  if K == .bool then toString (k != 0) else toString k

/-- **The printing fold**: a value as Solidity writes it, a struct's members
by name, an array's live elements, a mapping's entries over its default. -/
def fmtFold : Fold where
  V _ := String
  F _ := List (Name × String)
  L _ := Unit
  W _ _ := List String
  M _ := (Int → String) → List String
  prim v := Value.fmt (PrimTy.erase v)
  struct _ r := "{" ++ ", ".intercalate (r.map fun (f, v) => s!"{f}: {v}") ++ "}"
  array _ _ _ w _ := "[" ++ ", ".intercalate w ++ "]"
  fixed _ w := "[" ++ ", ".intercalate w ++ "]"
  map {K _} _ _ m d := "{" ++ ", ".intercalate (m (keyFmt K) ++ [s!"_: {d}"]) ++ "}"
  fnil := []
  fcons {f _ _} _ _ v r := (f, v) :: r
  lnil := ()
  lcons _ _ _ _ := ()
  wnil := []
  wcons _ _ v r := v :: r
  mnil := fun _ => []
  mcons k _ _ v r := fun key => s!"{key k}: {v}" :: r key

/-- A storage value as Solidity writes it. -/
def _root_.Solidity.SVal.fmt {T : Ty} (v : SVal T) : String := v.fold fmtFold

/-- The storage, one state variable per line, in the contract's order. -/
def fmtStorage (C : Contract) (st : Storage C) : List String :=
  (SFields.fold fmtFold st).map fun (r, v) => s!"{r} = {v}"

/-- The state variable `r` as Solidity writes it, if the storage has one. -/
def fmtRoot {C : Contract} (st : Storage C) (r : Name) : Option String :=
  lookupBy r (SFields.fold fmtFold st)

/-- The storage on one line: `count = 1; total = 0`. -/
def fmtStorageLine (C : Contract) (st : Storage C) : String :=
  "; ".intercalate (fmtStorage C st)

/-- A typed state printed by `#eval`: its storage on one line. -/
instance {C : Contract} {Γ : Ctx} : Repr (State C Γ) :=
  ⟨fun σ _ => Std.Format.text ("⟨" ++ fmtStorageLine C σ.storage ++ "⟩")⟩

/-- What a run starts from besides the storage and the arguments, as `#run
… with` sets it: the sender and the value always, the time, the funds and
the ledger where they are not zero. -/
def fmtTx {C : Contract} {Γ : Ctx} (σ : State C Γ) : List String :=
  [s!"msg.sender = {σ.tx.msgSender.1}", s!"msg.value = {σ.tx.msgValue.1}"] ++
  (if σ.tx.timestamp.1 = 0 then [] else [s!"block.timestamp = {σ.tx.timestamp.1}"]) ++
  (if σ.selfBalance.1 = 0 then [] else [s!"balance = {σ.selfBalance.1}"]) ++
  (if σ.net.isEmpty then [] else
    ["net = " ++ "{" ++ ", ".intercalate (σ.net.map fun (a, b) => s!"{a}: {b}") ++ "}"])

/-- A typed run's halt: running out of gas prints as a loop that never ends
(`THalt.exhausted`, which the untyped run did not tell apart). -/
def fmtHalt : THalt → String
  | .revert => "revert"
  | .panic => "panic (an `assert` failed)"
  | .diverge | .exhausted => "diverge (a loop that never ends)"

/-- A typed run's outcome: `ok`, or how it halted. -/
def fmtTRes {α : Type} : TRes α → String
  | .ok _ => "ok"
  | .error h => fmtHalt h

/-- How tightly a clause binds, as `SpecSyntax.lean` parses it: `*` 70,
`+` 65, a comparison 50, `==` 45, `&&` 35, `||` 30, `->` 25, `<->` 20. -/
def SpecExpr.prec : SpecExpr → Nat
  | .binop op _ _ => match op with
    | .mul | .div | .mod => 70
    | .add | .sub => 65
    | .lt | .le | .gt | .ge => 50
    | .eqB | .neB => 45
    | .and => 35
    | .or => 30
    | _ => 60
  | .imp .. => 25
  | .iff .. => 20
  | .all .. | .ex .. => 0
  | .unop .. => 75
  | _ => 100

/-- A clause as written, `count == \old(count) + 1`, parenthesised where
the grammar needs it. -/
partial def SpecExpr.fmt : SpecExpr → String
  | .num n => toString n
  | .bool b => toString b
  | .name x => x
  | .result => "\\result"
  | .old e => s!"\\old({SpecExpr.fmt e})"
  | .net e => s!"net({SpecExpr.fmt e})"
  | .field e f => s!"{SpecExpr.fmt.at 100 e}.{f}"
  | .index e k => s!"{SpecExpr.fmt.at 100 e}[{SpecExpr.fmt k}]"
  | .unop op e => s!"{UnOp.sym op}{SpecExpr.fmt.at 75 e}"
  | e@(.binop op a b) =>
    let p := SpecExpr.prec e
    s!"{SpecExpr.fmt.at p a} {BinOp.sym op} {SpecExpr.fmt.at (p + 1) b}"
  | .imp a b => s!"{SpecExpr.fmt.at 26 a} -> {SpecExpr.fmt.at 25 b}"
  | .iff a b => s!"{SpecExpr.fmt.at 20 a} <-> {SpecExpr.fmt.at 21 b}"
  | .all p x e => s!"\\forall {Ty.toStr (.prim p)} {x}; {SpecExpr.fmt e}"
  | .ex p x e => s!"\\exists {Ty.toStr (.prim p)} {x}; {SpecExpr.fmt e}"
where
  /-- An operand where the grammar expects precedence `p`: parenthesised
  if it binds less tightly. -/
  «at» (p : Nat) (e : SpecExpr) : String :=
    if SpecExpr.prec e < p then s!"({SpecExpr.fmt e})" else SpecExpr.fmt e

/-- An `assignable` location as written: `balances[msg.sender]`, `m[*]`. -/
partial def SpecLoc.fmt : SpecLoc → String
  | .root r => r
  | .field l f => s!"{SpecLoc.fmt l}.{f}"
  | .index l e => s!"{SpecLoc.fmt l}[{SpecExpr.fmt e}]"
  | .all l => s!"{SpecLoc.fmt l}[*]"

end Solidity.Tools
