import Solidity.Calculus.Core.Delab

/-!
# `dl{ … }` writing scoped taclets: a prototype

How the cutover will read `Rules.lean`'s rule lines into scoped taclets
without changing their text (`docs/intrinsic.md`, "how `dl{ … }` will write
a scoped taclet"): the reader inserts what scoping needs, and the printer
(`Calculus/Core/Delab.lean`) hides it again.

* **The `\find` is read in its own context `Γ`**: a local schema variable
  (`v`) is a position `Idx Γ t`, an expression one (`se`, `nsp`) a part of
  `Γ`, a block (`thenStm`) a `Prog C Γ Γ₁`.
* **The premise counts the fresh locals it declares** (`T storage sp = nsp;`
  is `declStorage _ (.fresh "sp" k) …`): a fresh local is `.here` lifted past
  the ones declared after it, and a `\find` schema variable read after `d`
  of them is weakened `d` times, a position by `.there`, a part by its
  `up` (`Calculus/Core/Step.lean`).  An unfolding premise pops them after
  itself: `Premise.unfold P (Ext.push^d .refl)`, `pop .capture` once
  `Premise.fml` places it.
* **A branch is a block**: the split of an `if` ends its goals with `}`
  (`BlockKind.block`), of anything else invisibly (`.capture`).
* **A side condition** is read off the `\find` as today (`sideConds`): a
  non-simple `nsp` carries `SPath.isSimple nsp = false`, an `autoParam`
  (`taclet_side%`).

The rules are `scoped` to this namespace: inside it, `dl{ ⟨[ s; ]⟩ ⇝ p }`
writes `Taclet C k m s p` for the `Taclet` in scope where it is used, so the
lines below are `Rules.lean`'s, character for character, except
`storageFieldRead_unfold_rightFst`'s target: `v`, a local, as
`Calculus/Core/Taclet.lean` states it (the scoped syntax has no holes yet).
The prototype reads only what these three lines need; at the cutover the
same insertions go into `schemaAt`/`schemaStmt`/`declVar` themselves.
`Taclet.toCore` and `Taclet.ofCore` check that the lines write exactly the
hand-written constructors of `Core.Taclet`.
-/

namespace Solidity.Core.Schema

open Lean (Ident Macro MacroM mkIdent TSyntax Syntax)
open Solidity (schemaIdent stemOf nameParts partIdent proofIdent)

/-- The fresh locals a premise declared so far, newest first: a name, and
whether it is a storage alias. -/
abbrev Fresh := List (String × Bool)

/-- `f` applied `n` times. -/
def iter (f : Lean.Term → MacroM Lean.Term) : Nat → Lean.Term → MacroM Lean.Term
  | 0, t => pure t
  | n + 1, t => do iter f n (← f t)

/-- The fresh local `j` places below the newest. -/
def freshIdx (j : Nat) : MacroM Lean.Term := do iter (fun t => `(Idx.there $t)) j (← `(Idx.here))

/-- A `\find` position read under `d` fresh locals. -/
def idxAt (d : Nat) (x : Lean.Term) : MacroM Lean.Term := iter (fun t => `(Idx.there $t)) d x

/-- The sort an expression position asks for. -/
inductive Pos where
  | val | simple | spath
  deriving DecidableEq

/-- A name: a fresh local of the premise, or a `\find` schema variable by
its stem, weakened past the fresh locals. -/
def head (Γ : Fresh) (pos : Pos) (x : Ident) (n : String) : MacroM Lean.Term := do
  if let some j := Γ.findIdx? (·.1 == n) then
    let i ← freshIdx j
    match Γ[j]!.2, pos with
    | true, .spath => return ← `(SPath.alias $i)
    | false, .val => return ← `(Val.simple (Simple.local $i))
    | false, .simple => return ← `(Simple.local $i)
    | _, _ => Macro.throwErrorAt x s!"`{n}` cannot stand here"
  let d := Γ.length
  match stemOf n, pos with
  | "v", .val => do `(Val.simple (Simple.local $(← idxAt d x)))
  | "v", .simple => do `(Simple.local $(← idxAt d x))
  | "se", .val => do `(Val.simple $(← iter (fun t => `(Simple.up $t)) d x))
  | "se", .simple => iter (fun t => `(Simple.up $t)) d x
  | "nsp", .spath | "sp", .spath => iter (fun t => `(SPath.up $t)) d x
  | _, _ => Macro.throwErrorAt x s!"the prototype does not read `{n}` here"

/-- A program expression: a name, or a member of a storage path. -/
def expr (Γ : Fresh) (pos : Pos) : TSyntax `sol_expr → MacroM Lean.Term
  | `(sol_expr| $x:ident) => do
    match nameParts x.getId with
    | [n] => head Γ pos x n
    | [b, f] =>
      let base ← head Γ .spath (partIdent x b) b
      let fld := partIdent x f
      let loc ← `(Loc.field $base $fld $(proofIdent fld f))
      match pos with
      | .val => `(Val.read $loc)
      | .spath => `(SPath.loc $loc)
      | .simple => Macro.throwErrorAt x "a member is not simple"
    | _ => Macro.throwErrorAt x "the prototype reads one member deep"
  | e => Macro.throwErrorAt e "the prototype reads names and members only"

/-- A local written to: a fresh one, or a `\find` position. -/
def target (Γ : Fresh) (x : Ident) : MacroM Lean.Term := do
  let n := x.getId.toString
  if let some j := Γ.findIdx? (·.1 == n) then return ← freshIdx j
  idxAt Γ.length x

/-- A branch: a block schema variable. -/
def block : TSyntax `sol_block → MacroM Lean.Term
  | `(sol_block| $x:ident) => pure x
  | b => Macro.throwErrorAt b "the prototype reads a block variable only"

/-- A statement, and the fresh locals after it. -/
def stmt (fresh : Bool) (Γ : Fresh) : TSyntax `sol_stmt → MacroM (Lean.Term × Fresh)
  | `(sol_stmt| if ( $c:sol_expr ) $t:sol_block else $f:sol_block) => do
    return (← `(Stmt.ite $(← expr Γ .val c) $(← block t) $(← block f)), Γ)
  | stx@`(sol_stmt| $_:sol_ty storage $x:ident = $r:sol_expr) => do
    unless fresh do Macro.throwErrorAt stx "the prototype's `\\find` declares nothing"
    unless stemOf x.getId.toString == "sp" do Macro.throwErrorAt x "a fresh alias is an `sp`"
    let t ← `(Stmt.declStorage _ (Var.fresh "sp" $(schemaIdent "k"))
      (some (ARhs.path $(← expr Γ .spath r))))
    return (t, (x.getId.toString, true) :: Γ)
  | `(sol_stmt| $l:ident = $r:sol_expr) => do
    return (← `(Stmt.assignLocal $(← target Γ l) $(← expr Γ .val r)), Γ)
  | stx => Macro.throwErrorAt stx "the prototype does not read this statement"

/-- A term of a formula or an update: a simple schema variable lowered, a
local, or a Boolean literal. -/
def term (Γ : Fresh) : TSyntax `dl_term → MacroM Lean.Term
  | `(dl_term| $x:ident) => do
    let n := x.getId.toString
    if n == "true" || n == "false" then
      return ← `(Tm.app0 (Solidity.Op0.lit (Solidity.Semantics.PrimVal.bool $x)))
    match stemOf n with
    | "se" => do `(Simple.lower $(← iter (fun t => `(Simple.up $t)) Γ.length x))
    | "v" => do `(Tm.pvV $(← target Γ x))
    | _ => Macro.throwErrorAt x s!"the prototype does not read `{n}` in a term"
  | t => Macro.throwErrorAt t "the prototype reads names only"

/-- A condition: `a = b`. -/
def fml (Γ : Fresh) : TSyntax `dl_fml → MacroM Lean.Term
  | `(dl_fml| $a:dl_term = $b:dl_term) => do `(Fml.eq $(← term Γ a) $(← term Γ b))
  | φ => Macro.throwErrorAt φ "the prototype reads `a = b` only"

/-- The premise, its branches ended as `b` says. -/
def premise (b : Lean.Term) : TSyntax `dl_premise → MacroM Lean.Term
  | `(dl_premise| { $[$es]‖* } ⟨[ ]⟩) => do
    let mut U ← `(Upd.nil)
    for e in es do
      match e with
      | `(dl_upd_elem| $x:ident := $r:dl_term) =>
        U ← `(Upd.snoc $U (UpdElem.local $(← target [] x) (Rhs.val $(← term [] r))))
      | _ => Macro.throwErrorAt e "the prototype reads `v := t` only"
    `(Premise.update $U)
  | `(dl_premise| ⟨[ $[$ss:sol_stmt;]* ]⟩) => do
    let mut Γ : Fresh := []
    let mut ts : Array Lean.Term := #[]
    for s in ss do
      let (t, Γ') ← stmt true Γ s
      ts := ts.push t
      Γ := Γ'
    let P ← ts.foldrM (fun t acc => `(Prog.cons $t $acc)) (← `(Prog.nil))
    `(Premise.unfold $P $(← iter (fun t => `(Ext.push $t)) Γ.length (← `(Ext.refl))))
  | `(dl_premise| $[$_:str :]? $c:dl_fml ⟹ ⟨[ $t:ident ]⟩ ; $[$_:str :]? $c':dl_fml ⟹ ⟨[ $f:ident ]⟩) => do
    `(Premise.split $b $(← fml [] c) $(← fml [] c') $t $f)
  | p => Macro.throwErrorAt p "the prototype does not read this premise"

/-- The `\find`'s side conditions: a non-simple storage path. -/
partial def sideConds : Syntax → Array (Ident × Lean.Term)
  | stx@(.ident ..) =>
    match nameParts stx.getId with
    | n :: _ =>
      if stemOf n == "nsp" then
        let x : Ident := partIdent ⟨stx⟩ n
        #[(mkIdent (Lean.Name.mkSimple ("h" ++ n)), Lean.Unhygienic.run `(SPath.isSimple $x = false))]
      else #[]
    | [] => #[]
  | .node _ _ args => args.flatMap sideConds
  | _ => #[]

/-- `⟨[ s; ]⟩ ⇝ p`: the `Taclet` in scope where the line is used. -/
def taclet (s : TSyntax `sol_stmt) (p : TSyntax `dl_premise) : MacroM Lean.Term := do
  let (st, _) ← stmt false [] s
  let b ← match s with
    | `(sol_stmt| if ( $_:sol_expr ) $_:sol_block else $_:sol_block) => `(BlockKind.block)
    | _ => `(BlockKind.capture)
  let t ← `($(mkIdent `Taclet) $(schemaIdent "C") $(schemaIdent "k") $(schemaIdent "m") $st
    $(← premise b p))
  let conds := sideConds s
  if conds.isEmpty then return t
  let hs := conds.map (·.1)
  let cs := conds.map (·.2)
  `(taclet_side% $t $[($hs : $cs)]*)

scoped macro_rules
  | `(dl{ ⟨[ $s:sol_stmt; ]⟩ ⇝ $p:dl_premise }) => taclet s p

/-! ## Three lines of `Rules.lean` -/

/-- The scoped taclets the macro writes from today's lines. -/
inductive Taclet (C : Contract) (k : Nat) (m : Modality) :
    {Γ Γ' : Ctx} → Stmt C Γ Γ' → Premise C Γ Γ' → Prop where
  | localValueAssign :
      dl{ ⟨[ v = se; ]⟩ ⇝ { v := se } ⟨[ ]⟩ }
  | storageFieldRead_unfold_rightFst :
      dl{ ⟨[ v = nsp.fld; ]⟩ ⇝ ⟨[ T storage sp = nsp; v = sp.fld; ]⟩ }
  | ifElseSplit :
      dl{ ⟨[ if (se) thenStm else elseStm; ]⟩ ⇝
          "if s#se true": se = true ⟹ ⟨[ thenStm ]⟩ ; "if s#se false": se = false ⟹ ⟨[ elseStm ]⟩ }

/-- The lines write the hand-written constructors of `Core.Taclet`. -/
theorem Taclet.toCore {C : Contract} {k : Nat} {m : Modality} {Γ Γ' : Ctx} {s : Stmt C Γ Γ'}
    {p : Premise C Γ Γ'} (h : Taclet C k m s p) : Core.Taclet C k m s p := by
  cases h with
  | localValueAssign => exact .localValueAssign
  | storageFieldRead_unfold_rightFst hn => exact .storageFieldRead_unfold_rightFst hn
  | ifElseSplit => exact .ifElseSplit

theorem Taclet.ofCore {C : Contract} {k : Nat} {m : Modality} {Γ Γ' : Ctx} {s : Stmt C Γ Γ'}
    {p : Premise C Γ Γ'} (h : Core.Taclet C k m s p) : Taclet C k m s p := by
  cases h with
  | localValueAssign => exact .localValueAssign
  | storageFieldRead_unfold_rightFst hn => exact .storageFieldRead_unfold_rightFst hn
  | ifElseSplit => exact .ifElseSplit

/-! What the macro inserted, shown with the notation off: the weakening
`v.there`, the fresh alias as `Idx.here`, the pop `Ext.refl.push`, and the
side condition. -/

/--
info: @Taclet.storageFieldRead_unfold_rightFst : ∀ {C : Contract} {k : Nat} {m : Modality} {x : Ctx} {x_1 : PrimTy}
  {v : Idx x (LTy.val x_1)} {x_2 : Name} {nsp : SPath C x (Ty.struct x_2)} {fld : Name}
  {hfld : C.fieldType x_2 fld = some (Ty.prim x_1)},
  autoParam (nsp.isSimple = false) sideCond →
    Taclet C k m (Stmt.assignLocal v (Val.read (Loc.field nsp fld hfld)))
      (Premise.unfold
        (Prog.cons (Stmt.declStorage (RefTy.struct x_2) (Var.fresh "sp" k) (some (ARhs.path nsp)))
          (Prog.cons (Stmt.assignLocal v.there (Val.read (Loc.field (SPath.alias Idx.here) fld hfld))) Prog.nil))
        Ext.refl.push)
-/
#guard_msgs in
set_option pp.sol.dl false in
#check @Taclet.storageFieldRead_unfold_rightFst

end Solidity.Core.Schema
