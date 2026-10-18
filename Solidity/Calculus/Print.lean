import Solidity.Calculus.PrintStmt
import Solidity.Calculus.Quote
import Solidity.Syntax.Quote

/-!
# Printing scoped formulas

A formula of `Calculus/Fml.lean` printed in the `dl{ … }` notation of
`Calculus/RuleSyntax.lean`: the KeY text.
Terms and updates are quoted as they are (`Tm.quote`, `Upd.quote`,
`Calculus/Quote.lean`) and printed by `Calculus/PrintTerm.lean`'s printers
of the scoped terms (`ppTermS`, `ppUpdS`); a block is quoted as it is
(`Prog.quoteShared`) and printed by `Calculus/PrintStmt.lean`'s printer of
the scoped syntax (`ppProgS`); each with the names of its context.  This
module only walks the formula, with the names of its context beside it.

What has no KeY text prints as KeY would have it: a frame's statements
follow the program, a block's end is `}`, and a capture's end, a pop of an
update and a hidden binder (`Fml.bind`) print as nothing.

The contract is passed as the expression `c` that names it
(`mkConst ``StandardExample`), as the quoters take it.
-/

namespace Solidity

open Lean Meta

variable {C : Contract} [FreshNames] (c : Lean.Expr)

/-- One piece of notation on one line. -/
def fmtCat (cat : Lean.Name) (stx : Lean.Syntax) : MetaM String := do
  return (← PrettyPrinter.ppCategory cat stx).pretty 100000

def Tm.show {Γ : Ctx} {s : Srt} (ns : List Var) (t : Tm C Γ s) : MetaM String := do
  let new ← fmtCat `dl_term (← Delab.ppTermS (ns.map toExpr) (t.quote c))
  return new

/-- Whether an update has an element: else it prints as nothing (pops and
drops only). -/
def Upd.hasElem {Γ : Ctx} : {Δ : Ctx} → Upd C Γ Δ → Bool
  | _, .nil => false
  | _, .snoc .. | _, .decl .. => true
  | _, .pop U _ => U.hasElem
  | _, .drop U _ => U.hasElem

/-- An update read where the locals are named `ns`, printed. -/
def Upd.show {Γ Δ : Ctx} (ns : List Var) (U : Upd C Γ Δ) : MetaM String := do
  let new ← fmtCat `dl_upd (← Delab.ppUpdS (ns.map toExpr) (U.quote c)).1
  return new

/-- The statements of a block read where the locals are named `ns`, each
with its `;`. -/
def showStmts {Γ Γ' : Ctx} (ns : List Var) (P : Prog C Γ Γ') : MetaM (List String) := do
  let (Pe, _, _) := P.quoteShared c
  match ← (Delab.ppProgS (ns.map toExpr) Pe).run {} with
  | some out => out.toList.mapM fun s => return (← fmtCat `sol_stmt s.raw) ++ ";"
  | none => return ["‹stmt›;"]

/-- The items of a modality: the program's statements, then each frame's,
`}` where a block ends. -/
def Frames.items (ns : List Var) : {Γ Γ₀ : Ctx} → Frames C Γ Γ₀ → MetaM (List String)
  | _, _, .nil => return []
  | _, _, .seq ω κ => return (← showStmts c ns ω) ++ (← κ.items (ω.outNames ns))
  | _, _, .pop .block h κ => return "}" :: (← κ.items (ns.drop h.depth))
  | _, _, .pop .capture h κ => κ.items (ns.drop h.depth)
  | _, _, .drop h κ => κ.items (h.names ns)

/-- The formula as it prints: the one under an update that prints as nothing
(only pops) or under a hidden binder. -/
def Fml.visible : {Γ : Ctx} → Fml C Γ → (Δ : Ctx) × Fml C Δ
  | Γ, φ@(.upd _ U ψ) => if U.hasElem then ⟨Γ, φ⟩ else Fml.visible ψ
  | _, .bind _ _ _ φ => Fml.visible φ
  | Γ, φ => ⟨Γ, φ⟩

/-- Whether two terms read where the locals are named `ns` are the same
text (`Delab.eqTmS`). -/
def Tm.sameAt {Γ : Ctx} {s s' : Srt} (ns : List Var) (a : Tm C Γ s) (a' : Tm C Γ s') :
    MetaM Bool := do
  let ns' := ns.map toExpr
  let new ← Delab.eqTmS ns' (a.quote c) ns' (a'.quote c)
  return new

/-- A connective, which the operand of `¬`, `{U}` and `⟨P⟩` parenthesises. -/
def Fml.isConnective {Γ : Ctx} (φ : Fml C Γ) : Bool :=
  match (Fml.visible φ).2 with
    | .and .. | .imp .. | .all .. => true
    | _ => false

/-- The literal `true`. -/
def Tm.isTrue {Γ : Ctx} : {s : Srt} → Tm C Γ s → Bool
  | _, .app0 o => match o with
    | @Op0.lit _ .bool v => show Bool from v
    | _ => false
  | _, _ => false

/-- A binary operator's application, its operator and operands. -/
def Tm.binopParts? {Γ : Ctx} : {s : Srt} → Tm C Γ s →
    Option (BinOp × (q : PrimTy) × Tm C Γ (.val q) × Tm C Γ (.val q))
  | _, .app2 o x y => match o, x, y with
    | .binop op _, l, r => some (op, ⟨_, l, r⟩)
    | _, _, _ => none
  | _, _ => none

/-- `a < b` as a specification writes it, `a < b = true`:
the operator and the operands. -/
def cmpParts? {Γ : Ctx} {s s' : Srt} (a : Tm C Γ s) (b : Tm C Γ s') :
    Option (String × (q : PrimTy) × Tm C Γ (.val q) × Tm C Γ (.val q)) := do
  guard (Tm.isTrue b)
  let (op, ⟨q, l, r⟩) ← Tm.binopParts? a
  let sym ← match op with
    | .lt => some "<"
    | .le => some "<="
    | .gt => some ">"
    | .ge => some ">="
    | _ => none
  pure (sym, ⟨q, l, r⟩)

def primName : PrimTy → String
  | .uint => "uint"
  | .int => "int"
  | .bool => "bool"

/-- `s` in parentheses where its precedence `p` is below `min`: what Lean's
parenthesizer does to the `dl_fml` syntax (`RuleSyntax.lean`'s grammar). -/
def paren (s : String × Nat) (min : Nat) : String := if s.2 < min then s!"({s.1})" else s.1

/-- The formula and its precedence (`max` is 1024), the names of its context
`ns` beside it.  Where `RuleSyntax.lean`'s `ppFml` parenthesises a
connective explicitly, so does this; the rest is the grammar's. -/
partial def Fml.showP {Γ : Ctx} (ns : List Var) (φ : Fml C Γ) : MetaM (String × Nat) := do
  let arg {Δ : Ctx} (ms : List Var) (ψ : Fml C Δ) (min : Nat) : MetaM String := do
    let s ← Fml.showP ms ψ
    return if ψ.isConnective then s!"({s.1})" else paren s min
  let sub {Δ : Ctx} (ms : List Var) (ψ : Fml C Δ) (min : Nat) : MetaM String :=
    return paren (← Fml.showP ms ψ) min
  match φ with
  | .tt => return ("true", 1024)
  | .not .tt => return ("false", 1024)
  | .not (.and (.not a) (.not b)) => return (s!"{← sub ns a 31} ∨ {← sub ns b 30}", 30)
  | .not (.all x p (.not a)) => return (s!"∃ {primName p} {x}; {← sub (x :: ns) a 25}", 25)
  | .not ψ => return (s!"¬{← arg ns ψ 50}", 1024)
  | .eq a b =>
    if let some (sym, ⟨_, l, r⟩) := cmpParts? a b then
      return (s!"{← l.show c ns} {sym} {← r.show c ns}", 55)
    return (s!"{← a.show c ns} = {← b.show c ns}", 50)
  | .wellFormed t => return (s!"wt({← t.show c ns})", 1024)
  | .all x p ψ => return (s!"∀ {primName p} {x}; {← sub (x :: ns) ψ 25}", 25)
  | .and ψ χ =>
    if let .imp a b := ψ then
      if let .imp b' a' := χ then
        let iff := a.quote c == a'.quote c && b.quote c == b'.quote c
        if iff then
          return (s!"{← sub ns a 21} ↔ {← sub ns b 21}", 20)
    let r ← if χ matches .imp .. then pure s!"({(← Fml.showP ns χ).1})" else sub ns χ 35
    return (s!"{← arg ns ψ 36} ∧ {r}", 35)
  | .imp ψ χ => return (s!"{← arg ns ψ 26} → {← sub ns χ 25}", 25)
  | .upd _ U ψ =>
    if !U.hasElem then return ← Fml.showP (U.names ns) ψ
    return (s!"{← U.show c ns} {← arg (U.names ns) ψ 50}", 1024)
  | .havoc ψ => return (s!"\{ havoc } {← arg ns ψ 50}", 1024)
  | .anon xs ψ =>
    return (s!"\{ anon({", ".intercalate (xs.map fun x => toString (x.2.name ns))}) } {← arg ns ψ 50}",
      1024)
  | .bind _ x _ ψ => Fml.showP (x :: ns) ψ
  | .modal m P κ ψ =>
    let items := (← showStmts c ns P) ++ (← κ.items c (P.outNames ns))
    let body ← arg (κ.outNames (P.outNames ns)) ψ 50
    let (l, r) := match m with
      | .diamond => ("⟨", "⟩")
      | .box => ("[", "]")
    return (if items.isEmpty then s!"{l} {r} {body}" else s!"{l} {" ".intercalate items} {r} {body}",
      1024)

/-- The formula, the names of its context `ns` beside it. -/
def Fml.show {Γ : Ctx} (ns : List Var) (φ : Fml C Γ) : MetaM String :=
  return (← φ.showP c ns).1

/-! ## Examples -/

section Example

private abbrev SE := StandardExample
private abbrev cSE : Lean.Expr := mkConst ``StandardExample

/-- The formula, printed. -/
def showFml {Γ : Ctx} (ns : List Var) (φ : Fml C Γ) : MetaM Unit := do
  logInfo (← φ.show c ns)

private def x : Var := .user "x"
private def y : Var := .user "y"
private def p : Var := .user "p"
private def lit {Γ : Ctx} (n : Int) (h : PrimTy.uint.inRange n = true := by rfl) :
    Tm SE Γ (.val .uint) := .app0 (.lit (PrimTy.ofLit .uint n h))
private def tru {Γ : Ctx} : Tm SE Γ (.val .bool) := .app0 (.lit (p := .bool) true)
private def pv {Γ : Ctx} {q : PrimTy} (i : Idx Γ (.val q)) : Tm SE Γ (.val q) := .pvV i
private def alice {Γ : Ctx} : SPath SE Γ (.struct "Person") := .loc (.root "alice" rfl)
private def litV {Γ : Ctx} (n : Int) (h : PrimTy.uint.inRange n = true := by rfl) :
    Val SE Γ .uint := .simple (.lit n h)
private def locV {Γ : Ctx} {q : PrimTy} (i : Idx Γ (.val q)) : Val SE Γ q := .simple (.local i)

/-- `{ x := 3 ‖ p := alice.account } x = 3`: two locals declared by the update. -/
private def upd₁ : Fml SE [] :=
  .upd .box ((Upd.nil.decl x (.val (p := .uint) (lit 3))).decl p
      (.path (.app1 (.field (s := "Person") (f := "account") rfl) (.app0 (.root "alice" rfl)))))
    (.eq (pv (.there .here)) (lit 3))

/-- info: { x := 3 ‖ p := alice.account } x = 3 -/
#guard_msgs in #eval showFml cSE [] upd₁

/-- A connective under `∀`, `¬`, `∨`, `∃`, `↔` and a comparison. -/
private def conn₁ : Fml SE [] :=
  .all x .uint (.and
    (.imp (.eq (.app2 (.binop .lt rfl) (pv (q := .uint) .here) (lit 3)) tru) (.not (.and (.not .tt) (.not .ff))))
    (.and (.imp .tt .ff) (.imp .ff .tt)))

/-- info: ∀ uint x; (x < 3 → true ∨ false) ∧ (true ↔ false) -/
#guard_msgs in #eval showFml cSE [] conn₁

/-- A program, scoped: the branch's `y` is not in scope after it. -/
private def prog₁ : Prog SE [] [.val .uint] :=
  .cons (.declLocal .uint x (some (litV 1))) <|
  .cons (.ite (.binop .gt rfl rfl (locV .here) (litV 0))
    (.cons (.declLocal .uint y (some (locV .here))) <|
      .cons (.assignLocal (.there .here) (locV .here)) .nil)
    (.cons .revert .nil)) .nil

/-- info: [ uint x = 1; if (x > 0) {uint y = x;x = y;} else {revert();}; ] x = 1 -/
#guard_msgs in #eval showFml cSE [] (.modal .box prog₁ .nil (.eq (pv .here) (lit 1)))

/-- The branches of `prog₁`'s `if`. -/
private def thn₁ : Prog SE [.val .uint] [.val .uint, .val .uint] :=
  .cons (.declLocal .uint y (some (locV .here))) <| .cons (.assignLocal (.there .here) (locV .here)) .nil
private def els₁ : Prog SE [.val .uint] [.val .uint] := .cons .revert .nil

/-- `x > 0`, as the condition of a goal. -/
private def pos₁ : Fml SE [.val .uint] :=
  .eq (.app2 (.binop .gt rfl) (pv (q := .uint) .here) (lit 0)) tru

/-- `ifElseSplit` on `if (x > 0) …; x = 2;`: each branch ends with a `}`. -/
private def split₁ : Fml SE [.val .uint] :=
  Premise.fml .box (.cons (.assignLocal .here (litV 2)) .nil) .nil (.eq (pv .here) (lit 1))
    (Premise.split .block pos₁ (.not pos₁) thn₁ els₁)

/--
info: (x > 0 → [ uint y = x; x = y; } x = 2; ] x = 1) ∧ (¬x > 0 → [ revert(); } x = 2; ] x = 1)
-/
#guard_msgs in #eval do logInfo (← split₁.show cSE [x])

/-- `T storage sp1 = alice; x = sp1.age;` in place of `x = alice.age;`, its
capture popped after it, invisibly; then the frames left: the pop is an
update that prints as nothing, and the empty modality is gone. -/
private def unfold₁ : Fml SE [.val .uint] :=
  Premise.fml .diamond .nil .nil (.eq (pv .here) (lit 1))
    (Premise.unfold (.cons (.declStorage (.struct "Person") (.fresh "sp" 1) (some (.path alice))) <|
      .cons (.assignLocal (.there .here) (.read (.field (.alias .here) "age" rfl))) .nil)
      (.push .refl))

/-- info: ⟨ Person storage sp1 = alice; x = sp1.age; ⟩ x = 1 -/
#guard_msgs in #eval showFml cSE [x] unfold₁

/-- info: x = 1 -/
#guard_msgs in #eval showFml cSE [.fresh "sp" 1, x]
  (Frames.exit (C := SE) (Γ := [.alias (.struct "Person"), .val .uint]) .diamond
    (.pop .capture (.push .refl) .nil) (.eq (pv .here) (lit 1)))

/-- `uint v = x;` with its initializer dropped (`localValueDeclInitDrop`):
`v = x;` under a hidden binder. -/
private def bind₁ : Fml SE [.val .uint] :=
  Premise.fml .box (.cons (.assignLocal (.there .here) (locV .here)) .nil) .nil
    (.eq (pv (.there .here)) (lit 1))
    (Premise.bind (.user "v") (.val .uint) (.cons (.assignLocal .here (locV (.there .here))) .nil))

/-- info: [ v = x; x = v; ] x = 1 -/
#guard_msgs in #eval showFml cSE [x] bind₁

/-- info: { anon(x) } { havoc } ¬x = 1 -/
#guard_msgs in #eval showFml cSE [x]
  (Fml.anon (C := SE) [⟨_, (.here : Idx [.val .uint] (.val .uint))⟩] (.havoc (.not (.eq (pv .here) (lit 1)))))

end Example

end Solidity
