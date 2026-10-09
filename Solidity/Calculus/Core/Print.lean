import Solidity.Calculus.Core.Fml
import Solidity.Calculus.RuleSyntax
import Solidity.Calculus.NFmlQuote

/-!
# Printing scoped formulas

A formula of `Calculus/Core/Fml.lean` printed as the `dl{ … }` printers of
`Calculus/RuleSyntax.lean` print its erasure (`Fml.eraseS`): the same KeY text.
Terms, updates and statements are printed by those printers themselves, on
the erased part quoted (`Calculus/NFmlQuote.lean`); this module only walks the
formula, with the names of its context beside it.

What erasure loses prints as KeY would have it: a frame's statements follow
the program, a block's end is `}`, and a capture's end, a pop of an update
and a hidden binder (`Fml.bind`) print as nothing.

The contract is passed as the expression `c` that names it
(`mkConst ``StandardExample`), as the quoters take it.
-/

namespace Solidity.Core

open Lean Meta
open Solidity (ppTerm ppUpd ppProg?)

variable {C : Contract} [FreshNames] (c : Lean.Expr)

/-- One piece of notation on one line. -/
def fmtCat (cat : Lean.Name) (stx : Lean.Syntax) : MetaM String := do
  return (← PrettyPrinter.ppCategory cat stx).pretty 100000

def Tm.show {Γ : Ctx} (ns : List Var) (t : Tm C Γ .val) : MetaM String := do
  fmtCat `dl_term (← ppTerm (Surface.Tm.quote c (t.erase ns)))

/-- The statements of an erased block, each with its `;`. -/
def showStmts (ss : List (Solidity.Surface.Stmt C)) : MetaM (List String) := do
  match ← ppProg? (Solidity.Surface.Prog.quote c ss) with
  | some out => out.toList.mapM fun s => return (← fmtCat `sol_stmt s.raw) ++ ";"
  | none => return ss.map fun _ => "‹stmt›;"

/-- The items of a modality: the program's statements, then each frame's,
`}` where a block ends. -/
def Frames.items (ns : List Var) : {Γ Γ₀ : Ctx} → Frames C Γ Γ₀ → MetaM (List String)
  | _, _, .nil => return []
  | _, _, .seq ω κ => return (← showStmts c (ω.erase ns)) ++ (← κ.items (ω.outNames ns))
  | _, _, .pop .block h κ => return "}" :: (← κ.items (ns.drop h.depth))
  | _, _, .pop .capture h κ => κ.items (ns.drop h.depth)
  | _, _, .drop h κ => κ.items (h.names ns)

/-- The formula as it prints: the one under an update that prints as nothing
(only pops) or under a hidden binder. -/
def Fml.visible : {Γ : Ctx} → Fml C Γ → (Δ : Ctx) × Fml C Δ
  | Γ, φ@(.upd _ U ψ) => if (U.erase []).isEmpty then Fml.visible ψ else ⟨Γ, φ⟩
  | _, .bind _ _ _ φ => Fml.visible φ
  | Γ, φ => ⟨Γ, φ⟩

/-- `a = b` as `Fml.eqD` writes it: `defined(a) ∧ defined(b) ∧ a ≐ b`. -/
def Fml.eqDParts? {Γ : Ctx} (ns : List Var) : Fml C Γ → Option (Tm C Γ .val × Tm C Γ .val)
  | .and (.defined a) (.and (.defined b) (.eq a' b')) =>
    if (a.erase ns).quote c == (a'.erase ns).quote c && (b.erase ns).quote c == (b'.erase ns).quote c
    then some (a, b) else none
  | _ => none

/-- A connective, which the operand of `¬`, `{U}` and `⟨P⟩` parenthesises. -/
def Fml.isConnective {Γ : Ctx} (ns : List Var) (φ : Fml C Γ) : Bool :=
  (φ.eqDParts? c ns).isNone &&
    match (Fml.visible φ).2 with
    | .and .. | .imp .. | .all .. => true
    | _ => false

/-- `a < b` as a specification writes it, `defined(a < b) ∧ … ∧ a < b ≐ true`:
the operator and the operands. -/
def cmpParts? {Γ : Ctx} : Tm C Γ .val → Tm C Γ .val → Option (String × Tm C Γ .val × Tm C Γ .val)
  | .app2 (.binop op _) l r, .app0 (.lit (.bool true)) =>
    match op with
    | .lt => some ("<", l, r)
    | .le => some ("<=", l, r)
    | .gt => some (">", l, r)
    | .ge => some (">=", l, r)
    | _ => none
  | _, _ => none

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
    return if ψ.isConnective c ms then s!"({s.1})" else paren s min
  let sub {Δ : Ctx} (ms : List Var) (ψ : Fml C Δ) (min : Nat) : MetaM String :=
    return paren (← Fml.showP ms ψ) min
  match φ with
  | .tt => return ("true", 1024)
  | .not .tt => return ("false", 1024)
  | .not (.and (.not a) (.not b)) => return (s!"{← sub ns a 31} ∨ {← sub ns b 30}", 30)
  | .not (.all x p (.not a)) => return (s!"∃ {primName p} {x}; {← sub (x :: ns) a 25}", 25)
  | .not ψ => return (s!"¬{← arg ns ψ 50}", 1024)
  | .eq a b => return (s!"{← a.show c ns} ≐ {← b.show c ns}", 50)
  | .defined t => return (s!"defined({← t.show c ns})", 1024)
  | .all x p ψ => return (s!"∀ {primName p} {x}; {← sub (x :: ns) ψ 25}", 25)
  | .and ψ χ =>
    if let some (a, b) := φ.eqDParts? c ns then
      if let some (sym, l, r) := cmpParts? a b then
        return (s!"{← l.show c ns} {sym} {← r.show c ns}", 55)
      return (s!"{← a.show c ns} = {← b.show c ns}", 50)
    if let .imp a b := ψ then
      if let .imp b' a' := χ then
        if (a.erase ns).quote c == (a'.erase ns).quote c &&
            (b.erase ns).quote c == (b'.erase ns).quote c then
          return (s!"{← sub ns a 21} ↔ {← sub ns b 21}", 20)
    let r ← if χ matches .imp .. then pure s!"({(← Fml.showP ns χ).1})" else sub ns χ 35
    return (s!"{← arg ns ψ 36} ∧ {r}", 35)
  | .imp ψ χ => return (s!"{← arg ns ψ 26} → {← sub ns χ 25}", 25)
  | .upd _ U ψ =>
    let U' := U.erase ns
    if U'.isEmpty then return ← Fml.showP (U.names ns) ψ
    return (s!"{← fmtCat `dl_upd (← ppUpd (Surface.Upd.quote c U'))} {← arg (U.names ns) ψ 50}",
      1024)
  | .havoc ψ => return (s!"\{ havoc } {← arg ns ψ 50}", 1024)
  | .anon xs ψ =>
    return (s!"\{ anon({", ".intercalate (xs.map fun x => toString (x.2.name ns))}) } {← arg ns ψ 50}",
      1024)
  | .bind _ x _ ψ => Fml.showP (x :: ns) ψ
  | .modal m P κ ψ =>
    let items := (← showStmts c (P.erase ns)) ++ (← κ.items c (P.outNames ns))
    let body ← arg (κ.outNames (P.outNames ns)) ψ 50
    let (l, r) := match m with
      | .diamond => ("⟨", "⟩")
      | .box => ("[", "]")
    return (if items.isEmpty then s!"{l} {r} {body}" else s!"{l} {" ".intercalate items} {r} {body}",
      1024)

/-- The formula, the names of its context `ns` beside it. -/
def Fml.show {Γ : Ctx} (ns : List Var) (φ : Fml C Γ) : MetaM String :=
  return (← φ.showP c ns).1

/-! ## Examples

Each prints as its erasure does (`legacyShow`, the `dl{ … }` printer of
`RuleSyntax.lean` on `Fml.eraseS`), except where erasure loses a block's end. -/

section Example

open Solidity (ppFml)

private abbrev SE := StandardExample
private abbrev cSE : Lean.Expr := mkConst ``StandardExample

/-- `Update.lean`'s formula as written, as `RuleSyntax.lean` prints it. -/
def legacyShow (φ : Solidity.Surface.Fml C) : MetaM String := do
  fmtCat `dl_fml (← ppFml (Solidity.Surface.Fml.quote c φ))

/-- The formula, checked to print as its erasure (`Fml.eraseS`). -/
def showSame {Γ : Ctx} (ns : List Var) (φ : Fml C Γ) : MetaM Unit := do
  let a ← φ.show c ns
  let b ← legacyShow c (φ.eraseS ns)
  unless a == b do throwError "prints\n{a}\nbut its erasure prints\n{b}"
  logInfo a

private def x : Var := .user "x"
private def y : Var := .user "y"
private def p : Var := .user "p"
private def lit {Γ : Ctx} (n : Int) : Tm SE Γ .val := .app0 (.lit (.int n))
private def tru {Γ : Ctx} : Tm SE Γ .val := .app0 (.lit (.bool true))
private def pv {Γ : Ctx} {q : PrimTy} (i : Idx Γ (.val q)) : Tm SE Γ .val := .pvV i
private def alice {Γ : Ctx} : SPath SE Γ (.struct "Person") := .loc (.root "alice" rfl)
private def litV {Γ : Ctx} (n : Int) (h : PrimTy.uint.inRange n = true := by rfl) :
    Val SE Γ .uint := .simple (.lit n h)
private def locV {Γ : Ctx} {q : PrimTy} (i : Idx Γ (.val q)) : Val SE Γ q := .simple (.local i)

/-- `{ x := 3 ‖ p := alice.age } x = 3`: two locals declared by the update. -/
private def upd₁ : Fml SE [] :=
  .upd .box ((Upd.nil.decl x (.val (p := .uint) (lit 3))).decl (t := .alias (.struct "Person")) p
      (.path (.app1 (.field "age") rfl (.app0 (.root "alice")))))
    (.eqD (pv (.there .here)) (lit 3))

/-- info: { x := 3 ‖ p := alice.age } x = 3 -/
#guard_msgs in #eval showSame cSE [] upd₁

/-- A connective under `∀`, `¬`, `∨`, `∃`, `↔` and a comparison. -/
private def conn₁ : Fml SE [] :=
  .all x .uint (.and
    (.imp (.eqD (.app2 (.binop .lt .uint) (pv .here) (lit 3)) tru) (.not (.and (.not .tt) (.not .ff))))
    (.and (.imp .tt .ff) (.imp .ff .tt)))

/-- info: ∀ uint x; (x < 3 → true ∨ false) ∧ (true ↔ false) -/
#guard_msgs in #eval showSame cSE [] conn₁

/-- A program, scoped: the branch's `y` is not in scope after it. -/
private def prog₁ : Prog SE [] [.val .uint] :=
  .cons (.declLocal .uint x (some (litV 1))) <|
  .cons (.ite (.binop .gt rfl rfl (locV .here) (litV 0))
    (.cons (.declLocal .uint y (some (locV .here))) <|
      .cons (.assignLocal (.there .here) (locV .here)) .nil)
    (.cons .revert .nil)) .nil

/-- info: [ uint x = 1; if (x > 0) {uint y = x;x = y;} else {revert();}; ] x = 1 -/
#guard_msgs in #eval showSame cSE [] (.modal .box prog₁ .nil (.eqD (pv .here) (lit 1)))

/-- The branches of `prog₁`'s `if`. -/
private def thn₁ : Prog SE [.val .uint] [.val .uint, .val .uint] :=
  .cons (.declLocal .uint y (some (locV .here))) <| .cons (.assignLocal (.there .here) (locV .here)) .nil
private def els₁ : Prog SE [.val .uint] [.val .uint] := .cons .revert .nil

/-- `x > 0`, as the condition of a goal. -/
private def pos₁ : Fml SE [.val .uint] := .eqD (.app2 (.binop .gt .uint) (pv .here) (lit 0)) tru

/-- `ifElseSplit` on `if (x > 0) …; x = 2;`: each branch ends with a `}`,
which erasure loses. -/
private def split₁ : Fml SE [.val .uint] :=
  Premise.fml .box (.cons (.assignLocal .here (litV 2)) .nil) .nil (.eqD (pv .here) (lit 1))
    (Premise.split .block pos₁ (.not pos₁) thn₁ els₁)

/--
info: (x > 0 → [ uint y = x; x = y; } x = 2; ] x = 1) ∧ (¬x > 0 → [ revert(); } x = 2; ] x = 1)
-/
#guard_msgs in #eval do logInfo (← split₁.show cSE [x])

/--
info: (x > 0 → [ uint y = x; x = y; x = 2; ] x = 1) ∧ (¬x > 0 → [ revert(); x = 2; ] x = 1)
-/
#guard_msgs in #eval do logInfo (← legacyShow cSE (split₁.eraseS [x]))

/-- `T storage sp1 = alice; x = sp1.age;` in place of `x = alice.age;`, its
capture popped after it, invisibly; then the frames left: the pop is an
update that prints as nothing, and the empty modality is gone. -/
private def unfold₁ : Fml SE [.val .uint] :=
  Premise.fml .diamond .nil .nil (.eqD (pv .here) (lit 1))
    (Premise.unfold (.cons (.declStorage (.struct "Person") (.fresh "sp" 1) (some (.path alice))) <|
      .cons (.assignLocal (.there .here) (.read (.field (.alias .here) "age" rfl))) .nil)
      (.push .refl))

/-- info: ⟨ Person storage sp1 = alice; x = sp1.age; ⟩ x = 1 -/
#guard_msgs in #eval showSame cSE [x] unfold₁

/-- info: x = 1 -/
#guard_msgs in #eval showSame cSE [.fresh "sp" 1, x]
  (Frames.exit (C := SE) (Γ := [.alias (.struct "Person"), .val .uint]) .diamond
    (.pop .capture (.push .refl) .nil) (.eqD (pv .here) (lit 1)))

/-- `uint v = x;` with its initializer dropped (`localValueDeclInitDrop`):
`v = x;` under a hidden binder. -/
private def bind₁ : Fml SE [.val .uint] :=
  Premise.fml .box (.cons (.assignLocal (.there .here) (locV .here)) .nil) .nil
    (.eqD (pv (.there .here)) (lit 1))
    (Premise.bind (.user "v") (.val .uint) (.cons (.assignLocal .here (locV (.there .here))) .nil))

/-- info: [ v = x; x = v; ] x = 1 -/
#guard_msgs in #eval showSame cSE [x] bind₁

/-- info: { anon(x) } { havoc } ¬defined(x) -/
#guard_msgs in #eval showSame cSE [x]
  (Fml.anon (C := SE) [⟨_, (.here : Idx [.val .uint] (.val .uint))⟩] (.havoc (.not (.defined (pv .here)))))

end Example

end Solidity.Core
