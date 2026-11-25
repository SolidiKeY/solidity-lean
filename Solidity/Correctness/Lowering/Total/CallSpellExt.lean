import Solidity.Correctness.Lowering.Total.Decode.BytesLiteral
import Solidity.Correctness.Lowering.Total.Spells

/-!
# Loop lowering: call-spelling extensions for the decoder (statement contract)

H1451 (Option B): the landed decoder tables (`Decode.Tables`) and the spelling
relation (`Total.Spells`) stay frozen. They spell every raw call `f(args)` as a
Source call of the identifier `f`, which is wrong for the model's internal call
spellings: `#bytes(…)` (`RawExpr.bytesLit`) is a fixed-bytes literal, not a call.

This module is the additive interface through which a later decoder version can
recognize such spellings. A `CallSpelling` claims one raw callee name and spells
the argument list; a `Registry` is a list of them. Each registered spelling
carries a faithfulness obligation (`CallSpelling.Faithful M`): in every reading
context, the Source value of its spelling is the model's value of the raw call.
The readings are one `Meaning` shared by every entry (H1455, Option B): an
entry cannot choose how it is judged. Binding that meaning to
`SemanticBoundary.relates` is a later step; until then every faithfulness
statement here is open, for an arbitrary shared meaning.
`Conforms` (node level) and `ConformsX` (the v2 spelling relation `ExprX`,
next to the frozen v1 `Spells.ExprT`) are the contract an extended decoder
must meet. Nothing here changes
the landed decoder, its admission or any goal; integration is later work
(e2b-decoder-rest).

Status: statement-level contract. Faithfulness of the first entry is stated
(`bytesFaithfulStatement`), not proved; only trivial bridges are. -/
namespace Solidity.Correctness.Lowering.Total.CallSpellExt

open Source (Syn)

/-- The shared reading of every registered call and its Source spelling: a
reading context (for `#bytes`, at least the target width of the fixed-bytes
conversion), the model's value of a raw expression in that context, and the
Source value of a Source expression in that context. Both readings are
relations, so a context in which the model rejects the call (a failed
conversion) imposes nothing. One meaning judges every entry of a registry;
it is to be fixed from `SemanticBoundary.relates` by the binding step. -/
structure Meaning where
  Ctx : Type
  Val : Type
  model : Ctx → RawExpr → Val → Prop
  source : Ctx → Syn .expr → Val → Prop

/-- A registered call spelling: the raw callee name it claims, the Source
spelling of an argument list (`none`: not this spelling's arguments, a gap).
It carries no meaning of its own. The spelling reads the raw arguments
directly; it does not call back into the decoder. -/
structure CallSpelling where
  name : String
  spell : List RawExpr → Option (Syn .expr)

namespace CallSpelling

/-- The claimed name is internal (`#…`): no user function can be shadowed. -/
def reserved (c : CallSpelling) : Bool := c.name.data.head? == some '#'

/-- **Faithfulness obligation of one registered spelling** under the shared
meaning `M`. Whatever the spelling returns has, in every reading context, the
model's value of the raw call `name(args)` with the same arguments. -/
def Faithful (M : Meaning) (c : CallSpelling) : Prop :=
  ∀ (args : List RawExpr) (t : Syn .expr), c.spell args = some t →
    ∀ (κ : M.Ctx) (v : M.Val), M.model κ (.call c.name args) v → M.source κ t v

end CallSpelling

/-- The registered call spellings of a decoder version, first match wins. -/
abbrev Registry := List CallSpelling

namespace Registry

/-- The spelling that claims a raw callee name. -/
def lookup (R : Registry) (f : String) : Option CallSpelling := R.find? (·.name == f)

/-- Whether a raw callee name is claimed. -/
def claims (R : Registry) (f : String) : Bool := (R.lookup f).isSome

/-- Names are distinct and internal. -/
def WellFormed (R : Registry) : Prop :=
  (R.map (·.name)).Nodup ∧ ∀ c ∈ R, c.reserved = true

/-- **Faithfulness obligation of a registry** under the shared meaning `M`:
one per registered spelling, all judged by the same `M`. -/
def Faithful (M : Meaning) (R : Registry) : Prop := ∀ c ∈ R, c.Faithful M

/-- No call anywhere in the expression is claimed. -/
def Unclaimed (R : Registry) (e : RawExpr) : Prop :=
  e.any (fun | .call f _ => R.claims f | _ => false) = false

end Registry

/-- **Contract of an extended expression decoder** `f` over version tables
`T` and registry `R`: a claimed call is spelled by its registered spelling,
and an expression with no claimed call anywhere is spelled as by `T`.
This node-level contract does not pin a claimed call nested inside another
construct; `ConformsX` below does. -/
structure Conforms (T : Decode.Tables) (R : Registry) (f : RawExpr → Option (Syn .expr)) :
    Prop where
  claimed : ∀ g args c, R.lookup g = some c → f (.call g args) = c.spell args
  conservative : ∀ e, R.Unclaimed e → f e = T.expr e

/-! ## Spelling relation v2: claimed calls at any depth

An additive version of the frozen `Spells.ExprT` (v1 is unchanged): the same
rules, except that a call is spelled as a Source call only when its name is
unclaimed, and a claimed call is spelled by its registered spelling. This pins
how a claimed call nested inside another construct is spelled. -/

open Decode (num uintElem intElem) in
mutual
inductive ExprX (T : Decode.Tables) (R : Registry) : RawExpr → Syn .expr → Prop where
  | num (n : Nat) : ExprX T R (.num n) (num n)
  | name (x : String) : ExprX T R (.name x) (.ident x)
  | bool (b : Bool) : ExprX T R (.bool b) (.lit (.bool b))
  | field {e e'} (f : String) : ExprX T R e e' → ExprX T R (.field e f) (.member e' f)
  | index {e e' k k'} : ExprX T R e e' → ExprX T R k k' →
      ExprX T R (.index e k) (.index e' (.some k'))
  | binop {op f a a' b b' t} : Decode.binop op = some f → ExprX T R a a' → ExprX T R b b' →
      t = f a' b' → ExprX T R (.binop op a b) t
  | neg {a a'} : ExprX T R a a' → ExprX T R (.unop .neg a) (.unaryPrefix .neg a')
  | not {a a'} : ExprX T R a a' → ExprX T R (.unop .not a) (.unaryPrefix .not a')
  | bnot {a a'} : ExprX T R a a' → ExprX T R (.unop .bnot a) (.unaryPrefix .bitNot a')
  | toInt {a a'} : ExprX T R a a' → ExprX T R (.unop .toInt a)
      (.call (.elemType intElem (by decide)) (.positional (.cons a' .nil)))
  | toUint {a a'} : ExprX T R a a' → ExprX T R (.unop .toUint a)
      (.call (.elemType uintElem (by decide)) (.positional (.cons a' .nil)))
  | ternary {c c' a a' b b'} : ExprX T R c c' → ExprX T R a a' → ExprX T R b b' →
      ExprX T R (.ternary c a b) (.cond c' a' b')
  | preInc {e e'} : ExprX T R e e' → ExprX T R (.incDec .preInc e) (.unaryPrefix .inc e')
  | preDec {e e'} : ExprX T R e e' → ExprX T R (.incDec .preDec e) (.unaryPrefix .dec e')
  | postInc {e e'} : ExprX T R e e' → ExprX T R (.incDec .postInc e) (.unarySuffix .inc e')
  | postDec {e e'} : ExprX T R e e' → ExprX T R (.incDec .postDec e) (.unarySuffix .dec e')
  /-- An unclaimed call: as in v1. -/
  | call {args args'} (f : String) : R.claims f = false → ExprsX T R args args' →
      ExprX T R (.call f args) (.call (.ident f) (.positional args'))
  /-- A claimed call: by its registered spelling, which reads the raw arguments. -/
  | claimed {f args c t} : R.lookup f = some c → c.spell args = some t →
      ExprX T R (.call f args) t
  | modular {a a' b b' k k'} (op : ModOp) : ExprX T R a a' → ExprX T R b b' →
      ExprX T R k k' → ExprX T R (.modular op a b k)
        (.call (.ident op.toStr) (.positional (.cons a' (.cons b' (.cons k' .nil)))))
  | env {k t} : T.env k = some t → ExprX T R (.env k) t
  | tuple {a a' b b' rest rest'} : ExprX T R a a' → ExprX T R b b' →
      ComponentsX T R rest rest' →
      ExprX T R (.tuple (a :: b :: rest)) (.tuple (.some a') (.cons (.some b') rest'))
  | assign {l l' r r'} : ExprX T R l l' → ExprX T R r r' →
      ExprX T R (.assign l r) (.assign .assign l' r')
  | opAssign {op o l l' r r'} : Decode.assignOp op = some o → ExprX T R l l' →
      ExprX T R r r' → ExprX T R (.opAssign op l r) (.assign o l' r')
inductive ExprsX (T : Decode.Tables) (R : Registry) : List RawExpr → Syn (.list .expr) → Prop where
  | nil : ExprsX T R [] .nil
  | cons {e e' es es'} : ExprX T R e e' → ExprsX T R es es' →
      ExprsX T R (e :: es) (.cons e' es')
inductive ComponentsX (T : Decode.Tables) (R : Registry) :
    List RawExpr → Syn (.list (.opt .expr)) → Prop where
  | nil : ComponentsX T R [] .nil
  | cons {e e' es es'} : ExprX T R e e' → ComponentsX T R es es' →
      ComponentsX T R (e :: es) (.cons (.some e') es')
end

/-- **Full contract of an extended expression decoder**: it returns exactly
the v2 spellings. Implies `Conforms` (`conformsX_conforms_statement`). -/
def ConformsX (T : Decode.Tables) (R : Registry) (f : RawExpr → Option (Syn .expr)) : Prop :=
  ∀ e t, f e = some t ↔ ExprX T R e t

/-- **Statement (to prove after review):** the full contract implies the
node-level one. -/
def conformsX_conforms_statement : Prop :=
  ∀ T R f, ConformsX T R f → Conforms T R f

/-- **Statement (to prove after review):** v2 at the empty registry is v1. -/
def exprX_nil_statement : Prop :=
  ∀ T e t, ExprX T [] e t ↔ Spells.ExprT T e t

/-- **Statement (to prove after review):** on an expression with no claimed
call, v2 is v1. -/
def exprX_unclaimed_statement : Prop :=
  ∀ T R e t, Registry.Unclaimed R e → (ExprX T R e t ↔ Spells.ExprT T e t)

/-! ## Trivial bridges -/

/-- The empty registry claims nothing. -/
theorem claims_nil (f : String) : Registry.claims [] f = false := rfl

/-- The empty registry is faithful under every shared meaning. -/
theorem faithful_nil (M : Meaning) : Registry.Faithful M [] := nofun

/-- With the empty registry, a version's own expression decoder conforms. -/
theorem conforms_nil (T : Decode.Tables) : Conforms T [] T.expr :=
  ⟨fun _ _ _ h => (nomatch h), fun _ _ => rfl⟩

/-! ## The first registered spelling: fixed-bytes literals

`#bytes(n₁, …, nₖ)` with numeral arguments, spelled by the existing
`Decode.BytesLiteral.decode` (not a copy). Its faithfulness is judged by
the shared meaning; the local value facts the binding step can use are
`Decode.BytesLiteral.faithful` and `faithful_checked` (the model's
`bytesAlign`/`toBytesAt` value equals the Source padding of the spelling). -/

/-- The fixed-bytes literal spelling. -/
def bytesSpelling : CallSpelling where
  name := bytesLitName
  spell args := Decode.BytesLiteral.decode (.call bytesLitName args)

/-- The first registry: fixed-bytes literals only. -/
def registry1 : Registry := [bytesSpelling]

/-- **Statement (open until the shared meaning is bound):** the fixed-bytes
spelling is faithful under `M`. -/
def bytesFaithfulStatement (M : Meaning) : Prop := bytesSpelling.Faithful M

/-- **Statement (open until the shared meaning is bound):** the first registry
is faithful under `M`. -/
def registry1FaithfulStatement (M : Meaning) : Prop := registry1.Faithful M

theorem registry1_wellFormed : registry1.WellFormed := by
  refine ⟨by decide, ?_⟩
  intro c hc
  simp only [registry1, List.mem_singleton] at hc
  subst hc
  decide

end Solidity.Correctness.Lowering.Total.CallSpellExt
