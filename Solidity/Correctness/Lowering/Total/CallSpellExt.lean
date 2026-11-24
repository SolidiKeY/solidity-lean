import Solidity.Correctness.Lowering.Total.Decode.BytesLiteral

/-!
# Loop lowering: call-spelling extensions for the decoder (statement contract)

H1451 (Option B): the landed decoder tables (`Decode.Tables`) and the spelling
relation (`Total.Spells`) stay frozen. They spell every raw call `f(args)` as a
Source call of the identifier `f`, which is wrong for the model's internal call
spellings: `#bytes(…)` (`RawExpr.bytesLit`) is a fixed-bytes literal, not a call.

This module is the additive interface through which a later decoder version can
recognize such spellings. A `CallSpelling` claims one raw callee name and spells
the argument list; a `Registry` is a list of them. Each registered spelling
carries a faithfulness obligation (`CallSpelling.Faithful`): in every reading
context, the Source value of its spelling is the model's value of the raw call.
`Conforms` is the contract an extended decoder must meet. Nothing here changes
the landed decoder, its admission or any goal; integration is later work
(e2b-decoder-rest).

Status: statement-level contract under review. Faithfulness of the first entry
is stated (`bytesFaithfulStatement`), not proved; only trivial bridges are. -/
namespace Solidity.Correctness.Lowering.Total.CallSpellExt

open Source (Syn)

/-- How a registered call and its Source spelling are read: a reading context
(for `#bytes`, the target width of the fixed-bytes conversion), the model's
value of the raw call's arguments in that context, and the Source value of a
spelling in that context. Both readings are relations, so a context in which
the model rejects the call (a failed conversion) imposes nothing. -/
structure Meaning where
  Ctx : Type
  Val : Type
  model : Ctx → List RawExpr → Val → Prop
  source : Ctx → Syn .expr → Val → Prop

/-- A registered call spelling: the raw callee name it claims, the Source
spelling of an argument list (`none`: not this spelling's arguments, a gap),
and the meaning its faithfulness is judged by. The spelling reads the raw
arguments directly; it does not call back into the decoder. -/
structure CallSpelling where
  name : String
  spell : List RawExpr → Option (Syn .expr)
  meaning : Meaning

namespace CallSpelling

/-- The claimed name is internal (`#…`): no user function can be shadowed. -/
def reserved (c : CallSpelling) : Bool := c.name.data.head? == some '#'

/-- **Faithfulness obligation of one registered spelling.** Whatever the
spelling returns has, in every reading context, the model's value of the raw
call with the same arguments. -/
def Faithful (c : CallSpelling) : Prop :=
  ∀ (args : List RawExpr) (t : Syn .expr), c.spell args = some t →
    ∀ (κ : c.meaning.Ctx) (v : c.meaning.Val), c.meaning.model κ args v → c.meaning.source κ t v

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

/-- **Faithfulness obligation of a registry**: one per registered spelling. -/
def Faithful (R : Registry) : Prop := ∀ c ∈ R, c.Faithful

/-- No call anywhere in the expression is claimed. -/
def Unclaimed (R : Registry) (e : RawExpr) : Prop :=
  e.any (fun | .call f _ => R.claims f | _ => false) = false

end Registry

/-- **Contract of an extended expression decoder** `f` over version tables
`T` and registry `R`: a claimed call is spelled by its registered spelling,
and an expression with no claimed call anywhere is spelled as by `T`.
How a claimed call nested inside another construct is spelled is fixed by
the integration that defines `f` (its recursion is the decoder's, not this
interface's). -/
structure Conforms (T : Decode.Tables) (R : Registry) (f : RawExpr → Option (Syn .expr)) :
    Prop where
  claimed : ∀ g args c, R.lookup g = some c → f (.call g args) = c.spell args
  conservative : ∀ e, R.Unclaimed e → f e = T.expr e

/-! ## Trivial bridges -/

/-- The empty registry claims nothing. -/
theorem claims_nil (f : String) : Registry.claims [] f = false := rfl

/-- The empty registry is faithful. -/
theorem faithful_nil : Registry.Faithful [] := nofun

/-- With the empty registry, a version's own expression decoder conforms. -/
theorem conforms_nil (T : Decode.Tables) : Conforms T [] T.expr :=
  ⟨fun _ _ _ h => (nomatch h), fun _ _ => rfl⟩

/-! ## The first registered spelling: fixed-bytes literals

`#bytes(n₁, …, nₖ)` with numeral arguments, spelled by the existing
`Decode.BytesLiteral.decode` (not a copy). The model reads it by the
fixed-bytes conversion `bytesAlign` at the target width, and only where the
result fits that width; Source reads a `hex"…"` literal padded to the width. -/

/-- The fixed-bytes reading: context the target width `n`, value a natural. -/
def bytesMeaning : Meaning where
  Ctx := Nat
  Val := Nat
  model n args v := ∃ bs, (RawExpr.call bytesLitName args).bytesLit? = some bs ∧
    bytesAlign n bs = .ok v ∧ v < 256 ^ n
  source n t v := ∃ bs, t = .lit (.hexStr bs) ∧ Source.bytesNat (Source.fitBytes n bs) = v

/-- The fixed-bytes literal spelling. -/
def bytesSpelling : CallSpelling where
  name := bytesLitName
  spell args := Decode.BytesLiteral.decode (.call bytesLitName args)
  meaning := bytesMeaning

/-- The first registry: fixed-bytes literals only. -/
def registry1 : Registry := [bytesSpelling]

/-- **Statement (to prove after review):** the fixed-bytes spelling is faithful. -/
def bytesFaithfulStatement : Prop := bytesSpelling.Faithful

/-- **Statement (to prove after review):** the first registry is faithful. -/
def registry1FaithfulStatement : Prop := registry1.Faithful

theorem registry1_wellFormed : registry1.WellFormed := by
  refine ⟨by decide, ?_⟩
  intro c hc
  simp only [registry1, List.mem_singleton] at hc
  subst hc
  decide

end Solidity.Correctness.Lowering.Total.CallSpellExt
