import Solidity.Correctness.Lowering.Total.Decode.Callee.Parameters
import Solidity.Correctness.Lowering.Total.Decode.WithExpr

/-!
# Ordinary contract-function declaration assembly

Identity, visibility and mutability are explicit inputs from declaration
selection; this component does not guess them from erased model metadata.
It combines original parameter/return lists, original body spelling and ordered
modifier invocations. Modifier definitions, inheritance, metadata selection,
constructors and the complete unit/output producer remain separate work.
Unsupported bodies and signatures still return `none`; no admission or
universal-coverage statement is changed.
-/
namespace Solidity.Correctness.Lowering.Total.Decode.Callee

open Source (Syn)

/-- Modifier invocations in declaration order, with registered expression
spelling for their original arguments. Invocations are preserved; modifier
definitions require separate translation. -/
def modifiers (T : Tables) (R : CallSpellExt.Registry) :
    List ModApp → Option (Syn (.list .modInv))
  | [] => some .nil
  | m :: ms => do
      pure (.cons (.modInv ⟨m.name, []⟩ (.some (.positional (← Calls.exprs T R m.args))))
        (← modifiers T R ms))

/-- Exact ordered correspondence of modifier names and argument spellings.
This says nothing about modifier definition or execution correspondence. -/
inductive ModifierSpelling (T : Tables) (R : CallSpellExt.Registry) :
    List ModApp → Syn (.list .modInv) → Prop where
  | nil : ModifierSpelling T R [] .nil
  | cons {m ms args rest} : CallSpellExt.ExprsX T R m.args args →
      ModifierSpelling T R ms rest →
      ModifierSpelling T R (m :: ms)
        (.cons (.modInv ⟨m.name, []⟩ (.some (.positional args))) rest)

theorem modifiers_spelled (T : Tables) (R : CallSpellExt.Registry) :
    ∀ ms out, modifiers T R ms = some out → ModifierSpelling T R ms out := by
  intro ms
  induction ms with
  | nil => intro out h; cases h; exact .nil
  | cons m ms ih =>
      intro out h
      simp only [modifiers, Option.bind_eq_bind, Option.pure_def,
        Option.bind_eq_some_iff, Option.some.injEq] at h
      obtain ⟨args, ha, rest, hr, rfl⟩ := h
      exact .cons (Calls.exprs_spellsX _ _ ha) (ih _ hr)

/-- A declaration of the selected ordinary function. Header selection and
virtual/override reconstruction are not provided here; this spells a concrete
non-virtual implementation with the supplied identity and call header. -/
def functionDecl (T : Tables) (R : CallSpellExt.Registry)
    (scope name : String) (vis : Option Source.Visibility)
    (mutability : Option Source.Mutability) (d : FunDecl) : Option Source.Decl := do
  let (ps, rs) ← signature d
  let ms ← modifiers T R d.mods
  let body ← Tables.WithExpr.items T (Calls.expr T R) .body d.body
  pure ⟨.function, name, some scope, false,
    .function (.ident name) ps vis mutability ms false none rs (.some (.block body))⟩

/-- Successful assembly preserves the exact declaration shape, original
body spelling, all modifier invocations and the actual Source frame with its
ordered table-corresponding parameter and return slots. No resolved-body or
semantic agreement is inferred merely from successful assembly. -/
theorem functionDecl_faithful (T : Tables) (R : CallSpellExt.Registry)
    (scope name : String) (vis : Option Source.Visibility)
    (mutability : Option Source.Mutability) (d : FunDecl) (out : Source.Decl)
    (h : functionDecl T R scope name vis mutability d = some out) (E : Source.Env) :
    ∃ ps rs ms body f,
      signature d = some (ps, rs) ∧ ModifierSpelling T R d.mods ms ∧
      Tables.WithExpr.items T (Calls.expr T R) .body d.body = some body ∧
      out = ⟨.function, name, some scope, false,
        .function (.ident name) ps vis mutability ms false none rs (.some (.block body))⟩ ∧
      out.frame? E = some f ∧
      f.names = d.params.map (fun p => some p.1) ∧
      f.rnames = d.rets.map (fun p => some p.1) ∧
      Slots d.widths d.params f.ps ∧ Slots d.widths d.rets f.rs ∧
      f.body = body ∧ f.msgValue = Source.readsValue vis mutability ∧ f.inModifier = false := by
  simp only [functionDecl, Option.bind_eq_bind, Option.pure_def,
    Option.bind_eq_some_iff, Option.some.injEq] at h
  obtain ⟨⟨ps, rs⟩, hs, ms, hm, body, hb, rfl⟩ := h
  obtain ⟨f, hf, pn, rn, pts, rts, fb, fv, fm⟩ :=
    signature_frame hs E (some scope) body (Source.readsValue vis mutability) false
  exact ⟨ps, rs, ms, body, f, hs, modifiers_spelled T R _ _ hm, hb,
    rfl, hf, pn, rn, pts, rts, fb, fv, fm⟩

end Solidity.Correctness.Lowering.Total.Decode.Callee
