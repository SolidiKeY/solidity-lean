import Solidity.Correctness.Lowering.Total.CalleeResolution

/-!
# Signatures and callability of translated callee entries

Per-entry facts read from a successful `Callee.fromMetadata` translation.
The Source signature is derived from `functionDecl_faithful` and its ordered
`Slots` (`fromMetadata_signature`), which the retained table fixes
(`slots_unique`). Bare-name callability from the generated contract's scope is
the retained role (`callable`, `fromMetadata_callableFrom`): external-only
entries are rejected, private ones callable from their own contract. The Source
argument filter is `Accepts` on the retained parameters (`fromMetadata_fits`).
-/
namespace Solidity.Correctness.Lowering.Total.CalleeSelection

open Decode Decode.Callee
open Source (STy)

variable {T : Tables} {R : CallSpellExt.Registry} {scope : String} {f : FunDecl}
  {out : Source.Decl}

/-- The retained role has an ordinary visibility other than `external`. -/
def callable (f : FunDecl) : Bool :=
  (f.sourceDecl.bind fun s => ordinaryVisibility s.callable).any (· != .external)

/-- The Source overload filter of `Typed.callInternal` and `inferCall`. -/
def fits (Γ : Source.Ctx) (σs : List STy) (d : Source.Decl) : Bool :=
  match d.fnSig Γ.env with
  | some (ps, _) => Source.argsFit Γ.isBase Γ.mapFree σs ps
  | none => false

/-- The retained ordered parameter types accept `σs` under the conversion relation. -/
def Accepts (isBase : Source.DeclName → Source.DeclName → Bool)
    (mapFree : Source.DeclName → Bool) (σs : List STy) (f : FunDecl) : Prop :=
  ∃ ps, Slots f.widths f.params ps ∧ Source.argsFit isBase mapFree σs ps = true

/-- The width table fixes the ordered slot types. -/
theorem slots_unique {widths : List (Name × Nat)} {xs : List (Name × Ty)} {τs τs' : List STy}
    (h : Slots widths xs τs) (h' : Slots widths xs τs') : τs = τs' := by
  induction h generalizing τs' with
  | nil => cases h'; rfl
  | cons hs _ ih =>
      cases h' with
      | cons hs' ht' =>
          obtain ⟨p, e, hp, he, rfl, _⟩ := hs
          obtain ⟨p', e', hp', he', rfl, _⟩ := hs'
          cases hp.symm.trans hp'
          cases he.symm.trans he'
          rw [ih ht']

/-- External-only entries are not callable by bare name. -/
theorem callable_external {s : SourceFunction} {sel : SourceSelection}
    {sig : Option (Fin (2 ^ 32))} (hs : f.sourceDecl = some s)
    (hc : s.callable = .abi .externalFn sel sig) : callable f = false := by
  cases sel <;> simp [callable, hs, hc, ordinaryVisibility]

/-- Private and internal entries are callable from the generated contract. -/
theorem callable_local {s : SourceFunction} {v : SourceLocalVisibility}
    (hs : f.sourceDecl = some s) (hc : s.callable = .local v) (hv : v ≠ .freeFn) :
    callable f = true := by
  cases v <;> simp_all [callable, ordinaryVisibility]

/-- The Source signature of a translated entry, in any environment: its
parameter and return types are the ordered slots of the retained tables. -/
theorem fromMetadata_signature (h : fromMetadata T R scope f = some out) (E : Source.Env) :
    ∃ source vis ps rs, f.sourceDecl = some source ∧
      ordinaryVisibility source.callable = some vis ∧ out.name = source.name ∧
      out.scope = some scope ∧ out.kind = .function ∧ out.fnVis = some vis ∧
      out.fnSig E = some (ps, rs) ∧ Slots f.widths f.params ps ∧ Slots f.widths f.rets rs := by
  obtain ⟨source, vis, hs, hv, hf, hn, hsc⟩ := fromMetadata_header h
  obtain ⟨ps, rs, _, _, fr, _, _, _, he, hfr, _, _, hps, hrs, _⟩ :=
    functionDecl_faithful T R scope source.name (some vis)
      (sourceMutability source.mutability) f out hf E
  subst he
  refine ⟨source, vis, fr.ps, fr.rs, hs, hv, hn, hsc, rfl, rfl, ?_, hps, hrs⟩
  simp only [Source.Decl.frame?, Source.Frame.mk?] at hfr
  simp only [Source.Decl.fnSig]
  cases ha : ps.tys E (some scope) .memory <;> cases hr : rs.tys E (some scope) .memory <;>
    simp only [ha, hr, reduceCtorEq, Option.some.injEq] at hfr ⊢
  subst hfr
  rfl

/-- The Source visibility filter on a translated entry, from the generated
contract's scope, is the retained callable role. -/
theorem fromMetadata_callableFrom (h : fromMetadata T R scope f = some out) :
    (out.kind == .function && out.callableFrom (some scope)) = callable f := by
  obtain ⟨source, vis, _, _, hs, hv, _, hsc, hk, hvis, _⟩ :=
    fromMetadata_signature h { decls := [] }
  cases vis <;> simp [Source.Decl.callableFrom, hvis, hsc, hk, callable, hs, hv]

/-- The Source argument filter on a translated entry is acceptance by its
retained ordered parameter types. -/
theorem fromMetadata_fits (h : fromMetadata T R scope f = some out) (Γ : Source.Ctx)
    (σs : List STy) : fits Γ σs out = true ↔ Accepts Γ.isBase Γ.mapFree σs f := by
  obtain ⟨_, _, ps, rs, _, _, _, _, _, _, hsig, hps, _⟩ := fromMetadata_signature h Γ.env
  simp only [fits, hsig]
  exact ⟨fun hfit => ⟨ps, hps, hfit⟩, fun ⟨ps', hps', hfit⟩ => slots_unique hps hps' ▸ hfit⟩

end Solidity.Correctness.Lowering.Total.CalleeSelection
