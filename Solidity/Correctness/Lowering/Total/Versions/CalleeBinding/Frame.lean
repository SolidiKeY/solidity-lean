import Solidity.Correctness.Lowering.Total.Versions.CalleeBinding.Functions

/-!
# Original declaration metadata in the bound Source frame

The frame is the one returned by whole-unit elaboration and selected-body
binding. Its names, slot types, body spelling and flags follow from the shared
declaration assembler; no independently chosen frame is substituted. Slot
correspondence is the existing primitive relation, not a proof of parameter
values, reference locations, renaming or execution agreement.
-/
namespace Solidity.Correctness.Lowering.Total.Version.CalleeBinding

/-- Bind original parameter/return names, slot correspondence, original body
spelling and retained call-header flags to the actual selected Source frame.
This conditional certificate does not establish universal callee coverage. -/
theorem fromFunctions_frame {T : Decode.Tables} {R : CallSpellExt.Registry}
    {settings : Source.Settings} {scope : String}
    {leadingParts : Source.Syn (.list (.part false))}
    {fs : List (Name × FunDecl)} {index : Nat} {entry : Name × FunDecl} {s : Output}
    (h : fromFunctions T R settings scope leadingParts fs index = some s)
    (hi : fs[index]? = some entry) :
    ∃ source visibility body, entry.2.sourceDecl = some source ∧
      Decode.Callee.ordinaryVisibility source.callable = some visibility ∧
      Decode.Tables.WithExpr.items T (Decode.Calls.expr T R) .body entry.2.body = some body ∧
      s.frame.body = body ∧
      s.frame.names = entry.2.params.map (fun p => some p.1) ∧
      s.frame.rnames = entry.2.rets.map (fun p => some p.1) ∧
      Decode.Callee.Slots entry.2.widths entry.2.params s.frame.ps ∧
      Decode.Callee.Slots entry.2.widths entry.2.rets s.frame.rs ∧
      s.frame.msgValue = Source.readsValue (some visibility)
        (Decode.Callee.sourceMutability source.mutability) ∧
      s.frame.inModifier = false := by
  obtain ⟨_, _, _, hd, _, hb⟩ := fromFunctions_bound h hi
  obtain ⟨source, visibility, hs, hv, ha, _, _⟩ := Decode.Callee.fromMetadata_header hd
  obtain ⟨_, _, _, body, frame, _, _, hbody, _, hf, hn, hrn, hp, hr, hfb, hval, hm⟩ :=
    Decode.Callee.functionDecl_faithful T R scope source.name (some visibility)
      (Decode.Callee.sourceMutability source.mutability) entry.2 s.declaration ha s.source.res.env
  have actual := (fromResolution_bound hb).2.2.2.1
  have he : frame = s.frame := Option.some.inj (hf.symm.trans actual)
  subst frame
  exact ⟨source, visibility, body, hs, hv, hbody, hfb, hn, hrn, hp, hr, hval, hm⟩

end Solidity.Correctness.Lowering.Total.Version.CalleeBinding
