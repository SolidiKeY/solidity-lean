import Solidity.Correctness.Lowering.Total.Versions.CalleeBinding

/-!
# Binding a selected declaration to its elaborated Source program

The resolution and declaration are explicit inputs. This component performs
whole-unit Source elaboration and retains the selected body's actual frame and
complete resolved body, including modifiers. Indexed selection also proves
declaration membership. Selecting the declaration corresponding to a model
callee, translating the model contract and establishing coverage remain open.
-/
namespace Solidity.Correctness.Lowering.Total.Version.CalleeBinding

/-- Elaborate the resolution and bind the selected declaration's actual body.
No independently supplied body or derivation can replace the elaborator result. -/
def fromResolution (res : Source.Resolution) (d : Source.Decl) : Option Output := do
  let s ← Source.elaborate res
  let f ← d.frame? s.res.env
  let b ← Source.elabBody s.res.env d
  pure ⟨s, d, f, b.val⟩

/-- Source's successful whole-unit elaboration uses its canonical body table. -/
private theorem elaborate_result {res : Source.Resolution} {s : Source.Elaborated}
    (h : Source.elaborate res = some s) :
    s.res = res ∧ ∀ d, s.prog.body d = (Source.elabBody s.res.env d).map Subtype.val := by
  unfold Source.elaborate at h
  split at h
  · cases h
    exact ⟨rfl, fun _ => rfl⟩
  · cases h

/-- The output retains the selected declaration, its actual frame, and the
complete body in both the elaborator result and program table. Names, original
body spelling, declaration membership and model semantics require their own
translation certificates; successful binding does not imply those facts. -/
theorem fromResolution_bound {res : Source.Resolution} {d : Source.Decl} {s : Output}
    (h : fromResolution res d = some s) :
    s.declaration = d ∧ s.source.res = res ∧ Source.elaborate res = some s.source ∧
    d.frame? s.source.res.env = some s.frame ∧
    s.source.prog.body d = some s.body ∧
    (Source.elabBody s.source.res.env d).map Subtype.val = some s.body := by
  simp only [fromResolution, Option.bind_eq_bind, Option.pure_def,
    Option.bind_eq_some_iff, Option.some.injEq] at h
  obtain ⟨source, hs, frame, hf, body, hb, rfl⟩ := h
  obtain ⟨hr, hp⟩ := elaborate_result hs
  have hp := hp d
  rw [hb] at hp
  exact ⟨rfl, hr, hs, hf, hp, by rw [hb]; rfl⟩

/-- Select from the actual declaration table before binding the body. An
out-of-range index, absent body or failed unit elaboration returns `none`. -/
def fromResolutionAt (res : Source.Resolution) (index : Nat) : Option Output := do
  let d ← res.env.decls[index]?
  fromResolution res d

/-- Indexed selection proves membership and retains the exact selected index.
This does not identify which model callee the declaration represents. -/
theorem fromResolutionAt_member {res : Source.Resolution} {index : Nat} {s : Output}
    (h : fromResolutionAt res index = some s) :
    res.env.decls[index]? = some s.declaration ∧
    s.declaration ∈ s.source.res.env.decls ∧
    fromResolution res s.declaration = some s := by
  simp only [fromResolutionAt, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨d, hd, hs⟩ := h
  obtain ⟨he, hr, _⟩ := fromResolution_bound hs
  subst d
  exact ⟨hd, hr.symm ▸ List.mem_of_getElem? hd, hs⟩

end Solidity.Correctness.Lowering.Total.Version.CalleeBinding
