import SolidityBridge.ExternalEvm.Assembly.Layout
namespace Solidity.Evm.External.Assembly

/-- Image data are fixed by the existing emitter/span/target functions;
all remaining fields are proof-irrelevant certification evidence. -/
theorem Image.unique {code : List Instr} {base : Nat} (a b : Image code base) : a = b := by
  have hb := Option.some.inj (a.emitted.symm.trans b.emitted)
  have hs := Option.some.inj (a.span_eq.symm.trans b.span_eq)
  have hr := Option.some.inj (a.targets_eq.symm.trans b.targets_eq)
  cases a
  cases b
  cases hb
  cases hs
  cases hr
  rfl

/-- The raw layout validator accepts an already proved image. This does not
assert syntactic coverage or completeness of execution/scanner certification. -/
theorem Image.assemble_eq {code : List Instr} {base : Nat} (image : Image code base) :
    assemble code base = some image := by
  have hd : ∀ l : Label code, (address code base l).any
      (fun n => image.bytes[n - base]? == some 0x5b) = true := by
    intro l
    obtain ⟨n, ha, hb⟩ := image.destinations l
    simp only [ha, Option.any_some, hb, BEq.rfl]
  unfold Solidity.Evm.External.Assembly.assemble
  split
  next size bytes refs hs he ht =>
    have hsize : size = image.size := Option.some.inj (hs.symm.trans image.span_eq)
    have hbytes : bytes = image.bytes := Option.some.inj (he.symm.trans image.emitted)
    have hrefs : refs = image.refs := Option.some.inj (ht.symm.trans image.targets_eq)
    subst size
    subst bytes
    subst refs
    simp only [dif_pos image.length_eq, dif_pos image.fits, dif_pos hd, dif_pos image.validRefs]
  next impossible =>
    exact False.elim (impossible image.size image.bytes image.refs image.span_eq image.emitted image.targets_eq)

end Solidity.Evm.External.Assembly
