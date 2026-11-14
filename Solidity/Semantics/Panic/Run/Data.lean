import Solidity.Semantics.Panic.Run.Updates

namespace Solidity.Semantics.Panic.Run

variable {C : Contract} {Γ : Ctx}

def revPart (σ : State C Γ) : RevPart C Γ → EvalResult (List UInt8)
  | .bytes bs => pure bs
  | .sel sig => pure (Semantics.selectorBytes (Semantics.customSelector sig))
  | .word v => do
    let x ← value σ v
    pure (Semantics.wordBytes (PrimTy.toWord x).1.toNat)
  | .mem kind src => do
    let r ← mpath σ (MPath.var src rfl)
    let bs : List UInt8 := (σ.heap.get r).1.map (fun v => UInt8.ofNat v.val.toNat)
    pure (match kind with | .raw => bs | .reason => Semantics.encodeError bs)

/-- `revert(d)`: the parts in order, then a revert with their bytes. -/
def revertData (d : List (RevPart C Γ)) : Step C Γ Γ := fun σ => do
  let bs ← d.mapM (revPart σ)
  .error (match bs.flatten with | [] => .revert | data => .revertWith data)

/-- The writes of a literal's bytes, then `k` (`litWrites`), run. -/
def litWrites {Γ₁ : Ctx} : List UInt8 → Nat → Step C (.mem bytesR :: Γ) Γ₁ →
    Step C (.mem bytesR :: Γ) Γ₁
  | [], _, k => k
  | b :: bs, i, k => if hi : i < 2 ^ 256 then
      seq (assignMem (litLoc i hi) (litSrc b)) (litWrites bs (i + 1) k)
    else k

/-- A literal's bytes allocated, then `k` (`litBytes`), run. -/
def litBytes {Γ₁ : Ctx} (bs : List UInt8) (k : Step C (.mem bytesR :: Γ) Γ₁) : Step C Γ Γ₁ :=
  if hn : bs.length < 2 ^ 256 then
    seq (declMem bytesR (some (.newArr (.lit (bs.length : Int) (PrimTy.inRange_uint_of_lt hn)) rfl))
      rfl) (litWrites bs 0 k)
  else seq (declMem bytesR none rfl) k

/-- Bind catch data from the actual rich self-call outcome, then execute the clause. -/
def catchData {ρ ps Γf Γ₁ : Ctx} (c : ExtCall C Γ) (rets : Binders ρ) (sargs : Args C Γ ps)
    (hs : Ext (ρ ++ ps) Γf) (sbody : Step C (ρ ++ ps) Γf) (self : Bool) (kind : CatchKind)
    (h₁ : Ext (.mem bytesR :: Γ) Γ₁) (body : Step C (.mem bytesR :: Γ) Γ₁) : Step C Γ Γ :=
  fun σ => do
    let d ← catchBytes c rets sargs hs sbody self σ
    match kind.decode d with
    | none => .error .revert
    | some bs => (litBytes bs body σ).map fun o => ⟨o.st.drop ((Ext.push .refl).trans h₁), o.ext⟩

end Solidity.Semantics.Panic.Run
